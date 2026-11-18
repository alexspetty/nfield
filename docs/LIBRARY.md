# libnfield C API

libnfield performs exact finite collision calculations inside a C program.
Supply your own rational source, select reset masses, and read the resulting
source, complement, energies and ordered work through ordinary function calls.
The prime-square forest interface also returns each clock's contribution to
the sampling defect. Core API functions do not print or launch processes.

This is library version **1.0.0**, with **C API version 1**. Its public contract
is the installed `nfield/core.h`, `nfield/collision.h` and umbrella
`nfield/nfield.h` headers. The first module covers source selection and
prime-square forests. The additional `<nfield/research.h>` profile exposes existing calculation
and rendering interfaces across other modules; see [RESEARCH_LIBRARY.md](RESEARCH_LIBRARY.md).
Those legacy interfaces retain their individual types and conventions. The library version is separate from CLI build dates.
API version 1 preserves existing function signatures, enum values and metadata
layouts. Relink static clients when upgrading the library. This release supplies
a static archive and makes no shared-library ABI commitment.

## Build, install and link

Building the full archive requires a C99 compiler, Make, GMP and MPFR
development headers/libraries, with LAPACK/BLAS available for spectral clients.
Core-only clients continue to require only GMP at link time. pkg-config provides convenient client flags and
is used by the examples' Makefile. From the source checkout:

```sh
make library
make install-lib PREFIX="$HOME/.local"
export PKG_CONFIG_PATH="$HOME/.local/lib/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"
pkg-config --modversion nfield
make -C examples
make -C examples run
```

The default prefix is `/usr/local`. Installation places the three public
core headers under `include/nfield`, additional research headers under
`include/nfield/research`, `libnfield.a` under `lib`, and the `nfield.pc` and
`nfield-research.pc` profiles under `lib/pkgconfig`. This guide and the example sources are installed under
`share/doc/nfield`, with the examples in its `examples` subdirectory. `LIBDIR`,
`INCLUDEDIR`, `DOCDIR` and `EXAMPLEDIR` can be overridden when installing.

`DESTDIR` stages files for packaging while preserving the intended final prefix:

```sh
make install-lib PREFIX=/opt/nfield DESTDIR="$PWD/stage"
```

That command writes beneath `stage/opt/nfield`. `DESTDIR` is not a runtime
search path. To build against such a staged installation, use its pkg-config
directory and set `PKG_CONFIG_SYSROOT_DIR` to the staging root.

Include the umbrella header in a client:

```c
#include <nfield/nfield.h>
```

Obtain compile flags with `pkg-config --cflags nfield` and static link flags
with `pkg-config --libs --static nfield`. Put the library flags after client
object files. GMP is the core profile's external link dependency. Static linkage
selects `libnfield.a`; it does not require linking every system dependency
statically.

For a client without pkg-config, pass the installed header directory and
archive explicitly. For example, from the directory containing
`source_projection.c`:

```sh
nfield_prefix="$HOME/.local"
cc -std=c99 -I"$nfield_prefix/include" source_projection.c \
  "$nfield_prefix/lib/libnfield.a" -lgmp -o source_projection
```

The examples' standalone Makefile handles these flags and can be copied with
the C files into another directory. It accepts `CC`, `CFLAGS`, `CPPFLAGS`,
`LDFLAGS`, `LDLIBS` and `PKG_CONFIG`. It also preserves pkg-config's quoting for
installation prefixes containing spaces. Use that Makefile when working with
such a prefix; ordinary shell command substitution does not reinterpret
escaped spaces in flag output.

## Three small programs

`forest_readings.c` computes the unit-source forest at `p=5`, so `N=4` and
`Q=25`. It prints all twelve aggregate readings and the individual clock rows.
Its optional argument is a positive divisor:

```sh
./forest_readings
./forest_readings 3
```

With the default `D=1`, the continuous energy is `23/9`, sampled energy is
`48/25`, defect is `143/225`, and origin contact is `16/25`. The corrected
defect is `-1/225`. The selected signed work is zero; complementary signed work
is `1/9`. Changing `D` changes the forest selection while retaining the same
complete four-harmonic field.

`source_projection.c` supplies `c=(1,-2,3/2,1)` and selects reset indices 2 and
3 on the 25-point grid. The selected coefficients are `(-1/2,-1,3/2,0)`.
In particular, the first selected coefficient is nonzero even though reset 1
was not selected. This is a selection of reset masses followed by source
reconstruction.

The continuous energy decomposition is

```text
5/3 = 1 + 5/6 - 1/6
full = selected + complement + twice_mixed
```

On the grid it is `934/625 = 616/625 + 86/125 - 112/625`. The mixed contribution
is signed and is essential to both equalities. The program also prints the
selected and complementary ordered readings against the full original field.

`source_divisor.c` reuses one handle. First it supplies the four unit weights
and `D=1`, requesting coordinates only. The resulting modulus is `4^4=256`,
with harmonic destinations `(1,2,1,4)` and selected coefficients `(2,1,0,1)`.
It then recomputes with modulus zero and `Q=25`, obtaining the identity
selection and its energy. Each program initializes and clears its GMP values,
checks status returns, and destroys its result handle.

## Ownership and errors

`nfield_source` and `nfield_forest` are opaque, owned result handles. Initialize
the pointer to `NULL` before passing its address to `nfield_source_create` or
`nfield_forest_create`. Creation rejects a non-NULL `*out`; it never overwrites
an existing handle. Release it with `nfield_source_destroy` or
`nfield_forest_destroy`, respectively. Both accept `NULL`. Clear your own
pointer if you intend to reuse it after destruction.

A successful compute call replaces the previous computation on the handle.
A recoverable error preserves the previous computation and leaves output
arguments unchanged. Getters return `NFIELD_ESTATE` until the first successful
computation. Metadata structures are caller-owned snapshots with a fixed layout
for API version 1; the calculation's storage remains opaque.

Initialize every `mpq_t` and `mpz_t` before using it as an input or output.
Inputs are borrowed during the call and copied into the result. They can be
modified or cleared afterward. Getters copy exact numbers into caller-owned
GMP objects; they never expose internal storage. Rational inputs may be
unreduced or have a negative denominator. The library canonicalizes copies and
rejects a zero denominator without modifying the input.

| Status | Meaning |
| --- | --- |
| `NFIELD_OK` | The requested operation succeeded. |
| `NFIELD_EINVAL` | Invalid argument, selection, enum value or number. |
| `NFIELD_ERANGE` | Dimension or mathematical index outside supported bounds. |
| `NFIELD_ESTATE` | The handle has no successful computation yet. |
| `NFIELD_ENODATA` | This computation did not produce the requested quantity. |
| `NFIELD_ENOMEM` | Allocation of a result handle failed. |

`NFIELD_ENOMEM` does not catch GMP allocation failures. GMP follows its
allocator policy, which normally aborts on memory exhaustion. The recoverable
error guarantee applies to status returns, not to that allocator behavior.

`nfield_status_string(status)` returns a static description, including for
unknown status values. Do not free it. `nfield_version()` returns the static
library version string; `nfield_api_version()` returns the API version number.
The compile-time counterparts are `NFIELD_VERSION` and `NFIELD_API_VERSION`.

Calls on distinct handles can run concurrently. Do not modify or destroy a
handle while another thread is using it. There is no global initialization
function or mutable global error slot.

## Source inputs and selection

The field is

```text
B_c(x) = 2 sum_(j=1..N) c_j psi(j*x)
psi(x) = fractional_part(x) - 1/2 away from integers
psi(integer) = 0
```

Input arrays are zero-based: `weights[0]` is `c_1`, and `mask[0]` selects reset
1. Supply exactly `N` initialized rationals and, for a mask, `N` bytes equal
to zero or one. Both arrays may be `NULL` when `N=0`. Public indexed getters
use mathematical indices **1 through N**; zero and indices greater than `N`
return `NFIELD_ERANGE`.

The reset mass at `k` is `m_k(c)=sum_(k divides j) c_j`. A mask keeps selected
masses, then applies divisor inversion to recover the selected coefficients.
The complement is the original source minus that selected source. A selected
coefficient can be negative even for nonnegative original coefficients.

| Function | Calculation |
| --- | --- |
| `nfield_source_project(source,N,weights,mask,Q)` | Select the reset masses indicated by the Boolean mask. |
| `nfield_source_collapse(source,N,weights,M,Q)` | Select resets whose index divides nonnegative `M`. Harmonic `j` goes to `gcd(j,M)`, and coefficients with the same destination are added. |
| `nfield_source_divisor(source,N,weights,D,Q)` | For positive `D`, perform the collapse with `M=N^N D`. At `N=0`, the factor `N^N` is defined as 1. |

Modulus `M=0` selects every reset and gives the identity projection. Divisor
`D=0` is invalid. The two parameters have different meanings. For positive
`N`, the divisor operation selects `k` when the factor of `k` left after
removing all primes dividing `N` divides `D`.

`Q=0` requests source coordinates and masses only. Both continuous and sampled
energies, mixed pairings and all work getters then return `NFIELD_ENODATA`.
For positive `Q`, grids need not be prime or coprime to the source frequencies.
The midpoint convention also applies at grid points that meet nonorigin resets.

## Source getters and normalization

Use `NFIELD_ORIGINAL`, `NFIELD_SELECTED` or `NFIELD_COMPLEMENT` to identify a
component. `nfield_source_get_info` copies `cutoff`, `grid`, `has_work` and
`has_modulus`. The flags indicate available calculations, including when the
cutoff is zero.

| Getter | Copied result |
| --- | --- |
| `nfield_source_coefficient(source,component,k,out)` | Component coefficient at harmonic `k`. |
| `nfield_source_mass(source,component,k,out)` | Sum of component coefficients at multiples of reset `k`. |
| `nfield_source_total(source,component,out)` | Sum of all component coefficients. |
| `nfield_source_mask(source,k,out)` | Whether reset `k` is selected, as an unsigned zero or one. |
| `nfield_source_modulus(source,out)` | The modulus used for collapse/divisor selection. |
| `nfield_source_destination(source,k,out)` | Destination `gcd(k,M)` of harmonic `k`. |

Arbitrary-mask computations do not infer a modulus. Their modulus and
destination getters return `NFIELD_ENODATA`, even if a particular mask could
also have arisen from a collapse.

`nfield_source_energy(source,form,component,out)` returns the quadratic energy
of that component's field. `NFIELD_CONTINUOUS` means the integral over `[0,1]`.
`NFIELD_SAMPLED` means the average over `a/Q` for `a=0,...,Q-1`, including the
assigned value zero at the origin. These are mathematical field units; no
physical calibration is attached.

`nfield_source_mixed(source,form,out)` returns **twice** the selected/complement
pairing, with its sign. In either form,

```text
energy(original) = energy(selected) + energy(complement) + mixed
```

For work, define the primitive reading and complete clock reading against the
original source `c`:

```text
P_k = sum_(1<=a<k, gcd(a,k)=1) B_c(a/k) psi(Q*a/k)
W_k = (1/2) sum_(1<=a<k) B_c(a/k) psi(Q*a/k)
```

`nfield_source_primitive_work(source,k,out)` returns `P_k`.
`nfield_source_clock_work(source,k,out)` returns `W_k`. Both are zero at `k=1`.
For component coefficients `u`, the aggregate getters are

```text
nfield_source_reset_work:    sum_(k=1..N) m_k(u) P_k
nfield_source_ordered_work:  2 sum_(k=1..N) u_k W_k
```

These give the same ordered reading in reset and coefficient coordinates.
The component changes the first source; the receiver remains the **complete
original field**. These getters return unnormalized work, without a `4/Q`
factor. An energy of a selected component is a different quantity from its
ordered reading against the original field.

## Prime-square forests

`nfield_forest_compute(forest,p,D)` uses the unit source `c_j=1`, cutoff `N=p-1`
and grid `Q=p^2`. Supply an odd prime `p` and a positive GMP integer `D`.
For each `k`, let `rough_N(k)` be what remains after removing every prime
factor supported on `N`. Reset `k` is selected when `rough_N(k)` divides `D`.
The associated harmonic collapse is `j -> gcd(j,N^N D)`.

`nfield_forest_get_info` returns `prime`, `cutoff`, `grid` and `selected_count`.
The count includes selected clocks `2..N`; reset 1 is available through the
getters but does not contribute a nontrivial clock reading.
`nfield_forest_divisor` copies the supplied `D`.
`nfield_forest_get_clock_info(forest,k,out)` returns:

| Field | Meaning |
| --- | --- |
| `rough` | `rough_N(k)`. |
| `selected` | Whether reset `k` belongs to the forest. |
| `destination` | Destination of harmonic `k` under the collapse. |
| `population` | Number of harmonics `j=1..N` whose destination is `k`. |

With `P_k,W_k` as above for the unit source, the clock getter
`nfield_forest_clock_work(forest,quantity,k,out)` returns:

| Quantity | Result |
| --- | --- |
| `NFIELD_CLOCK_SIGNED_WORK` | `A_k = floor(N/k) P_k`. |
| `NFIELD_CLOCK_ABSOLUTE_WORK` | `floor(N/k)` times the sum of absolute primitive-residue products `abs(B_N(a/k) psi(Q*a/k))`. |
| `NFIELD_CLOCK_ORDERED_WORK` | `W_k`, with all residues on the clock included. |

Every clock reads the full original `N`-harmonic field. Taking absolute values
inside the residue sum can give a larger quantity than `abs(A_k)`.

Call `nfield_forest_value(forest,quantity,out)` for aggregate results. Write
`S` for the selected clocks `2..N`, `b_k` for their collapse populations, and
`H_r=sum_(j=1..r) 1/j`:

| Quantity | Result |
| --- | --- |
| `NFIELD_FOREST_CONTINUOUS_ENERGY` | `integral_0^1 B_N(x)^2 dx`. |
| `NFIELD_FOREST_SAMPLED_ENERGY` | `(1/Q) sum_(a=0..Q-1) B_N(a/Q)^2`. |
| `NFIELD_FOREST_DEFECT` | Continuous energy minus sampled energy. |
| `NFIELD_FOREST_ORIGIN_CONTACT` | `N^2/Q`. |
| `NFIELD_FOREST_CORRECTED_DEFECT` | Defect minus origin contact. |
| `NFIELD_FOREST_SIGNED_WORK` | `F=sum_(k in S) A_k`. |
| `NFIELD_FOREST_COMPLEMENT_WORK` | `C=sum_(k not in S, 2<=k<=N) A_k`. |
| `NFIELD_FOREST_ABSOLUTE_WORK` | Sum of the selected clocks' absolute primitive-residue work. |
| `NFIELD_FOREST_RESTORATION_WORK` | `R=2 sum_(k in S) (1-b_k) W_k`. |
| `NFIELD_FOREST_COMPLEMENT_CLOCK_WORK` | `2 sum_(k not in S, 2<=k<=N) W_k`. |
| `NFIELD_FOREST_CURVATURE` | `-N H_N/(3 p^3)`. |
| `NFIELD_FOREST_SIGNED_WORK_BOUND` | `(N/2) sum_(k in S) H_floor(k/2)^2`, a bound for the magnitude of the signed forest sum. |

The signed-work bound is not a bound for the absolute-residue-work sum.
Work totals retain their `A` or `W` units. Multiply a signed `A` total by `4/Q`
to obtain its defect contribution. The complete identity is

```text
defect = origin_contact + (4/Q) (F + C) + curvature
```

The complementary reading also has the exact split
`C = restoration_work + complement_clock_work`.

`nfield_forest_return_divisor(out,p,L)` constructs the return divisor without
needing a forest handle:

```text
D = 15 (N*Q+1) (N^2-N-1) product_(odd j, 1<=j<=L) (Q^j-N^j)
```

Initialize `out` first, then pass the resulting integer to
`nfield_forest_compute`. Even values of `L` include the same odd exponents as
`L-1`. A chosen finite divisor and its exact readings do not by themselves
establish an all-cutoff decay estimate.

## Precision and resource bounds

| Input | Supported domain in API version 1 |
| --- | --- |
| Source cutoff `N` | `0..NFIELD_SOURCE_MAX_CUTOFF`, currently 64. |
| Source grid `Q` | `0..NFIELD_SOURCE_MAX_GRID`, currently 65536. |
| Forest prime `p` | Odd primes `3..NFIELD_FOREST_MAX_PRIME`, currently 251. |
| Return window `L` | `NFIELD_FOREST_MIN_RETURN..NFIELD_FOREST_MAX_RETURN`, currently `3..31`. |
| Source coefficients | Exact GMP rationals with nonzero denominators. |
| Collapse modulus `M` | Any nonnegative GMP integer, including zero. |
| Divisor `D` | Any positive GMP integer. |

There is no fixed bit or decimal-digit cap on library rational inputs or
moduli. Their size affects memory and computation time. The dimension limits
are separate from precision limits, and a library client need not use the
CLI's text-input size limits. Outputs remain canonical exact GMP numbers.
Floating-point conversion, formatting, persistence and visualization belong
to the calling application.
