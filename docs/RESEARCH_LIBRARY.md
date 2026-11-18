# Research interfaces

The research profile makes existing nfield calculations callable from a C99
program. It uses the same mathematical implementations as the CLI. Include
`<nfield/research.h>` and link through `pkg-config --libs --static
nfield-research`. Individual headers live under `nfield/research/`.

The source/forest API in `<nfield/nfield.h>` remains unchanged. Its functions
use `nfield_status`, owned handles and copied exact results as described in
[LIBRARY.md](LIBRARY.md). Core-only clients still link using `pkg-config
--libs --static nfield`, whose external dependency is GMP. Both profiles use
`libnfield.a`; a static linker selects the objects needed by each client.

## Compile a client

```sh
cc -std=c99 -O2 $(pkg-config --cflags nfield-research) research.c \
    $(pkg-config --libs --static nfield-research) -o research
```

For installation paths containing spaces, use a Make recipe whose
`$(shell pkg-config ...)` results become shell command text, as in the installed
examples' Makefile. Shell command substitution alone does not reinterpret
backslash escapes emitted by pkg-config.

The full research link profile includes GMP, MPFR, libm, pthread, LAPACK and
BLAS. The selected LAPACK/BLAS flags follow the build platform. The module
headers are C99 interfaces and include C complex types where appropriate.
The existing core headers remain separately usable by C and C++ clients.

For example, obtain an exact count and a numerical spectrum without invoking
the CLI or parsing its output:

```c
#include <nfield/research.h>
#include <stdio.h>

int main(void)
{
    int collisions = 0, length = 0;
    double power[7];
    if (!autocorrelation_collision_count(7, 10, 2, &collisions) ||
        !spectral_power_values(7, 10, power, 7, &length))
        return 1;
    printf("collisions=%d frequencies=%d power0=%.12g\n",
           collisions, length, power[0]);
    return 0;
}
```

## Select a module

| Header | Existing data interfaces |
| --- | --- |
| `arithmetic.h` | `Field`, `Repetend`, `Invariants`; exact collision-table entries; alignment and deficit fractions; collision counts; spectral arrays; finite arithmetic identities. |
| `native_arithmetic.h` | Exact tapered packet coefficients in initialized GMP rational arrays. |
| `collision_sampling.h` | Exact capacities, sampled energies, carrier readings, switching states and finite Fourier observations. |
| `collision_kernel_readout.h` | Exact kernel seed and carry-measurement records. |
| `collision_capacity_transition.h` | Finite cutoff, centered and residual readings from an initialized transition object. |
| `collision_capacity_generation.h` | Exact source, carry, recovery, control and current readings. |
| `finite_character_core.h`, `primitive_odd_sector_core.h` | Finite character tables, transforms and primitive odd sectors. |
| `collision_spectrum_core.h`, `collision_magnitude_moments.h` | Finite collision spectra, moments and their comparison quantities. |
| `boundary_spectrum.h`, `orbit_boundary_core.h` | Boundary and orbit calculations on explicit finite inputs. |
| `periodic_zeta_core.h` | Periodic Dirichlet and character calculations with their stated numerical conventions. |
| `weighted_remainder_*.h` | Exact finite weights, rows, floor/clock models, Fourier and amplitude rectangles, constants, spectral tails, pairings, conductors, alignment and activation. Each named header declares its own bounds and outputs. |

There is no universal replacement type for these different mathematical
objects. Existing function names, value types and array layouts are retained.
The module header is the authority for argument order, initialization,
ownership, output capacity and supported finite domain.

## Numeric results and renderers

The profile contains both numerical interfaces and legacy rendering
interfaces. They are different contracts.

Numerical examples include `collision_table_value`,
`coherence_decomposition_fractions`, `cross_alignment_entry_fraction`,
`spectral_structure_metrics`, `spectral_power_values`,
`autocorrelation_aggregate_values`, `phase_gate_components`, and the GMP
`*_q` operations. These return values through their declared result objects,
scalars or caller-owned arrays. `Field` and `Repetend` have corresponding
`field_free` and `repetend_free` functions. GMP result structs require their
matching `init`/`clear` functions.

Legacy functions such as `*_inspect`, `*_print`, `survey`, and `survey_range`
write text to stdout. They are callable renderers, not structured numeric
result APIs. The functions in `native_refinement.h` and
`native_directional.h` write to a caller-owned `FILE *`; the native-refinement
functions with a `json` argument can render JSON. Calling a text renderer does
not make its output a numerical data structure.

Return conventions are also retained. Many numerical routines return 1 on
success and 0 on invalid input. Several rendering routines return 0 on success.
Do not compare these legacy results to `NFIELD_OK` by assumption. The original
module contracts and existing caller conventions govern; the uniform
`nfield_status` convention applies only to the core API.

Legacy renderers can use module-level buffers. In particular, serialize calls
to `coherence_print`; it accepts bases 2 through 14 and a positive prime count,
capped at 500. The CLI rejects a count outside 1 through 500. A result type
does not by itself guarantee that its implementation supports concurrent calls.

The broad profile does not yet provide typed results for every CLI action.
Clock/pulse observation handlers, some native-refinement operations, partition
rows and several reference-table/rendering paths still need separate result
interfaces. Existing scalar or array access does not automatically expose
all intermediate CLI readings. The CLI remains available for those operations.

## Numerical and resource limits

GMP rational/integer APIs preserve exact arbitrary-precision values within
their declared finite input domains. Functions using `int`, `uint64_t` or
`long long` retain those widths and their existing bounds. Functions returning
`double`, `long double` or complex floating values are numerical calculations,
not exact rationals or interval certificates. Rational interval endpoints
and MPFR interval routines have their own documented contracts.

Respect explicit limits before allocating or iterating. In particular, legacy
field/repetend builders require valid positive denominators and bases, and
some old allocation paths do not offer the core API's recoverable
`NFIELD_ENOMEM` guarantee. Array capacities and caller-initialized GMP entries
are part of the contract. An omitted check in an old routine is not permission
to pass invalid pointers or exceed its numerical range.

These are source-compatible existing C interfaces, not a new shared-library
ABI commitment. Relink static clients after upgrading. The stable source/forest
API version remains 1; no legacy routine acquires its stronger failure or
ownership guarantees merely by appearing in the research profile.

## Computational verification

Ordinary library calculation and the existing C theorem checks do not require
Lean. Run named computational checks with `nfield verify <family>`. Fixed
panels stay in that command area and are not declared as research functions.

Some mathematical source files also contain rendering and finite checking code.
Four traditional C check objects are internal link dependencies of the existing
sampling, boundary-spectrum, capacity-transition and capacity-generation
objects. The research archive includes those dependencies. It excludes the
CLI main, daemon, theorem registry and verification-routing infrastructure.
Their presence does not turn bounded checks into universal mathematical proofs.
