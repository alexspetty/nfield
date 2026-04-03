# nfield

The collision invariant of the digit function floor(br/p) encodes
L-function special values through a three-line identity: the collision
transform equals the sum of squared partial character sums over the
digit function's bins. The papers prove it. The engine computes with it.

## Publications

- [**The Collision Invariant**](publication/the_collision_invariant.pdf) (2026)
  Gate width theorem, finite determination, reflection identity, half-group theorem.

- [**The Collision Transform**](publication/the_collision_transform.pdf) (2026)
  Antisymmetry, centered convergence at s=1, conditional penetration, neutrality.

- [**The Collision Spectrum**](publication/the_collision_spectrum.pdf) (2026)
  Decomposition theorem, L-encoding, Parseval moment identity, correlation decay.

- **Partial Character Sums and the Collision Transform** (April 2026, in preparation)
  Bin character sum identity, Polya-Vinogradov and Burgess connections,
  ghost collision dominance at composites, the factoring wall.

- **The Collision Prime Number Theorem** (April 2026, in preparation)
  Collision PNT with Siegel immunity. Collision periodic table.
  L-value extraction from 40 integers. Antisymmetry S(a)+S(-a)=-1.

- **The Collision Mean Value Theorem** (April 2026, in preparation)
  V_rms^2 = O(b^l) proved from floor(br/p). Flow conservation,
  source uniformity, polarity cancellation. No L-function theory.

## Software

The `nfield` engine is written in C (MIT license). Requires a C compiler and make.

**Linux / macOS:**

```
git clone https://github.com/alexspetty/nfield.git
cd nfield && make
```

**Windows (via WSL):**

Install [WSL](https://learn.microsoft.com/en-us/windows/wsl/install) (Windows 11), then from a WSL terminal:

```
sudo apt update && sudo apt install gcc make
git clone https://github.com/alexspetty/nfield.git
cd nfield && make
```

**Usage:**

```
./nfield field 7         # the fractional field of 7
./nfield align 12        # alignment of n=12
./nfield spectral 13     # spectral power at p=13
./nfield decompose 21    # coherence decomposition
./build.sh code          # build and run 116 unit tests
```

## Reproducing the MVT Computations

The experiments supporting the collision mean value theorem are in `experiments/`.
Requires GCC with OpenMP. GPU experiments require CUDA (nvcc).

**Per-bin flow bound (lag 2, all 400 classes):**
```
gcc -O3 -fopenmp -o verify_perbin experiments/verify_perbin.cu -lm
./verify_perbin 10 2
```

**Per-radial flow analysis (lag 2-3):**
```
gcc -O3 -fopenmp -o verify_radial experiments/verify_radial.c -lm
./verify_radial 10 3
```

**Vortex flow decomposition (radial vs transverse):**
```
gcc -O3 -fopenmp -o vortex_structure experiments/vortex_structure.c -lm
./vortex_structure 10 3
```

**GPU-accelerated F(d,d') at arbitrary lag (requires CUDA):**
```
nvcc -O3 -allow-unsupported-compiler -Xcompiler -fopenmp \
     -o verify_perbin_gpu experiments/verify_perbin_gpu.cu -lm
./verify_perbin_gpu 10 4
```

**Multi-base verification (bases 3, 7, 10, 12):**
```
for b in 3 7 10 12; do ./verify_radial $b 3; done
```

## Research Notes

26 research notes (2020-2026) in [research/](research/).

## Author

**Alexander S. Petty** | alexander.petty@gmail.com
