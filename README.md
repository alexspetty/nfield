# nfield

The collision invariant of the digit function floor(br/p) encodes
L-function special values through a three-line identity: the collision
transform equals the sum of squared partial character sums over the
digit function's bins. The papers prove it. The engine computes with it.

## Publications

- [**The Collision Invariant**](publication/the_collision_invariant.pdf) (2026, submitted to Experimental Mathematics April 4, 2026)
  Gate width theorem, finite determination, reflection identity, half-group theorem.

- [**The Collision Transform**](publication/the_collision_transform.pdf) (2026)
  Antisymmetry, centered convergence at s=1, conditional penetration, neutrality.

- [**The Collision Spectrum**](publication/the_collision_spectrum.pdf) (2026)
  Decomposition theorem, L-encoding, Parseval moment identity, correlation decay.

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

## Author

**Alexander S. Petty** | [alexander.petty@gmail.com](mailto:alexander.petty@gmail.com) | [alexpetty.com](https://alexpetty.com) | .:.
