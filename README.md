# nfield

The collision invariant of the digit function floor(br/p) encodes
L-function special values through a three-line identity: the collision
transform equals the sum of squared partial character sums over the
digit function's bins. This program proves it and computes with it.

## Publications

- [**The Collision Invariant**](publication/the_collision_invariant.pdf) (2026)
  Gate width theorem, finite determination, reflection identity, half-group theorem.

- [**The Collision Transform**](publication/the_collision_transform.pdf) (2026)
  Antisymmetry, centered convergence at s=1, conditional penetration, neutrality.

- [**The Collision Spectrum**](publication/the_collision_spectrum.pdf) (2026)
  Decomposition theorem, L-encoding, Parseval moment identity, correlation decay.

## Software

The `nfield` engine is written in C (MIT license).

```
make
./build.sh code          # build and run 116 unit tests
./nfield 7               # analyze n=7 in base 10
./nfield align 12        # alignment of n=12
./nfield spectral 13     # spectral power at p=13
./nfield decompose 21    # coherence decomposition
```

## Experiments

156 C and Python programs in `experiments/` reproduce
every computational result in the papers.

## Author

Alexander S. Petty
alexander.petty@gmail.com
https://alexpetty.com
