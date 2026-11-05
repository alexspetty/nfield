# Analytic number theory proof inputs

These fifteen modules are reused from **Alex Kontorovich and contributors,
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)**,
at commit `a5154676af9aa3095150ee410cdda80555aa0642`, under the accompanying
[Apache License 2.0](LICENSE). They are upstream work, not original nfield
proofs. Existing source notices are preserved.

| Included module | Upstream source | Raw upstream SHA-256 |
|---|---|---|
| `EulerMaclaurin.lean` | [EulerMaclaurin.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/EulerMaclaurin.lean) | `a1def4a9f8f0b36864c5d480db137c1d86be3db1a47b67ae151e587a99167146` |
| `IEANTN/Mertens.lean` | [Mertens.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/IEANTN/Mertens.lean) | `30387cba9cbd61b129d02993c6cb503820dd453237c899bea373a108adf7f793` |

The Euler-Maclaurin source body is unchanged. The Mertens module removes
Architect blueprint documentation metadata and rewrites its local import to
`NField.External.ConservationPNT.EulerMaclaurin`. Its adapted source body has
SHA-256 `4540343b5a2759e63626ef6ca124891511cf0837157944d5d8888f0c11502751`.
Each exported file adds a provenance comment; the hashes above exclude that
added comment. No mathematical declaration is changed by this export.

The upstream snapshot specifies Lean 4.32.2. The selected modules were
compiled and checked with nfield's pinned Lean and Mathlib 4.32.1. The package
includes the fifteen dependencies needed by the public proof library; it
does not include the complete upstream project or claim its authorship.

## Additional inputs for the Conservation companion

The following thirteen modules extend the two inputs above at the same upstream
revision. Original source notices and the accompanying Apache 2.0 license are
retained. Local integration removes Architect documentation metadata, redirects
local imports into `NField.External.ConservationPNT`, and adapts the selected
proofs to the pinned Lean and Mathlib version. The adapted-body hashes exclude
the added public provenance comment.

| Included module | Raw upstream SHA-256 | Adapted body SHA-256 |
|---|---|---|
| [Auxiliary.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/Auxiliary.lean) | `6a57cc112e9a6dbe780c019cb22fa1469733afc78976f3aeeaaa80949acf0cfc` | `6a57cc112e9a6dbe780c019cb22fa1469733afc78976f3aeeaaa80949acf0cfc` |
| [Fourier.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/Fourier.lean) | `e9db3c235cabf356d2b4aed528d0ceca6ad3e23c7a150d7049fd9ac796315823` | `62de3aa03c8cfe2b0c48cb706e41033e0a8042d7e89780e2564146628332e4f5` |
| [Mathlib/Algebra/Notation/Support.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean) | `e688bf925c2130b291c536d3b93b72c20e41ae95d530c90915921d75a6f52504` | `e688bf925c2130b291c536d3b93b72c20e41ae95d530c90915921d75a6f52504` |
| [Mathlib/Analysis/SpecialFunctions/Log/Basic.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean) | `7e3e2b8f84e6c170051a6474272455bed2432e6fddac5660072318b9b4eda7ec` | `7e3e2b8f84e6c170051a6474272455bed2432e6fddac5660072318b9b4eda7ec` |
| [MediumPNT.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/MediumPNT.lean) | `7044c41ae6df6798c743434ea82a682cc784b1dbf4a4817662eb7a0579ad747f` | `82c074618688ef6d408244fcbd4334f51bf088badf44b361fee6b555f174517c` |
| [MellinCalculus.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/MellinCalculus.lean) | `2a3d42e3fd811faff72cba349943144d063571f23ce5b13f82d897fe8bb9789b` | `7a7c23559ffa37ef2ab6dc78250652fb92915dddc093c85feaa9d1a57c933a4d` |
| [Rectangle.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/Rectangle.lean) | `ab1c0c7c16ad9f3765e439fe42a739d4d25f09aa991df6c4c303f77380a89885` | `f55a6989b82bcea793408619cf6fb9b0ef76f6bc1e1d66de56dd3c90d7bae275` |
| [ResidueCalcOnRectangles.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean) | `6a8ab0005546490f91b615f6bfbe8818ba21f3afe008a893174ab1a0e3e45cb8` | `e5a3c183a445078327eac6d5f7cea45ec8889942f88563b1adc56ba0892135e1` |
| [SmoothExistence.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/SmoothExistence.lean) | `e689045a2d7f92c71c68fda6aa69a89d4a8692187475ba432ed010f453110ea0` | `4da91d451c969d3d7de50bbd04207012ee8ea1f800b6527f164ab2c788bab2e7` |
| [Sobolev.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/Sobolev.lean) | `fe06e13fad5b47dbd324307ba246110515c4cb50f4c41d6cb15764fd53b1b8ef` | `fe06e13fad5b47dbd324307ba246110515c4cb50f4c41d6cb15764fd53b1b8ef` |
| [Tactic/AdditiveCombination.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean) | `ea898bb0a4889d82fe4b94b7052daa73083d1f3aa3cddb5336f0513580a17040` | `72d482dd585fe859720833a117a043322e7469034e8e6828fa8dfb73bd116e3e` |
| [ZetaBounds.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/ZetaBounds.lean) | `aab01d422c0190b95dade7873261943997c554d55fcc9fff94a39005e5b5ad5a` | `4f8337608ada20c16c21ea84a7ca20fc2b8f5b2acb2557e056066801e3f5997f` |
| [ZetaConj.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/ZetaConj.lean) | `08a9153c6500464c574f466a5569e82adbd5fb152a96a914fbb77c3208d0a71c` | `ac3be8091b6d1b2eb1d4f57f315926c9c02618fe2f665a9b1832dcd36ef69856` |

These inputs establish their written unconditional analytic statements. They do
not supply an RH or GRH theorem, or pointwise control of the exceptional integer
orbit. The nfield bridges and Conservation companion remain outside this
upstream directory.
