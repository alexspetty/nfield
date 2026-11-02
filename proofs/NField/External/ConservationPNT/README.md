# Analytic number theory proof inputs

These two modules are reused from **Alex Kontorovich and contributors,
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

The upstream snapshot specifies Lean 4.32.2. These selected modules were
compiled and checked with nfield's pinned Lean and Mathlib 4.32.1. The package
includes only these two dependencies needed by the public proof library; it
does not include the complete upstream project or claim its authorship.
