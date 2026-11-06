# Fixed-modulus prime distribution inputs

This source selection supplies the Tauberian and elementary prime-count
steps absent from the pinned Mathlib revision. The actual residue-class
Dirichlet series, pole subtraction, continuous boundary, nonvanishing,
character orthogonality and Chebyshev bounds come from Mathlib. The local
bridge is `NField.Alignment.PrimeProgressionAsymptotic`.

`Asymptotics.lean`, `Wiener.lean` and `Consequences.lean` are selected from
Alex Kontorovich and contributors, PrimeNumberTheoremAnd, revision
`769d3b81fbff001d9fa7028df0168a8e546cf692`, available at
https://github.com/ajirving/PrimeNumberTheoremAnd/tree/769d3b81fbff001d9fa7028df0168a8e546cf692.
They use the Apache 2.0 license included in the adjacent
`../ConservationPNT/LICENSE` file. Existing Conservation Fourier, smooth
function and Sobolev proofs are reused rather than copied.

The selection removes Architect documentation metadata and renames local
imports. The unused upstream lemmas `prelim_decay_2`, `prelim_decay_3`,
their dependent `decay_alt`, and the unused alternative decay definition
are omitted. The selected Wiener--Ikehara proof contains no admitted
declaration. The later automatic Chebyshev section is unnecessary because
Mathlib already supplies the required majorant. One set-membership lemma
name is adapted to the pinned Mathlib. The Consequences namespace openings
are made explicit to distinguish the real logarithm from the natural and
arithmetic-function logarithms.

`PNTAP.lean` adapts William J. Blair's ordinary prime-count consequence from
https://github.com/williamjblair/lean-proofs/blob/f297d710018270c66b296082766334974260bcbc/ErdosProblems/Erdos730/PNTAP.lean.
The selected source was fetched at that exact commit and compared byte for
byte with the archived input. Repository-specific density predicates are
omitted. Its weighted input is the unconditional local progression theorem.
This file is distributed under the following MIT license.

MIT License

Copyright (c) 2026 Will Blair

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
