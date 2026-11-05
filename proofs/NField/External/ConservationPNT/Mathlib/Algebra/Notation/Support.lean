/-
SPDX-License-Identifier: Apache-2.0
Vendored from PrimeNumberTheoremAnd, Alex Kontorovich and contributors.
Upstream revision: a5154676af9aa3095150ee410cdda80555aa0642.
See this directory's README.md and LICENSE for attribution and local changes.
-/

import Mathlib.Algebra.Notation.Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
