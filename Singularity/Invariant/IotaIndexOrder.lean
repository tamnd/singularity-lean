/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.Prod.Lex.Basic

/-!
# The well order on the values of the invariant iota

Volume 6, Section 3.2 of the handbook gives the invariant `ι(x)` of Cossart and Piltant values in the set `I = {1, ..., p} × ℕ × {1, 2, 3, 4}` with the lexicographic order. This file proves that `I` is well ordered (Volume 6, Lemma 3.2.10 of the handbook). Thus each nonempty subset of `I` has a least element, and there is no infinite strictly decreasing sequence in `I`.

The type `Singularity.IotaIndex p` is `Set.Icc 1 p ×ₗ ℕ ×ₗ Set.Icc 1 4`. The order of `×ₗ` is the lexicographic order. The proof uses the instance of Mathlib that a lexicographic product of two well founded orders is well founded.

## Main results

* `Singularity.IotaIndex.exists_least`: each nonempty subset of `I` has a least element.
* `Singularity.IotaIndex.not_strictAnti`: there is no infinite strictly decreasing sequence in `I`.
-/

namespace Singularity

/-- The set `I = {1, ..., p} × ℕ × {1, 2, 3, 4}` with the lexicographic order, where the invariant `ι` of Volume 6, Section 3.2 of the handbook takes its values. -/
abbrev IotaIndex (p : ℕ) : Type := ↥(Set.Icc 1 p) ×ₗ ℕ ×ₗ ↥(Set.Icc (1 : ℕ) 4)

namespace IotaIndex

variable {p : ℕ}

/-- The lexicographic order on `I` is well founded. -/
instance : WellFoundedLT (IotaIndex p) := inferInstance

/-- Volume 6, Lemma 3.2.10 of the handbook, first part: each nonempty subset of `I = {1, ..., p} × ℕ × {1, 2, 3, 4}` has a least element for the lexicographic order. -/
theorem exists_least (A : Set (IotaIndex p)) (hA : A.Nonempty) :
    ∃ a ∈ A, ∀ b ∈ A, a ≤ b := by
  obtain ⟨a, ha, hmin⟩ := (wellFounded_lt (α := IotaIndex p)).has_min A hA
  exact ⟨a, ha, fun b hb => not_lt.mp (hmin b hb)⟩

/-- Volume 6, Lemma 3.2.10 of the handbook, second part: there is no infinite strictly decreasing sequence in `I = {1, ..., p} × ℕ × {1, 2, 3, 4}` for the lexicographic order. -/
theorem not_strictAnti (f : ℕ → IotaIndex p) : ¬ StrictAnti f :=
  not_strictAnti_of_wellFoundedLT f

end IotaIndex

end Singularity
