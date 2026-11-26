/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Filtration

/-!
# The lemma of Artin-Rees and the intersection theorem of Krull

This file states three results of Volume 1, Section 4.1 of the handbook in the form of the handbook. Mathlib proves the lemma of Artin-Rees (`Ideal.exists_pow_inf_eq_pow_smul`), and the results here are short consequences.

* `Singularity.Algebra.artinRees`: `I^n M ∩ N = I^(n-c) (I^c M ∩ N)` for `n ≥ c` (Volume 1, Theorem 4.1.5 of the handbook).
* `Singularity.Algebra.artinRees_le`: `I^n N ⊆ I^n M ∩ N ⊆ I^(n-c) N` for `n ≥ c` (Volume 1, Corollary 4.1.6 of the handbook).
* `Singularity.Algebra.krull_intersection`: let `E = ⋂ I^n M`. Then `I E = E`, and there is `a ∈ I` with `(1 + a) E = 0` (Volume 1, Theorem 4.1.7 of the handbook).

In Lean, `I^n M` is the submodule `I ^ n • ⊤` of `M`.
-/

namespace Singularity.Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherianRing R]
  [Module.Finite R M] (I : Ideal R)

/-- The lemma of Artin-Rees (Volume 1, Theorem 4.1.5 of the handbook). Let `R` be a Noetherian ring, let `I` be an ideal, let `M` be a finitely generated `R`-module and let `N` be a submodule of `M`. Then there is `c` such that `I^n M ∩ N = I^(n-c) (I^c M ∩ N)` for each `n ≥ c`. This is `Ideal.exists_pow_inf_eq_pow_smul` of Mathlib. -/
theorem artinRees (N : Submodule R M) :
    ∃ c : ℕ, ∀ n ≥ c, I ^ n • (⊤ : Submodule R M) ⊓ N = I ^ (n - c) • (I ^ c • ⊤ ⊓ N) :=
  Ideal.exists_pow_inf_eq_pow_smul I N

/-- The topology that the `I`-adic topology of `M` induces on `N` is the `I`-adic topology (Volume 1, Corollary 4.1.6 of the handbook). There is `c` such that `I^n N ⊆ I^n M ∩ N ⊆ I^(n-c) N` for each `n ≥ c`. -/
theorem artinRees_le (N : Submodule R M) :
    ∃ c : ℕ, ∀ n ≥ c, I ^ n • N ≤ I ^ n • (⊤ : Submodule R M) ⊓ N ∧
      I ^ n • (⊤ : Submodule R M) ⊓ N ≤ I ^ (n - c) • N := by
  obtain ⟨c, hc⟩ := artinRees I N
  refine ⟨c, fun n hn => ⟨le_inf (smul_mono_right _ le_top) Submodule.smul_le_right, ?_⟩⟩
  rw [hc n hn]
  exact smul_mono_right _ inf_le_right

/-- The intersection theorem of Krull (Volume 1, Theorem 4.1.7 of the handbook). Let `R` be a Noetherian ring, let `I` be an ideal, let `M` be a finitely generated `R`-module and let `E = ⋂ I^n M`. Then `I E = E`, and there is `a ∈ I` with `(1 + a) E = 0`. -/
theorem krull_intersection :
    I • (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)) = ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) ∧
      ∃ a ∈ I, ∀ e ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)), (1 + a) • e = 0 := by
  set E : Submodule R M := ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) with hE
  obtain ⟨c, hc⟩ := artinRees I E
  have hle : ∀ n, E ≤ I ^ n • (⊤ : Submodule R M) := fun n => iInf_le _ n
  have h1 : E ≤ I • E := by
    have h := hc (c + 1) (Nat.le_succ c)
    rw [inf_eq_right.mpr (hle (c + 1)), inf_eq_right.mpr (hle c), Nat.add_sub_cancel_left,
      pow_one] at h
    exact h.le
  have hIE : I • E = E := le_antisymm Submodule.smul_le_right h1
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I E
    (IsNoetherian.noetherian E) h1
  refine ⟨hIE, r - 1, hr, fun e he => ?_⟩
  rw [show (1 : R) + (r - 1) = r by ring]
  exact hr0 e he

end Singularity.Algebra
