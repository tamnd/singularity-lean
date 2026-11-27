/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.PBasis
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# p-bases and the module of differentials

This file proves the uniqueness half of Volume 1, Theorem 6.2.3 of the handbook. Let `k ⊆ K` be fields of characteristic `p`, let `L = k K^p` and let `B` be a finite `p`-basis of `K` over `k`.

* `Singularity.Algebra.derivation_map_pSubring`: a `k`-derivation of `K` is zero on `L`.
* `Singularity.Algebra.derivation_mem_span_pBasis`: for a `k`-derivation `D`, each `D x` is in the `K`-span of the `D b` for `b ∈ B`.
* `Singularity.Algebra.derivation_ext_pBasis`: two `k`-derivations that agree on `B` are equal.
* `Singularity.Algebra.span_D_pBasis`: the `db` for `b ∈ B` span `Ω_{K/k}` over `K`.
* `Singularity.Algebra.finrank_kaehler_le_card`: `dim_K Ω_{K/k} ≤ |B|`.

The existence half of Theorem 6.2.3 is not in Lean. It says that the `db` are linearly independent, so it gives the equality `dim_K Ω_{K/k} = |B|` of Corollary 6.2.4.
-/

namespace Singularity.Algebra

variable {k K M : Type*} [Field k] [Field K] [Algebra k K] {p : ℕ}
  [AddCommGroup M] [Module K M] [Module k M]

/-- A `k`-derivation of `K` in characteristic `p` is zero on the subring `L = k K^p`. -/
theorem derivation_map_pSubring [CharP K p] (D : Derivation k K M) {x : K}
    (hx : x ∈ pSubring (K := K) k p) : D x = 0 := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨r, rfl⟩ | ⟨a, rfl⟩
    · exact D.map_algebraMap r
    · rw [D.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  | zero => exact D.map_zero
  | one => exact D.map_one_eq_zero
  | add x y _ _ hx hy => rw [D.map_add, hx, hy, add_zero]
  | neg x _ hx => rw [D.map_neg, hx, neg_zero]
  | mul x y _ _ hx hy => rw [D.leibniz, hx, hy, smul_zero, smul_zero, add_zero]

/-- A `k`-derivation of `K` in characteristic `p` is linear over `L = k K^p`. -/
theorem derivation_map_pSubring_mul [CharP K p] (D : Derivation k K M)
    (c : pSubring (K := K) k p) (x : K) : D ((c : K) * x) = (c : K) • D x := by
  rw [D.leibniz, derivation_map_pSubring D c.2, smul_zero, add_zero]

/-- For a `k`-derivation `D`, the value on a `p`-monomial in `B` is in the `K`-span of the `D b`. -/
theorem derivation_pMonomial_mem_span (D : Derivation k K M) (B : Finset K) (α : B → Fin p) :
    D (pMonomial B α) ∈ Submodule.span K (Set.range fun b : B => D (b : K)) := by
  classical
  unfold pMonomial
  induction (Finset.univ : Finset B) using Finset.induction_on with
  | empty => rw [Finset.prod_empty, D.map_one_eq_zero]; exact zero_mem _
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, D.leibniz, D.leibniz_pow]
    refine add_mem (Submodule.smul_mem _ _ ih) (Submodule.smul_mem _ _ ?_)
    rw [← Nat.cast_smul_eq_nsmul K]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))

/-- Let `B` be a finite `p`-basis of `K` over `k`. For a `k`-derivation `D` of `K`, each `D x` is in the `K`-span of the `D b` for `b ∈ B`. -/
theorem derivation_mem_span_pBasis [CharP K p] {B : Finset K} (hB : IsPBasis k p B)
    (D : Derivation k K M) (x : K) :
    D x ∈ Submodule.span K (Set.range fun b : B => D (b : K)) := by
  have hx := hB.2 (Submodule.mem_top (x := x))
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, rfl⟩ := hy
    exact derivation_pMonomial_mem_span D B α
  | zero => rw [D.map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [D.map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [Subring.smul_def, smul_eq_mul, derivation_map_pSubring_mul D c y]
    exact Submodule.smul_mem _ _ hy

/-- The uniqueness half of Theorem 6.2.3: two `k`-derivations of `K` that agree on a finite `p`-basis `B` are equal. -/
theorem derivation_ext_pBasis [CharP K p] {B : Finset K} (hB : IsPBasis k p B)
    {D₁ D₂ : Derivation k K M} (h : ∀ b ∈ B, D₁ b = D₂ b) : D₁ = D₂ := by
  ext x
  rw [← sub_eq_zero]
  change (D₁ - D₂) x = 0
  have hx := derivation_mem_span_pBasis hB (D₁ - D₂) x
  have h0 : (Set.range fun b : B => (D₁ - D₂) (b : K)) ⊆ {0} := by
    rintro _ ⟨b, rfl⟩
    simp [h b b.2]
  have := Submodule.span_mono (R := K) h0 hx
  simpa using this

/-- Theorem 6.2.3, spanning part: if `B` is a finite `p`-basis of `K` over `k`, then the `db` for `b ∈ B` span `Ω_{K/k}` over `K`. -/
theorem span_D_pBasis [CharP K p] {B : Finset K} (hB : IsPBasis k p B) :
    Submodule.span K (Set.range fun b : B => KaehlerDifferential.D k K b) = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact derivation_mem_span_pBasis hB (KaehlerDifferential.D k K) x

/-- One inequality of Corollary 6.2.4: if `B` is a finite `p`-basis of `K` over `k`, then `dim_K Ω_{K/k} ≤ |B|`. -/
theorem finrank_kaehler_le_card [CharP K p] {B : Finset K} (hB : IsPBasis k p B) :
    Module.finrank K (Ω[K⁄k]) ≤ B.card := by
  have := finrank_range_le_card (R := K) fun b : B => KaehlerDifferential.D k K b
  rwa [Set.finrank, span_D_pBasis hB, finrank_top, Fintype.card_coe] at this

end Singularity.Algebra
