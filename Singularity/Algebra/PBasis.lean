/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Finite p-bases

This file proves the first part of Volume 1, Corollary 6.2.4 of the handbook. Let `k ⊆ K` be fields and let `L = k K^p` be the subring of `K` that `k` and the `p`-th powers generate. If `B` is a finite `p`-basis of `K` over `k`, then `[K : L] = p^|B|`. So any two finite `p`-bases of `K` over `k` have the same number of elements.

The definition is Definition 6.2.1 of the handbook for a finite set `B`. The `p`-monomials in `B` are the products `∏ b^α(b)` with `0 ≤ α(b) < p`, and `B` is a `p`-basis if they are a basis of `K` over `L`.

* `Singularity.Algebra.pSubring`: the subring `L = k K^p` of `K`.
* `Singularity.Algebra.pMonomial`: the `p`-monomial `∏ b^α(b)` for `α : B → Fin p`.
* `Singularity.Algebra.IsPBasis`: a finite set `B` is a `p`-basis of `K` over `k`.
* `Singularity.Algebra.finrank_pSubring_eq`: `[K : L] = p^|B|`, the first claim of Corollary 6.2.4.
* `Singularity.Algebra.IsPBasis.card_eq`: two finite `p`-bases have the same number of elements.

The second claim of Corollary 6.2.4, `dim_K Ω_{K/k} = |B|`, needs Theorem 6.2.3. The file `Singularity/Algebra/PBasisDifferentials.lean` proves the inequality `dim_K Ω_{K/k} ≤ |B|`, and the file `Singularity/Algebra/PBasisExistence.lean` proves the equality.
-/

namespace Singularity.Algebra

variable (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ)

/-- The subring `L = k K^p` of `K` that the image of `k` and the `p`-th powers generate. -/
def pSubring : Subring K :=
  Subring.closure (Set.range (algebraMap k K) ∪ Set.range fun a : K => a ^ p)

variable {k p}

/-- The `p`-monomial `∏_{b ∈ B} b^α(b)` for an exponent `α : B → Fin p`. -/
def pMonomial (B : Finset K) (α : B → Fin p) : K :=
  ∏ b : B, (b : K) ^ (α b : ℕ)

/-- A finite set `B` is a `p`-basis of `K` over `k` if the `p`-monomials in `B` are linearly independent over `L = k K^p` and span `K` over `L` (Definition 6.2.1 of the handbook). -/
def IsPBasis (k : Type*) [Field k] [Algebra k K] (p : ℕ) (B : Finset K) : Prop :=
  LinearIndependent (pSubring (K := K) k p) (pMonomial (p := p) B) ∧
    ⊤ ≤ Submodule.span (pSubring (K := K) k p) (Set.range (pMonomial (p := p) B))

/-- If `B` is a finite `p`-basis of `K` over `k`, then `[K : k K^p] = p^|B|` (Volume 1, Corollary 6.2.4 of the handbook, first claim). -/
theorem finrank_pSubring_eq {B : Finset K} (hB : IsPBasis k p B) :
    Module.finrank (pSubring (K := K) k p) K = p ^ B.card := by
  classical
  have : Nontrivial (pSubring (K := K) k p) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hB.1 hB.2), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe]

/-- Any two finite `p`-bases of `K` over `k` have the same number of elements, for `p ≥ 2` (Volume 1, Corollary 6.2.4 of the handbook, last claim). -/
theorem IsPBasis.card_eq (hp : 2 ≤ p) {B B' : Finset K} (hB : IsPBasis k p B)
    (hB' : IsPBasis k p B') : B.card = B'.card := by
  have h := (finrank_pSubring_eq hB).symm.trans (finrank_pSubring_eq hB')
  exact Nat.pow_right_injective hp h

end Singularity.Algebra
