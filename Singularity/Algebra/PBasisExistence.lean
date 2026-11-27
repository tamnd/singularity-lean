/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.PBasisDifferentials
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The existence half of Theorem 6.2.3

This file proves the existence half of Volume 1, Theorem 6.2.3 of the handbook and the equality of Corollary 6.2.4. Let `k ⊆ K` be fields of characteristic `p > 0`, let `L = k K^p` and let `B` be a finite `p`-basis of `K` over `k`. Each function `f : B → K` extends to a `k`-derivation of `K`.

The proof defines the derivation on the basis of the `p`-monomials. The `p`-monomial of `α` goes to `∑_b f(b) ∂/∂X_b (∏ X_c^α(c))` at `X = B`. The map is `L`-linear. The key step is that the map agrees with `P ↦ ∑_b f(b) ∂P/∂X_b (B)` for each polynomial `P` over `L`. A monomial `X^u` is `Q^p X^r` with `r = u mod p`, and `∂(Q^p)/∂X_b = 0` in characteristic `p`. The Leibniz rule then follows from the Leibniz rule for polynomials.

* `Singularity.Algebra.pBasisDerivation`: the `k`-derivation of `K` that sends `b` to `f b`.
* `Singularity.Algebra.pBasisDerivation_apply`: it sends `b` to `f b`.
* `Singularity.Algebra.existsUnique_derivation_pBasis`: Theorem 6.2.3, each `f : B → K` extends to a unique `k`-derivation.
* `Singularity.Algebra.linearIndependent_D_pBasis`: the `db` for `b ∈ B` are linearly independent in `Ω_{K/k}`.
* `Singularity.Algebra.finrank_kaehler_eq_card`: `dim_K Ω_{K/k} = |B|`, Corollary 6.2.4.

The file takes `B` finite. The handbook states Theorem 6.2.3 for each `p`-basis, and the infinite case is not in Lean.
-/

namespace Singularity.Algebra

open MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {p : ℕ}

section Construction

variable (k p) (B : Finset K)

/-- The evaluation map `L[X_b : b ∈ B] → K` that sends `X_b` to `b`, for `L = k K^p`. -/
noncomputable def pEval : MvPolynomial B (pSubring (K := K) k p) →ₐ[pSubring (K := K) k p] K :=
  aeval fun b : B => (b : K)

/-- The polynomial `∏_{b ∈ B} X_b^α(b)` that `pEval` sends to the `p`-monomial of `α`. -/
noncomputable def pMonomialPoly (α : B → Fin p) : MvPolynomial B (pSubring (K := K) k p) :=
  ∏ b : B, X b ^ (α b : ℕ)

/-- The map `P ↦ ∑_b f(b) ∂P/∂X_b (B)` from `L[X_b : b ∈ B]` to `K`. -/
noncomputable def pPolyDer (f : B → K) (P : MvPolynomial B (pSubring (K := K) k p)) : K :=
  ∑ b : B, f b * pEval k p B (pderiv b P)

variable {k p B}

theorem pEval_pMonomialPoly (α : B → Fin p) :
    pEval k p B (pMonomialPoly k p B α) = pMonomial B α := by
  simp [pEval, pMonomialPoly, pMonomial, map_prod]

theorem pPolyDer_mul (f : B → K) (P Q : MvPolynomial B (pSubring (K := K) k p)) :
    pPolyDer k p B f (P * Q) =
      pEval k p B P * pPolyDer k p B f Q + pEval k p B Q * pPolyDer k p B f P := by
  simp only [pPolyDer, Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun b _ => by ring

theorem pPolyDer_smul (f : B → K) (a : pSubring (K := K) k p)
    (P : MvPolynomial B (pSubring (K := K) k p)) :
    pPolyDer k p B f (a • P) = (a : K) * pPolyDer k p B f P := by
  rw [pPolyDer, pPolyDer, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [(pderiv b).map_smul, map_smul, Algebra.smul_def]
  change f b * ((a : K) * _) = _
  ring

theorem pPolyDer_pow_char [CharP K p] (f : B → K) (Q : MvPolynomial B (pSubring (K := K) k p)) :
    pPolyDer k p B f (Q ^ p) = 0 := by
  simp [pPolyDer, Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero]

theorem pPolyDer_X (f : B → K) (b : B) : pPolyDer k p B f (X b) = f b := by
  classical
  rw [pPolyDer, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [pderiv_X, Ne.symm hc]
  · simp

end Construction

variable {B : Finset K}

/-- The `L`-linear map `K → K` that sends the `p`-monomial of `α` to `pPolyDer f` of the polynomial `∏ X_b^α(b)`. -/
noncomputable def pBasisDerLinear (hB : IsPBasis k p B) (f : B → K) :
    K →ₗ[pSubring (K := K) k p] K :=
  (Module.Basis.mk hB.1 hB.2).constr (pSubring (K := K) k p)
    fun α => pPolyDer k p B f (pMonomialPoly k p B α)

theorem pBasisDerLinear_pMonomial (hB : IsPBasis k p B) (f : B → K) (α : B → Fin p) :
    pBasisDerLinear hB f (pMonomial B α) = pPolyDer k p B f (pMonomialPoly k p B α) := by
  have := (Module.Basis.mk hB.1 hB.2).constr_basis (pSubring (K := K) k p)
    (fun α => pPolyDer k p B f (pMonomialPoly k p B α)) α
  rwa [Module.Basis.mk_apply] at this

/-- The key step: the map `pBasisDerLinear f` composed with the evaluation is `pPolyDer f`. The proof uses that `∂(Q^p)/∂X_b = 0` in characteristic `p`. -/
theorem pBasisDerLinear_pEval [CharP K p] [NeZero p] (hB : IsPBasis k p B) (f : B → K)
    (P : MvPolynomial B (pSubring (K := K) k p)) :
    pBasisDerLinear hB f (pEval k p B P) = pPolyDer k p B f P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hu : monomial u a = a • ∏ b : B, (X b : MvPolynomial B (pSubring (K := K) k p)) ^ u b := by
      rw [monomial_eq, C_mul', Finsupp.prod_fintype]
      intro b; rw [pow_zero]
    rw [hu, map_smul, map_smul, pPolyDer_smul]
    congr 1
    obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial B (pSubring (K := K) k p), Q = ∏ b : B, X b ^ (u b / p) :=
      ⟨_, rfl⟩
    obtain ⟨α, hα⟩ : ∃ α : B → Fin p, ∀ b, (α b : ℕ) = u b % p :=
      ⟨fun b => ⟨u b % p, Nat.mod_lt _ (NeZero.pos p)⟩, fun _ => rfl⟩
    have hd : ∏ b : B, (X b : MvPolynomial B (pSubring (K := K) k p)) ^ u b =
        Q ^ p * pMonomialPoly k p B α := by
      rw [hQ, pMonomialPoly, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hα, ← pow_mul, ← pow_add, Nat.div_add_mod']
    have hc : pEval k p B Q ^ p ∈ pSubring (K := K) k p :=
      Subring.subset_closure (Or.inr ⟨_, rfl⟩)
    rw [hd, pPolyDer_mul, pPolyDer_pow_char, mul_zero, add_zero, map_mul, map_pow,
      pEval_pMonomialPoly]
    have : pEval k p B Q ^ p * pMonomial B α =
        (⟨pEval k p B Q ^ p, hc⟩ : pSubring (K := K) k p) • pMonomial B α := rfl
    rw [this, map_smul, pBasisDerLinear_pMonomial]
    rfl
  | add P Q hP hQ =>
    rw [map_add, map_add, hP, hQ, pPolyDer, pPolyDer, pPolyDer, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_add, map_add, mul_add]

theorem pEval_surjective (hB : IsPBasis k p B) (x : K) :
    ∃ P, pEval k p B P = x := by
  classical
  refine ⟨∑ α, (Module.Basis.mk hB.1 hB.2).repr x α • pMonomialPoly k p B α, ?_⟩
  rw [map_sum]
  conv_rhs => rw [← (Module.Basis.mk hB.1 hB.2).sum_repr x]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_smul, pEval_pMonomialPoly, Module.Basis.mk_apply]

/-- The derivation of the existence half of Theorem 6.2.3: for a finite `p`-basis `B` and a function `f : B → K`, a `k`-derivation of `K` that sends `b` to `f b`. -/
noncomputable def pBasisDerivation [CharP K p] [NeZero p] (hB : IsPBasis k p B) (f : B → K) :
    Derivation k K K :=
  Derivation.mk'
    { toFun := pBasisDerLinear hB f
      map_add' := map_add _
      map_smul' := fun c x => by
        have hc : algebraMap k K c ∈ pSubring (K := K) k p :=
          Subring.subset_closure (Or.inl ⟨c, rfl⟩)
        have : c • x = (⟨algebraMap k K c, hc⟩ : pSubring (K := K) k p) • x := by
          rw [Algebra.smul_def]; rfl
        rw [this, map_smul, RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
        rfl }
    fun x y => by
      obtain ⟨P, rfl⟩ := pEval_surjective hB x
      obtain ⟨Q, rfl⟩ := pEval_surjective hB y
      change pBasisDerLinear hB f _ = _ • pBasisDerLinear hB f _ + _ • pBasisDerLinear hB f _
      rw [← map_mul, pBasisDerLinear_pEval, pBasisDerLinear_pEval, pBasisDerLinear_pEval,
        pPolyDer_mul, smul_eq_mul, smul_eq_mul]

theorem pBasisDerivation_apply [CharP K p] [NeZero p] (hB : IsPBasis k p B) (f : B → K) (b : B) :
    pBasisDerivation hB f b = f b := by
  change pBasisDerLinear hB f (b : K) = f b
  have : (b : K) = pEval k p B (X b) := by simp [pEval]
  rw [this, pBasisDerLinear_pEval, pPolyDer_X]

/-- Theorem 6.2.3 of the handbook for a finite `p`-basis `B`: each function `B → K` extends to a unique `k`-derivation of `K`. -/
theorem existsUnique_derivation_pBasis [CharP K p] [NeZero p] (hB : IsPBasis k p B)
    (f : B → K) : ∃! D : Derivation k K K, ∀ b : B, D b = f b :=
  ⟨pBasisDerivation hB f, pBasisDerivation_apply hB f, fun D hD =>
    derivation_ext_pBasis hB fun b hb => by
      rw [hD ⟨b, hb⟩, pBasisDerivation_apply hB f ⟨b, hb⟩]⟩

/-- The `db` for `b` in a finite `p`-basis `B` are linearly independent in `Ω_{K/k}`. -/
theorem linearIndependent_D_pBasis [CharP K p] [NeZero p] (hB : IsPBasis k p B) :
    LinearIndependent K fun b : B => KaehlerDifferential.D k K b := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  let D := pBasisDerivation hB fun b => if b = i then (1 : K) else 0
  have := congrArg D.liftKaehlerDifferential hg
  rw [map_sum, map_zero, Finset.sum_eq_single i] at this
  · simpa [Derivation.liftKaehlerDifferential_comp_D, D, pBasisDerivation_apply] using this
  · intro j _ hj
    simp [Derivation.liftKaehlerDifferential_comp_D, D, pBasisDerivation_apply, hj]
  · intro h; exact absurd hi h

/-- Corollary 6.2.4 of the handbook, second claim: if `B` is a finite `p`-basis of `K` over `k`, then `dim_K Ω_{K/k} = |B|`. -/
theorem finrank_kaehler_eq_card [CharP K p] [NeZero p] (hB : IsPBasis k p B) :
    Module.finrank K (Ω[K⁄k]) = B.card := by
  have := finrank_span_eq_card (linearIndependent_D_pBasis hB)
  rwa [span_D_pBasis hB, finrank_top, Fintype.card_coe] at this

end Singularity.Algebra
