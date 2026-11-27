/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.FrobeniusBasis
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The monomial basis of a polynomial ring over the polynomials in `x^q`

This file proves Volume 1, Proposition 6.1.5 of the handbook for polynomials. Let `K` be a commutative ring, let `q > 0` and let `S = K[x_1, ..., x_n]`. Let `S_e` be the subalgebra of the polynomials whose coefficients vanish outside the exponents in `q ℕ^n`. This is the ring `K[x_1^q, ..., x_n^q]`. Then `S` is a free `S_e`-module, with basis the monomials `x^α` with `0 ≤ α_i < q` for each `i`.

* `Singularity.Algebra.powSubalgebraPoly`: the subalgebra `S_e`.
* `Singularity.Algebra.boxBasisPoly`: the basis of the monomials `x^α` with `α_i < q`.
* `Singularity.Algebra.finrank_powSubalgebraPoly`: the rank of `S` over `S_e` is `q^n`.

The proof is the proof of `Singularity/Algebra/FrobeniusBasis.lean` for power series. Each exponent `β` is `qγ + α` in exactly one way with `α_i < q`. The handbook states the result for a field `K` of characteristic `p` and `q = p^e`. The proof uses neither hypothesis. The file does not prove that `S_e` is the image of the map `x_i ↦ x_i^q`.
-/

open MvPolynomial

namespace Singularity.Algebra

variable (σ K : Type*) [CommRing K]

/-- The subalgebra `K[x_1^q, ..., x_n^q]` of `K[x_1, ..., x_n]`: the polynomials whose coefficient at `β` is zero unless `q` divides each `β_i`. -/
def powSubalgebraPoly (q : ℕ) : Subalgebra K (MvPolynomial σ K) where
  carrier := {f | ∀ β : σ →₀ ℕ, (¬ ∀ i, q ∣ β i) → f.coeff β = 0}
  mul_mem' := by
    classical
    intro f g hf hg β hβ
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    by_cases h1 : ∀ i, q ∣ p.1 i
    · have h2 : ¬ ∀ i, q ∣ p.2 i := by
        intro h2
        apply hβ
        intro i
        rw [← hp, Finsupp.add_apply]
        exact dvd_add (h1 i) (h2 i)
      rw [hg _ h2, mul_zero]
    · rw [hf _ h1, zero_mul]
  add_mem' := by
    intro f g hf hg β hβ
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf β hβ, hg β hβ, add_zero]
  algebraMap_mem' := by
    classical
    intro a β hβ
    have h0 : β ≠ 0 := by rintro rfl; exact hβ fun i => by simp
    rw [algebraMap_eq, coeff_C, ite_eq_right (Ne.symm h0)]

variable {σ K}

theorem mem_powSubalgebraPoly {q : ℕ} {f : MvPolynomial σ K} :
    f ∈ powSubalgebraPoly σ K q ↔ ∀ β : σ →₀ ℕ, (¬ ∀ i, q ∣ β i) → f.coeff β = 0 :=
  Iff.rfl

variable [Fintype σ] [DecidableEq σ]

/-- The coefficient of `∑_α g_α x^α` at `m`, for polynomials. -/
theorem coeff_sum_mul_monomial_poly {q : ℕ} (g : (σ → Fin q) → MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    (∑ α, g α * monomial (boxExp α) (1 : K)).coeff m =
      ∑ α, if boxExp α ≤ m then (g α).coeff (m - boxExp α) else 0 := by
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_mul_monomial', mul_one]

variable (K) in
theorem linearIndependent_boxMonomialPoly {q : ℕ} :
    LinearIndependent (powSubalgebraPoly σ K q)
      (fun α : σ → Fin q => (monomial (boxExp α) (1 : K) : MvPolynomial σ K)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg α
  simp only [Subalgebra.smul_def, smul_eq_mul] at hg
  apply Subtype.ext
  ext β
  rw [ZeroMemClass.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_cases hβ : ∀ i, q ∣ β i
  · have h := congrArg (fun F : MvPolynomial σ K => F.coeff (β + boxExp α)) hg
    rw [coeff_sum_mul_monomial_poly, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      Finset.sum_eq_single α] at h
    · rwa [ite_eq_left le_add_self, add_tsub_cancel_right] at h
    · intro α' _ hne
      split_ifs with hle
      · apply (g α').2
        intro hdvd
        apply hne
        funext i
        apply Fin.ext
        have hle' := (Finsupp.le_def.1 hle) i
        rw [boxExp_apply, Finsupp.add_apply, boxExp_apply] at hle'
        have h1 : (β i + α i) % q = α' i := by
          refine mod_eq_of_dvd_sub (α' i).2 hle' ?_
          have := hdvd i
          rwa [Finsupp.tsub_apply, Finsupp.add_apply, boxExp_apply, boxExp_apply] at this
        have h2 : (β i + α i) % q = α i := by
          refine mod_eq_of_dvd_sub (α i).2 le_add_self ?_
          rw [Nat.add_sub_cancel]
          exact hβ i
        exact h1.symm.trans h2
      · rfl
    · intro h
      exact absurd (Finset.mem_univ α) h
  · exact (g α).2 β hβ

/-- The coordinate `f_α ∈ K[x_1^q, ..., x_n^q]` of a polynomial `f` at `α`: the polynomial with coefficient `c_{β + α}` at each `β ∈ q ℕ^n`. -/
noncomputable def boxCoordPoly {q : ℕ} (f : MvPolynomial σ K) (α : σ → Fin q) :
    powSubalgebraPoly σ K q := by
  classical
  exact ⟨AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun β : σ →₀ ℕ => ∀ i, q ∣ β i)
      (Finsupp.comapDomain (· + boxExp α) f.coeff
        (add_left_injective (boxExp α)).injOn)), fun β hβ =>
    Finsupp.filter_apply_neg _ _ hβ⟩

omit [DecidableEq σ] in
theorem coeff_boxCoordPoly {q : ℕ} (f : MvPolynomial σ K) (α : σ → Fin q) (β : σ →₀ ℕ) :
    (boxCoordPoly f α : MvPolynomial σ K).coeff β =
      if ∀ i, q ∣ β i then f.coeff (β + boxExp α) else 0 := by
  classical
  change (Finsupp.filter _ _ : (σ →₀ ℕ) →₀ K) β = _
  rw [Finsupp.filter_apply, Finsupp.comapDomain_apply]

theorem sum_boxCoordPoly_mul {q : ℕ} (hq : 0 < q) (f : MvPolynomial σ K) :
    ∑ α : σ → Fin q, (boxCoordPoly f α : MvPolynomial σ K) * monomial (boxExp α) (1 : K) =
      f := by
  classical
  ext m
  rw [coeff_sum_mul_monomial_poly]
  let α₀ : σ → Fin q := fun i => ⟨m i % q, Nat.mod_lt _ hq⟩
  have hle₀ : boxExp α₀ ≤ m := Finsupp.le_def.2 fun i => by
    rw [boxExp_apply]
    exact Nat.mod_le _ _
  rw [Finset.sum_eq_single α₀]
  · rw [ite_eq_left hle₀, coeff_boxCoordPoly, ite_eq_left, tsub_add_cancel_of_le hle₀]
    intro i
    rw [Finsupp.tsub_apply, boxExp_apply]
    exact Nat.dvd_sub_mod _
  · intro α _ hne
    split_ifs with hle
    · rw [coeff_boxCoordPoly, ite_eq_right]
      intro hdvd
      apply hne
      funext i
      apply Fin.ext
      have hle' := (Finsupp.le_def.1 hle) i
      rw [boxExp_apply] at hle'
      have := hdvd i
      rw [Finsupp.tsub_apply, boxExp_apply] at this
      exact (mod_eq_of_dvd_sub (α i).2 hle' this).symm
    · rfl
  · intro h
    exact absurd (Finset.mem_univ α₀) h

variable (σ K) in
/-- Volume 1, Proposition 6.1.5 of the handbook for polynomials: the monomials `x^α` with `0 ≤ α_i < q` are a basis of `K[x_1, ..., x_n]` over `K[x_1^q, ..., x_n^q]`. -/
noncomputable def boxBasisPoly {q : ℕ} (hq : 0 < q) :
    Module.Basis (σ → Fin q) (powSubalgebraPoly σ K q) (MvPolynomial σ K) :=
  Module.Basis.mk (linearIndependent_boxMonomialPoly K) fun f _ => by
    rw [← sum_boxCoordPoly_mul hq f]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [← smul_eq_mul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

theorem boxBasisPoly_apply {q : ℕ} (hq : 0 < q) (α : σ → Fin q) :
    boxBasisPoly σ K hq α = monomial (boxExp α) 1 :=
  Module.Basis.mk_apply _ _ _

variable (σ K) in
/-- The ring `K[x_1, ..., x_n]` is a free module of rank `q^n` over `K[x_1^q, ..., x_n^q]`. -/
theorem finrank_powSubalgebraPoly [Nontrivial K] {q : ℕ} (hq : 0 < q) :
    Module.Free (powSubalgebraPoly σ K q) (MvPolynomial σ K) ∧
      Module.finrank (powSubalgebraPoly σ K q) (MvPolynomial σ K) = q ^ Fintype.card σ := by
  refine ⟨Module.Free.of_basis (boxBasisPoly σ K hq), ?_⟩
  rw [Module.finrank_eq_card_basis (boxBasisPoly σ K hq)]
  simp

end Singularity.Algebra
