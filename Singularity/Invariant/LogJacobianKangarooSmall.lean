/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianCaseAForms

/-!
# The kangaroo path conjecture if `τ_ρ(P_0) ≤ 1`

This file proves Proposition 3.11.5 of Volume 7, Section 3.11 of the handbook: Conjecture 3.11.3
holds if `τ_ρ(P_0) ≤ 1`. The proof uses two facts on `τ_ρ`, which hold at each point.

* If `ρ = 0`, then `τ_ρ = 0`. The part of degree `0` of each `ψ` is a constant, and the directrix
  of a constant is the full space.
* If `1 ≤ ρ < ∞` and the point is of case A, then `τ_ρ ≥ 1`. The order of `Θ₀(g)` is `|r| + ρ`,
  and the ideal has an element of this order. This element is `x^r ψ` with `ord ψ = ρ`, so the
  part `ψ_ρ` of degree `ρ` of `ψ` is a form of positive degree and is not `0`. The directrix of
  such a form is not the full space (`eq_zero_of_directrix_eq_top`).

The directrix of `F` is the set of the `v` with `F(x + s v) = F(x)` in `k[x, s]`. If it is the
full space, then for each `i` the substitution `s ↦ x_i`, `x_i ↦ 0` gives `F = F|_{x_i = 0}`, so
no monomial of `F` contains `x_i`. Thus `F` is a constant. This argument works over each field,
also over a finite field.

## Main results

* `eq_zero_of_directrix_eq_top`: a polynomial with constant term `0` and with the full space as
  directrix is `0`.
* `logJacobianDirectrixCodim_eq_zero_of_order_eq_zero`: if `ρ = 0`, then `τ_ρ = 0`.
* `one_le_logJacobianDirectrixCodim_of_caseA`: in case A with `ρ = m ≥ 1`, `τ_ρ ≥ 1`.
* `logJacobianDirectrixCodim_le_of_le_one`: if `ρ = m` at `P` and at `R`, `R` is of case A and
  `τ_ρ(P) ≤ 1`, then `τ_ρ(P) ≤ τ_ρ(R)`.
* `kangarooPath_of_codim_le_one`: Proposition 3.11.5, the conclusion of `KangarooPathConjecture`
  if `τ_ρ(P_0) ≤ 1`.

## References

* Volume 7, Section 3.11 of the handbook: Conjecture 3.11.3 and Proposition 3.11.5.
-/

open MvPolynomial Finsupp Module

namespace Singularity

section KillVar

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- The substitution `x_i ↦ 0` kills each monomial that contains `x_i`, and fixes the other
monomials. -/
theorem killVar_monomial (i : σ) (a : σ →₀ ℕ) (c : k) :
    killVar i (monomial a c) = if a i = 0 then monomial a c else 0 := by
  rw [killVar, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finsupp.prod_congr fun l hl => ?_
    rw [ite_eq_right]
    rintro rfl
    exact Finsupp.mem_support_iff.mp hl h
  · rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr h)
      (by rw [ite_eq_left rfl, zero_pow h]), mul_zero]

/-- The polynomial `F|_{x_i = 0}` has no monomial that contains `x_i`. -/
theorem coeff_killVar_eq_zero {i : σ} {a : σ →₀ ℕ} (ha : a i ≠ 0) (F : MvPolynomial σ k) :
    (killVar i F).coeff a = 0 := by
  refine MvPolynomial.induction_on' F (fun b c => ?_) (fun f g hf hg => ?_)
  · rw [killVar_monomial]
    split_ifs with hb
    · rw [coeff_monomial, ite_eq_right]
      rintro rfl
      exact ha hb
    · rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg, add_zero]

/-- The substitution `s ↦ x_i`, `x_i ↦ 0` from `k[x, s]` into `k[x]`. The other variables are
fixed. -/
noncomputable def killVarSwap (i : σ) : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
  aeval fun o => Option.elim o (X i) fun l => if l = i then 0 else X l

/-- The substitution `killVarSwap i` sends `F(x + s e_i)` to `F`. -/
theorem killVarSwap_comp_translate (i : σ) :
    (killVarSwap i).comp (translate (Pi.single i 1 : σ → k)) = AlgHom.id k _ := by
  refine algHom_ext fun l => ?_
  by_cases hl : l = i
  · subst hl
    simp [killVarSwap, translate]
  · simp [killVarSwap, translate, hl, Pi.single_apply]

/-- The substitution `killVarSwap i` sends `F(x)` to `F|_{x_i = 0}`. -/
theorem killVarSwap_comp_rename (i : σ) :
    (killVarSwap i).comp (rename some : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k) =
      killVar i := by
  refine algHom_ext fun l => ?_
  simp [killVarSwap, killVar]

/-- **A polynomial with the full space as directrix is a constant.** If the constant term of `F`
is `0` and `T(F)` is the full space, then `F = 0`. -/
theorem eq_zero_of_directrix_eq_top {F : MvPolynomial σ k} (h0 : constantCoeff F = 0)
    (h : directrix F = ⊤) : F = 0 := by
  have hk : ∀ i, killVar i F = F := by
    intro i
    have hv : (Pi.single i 1 : σ → k) ∈ directrix F := by
      rw [h]
      exact Submodule.mem_top
    calc killVar i F = killVarSwap i (rename some F) :=
          (AlgHom.congr_fun (killVarSwap_comp_rename i) F).symm
      _ = killVarSwap i (translate (Pi.single i 1) F) := congrArg _ (mem_directrix_iff.mp hv).symm
      _ = F := AlgHom.congr_fun (killVarSwap_comp_translate i) F
  ext a
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_cases ha : a = 0
  · rw [ha]
    exact h0
  · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp ha
    rw [← hk i]
    exact coeff_killVar_eq_zero hi F

end KillVar

section Small

variable {σ k : Type*} [Field k] [Fintype σ]

/-- **If `ρ = 0`, then `τ_ρ = 0`.** The part of degree `0` of each `ψ` is a constant. -/
theorem logJacobianDirectrixCodim_eq_zero_of_order_eq_zero {Δ : Finset σ}
    {g : MvPolynomial σ k} (hρ : logJacobianOrder Δ g = 0) :
    logJacobianDirectrixCodim Δ g = 0 := by
  have htop : logJacobianDirectrix Δ g = ⊤ := by
    refine eq_top_iff.mpr (le_logJacobianDirectrix fun ψ _ => ?_)
    rw [hρ, ENat.toNat_zero, homogeneousComponent_zero]
    intro v _
    rw [mem_directrix_iff, algHom_C, algHom_C]
  rw [logJacobianDirectrixCodim, htop, finrank_top, Module.finrank_fintype_fun_eq_card,
    Nat.sub_self]

/-- **In case A with `ρ ≥ 1`, `τ_ρ ≥ 1`.** The ideal `Θ₀(g)` has an element `x^r ψ` of order
`|r| + ρ`, and the part of degree `ρ` of `ψ` is a nonzero form of positive degree. -/
theorem one_le_logJacobianDirectrixCodim_of_caseA {Δ : Finset σ} {g : MvPolynomial σ k} {m : ℕ}
    (hρ : logJacobianOrder Δ g = m) (hm : m ≠ 0) (hA : IsLogJacobianCaseA (Δ, g)) :
    1 ≤ logJacobianDirectrixCodim Δ g := by
  have hA' : idealOrd (logJacobianTangent Δ g) =
      ((degree (divisorExponent Δ g) : ℕ) : ℕ∞) + logJacobianOrder Δ g := hA
  have hI : logJacobianCaseIdeal Δ g = logJacobianTangent Δ g :=
    logJacobianCaseIdeal_of_eq (by exact_mod_cast hA')
  have hm' : (logJacobianOrder Δ g).toNat = m := by rw [hρ]; rfl
  have heq : logJacobianTangent Δ g = Ideal.span {monomial (divisorExponent Δ g) 1} *
      residualLogJacobianTangent Δ (divisorExponent Δ g) (residualFactor Δ g) := by
    conv_lhs => rw [← monomial_mul_residualFactor Δ g]
    exact logJacobianTangent_monomial_mul (fun _ hi => divisorExponent_eq_zero hi) _
  obtain ⟨f, hf, hford⟩ := exists_mem_ord_eq_idealOrd (logJacobianTangent Δ g)
  have hf' := hf
  rw [heq] at hf'
  obtain ⟨ψ, -, rfl⟩ := Ideal.mem_span_singleton_mul.mp hf'
  have h1 := hford
  rw [ord_mul, ord_monomial one_ne_zero, hA', hρ] at h1
  have hψ : ord ψ = m := WithTop.add_left_cancel (ENat.natCast_ne_top _) h1
  have hmem : ψ ∈ logJacobianDirectrixSet Δ g := ⟨by rw [hψ, hρ], by rw [hI]; exact hf⟩
  have hψ0 : ψ ≠ 0 := by
    intro h
    have h' := ord_eq_top_iff.mpr h
    rw [hψ] at h'
    exact ENat.natCast_ne_top m h'
  obtain ⟨a, ha, hdeg⟩ := exists_coeff_ne_zero_and_ord_eq hψ0
  have hda : degree a = m := by
    rw [hψ] at hdeg
    exact_mod_cast hdeg.symm
  have hne0 : homogeneousComponent m ψ ≠ 0 := by
    intro h0
    have := congrArg (fun q => q.coeff a) h0
    simp only [coeff_homogeneousComponent, hda, ↓reduceIte, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at this
    exact ha this
  have hcc : constantCoeff (homogeneousComponent m ψ) = 0 := by
    rw [constantCoeff_eq, coeff_homogeneousComponent, ite_eq_right]
    intro h
    rw [map_zero] at h
    exact hm h.symm
  have hT : logJacobianDirectrix Δ g ≠ ⊤ := by
    intro htop
    have hle := logJacobianDirectrix_le hmem
    rw [htop, hm', top_le_iff] at hle
    classical
    exact hne0 (eq_zero_of_directrix_eq_top hcc hle)
  have hlt := Submodule.finrank_lt hT
  rw [Module.finrank_fintype_fun_eq_card] at hlt
  unfold logJacobianDirectrixCodim
  omega

/-- **The comparison if `τ_ρ(P) ≤ 1`.** Let `ρ = m` at `P` and at `R`, and let `R` be of case A.
If `τ_ρ(P) ≤ 1`, then `τ_ρ(P) ≤ τ_ρ(R)`. -/
theorem logJacobianDirectrixCodim_le_of_le_one {m : ℕ} {P R : Finset σ × MvPolynomial σ k}
    (hP : logJacobianOrder P.1 P.2 = m) (hR : logJacobianOrder R.1 R.2 = m)
    (hA : IsLogJacobianCaseA R) (h1 : logJacobianDirectrixCodim P.1 P.2 ≤ 1) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianDirectrixCodim R.1 R.2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [logJacobianDirectrixCodim_eq_zero_of_order_eq_zero (by rw [hP, Nat.cast_zero])]
    exact Nat.zero_le _
  · exact h1.trans (one_le_logJacobianDirectrixCodim_of_caseA hR hm.ne' hA)

end Small

section Path

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ]

/-- **The kangaroo path if `τ_ρ(P_0) ≤ 1`** (Volume 7, Section 3.11 of the handbook,
Proposition 3.11.5). The conclusion of `KangarooPathConjecture` holds if `τ_ρ(P_0) ≤ 1`. -/
theorem kangarooPath_of_codim_le_one {p : ℕ} [CharP k p] {m : ℕ}
    {P Q R : Finset σ × MvPolynomial σ k}
    (hPQ : Relation.TransGen (fun A B => RhoStep p m A B ∧ IsLogJacobianCaseB B) P Q)
    (hQR : RhoStep p m Q R) (hR : IsLogJacobianCaseA R)
    (h1 : logJacobianDirectrixCodim P.1 P.2 ≤ 1) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianDirectrixCodim R.1 R.2 := by
  obtain ⟨B, ⟨hs, -⟩, -⟩ := Relation.TransGen.head'_iff.mp hPQ
  obtain ⟨_, _, _, _, _, _, _, _, hρP, -⟩ := hs
  obtain ⟨_, _, _, _, _, _, _, _, -, hρR⟩ := hQR
  exact logJacobianDirectrixCodim_le_of_le_one hρP hρR hR h1

end Path

end Singularity
