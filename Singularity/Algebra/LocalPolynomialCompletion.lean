import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# The completion of the local polynomial ring

This file proves Volume 1, Corollary 4.3.4 of the handbook.

Let `k` be a field and let `σ` be a finite type of variables. Let `A` be the
localization of `k[X_i : i ∈ σ]` at the ideal `(X_i : i ∈ σ)`. Then the
completion of `A` at its maximal ideal is isomorphic to `k[[X_i : i ∈ σ]]`.
Thus this completion is a domain.

The proof uses two steps.

* For each `n`, the quotient of `A` by the `n`-th power of its maximal ideal
  is isomorphic to the quotient of `k[X]` by `(X)^n`. These isomorphisms
  agree with the transition maps. Thus the two adic completions are
  isomorphic.
* Mathlib gives an isomorphism of `k[[X]]` with the `(X)`-adic completion
  of `k[X]`.

The handbook also states that the completion is a regular local ring of
dimension `n`. This file does not prove that part.
-/

namespace Singularity.Algebra

open IsLocalRing

section General

variable {S A : Type*} [CommRing S] [CommRing A]

/-- The map from the adic completion to `S ⧸ I ^ n` agrees with the
transition map from `S ⧸ I ^ n` to `S ⧸ I ^ m`. -/
theorem adicCompletion_factorPow_evalₐ (I : Ideal S) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I S) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I S x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have h := AdicCompletion.AdicCauchySequence.mk_eq_mk hle f
  rw [Submodule.Quotient.eq] at h
  simpa [smul_eq_mul, Ideal.mul_top] using h

/-- Let `e n` be ring isomorphisms from `S ⧸ I ^ n` to `A ⧸ J ^ n` that agree
with the transition maps. Then the `I`-adic completion of `S` is isomorphic to
the `J`-adic completion of `A`. -/
noncomputable def adicCompletionRingEquivOfQuotEquiv (I : Ideal S) (J : Ideal A)
    (e : ∀ n : ℕ, (S ⧸ I ^ n) ≃+* (A ⧸ J ^ n))
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (x : S ⧸ I ^ n),
      Ideal.Quotient.factorPow J hle (e n x) = e m (Ideal.Quotient.factorPow I hle x)) :
    AdicCompletion I S ≃+* AdicCompletion J A := by
  have he' : ∀ {m n : ℕ} (hle : m ≤ n) (y : A ⧸ J ^ n),
      Ideal.Quotient.factorPow I hle ((e n).symm y) =
        (e m).symm (Ideal.Quotient.factorPow J hle y) := by
    intro m n hle y
    apply (e m).injective
    rw [← he hle, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  let F : AdicCompletion I S →+* AdicCompletion J A :=
    AdicCompletion.liftRingHom J
      (fun n ↦ (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
      (fun hle ↦ by
        ext x
        simp [he hle, adicCompletion_factorPow_evalₐ])
  let G : AdicCompletion J A →+* AdicCompletion I S :=
    AdicCompletion.liftRingHom I
      (fun n ↦ (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom)
      (fun hle ↦ by
        ext y
        simp [he' hle, adicCompletion_factorPow_evalₐ])
  have hF : ∀ (n : ℕ) (x : AdicCompletion I S),
      AdicCompletion.evalₐ J n (F x) = e n (AdicCompletion.evalₐ I n x) :=
    fun n x ↦ AdicCompletion.evalₐ_liftRingHom J _ _ n x
  have hG : ∀ (n : ℕ) (y : AdicCompletion J A),
      AdicCompletion.evalₐ I n (G y) = (e n).symm (AdicCompletion.evalₐ J n y) :=
    fun n y ↦ AdicCompletion.evalₐ_liftRingHom I _ _ n y
  refine RingEquiv.ofRingHom F G ?_ ?_
  · ext y : 1
    refine AdicCompletion.ext_evalₐ (fun n ↦ ?_)
    rw [RingHom.comp_apply, hF, hG, RingEquiv.apply_symm_apply, RingHom.id_apply]
  · ext x : 1
    refine AdicCompletion.ext_evalₐ (fun n ↦ ?_)
    rw [RingHom.comp_apply, hG, hF, RingEquiv.symm_apply_apply, RingHom.id_apply]

end General

section Polynomial

variable (σ k : Type*) [Field k]

/-- The ideal `(X_i : i ∈ σ)` of `k[X_i : i ∈ σ]` is maximal. -/
theorem isMaximal_idealOfVars : (MvPolynomial.idealOfVars σ k).IsMaximal := by
  have h : MvPolynomial.idealOfVars σ k =
      RingHom.ker (MvPolynomial.constantCoeff (σ := σ) (R := k)) := by
    ext p
    rw [RingHom.mem_ker, ← pow_one (MvPolynomial.idealOfVars σ k),
      MvPolynomial.mem_pow_idealOfVars_iff']
    constructor
    · intro hp
      simpa [MvPolynomial.constantCoeff_eq] using hp 0 (by simp)
    · intro hp x hx
      rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hx
      subst hx
      simpa [MvPolynomial.constantCoeff_eq] using hp
  rw [h]
  exact RingHom.ker_isMaximal_of_surjective _
    (fun r ↦ ⟨MvPolynomial.C r, MvPolynomial.constantCoeff_C σ r⟩)

instance : (MvPolynomial.idealOfVars σ k).IsMaximal := isMaximal_idealOfVars σ k

/-- The local ring `k[X_i : i ∈ σ]` localized at `(X_i : i ∈ σ)`. -/
abbrev LocalPolynomialRing : Type _ :=
  Localization.AtPrime (MvPolynomial.idealOfVars σ k)

/-- Volume 1, Corollary 4.3.4 of the handbook. For a field `k` and a finite type
of variables `σ`, the completion of `k[X_i : i ∈ σ]` localized at
`(X_i : i ∈ σ)` is isomorphic to `k[[X_i : i ∈ σ]]`. -/
noncomputable def adicCompletionLocalPolynomialRingEquiv [Finite σ] :
    AdicCompletion (maximalIdeal (LocalPolynomialRing σ k)) (LocalPolynomialRing σ k) ≃+*
      MvPowerSeries σ k :=
  (adicCompletionRingEquivOfQuotEquiv (MvPolynomial.idealOfVars σ k)
      (maximalIdeal (LocalPolynomialRing σ k))
      (fun n ↦ (IsLocalization.AtPrime.equivQuotMaximalIdealPow
        (MvPolynomial.idealOfVars σ k) (LocalPolynomialRing σ k) n).toRingEquiv)
      (fun hle x ↦ by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl)).symm.trans
    (MvPowerSeries.toAdicCompletionAlgEquiv σ k).symm.toRingEquiv

/-- The completion of the local polynomial ring over a field at its maximal
ideal is a domain. -/
theorem isDomain_adicCompletion_localPolynomialRing [Finite σ] :
    IsDomain (AdicCompletion (maximalIdeal (LocalPolynomialRing σ k))
      (LocalPolynomialRing σ k)) :=
  haveI : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
  (adicCompletionLocalPolynomialRingEquiv σ k).isDomain

end Polynomial

end Singularity.Algebra
