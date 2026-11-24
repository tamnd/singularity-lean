/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# The inequality of Abhyankar

This file proves the inequality of Abhyankar for a valuation of a field (node SG0000000Y, Theorem 2.1.5 of Volume 3 of the handbook). Let `A` be a valuation subring of a field `K`, and let `k` be a subfield of `A`. Then the rational rank of the value group of `A` plus the transcendence degree of the residue field of `A` over `k` is at most the transcendence degree of `K` over `k`.

The file also proves the relative form (Theorem 2.1.4 of the handbook). Let `vL` be a valuation of `L` that extends a valuation `vK` of a subfield `K`. Then the rank of the value group of `vL` modulo the value group of `vK`, plus the transcendence degree of the residue field extension, is at most the transcendence degree of `L` over `K`.

## Main results

* `Singularity.algebraicIndependent_sumElim_of_monoidHom`: the monomial argument. Elements with values that are independent over `ℤ`, together with elements whose polynomials have unit values, are algebraically independent.
* `Singularity.algebraicIndependent_sumElim_of_valuationSubring`: the case of a valuation subring that contains `k`.
* `Singularity.abhyankar_inequality`: the inequality of Abhyankar, with the rank over `ℚ` of `ℚ ⊗[ℤ] Γ`.
* `Singularity.exists_valuation_aeval_eq`: Lemma 2.1.2 of the handbook. If the residues of `y` are algebraically independent over the residue field of `K`, then each nonzero polynomial over `K` in `y` has the value of an element of `K`.
* `Singularity.algebraicIndependent_sumElim_of_hasExtension`: Theorem 2.1.4 of the handbook, for families of each size.
* `Singularity.rank_int_valueGroup_map_add_trdeg_le` and `Singularity.abhyankar_inequality_relative`: the relative inequality.

## The proof

Let `F` be a polynomial in the variables `x` and `y` with `F(x, y) = 0`. Write `F` as a sum of monomials `G_d(y) x^d`, where each `G_d` is a polynomial in `y` only. Each nonzero `G_d(y)` has the value of an element `c_d` with trivial class. The values of `x` are independent, so the values of the terms `G_d(y) x^d` are all different. The term of maximal value then has the value of the sum, and this value is not zero. This is a contradiction.

The inequality for cardinals follows from the inequality for each pair of an independent family of the value group and an algebraically independent family of the residue field. The lemma `ciSup_add_ciSup_le_of_forall` takes the supremum over these pairs.

The relative value group is the image of the value group of `vL` in the quotient of `Γ₁ˣ` by the value group of the restriction of `vL` to `K`. This image is isomorphic to the quotient of the two value groups.

## References

* [Abh56] S. Abhyankar, On the valuations centered in a local domain.
* [ZS2] O. Zariski and P. Samuel, Commutative Algebra II, Chapter VI, Section 10.
* [Kuh-book] F.-V. Kuhlmann, Valuation Theory.
-/

universe u

namespace Singularity

open MvPolynomial Cardinal TensorProduct

section Monomial

/-- If the family `u` of a commutative group is linearly independent over `ℤ` in additive
notation, then distinct exponents give distinct monomials `∏ uᵢ ^ aᵢ`. -/
theorem injective_prod_pow_of_linearIndependent {ι G : Type*} [CommGroup G] {u : ι → G}
    (hu : LinearIndependent ℤ (fun i => Additive.ofMul (u i))) :
    Function.Injective (fun a : ι →₀ ℕ => a.prod fun i n => u i ^ n) := by
  have hN : LinearIndependent ℕ (fun i => Additive.ofMul (u i)) :=
    hu.restrict_scalars' ℕ
  intro a b hab
  apply hN
  have := congrArg Additive.ofMul hab
  simpa [Finsupp.linearCombination_apply, Finsupp.prod, Finsupp.sum, ofMul_prod, ofMul_pow]
    using this

end Monomial

section Valuation

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The monomial argument. Let `π` be a map of `Kˣ` to a group `Q` that is constant on each class of
elements with the same value. Let `x` be units whose images under `π` are independent over `ℤ`.
Let `y` be elements such that each nonzero polynomial over `k` in `y` has the value of a unit `c`
with `π c = 1`. Then the family of `x` and `y` is algebraically independent over `k`. -/
theorem algebraicIndependent_sumElim_of_monoidHom {k : Type*} [CommRing k] [Algebra k K]
    (v : Valuation K Γ₀) {Q : Type*} [CommGroup Q] (π : Kˣ →* Q)
    (hπ : ∀ a b : Kˣ, v a = v b → π a = π b) {ι κ : Type*} (x : ι → Kˣ)
    (hx : LinearIndependent ℤ (fun i => Additive.ofMul (π (x i))))
    (y : κ → K)
    (hy : ∀ P : MvPolynomial κ k, P ≠ 0 → ∃ c : Kˣ, π c = 1 ∧ v (aeval y P) = v c) :
    AlgebraicIndependent k (Sum.elim (fun i => (x i : K)) y) := by
  classical
  rw [algebraicIndependent_iff]
  intro F hF
  by_contra hF0
  set G := sumRingEquiv k ι κ F
  have hG0 : G ≠ 0 := (map_ne_zero_iff _ (sumRingEquiv k ι κ).injective).mpr hF0
  have hev : (aeval (Sum.elim (fun i => (x i : K)) y)).toRingHom =
      (eval₂Hom (aeval y).toRingHom (fun i => (x i : K))).comp
        (sumRingEquiv k ι κ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [sumRingEquiv_C]
    · rintro (i | j) <;> simp [sumRingEquiv_X_inl, sumRingEquiv_X_inr]
  have heval : aeval (Sum.elim (fun i => (x i : K)) y) F =
      eval₂ (aeval y).toRingHom (fun i => (x i : K)) G := by
    have := RingHom.congr_fun hev F
    simpa using this
  rw [heval, eval₂_eq] at hF
  have hc : ∀ d, ∃ c : Kˣ, G.coeff d ≠ 0 → π c = 1 ∧ v (aeval y (G.coeff d)) = v c := by
    intro d
    by_cases hd : G.coeff d = 0
    · exact ⟨1, fun h => absurd hd h⟩
    · obtain ⟨c, hc⟩ := hy _ hd
      exact ⟨c, fun _ => hc⟩
  choose c hc using hc
  set e : (ι →₀ ℕ) → Kˣ := fun d => c d * d.prod fun i n => x i ^ n with he_def
  have hterm : ∀ d ∈ G.support,
      v ((aeval y).toRingHom (G.coeff d) * ∏ i ∈ d.support, (x i : K) ^ d i) = v (e d : K) := by
    intro d hd
    have h1 := (hc d (mem_support_iff.mp hd)).2
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, he_def, Units.val_mul, map_mul, h1,
      Finsupp.prod, Units.coe_prod, Units.val_pow_eq_pow_val]
  have hπe : ∀ d ∈ G.support, π (e d) = d.prod fun i n => π (x i) ^ n := by
    intro d hd
    rw [he_def, map_mul, (hc d (mem_support_iff.mp hd)).1, one_mul, map_finsuppProd]
    simp [map_pow]
  have hinj := injective_prod_pow_of_linearIndependent hx
  have hne : G.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hG0)
  obtain ⟨d₀, hd₀, hmax⟩ := G.support.exists_max_image (fun d => v (e d : K)) hne
  have hsum := v.map_sum_eq_of_lt hd₀ (f := fun d =>
      (aeval y).toRingHom (G.coeff d) * ∏ i ∈ d.support, (x i : K) ^ d i) (by
    intro d hd
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hd
    rw [hterm d hd.1, hterm d₀ hd₀]
    refine lt_of_le_of_ne (hmax d hd.1) ?_
    intro h
    apply hd.2
    apply hinj
    simp only
    rw [← hπe d hd.1, ← hπe d₀ hd₀]
    exact hπ _ _ h)
  rw [hF, map_zero, hterm d₀ hd₀] at hsum
  exact (Valuation.ne_zero_iff v).mpr (e d₀).ne_zero hsum.symm

/-- Units with values that are independent over `ℤ`, together with elements such that each nonzero
polynomial in them has value `1`, are algebraically independent. -/
theorem algebraicIndependent_sumElim_of_valuation {k : Type*} [CommRing k] [Algebra k K]
    (v : Valuation K Γ₀) {ι κ : Type*} (x : ι → Kˣ)
    (hx : LinearIndependent ℤ (fun i => Additive.ofMul (Units.map (v : K →* Γ₀) (x i))))
    (y : κ → K) (hy : ∀ P : MvPolynomial κ k, P ≠ 0 → v (aeval y P) = 1) :
    AlgebraicIndependent k (Sum.elim (fun i => (x i : K)) y) :=
  algebraicIndependent_sumElim_of_monoidHom v (Units.map (v : K →* Γ₀))
    (fun a b h => Units.ext (by simpa using h)) x hx y
    (fun P hP => ⟨1, map_one _, by rw [hy P hP, Units.val_one, map_one]⟩)

end Valuation

section Cardinal

/-- The sum of two suprema of cardinals is at most `c` when each sum of two terms is at most
`c`. -/
theorem ciSup_add_ciSup_le_of_forall {ι κ : Type*} [Nonempty ι] [Nonempty κ]
    {f : ι → Cardinal.{u}} {g : κ → Cardinal.{u}} (hf : BddAbove (Set.range f))
    (hg : BddAbove (Set.range g)) {c : Cardinal.{u}} (h : ∀ i j, f i + g j ≤ c) :
    iSup f + iSup g ≤ c := by
  have hfc : iSup f ≤ c :=
    ciSup_le' fun i => (self_le_add_right _ _).trans (h i (Classical.arbitrary κ))
  have hgc : iSup g ≤ c :=
    ciSup_le' fun j => (self_le_add_left _ _).trans (h (Classical.arbitrary ι) j)
  by_cases hc : ℵ₀ ≤ c
  · calc iSup f + iSup g ≤ c + c := add_le_add hfc hgc
      _ = c := Cardinal.add_eq_self hc
  · have hfl : ¬ Order.IsSuccLimit (iSup f) :=
      fun hl => hc ((Cardinal.aleph0_le_of_isSuccLimit hl).trans hfc)
    have hgl : ¬ Order.IsSuccLimit (iSup g) :=
      fun hl => hc ((Cardinal.aleph0_le_of_isSuccLimit hl).trans hgc)
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_not_isSuccLimit hf hfl
    obtain ⟨j, hj⟩ := exists_eq_ciSup_of_not_isSuccLimit hg hgl
    rw [← hi, ← hj]
    exact h i j

end Cardinal

section ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- Let `A` be a valuation subring of `K` that is an algebra over `k`. Units of `K` with values that
are independent over `ℤ`, together with elements of `A` with residues that are algebraically
independent over `k`, are algebraically independent over `k`. -/
theorem algebraicIndependent_sumElim_of_valuationSubring {k : Type*} [CommRing k] [Algebra k K]
    [Algebra k A] [IsScalarTower k A K] {ι κ : Type*} (x : ι → Kˣ)
    (hx : LinearIndependent ℤ
      (fun i => Additive.ofMul (Units.map (A.valuation : K →* A.ValueGroup) (x i))))
    (y : κ → A) (hy : AlgebraicIndependent k (fun j => IsLocalRing.residue A (y j))) :
    AlgebraicIndependent k (Sum.elim (fun i => (x i : K)) (fun j => (y j : K))) := by
  refine algebraicIndependent_sumElim_of_valuation A.valuation x hx _ fun P hP => ?_
  have h1 : aeval (fun j => (y j : K)) P = ((aeval y P : A) : K) := by
    exact (MvPolynomial.comp_aeval_apply (f := y) (IsScalarTower.toAlgHom k A K) P).symm
  have h2 : aeval (fun j => IsLocalRing.residue A (y j)) P =
      IsLocalRing.residue A (aeval y P) := by
    have := MvPolynomial.comp_aeval_apply (f := y)
      (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)) P
    simpa using this.symm
  have h3 : IsLocalRing.residue A (aeval y P) ≠ 0 := by
    rw [← h2]
    exact fun h => hP (algebraicIndependent_iff.mp hy P h)
  rw [h1, ← A.valuation_eq_one_iff]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h3

/-- The inequality of Abhyankar with the rank over `ℤ` of the value group: the rank of the value
group of `A` plus the transcendence degree of the residue field of `A` over `k` is at most the
transcendence degree of `K` over `k`. -/
theorem rank_int_valueGroup_add_trdeg_le {k : Type*} [Field k] [Algebra k K] [Algebra k A]
    [IsScalarTower k A K] :
    Module.rank ℤ (Additive A.ValueGroupˣ) + Algebra.trdeg k (IsLocalRing.ResidueField A) ≤
      Algebra.trdeg k K := by
  rw [Module.rank_def, Algebra.trdeg]
  refine ciSup_add_ciSup_le_of_forall bddAbove_of_small bddAbove_of_small ?_
  rintro ⟨s, hs⟩ ⟨t, ht⟩
  have hx : ∀ γ : s, ∃ z : Kˣ, Units.map (A.valuation : K →* A.ValueGroup) z =
      Additive.toMul (γ : Additive A.ValueGroupˣ) := by
    intro γ
    obtain ⟨z, hz⟩ := A.valuation_surjective (Additive.toMul (γ : Additive A.ValueGroupˣ) : _)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact (Additive.toMul (γ : Additive A.ValueGroupˣ)).ne_zero (by simpa using hz.symm)
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose x hx using hx
  have hy : ∀ e : t, ∃ a : A, IsLocalRing.residue A a = e := fun e =>
    IsLocalRing.residue_surjective (R := A) (e : IsLocalRing.ResidueField A)
  choose y hy using hy
  have hs' : LinearIndependent ℤ (fun i : s => (i : Additive A.ValueGroupˣ)) := hs
  have ht' : AlgebraicIndependent k (fun j : t => (j : IsLocalRing.ResidueField A)) := ht
  have hli : LinearIndependent ℤ
      (fun i => Additive.ofMul (Units.map (A.valuation : K →* A.ValueGroup) (x i))) := by
    convert hs' using 1
    funext i
    simp [hx i]
  have hai : AlgebraicIndependent k (fun j => IsLocalRing.residue A (y j)) := by
    convert ht' using 1
    funext j
    simp [hy j]
  have := (algebraicIndependent_sumElim_of_valuationSubring A x hli y hai).cardinalMk_le_trdeg
  change #s + #t ≤ _
  rwa [← Cardinal.add_def] at this

/-- The inequality of Abhyankar (Theorem 2.1.5 of Volume 3 of the handbook). Let `A` be a valuation
subring of `K` that is an algebra over a field `k`. The rational rank of the value group of `A`
plus the transcendence degree of the residue field of `A` over `k` is at most the transcendence
degree of `K` over `k`. -/
theorem abhyankar_inequality {k : Type*} [Field k] [Algebra k K] [Algebra k A]
    [IsScalarTower k A K] :
    Module.rank ℚ (ℚ ⊗[ℤ] Additive A.ValueGroupˣ) +
        Algebra.trdeg k (IsLocalRing.ResidueField A) ≤ Algebra.trdeg k K := by
  rw [(TensorProduct.isBaseChange ℤ (Additive A.ValueGroupˣ) ℚ).rank_eq]
  exact rank_int_valueGroup_add_trdeg_le A

end ValuationSubring

section Relative

open IsLocalRing

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ₀ Γ₁ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL]

/-- Lemma 2.1.2 of the handbook. Let `y` be elements of the valuation ring of `vL` with residues
that are algebraically independent over the residue field of `vK`. Then each nonzero polynomial
over `K` in `y` has the value of a nonzero element of `K`. -/
theorem exists_valuation_aeval_eq {κ : Type*} (y : κ → vL.valuationSubring)
    (hy : AlgebraicIndependent (ResidueField vK.valuationSubring) (fun j => residue _ (y j)))
    (P : MvPolynomial κ K) (hP : P ≠ 0) :
    ∃ c : Kˣ, vL (aeval (fun j => (y j : L)) P) = vL (algebraMap K L c) := by
  classical
  have hne : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hP)
  obtain ⟨b₀, hb₀, hmax⟩ := P.support.exists_max_image (fun b => vK (P.coeff b)) hne
  set c := P.coeff b₀ with hc_def
  have hc : c ≠ 0 := mem_support_iff.mp hb₀
  have hvc : vK c ≠ 0 := (Valuation.ne_zero_iff vK).mpr hc
  set Q := C c⁻¹ * P with hQ_def
  have hQ : ∀ b, vK (Q.coeff b) ≤ 1 := by
    intro b
    rw [hQ_def, coeff_C_mul, map_mul, map_inv₀]
    by_cases hb : b ∈ P.support
    · rw [inv_mul_le_one₀ (zero_lt_iff.mpr hvc)]
      exact hmax b hb
    · rw [notMem_support_iff.mp hb]
      simp
  obtain ⟨Q', hQ'⟩ : Q ∈ Set.range (MvPolynomial.map (algebraMap vK.valuationSubring K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨b, -, rfl⟩ := (mem_coeffs_iff).mp ha
    exact ⟨⟨Q.coeff b, (vK.mem_valuationSubring_iff _).mpr (hQ b)⟩, rfl⟩
  have hQ'b : Q'.coeff b₀ = 1 := by
    apply Subtype.ext
    have := congrArg (fun p => p.coeff b₀) hQ'
    rw [coeff_map] at this
    simpa [hQ_def, coeff_C_mul, hc, ← hc_def] using this
  set R := MvPolynomial.map (residue vK.valuationSubring) Q' with hR_def
  have hR : R ≠ 0 := by
    intro h
    have := congrArg (fun p => p.coeff b₀) h
    rw [hR_def, coeff_map, hQ'b, map_one] at this
    simp at this
  have h1 : aeval (fun j => residue _ (y j)) R ≠ 0 :=
    fun h => hR (algebraicIndependent_iff.mp hy R h)
  have h2 : aeval (fun j => residue _ (y j)) R = residue _ (aeval y Q') := by
    rw [hR_def, aeval_def, eval₂_map, aeval_def, eval₂_comp_left]
    rfl
  have hu : IsUnit (aeval y Q') := (residue_ne_zero_iff_isUnit _).mp (h2 ▸ h1)
  have h3 : vL ((aeval y Q' : vL.valuationSubring) : L) = 1 :=
    (Valuation.isEquiv_valuation_valuationSubring vL).eq_one_iff_eq_one.mpr
      ((ValuationSubring.valuation_eq_one_iff _ _).mp hu)
  have h4 : ((aeval y Q' : vL.valuationSubring) : L) =
      algebraMap K L c⁻¹ * aeval (fun j => (y j : L)) P := by
    have h5 : ((aeval y Q' : vL.valuationSubring) : L) = aeval (fun j => (y j : L)) Q' :=
      comp_aeval_apply (f := y)
        (IsScalarTower.toAlgHom vK.valuationSubring vL.valuationSubring L) Q'
    rw [h5, ← aeval_map_algebraMap K, hQ', hQ_def, map_mul, aeval_C]
  refine ⟨Units.mk0 c hc, ?_⟩
  rw [h4, map_mul, map_inv₀, map_inv₀] at h3
  have hvc' : vL (algebraMap K L c) ≠ 0 :=
    (Valuation.ne_zero_iff vL).mpr ((map_ne_zero (algebraMap K L)).mpr hc)
  rw [Units.val_mk0]
  exact (inv_mul_eq_one₀ hvc').mp h3 |>.symm

/-- Theorem 2.1.4 of the handbook. Let `x` be units of `L` with values that are independent over
`ℤ` modulo the value group of `vK`. Let `y` be elements of the valuation ring of `vL` with
residues that are algebraically independent over the residue field of `vK`. Then the family of
`x` and `y` is algebraically independent over `K`. -/
theorem algebraicIndependent_sumElim_of_hasExtension {ι κ : Type*} (x : ι → Lˣ)
    (hx : LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup
        (Units.map (vL : L →* Γ₁) (x i)))))
    (y : κ → vL.valuationSubring)
    (hy : AlgebraicIndependent (ResidueField vK.valuationSubring) (fun j => residue _ (y j))) :
    AlgebraicIndependent K (Sum.elim (fun i => (x i : L)) (fun j => (y j : L))) := by
  refine algebraicIndependent_sumElim_of_monoidHom vL
    ((QuotientGroup.mk' _).comp (Units.map (vL : L →* Γ₁))) ?_ x hx _ ?_
  · intro a b h
    have : Units.map (vL : L →* Γ₁) a = Units.map (vL : L →* Γ₁) b :=
      Units.ext (by simpa using h)
    simp [this]
  · intro P hP
    obtain ⟨c, hc⟩ := exists_valuation_aeval_eq vK vL y hy P hP
    refine ⟨Units.map (algebraMap K L : K →* L) c, ?_, by simpa using hc⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    apply MonoidWithZeroHom.mem_valueGroup
    exact ⟨(c : K), by simp⟩

end Relative

section RelativeRank

open IsLocalRing

universe uL uΓ

variable {K : Type*} {L : Type uL} [Field K] [Field L] [Algebra K L] {Γ₀ : Type*}
  {Γ₁ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL]

/-- The relative inequality with the rank over `ℤ`. The group in the statement is the image of the
value group of `vL` in the quotient of `Γ₁ˣ` by the value group of the restriction of `vL` to `K`.
Its rank plus the transcendence degree of the residue field extension is at most the transcendence
degree of `L` over `K`. -/
theorem rank_int_valueGroup_map_add_trdeg_le :
    lift.{uL} (Module.rank ℤ (Additive ((vL : L →*₀ Γ₁).valueGroup.map
        (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup)))) +
      lift.{uΓ} (Algebra.trdeg (ResidueField vK.valuationSubring)
        (ResidueField vL.valuationSubring)) ≤ lift.{uΓ} (Algebra.trdeg K L) := by
  set H := (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup
  set M := (vL : L →*₀ Γ₁).valueGroup.map (QuotientGroup.mk' H)
  rw [Module.rank_def, Algebra.trdeg, lift_iSup bddAbove_of_small, lift_iSup bddAbove_of_small]
  refine ciSup_add_ciSup_le_of_forall bddAbove_of_small bddAbove_of_small ?_
  rintro ⟨s, hs⟩ ⟨t, ht⟩
  change lift.{uL} #s + lift.{uΓ} #t ≤ _
  have hx : ∀ γ : s, ∃ z : Lˣ, QuotientGroup.mk' H (Units.map (vL : L →* Γ₁) z) =
      ((Additive.toMul (γ : Additive M) : M) : Γ₁ˣ ⧸ H) := by
    intro γ
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.mp (Additive.toMul (γ : Additive M)).2
    have hgr : (g : Γ₁) ∈ Set.range (vL : L →*₀ Γ₁) \ {0} := by
      rw [← MonoidWithZeroHom.valueGroup_eq_range (vL : L →*₀ Γ₁)]
      exact ⟨g, hg, rfl⟩
    obtain ⟨⟨z, hz⟩, hz0⟩ := hgr
    have hz0' : z ≠ 0 := by
      rintro rfl
      exact g.ne_zero (by simpa using hz.symm)
    refine ⟨Units.mk0 z hz0', ?_⟩
    rw [← hgγ]
    congr 1
    exact Units.ext (by simpa using hz)
  choose x hx using hx
  have hy : ∀ e : t, ∃ a : vL.valuationSubring, residue _ a = e := fun e =>
    residue_surjective (R := vL.valuationSubring) (e : ResidueField vL.valuationSubring)
  choose y hy using hy
  have hs' : LinearIndependent ℤ (fun i : s => (i : Additive M)) := hs
  have ht' : AlgebraicIndependent (ResidueField vK.valuationSubring)
      (fun j : t => (j : ResidueField vL.valuationSubring)) := ht
  have hinj : Function.Injective (M.subtype.toAdditive.toIntLinearMap) := by
    intro a b hab
    exact Additive.toMul.injective (Subtype.ext (by simpa using hab))
  have hs'' := hs'.map' _ (LinearMap.ker_eq_bot.mpr hinj)
  have hli : LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk' H (Units.map (vL : L →* Γ₁) (x i)))) := by
    convert hs'' using 1
    funext i
    simp [hx i]
  have hai : AlgebraicIndependent (ResidueField vK.valuationSubring)
      (fun j => residue vL.valuationSubring (y j)) := by
    convert ht' using 1
    funext j
    simp [hy j]
  have :=
    (algebraicIndependent_sumElim_of_hasExtension vK vL x hli y hai).lift_cardinalMk_le_trdeg
  rw [mk_sum] at this
  simp only [lift_add, lift_lift] at this
  rwa [lift_umax.{uL, uΓ}] at this

/-- The relative inequality of Abhyankar (Theorem 2.1.4 of the handbook). The rational rank of the
image of the value group of `vL` modulo the value group of `vK`, plus the transcendence degree of
the residue field extension, is at most the transcendence degree of `L` over `K`. -/
theorem abhyankar_inequality_relative :
    lift.{uL} (Module.rank ℚ (ℚ ⊗[ℤ] Additive ((vL : L →*₀ Γ₁).valueGroup.map
        (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup)))) +
      lift.{uΓ} (Algebra.trdeg (ResidueField vK.valuationSubring)
        (ResidueField vL.valuationSubring)) ≤ lift.{uΓ} (Algebra.trdeg K L) := by
  rw [(TensorProduct.isBaseChange ℤ _ ℚ).rank_eq]
  exact rank_int_valueGroup_map_add_trdeg_le vK vL

end RelativeRank

end Singularity
