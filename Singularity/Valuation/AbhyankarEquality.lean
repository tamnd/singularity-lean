/-
Copyright (c) 2026 Singularity contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Singularity.Valuation.Abhyankar
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The value group of the subfield of independent elements

This file proves the value group part of Volume 3, Lemma 2.2.1 of the handbook. Let `(L/K, w)` be
an extension of valued fields. Let `x_1, ..., x_r` be units of `L` with values that are independent
over `ℤ` modulo the value group of `K`, and let `y_1, ..., y_s` be elements of the valuation ring of
`L` with residues that are algebraically independent over the residue field of `K`.

* `exists_valuation_aeval_sumElim_eq`: each nonzero polynomial over `K` in the `x_i` and the `y_j`
  has the value of a term `c x^a` with `c ∈ Kˣ`.
* `exists_valuation_eq_of_mem_adjoin`: each nonzero element `z` of `K_0 = K(x, y)` has the value
  of a quotient `c x^a / x^b` with `c ∈ Kˣ`. So the value group of `K_0` is contained in
  `Γ_v + ∑ ℤ w(x_i)`.

The handbook also proves that the sum is direct and that the residue field of `K_0` is
`Kv(ȳ_1, ..., ȳ_s)`. These two claims are not in this file.
-/

namespace Singularity

open MvPolynomial

section AbhyankarEquality

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ₀ Γ₁ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL]

/-- Part of Volume 3, Lemma 2.2.1 of the handbook. Each nonzero polynomial over `K` in the
independent elements `x` and `y` has the value of a term `c x^a` with `c ∈ Kˣ`. -/
theorem exists_valuation_aeval_sumElim_eq {ι κ : Type*} (x : ι → Lˣ)
    (hx : LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup
        (Units.map (vL : L →* Γ₁) (x i)))))
    (y : κ → vL.valuationSubring)
    (hy : AlgebraicIndependent (IsLocalRing.ResidueField vK.valuationSubring)
      (fun j => IsLocalRing.residue _ (y j)))
    (P : MvPolynomial (ι ⊕ κ) K) (hP : P ≠ 0) :
    ∃ (c : Kˣ) (a : ι →₀ ℕ),
      vL (aeval (Sum.elim (fun i => (x i : L)) (fun j => (y j : L))) P) =
        vL (algebraMap K L c * a.prod fun i n => (x i : L) ^ n) := by
  classical
  set π : Lˣ →* _ := (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup).comp
    (Units.map (vL : L →* Γ₁)) with hπ_def
  have hπ : ∀ a b : Lˣ, vL a = vL b → π a = π b := by
    intro a b h
    have : Units.map (vL : L →* Γ₁) a = Units.map (vL : L →* Γ₁) b :=
      Units.ext (by simpa using h)
    simp [hπ_def, this]
  have hπc : ∀ c : Kˣ, π (Units.map (algebraMap K L : K →* L) c) = 1 := by
    intro c
    simp only [hπ_def, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    apply MonoidWithZeroHom.mem_valueGroup
    exact ⟨(c : K), by simp⟩
  set y' : κ → L := fun j => (y j : L) with hy'
  set G := sumRingEquiv K ι κ P
  have hG0 : G ≠ 0 := (map_ne_zero_iff _ (sumRingEquiv K ι κ).injective).mpr hP
  have hev : (aeval (Sum.elim (fun i => (x i : L)) y')).toRingHom =
      (eval₂Hom (aeval y').toRingHom (fun i => (x i : L))).comp
        (sumRingEquiv K ι κ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [sumRingEquiv_C]
    · rintro (i | j) <;> simp [sumRingEquiv_X_inl, sumRingEquiv_X_inr]
  have heval : aeval (Sum.elim (fun i => (x i : L)) y') P =
      eval₂ (aeval y').toRingHom (fun i => (x i : L)) G := by
    have := RingHom.congr_fun hev P
    simpa using this
  have hc : ∀ d, ∃ c : Kˣ, G.coeff d ≠ 0 →
      vL (aeval y' (G.coeff d)) = vL (algebraMap K L c) := by
    intro d
    by_cases hd : G.coeff d = 0
    · exact ⟨1, fun h => absurd hd h⟩
    · obtain ⟨c, hc⟩ := exists_valuation_aeval_eq vK vL y hy _ hd
      exact ⟨c, fun _ => hc⟩
  choose c hc using hc
  set e : (ι →₀ ℕ) → Lˣ := fun d =>
    Units.map (algebraMap K L : K →* L) (c d) * d.prod fun i n => x i ^ n with he_def
  have he : ∀ d, (e d : L) = algebraMap K L (c d) * d.prod fun i n => (x i : L) ^ n := by
    intro d
    simp [he_def, Finsupp.prod, Units.coe_prod]
  have hterm : ∀ d ∈ G.support,
      vL ((aeval y').toRingHom (G.coeff d) * ∏ i ∈ d.support, (x i : L) ^ d i) = vL (e d : L) := by
    intro d hd
    rw [he d, map_mul, map_mul, ← hc d (mem_support_iff.mp hd)]
    rfl
  have hπe : ∀ d, π (e d) = d.prod fun i n => π (x i) ^ n := by
    intro d
    rw [he_def, map_mul, hπc, one_mul, map_finsuppProd]
    simp [map_pow]
  have hinj := injective_prod_pow_of_linearIndependent hx
  have hne : G.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hG0)
  obtain ⟨d₀, hd₀, hmax⟩ := G.support.exists_max_image (fun d => vL (e d : L)) hne
  have hsum := vL.map_sum_eq_of_lt hd₀ (f := fun d =>
      (aeval y').toRingHom (G.coeff d) * ∏ i ∈ d.support, (x i : L) ^ d i) (by
    intro d hd
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hd
    rw [hterm d hd.1, hterm d₀ hd₀]
    refine lt_of_le_of_ne (hmax d hd.1) ?_
    intro h
    apply hd.2
    apply hinj
    show (d.prod fun i n => π (x i) ^ n) = d₀.prod fun i n => π (x i) ^ n
    rw [← hπe d, ← hπe d₀]
    exact hπ _ _ h)
  refine ⟨c d₀, d₀, ?_⟩
  rw [heval, eval₂_eq, hsum, hterm d₀ hd₀, he d₀]

/-- The value group part of Volume 3, Lemma 2.2.1 of the handbook. Each nonzero element `z` of
`K_0 = K(x, y)` has the value of a quotient `c x^a / x^b` with `c ∈ Kˣ`. -/
theorem exists_valuation_eq_of_mem_adjoin {ι κ : Type*} (x : ι → Lˣ)
    (hx : LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup
        (Units.map (vL : L →* Γ₁) (x i)))))
    (y : κ → vL.valuationSubring)
    (hy : AlgebraicIndependent (IsLocalRing.ResidueField vK.valuationSubring)
      (fun j => IsLocalRing.residue _ (y j)))
    {z : L} (hz : z ∈ IntermediateField.adjoin K
      (Set.range (Sum.elim (fun i => (x i : L)) (fun j => (y j : L)))))
    (hz0 : z ≠ 0) :
    ∃ (c : Kˣ) (a b : ι →₀ ℕ),
      vL z * vL (b.prod fun i n => (x i : L) ^ n) =
        vL (algebraMap K L c) * vL (a.prod fun i n => (x i : L) ^ n) := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_range_iff _ _ _).mp hz
  set f := Sum.elim (fun i => (x i : L)) (fun j => (y j : L))
  have hs : aeval f s ≠ 0 := fun h => hz0 (by rw [h, div_zero])
  have hr : aeval f r ≠ 0 := fun h => hz0 (by rw [h, zero_div])
  have hs0 : s ≠ 0 := fun h => hs (by rw [h, map_zero])
  have hr0 : r ≠ 0 := fun h => hr (by rw [h, map_zero])
  obtain ⟨c₁, a, ha⟩ := exists_valuation_aeval_sumElim_eq vK vL x hx y hy r hr0
  obtain ⟨c₂, b, hb⟩ := exists_valuation_aeval_sumElim_eq vK vL x hx y hy s hs0
  refine ⟨c₁ * c₂⁻¹, a, b, ?_⟩
  have h2 : vL (algebraMap K L c₂) ≠ 0 :=
    (Valuation.ne_zero_iff vL).mpr ((map_ne_zero (algebraMap K L)).mpr c₂.ne_zero)
  have hq : aeval f r / aeval f s * aeval f s = aeval f r := div_mul_cancel₀ _ hs
  have key : vL (aeval f r / aeval f s) * vL (b.prod fun i n => (x i : L) ^ n) *
      vL (algebraMap K L c₂) = vL (algebraMap K L c₁) * vL (a.prod fun i n => (x i : L) ^ n) := by
    have h := congrArg vL hq
    rw [map_mul, hb, ha, map_mul, map_mul] at h
    rw [← h]
    ac_rfl
  rw [Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀,
    mul_right_comm, ← key, mul_inv_cancel_right₀ h2]

end AbhyankarEquality

end Singularity
