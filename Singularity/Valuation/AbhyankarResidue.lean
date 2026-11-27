/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.Abhyankar
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# The residue field of the subfield of independent elements

This file proves the residue field part of Volume 3, Lemma 2.2.1 of the handbook, in the relative form. Let `(L/K, w)` be an extension of valued fields. Let `x_1, ..., x_r` be units of `L` with values that are independent over `ℤ` modulo the value group of `K`, and let `y_1, ..., y_s` be elements of the valuation ring of `L` with residues that are algebraically independent over the residue field `Kv`. Let `K_0 = K(x, y)`. Then the residues of the elements of `K_0` in the valuation ring are exactly the elements of `Kv(ȳ_1, ..., ȳ_s)`.

The proof follows the handbook. A nonzero polynomial `F` in `x` and `y` is `c x^a u`, with `c ∈ Kˣ`, `u` a unit of the valuation ring, and the residue of `u` in `Kv[ȳ]`. The term of `F` with the largest value gives `c x^a`, and the other terms divide to elements of the maximal ideal. If `F / G` has value `1`, then the two exponents are equal, so `F / G` is an element of `K` of value `1` times `u / u'`.

## Main results

* `Singularity.exists_isUnit_eq_aeval_sumElim`: the form `F = c x^a u`.
* `Singularity.eq_of_valuation_mul_prod_eq`: if `c x^a` and `c' x^b` have the same value, then `a = b`.
* `Singularity.residue_mem_adjoin_of_hasExtension`: the residue of each element of `K_0` in the valuation ring is in `Kv(ȳ)`.
* `Singularity.residueIntermediateField_adjoin_eq`: the residues of `K_0` form the field `Kv(ȳ)`.

The absolute form for a function field over a trivially valued field is in `Singularity/Valuation/AbhyankarResidueField.lean`.
-/

namespace Singularity

open MvPolynomial IsLocalRing

section AbhyankarResidue

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ₀ Γ₁ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL]

/-- An element of the valuation ring of `vL` is a unit if and only if its value is `1`. -/
theorem isUnit_valuationSubring_iff (u : vL.valuationSubring) : IsUnit u ↔ vL (u : L) = 1 :=
  (ValuationSubring.valuation_eq_one_iff _ u).trans
    (Valuation.isEquiv_valuation_valuationSubring vL).eq_one_iff_eq_one.symm

/-- An element of the valuation ring of `vL` is in the maximal ideal if and only if its value is
less than `1`. -/
private theorem mem_maximalIdeal_valuationSubring_iff' (u : vL.valuationSubring) :
    u ∈ maximalIdeal vL.valuationSubring ↔ vL (u : L) < 1 :=
  (ValuationSubring.valuation_lt_one_iff _ u).trans
    (Valuation.isEquiv_valuation_valuationSubring vL).lt_one_iff_lt_one.symm

/-- Part of the proof of Volume 3, Lemma 2.2.1 of the handbook. Let `P` be a nonzero polynomial
over `K` in elements `y` with algebraically independent residues. Then `P(y) = c u`, with
`c ∈ Kˣ`, `u` a unit of the valuation ring of `vL`, and the residue of `u` in `Kv[ȳ]`. -/
theorem exists_isUnit_residue_mem_adjoin {κ : Type*} (y : κ → vL.valuationSubring)
    (hy : AlgebraicIndependent (ResidueField vK.valuationSubring) (fun j => residue _ (y j)))
    (P : MvPolynomial κ K) (hP : P ≠ 0) :
    ∃ (c : Kˣ) (u : vL.valuationSubring), IsUnit u ∧
      aeval (fun j => (y j : L)) P = algebraMap K L c * u ∧
      residue _ u ∈ Algebra.adjoin (ResidueField vK.valuationSubring)
        (Set.range fun j => residue _ (y j)) := by
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
  have h4 : ((aeval y Q' : vL.valuationSubring) : L) =
      algebraMap K L c⁻¹ * aeval (fun j => (y j : L)) P := by
    have h5 : ((aeval y Q' : vL.valuationSubring) : L) = aeval (fun j => (y j : L)) Q' :=
      comp_aeval_apply (f := y)
        (IsScalarTower.toAlgHom vK.valuationSubring vL.valuationSubring L) Q'
    rw [h5, ← aeval_map_algebraMap K, hQ', hQ_def, map_mul, aeval_C]
  have hc' : algebraMap K L c ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hc
  refine ⟨Units.mk0 c hc, aeval y Q', hu, ?_, ?_⟩
  · rw [h4, Units.val_mk0, map_inv₀, mul_inv_cancel_left₀ hc']
  · rw [← h2, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨R, rfl⟩

/-- The directness in Volume 3, Lemma 2.2.1 of the handbook. If two terms `c x^a` and `c' x^b`
with `c, c' ∈ Kˣ` have the same value, then `a = b`. -/
theorem eq_of_valuation_mul_prod_eq {ι : Type*} (x : ι → Lˣ)
    (hx : LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup
        (Units.map (vL : L →* Γ₁) (x i)))))
    {c c' : Kˣ} {a b : ι →₀ ℕ}
    (h : vL (algebraMap K L c * a.prod fun i n => (x i : L) ^ n) =
      vL (algebraMap K L c' * b.prod fun i n => (x i : L) ^ n)) : a = b := by
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
  set e : Kˣ → (ι →₀ ℕ) → Lˣ := fun c d =>
    Units.map (algebraMap K L : K →* L) c * d.prod fun i n => x i ^ n with he_def
  have he : ∀ c d, (e c d : L) = algebraMap K L c * d.prod fun i n => (x i : L) ^ n := by
    intro c d
    simp [he_def, Finsupp.prod, Units.coe_prod]
  have hπe : ∀ c d, π (e c d) = d.prod fun i n => π (x i) ^ n := by
    intro c d
    rw [he_def, map_mul, hπc, one_mul, map_finsuppProd]
    simp [map_pow]
  apply injective_prod_pow_of_linearIndependent hx
  show (a.prod fun i n => π (x i) ^ n) = b.prod fun i n => π (x i) ^ n
  rw [← hπe c a, ← hπe c' b]
  exact hπ _ _ (by rw [he, he]; exact h)

/-- Part of the proof of Volume 3, Lemma 2.2.1 of the handbook. Each nonzero polynomial `F` over
`K` in `x` and `y` is `c x^a u`, with `c ∈ Kˣ`, `u` a unit of the valuation ring of `vL`, and the
residue of `u` in `Kv[ȳ]`. -/
theorem exists_isUnit_eq_aeval_sumElim {ι κ : Type*} (x : ι → Lˣ)
    (hx : LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup
        (Units.map (vL : L →* Γ₁) (x i)))))
    (y : κ → vL.valuationSubring)
    (hy : AlgebraicIndependent (ResidueField vK.valuationSubring) (fun j => residue _ (y j)))
    (P : MvPolynomial (ι ⊕ κ) K) (hP : P ≠ 0) :
    ∃ (c : Kˣ) (a : ι →₀ ℕ) (u : vL.valuationSubring), IsUnit u ∧
      aeval (Sum.elim (fun i => (x i : L)) (fun j => (y j : L))) P =
        algebraMap K L c * (a.prod fun i n => (x i : L) ^ n) * u ∧
      residue _ u ∈ Algebra.adjoin (ResidueField vK.valuationSubring)
        (Set.range fun j => residue _ (y j)) := by
  classical
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
  have hc : ∀ d, ∃ (c : Kˣ) (u : vL.valuationSubring), G.coeff d ≠ 0 →
      (IsUnit u ∧ aeval y' (G.coeff d) = algebraMap K L c * u ∧
        residue _ u ∈ Algebra.adjoin (ResidueField vK.valuationSubring)
          (Set.range fun j => residue _ (y j))) := by
    intro d
    by_cases hd : G.coeff d = 0
    · exact ⟨1, 1, fun h => absurd hd h⟩
    · obtain ⟨c, u, h1, h2, h3⟩ := exists_isUnit_residue_mem_adjoin vK vL y hy _ hd
      exact ⟨c, u, fun _ => ⟨h1, h2, h3⟩⟩
  choose c u hcu using hc
  set e : (ι →₀ ℕ) → Lˣ := fun d =>
    Units.map (algebraMap K L : K →* L) (c d) * d.prod fun i n => x i ^ n with he_def
  have he : ∀ d, (e d : L) = algebraMap K L (c d) * d.prod fun i n => (x i : L) ^ n := by
    intro d
    simp [he_def, Finsupp.prod, Units.coe_prod]
  have hvu : ∀ d ∈ G.support, vL (u d : L) = 1 := fun d hd =>
    (isUnit_valuationSubring_iff vL _).mp (hcu d (mem_support_iff.mp hd)).1
  have hterm : ∀ d ∈ G.support,
      (aeval y').toRingHom (G.coeff d) * ∏ i ∈ d.support, (x i : L) ^ d i = (e d : L) * u d := by
    intro d hd
    rw [he d]
    change aeval y' (G.coeff d) * _ = _
    rw [(hcu d (mem_support_iff.mp hd)).2.1]
    simp only [Finsupp.prod]
    ring
  have hvterm : ∀ d ∈ G.support,
      vL ((aeval y').toRingHom (G.coeff d) * ∏ i ∈ d.support, (x i : L) ^ d i) = vL (e d : L) := by
    intro d hd
    rw [hterm d hd, map_mul, hvu d hd, mul_one]
  have hne : G.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hG0)
  obtain ⟨d₀, hd₀, hmax⟩ := G.support.exists_max_image (fun d => vL (e d : L)) hne
  have hlt : ∀ d ∈ G.support.erase d₀,
      vL ((aeval y').toRingHom (G.coeff d) * ∏ i ∈ d.support, (x i : L) ^ d i) <
        vL (e d₀ : L) := by
    intro d hd
    rw [Finset.mem_erase] at hd
    rw [hvterm d hd.2]
    refine lt_of_le_of_ne (hmax d hd.2) ?_
    intro h
    apply hd.1
    rw [he, he] at h
    exact eq_of_valuation_mul_prod_eq vL x hx h
  have he0 : (e d₀ : L) ≠ 0 := Units.ne_zero _
  have hve0 : vL (e d₀ : L) ≠ 0 := (Valuation.ne_zero_iff vL).mpr he0
  have hrest := vL.map_sum_lt hve0 hlt
  set S := ∑ d ∈ G.support.erase d₀,
    (aeval y').toRingHom (G.coeff d) * ∏ i ∈ d.support, (x i : L) ^ d i with hS
  have hρ : vL (S / (e d₀ : L)) < 1 := by
    rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr hve0)]
    exact hrest
  set r : vL.valuationSubring := ⟨S / (e d₀ : L), (vL.mem_valuationSubring_iff _).mpr hρ.le⟩
  have hr : r ∈ maximalIdeal vL.valuationSubring :=
    (mem_maximalIdeal_valuationSubring_iff' vL r).mpr hρ
  have hu₀ := hcu d₀ (mem_support_iff.mp hd₀)
  have hres : residue _ (u d₀ + r) = residue _ (u d₀) := by
    rw [map_add, (residue_eq_zero_iff r).mpr hr, add_zero]
  refine ⟨c d₀, d₀, u d₀ + r, ?_, ?_, ?_⟩
  · rw [← residue_ne_zero_iff_isUnit, hres, residue_ne_zero_iff_isUnit]
    exact hu₀.1
  · rw [heval, eval₂_eq, ← Finset.add_sum_erase _ _ hd₀, hterm d₀ hd₀, ← hS, ← he d₀]
    show _ = (e d₀ : L) * ((u d₀ : L) + S / (e d₀ : L))
    rw [mul_add, mul_div_cancel₀ _ he0]
  · rw [hres]
    exact hu₀.2.2

/-- The residue field part of Volume 3, Lemma 2.2.1 of the handbook, the inclusion
`K_0 w_0 ⊆ Kv(ȳ)`. Each element of the valuation ring of `vL` that is in `K_0 = K(x, y)` has its
residue in the field `Kv(ȳ_1, ..., ȳ_s)`. -/
theorem residue_mem_adjoin_of_hasExtension {ι κ : Type*} (x : ι → Lˣ)
    (hx : LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup
        (Units.map (vL : L →* Γ₁) (x i)))))
    (y : κ → vL.valuationSubring)
    (hy : AlgebraicIndependent (ResidueField vK.valuationSubring) (fun j => residue _ (y j)))
    (z : vL.valuationSubring) (hz : (z : L) ∈ IntermediateField.adjoin K
      (Set.range (Sum.elim (fun i => (x i : L)) (fun j => (y j : L))))) :
    residue _ z ∈ IntermediateField.adjoin (ResidueField vK.valuationSubring)
      (Set.range fun j => residue _ (y j)) := by
  set E := IntermediateField.adjoin (ResidueField vK.valuationSubring)
    (Set.range fun j => residue vL.valuationSubring (y j))
  have hA : Algebra.adjoin (ResidueField vK.valuationSubring)
      (Set.range fun j => residue vL.valuationSubring (y j)) ≤ E.toSubalgebra :=
    IntermediateField.algebra_adjoin_le_adjoin _ _
  by_cases hzu : IsUnit z
  swap
  · rw [(residue_eq_zero_iff z).mpr (by rwa [mem_maximalIdeal, mem_nonunits_iff])]
    exact E.zero_mem
  have hz1 : vL (z : L) = 1 := (isUnit_valuationSubring_iff vL z).mp hzu
  have hz0 : (z : L) ≠ 0 := by
    intro h
    rw [h, map_zero] at hz1
    exact zero_ne_one hz1
  set f := Sum.elim (fun i => (x i : L)) (fun j => (y j : L))
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_range_iff _ _ _).mp hz
  have hs : aeval f s ≠ 0 := fun h => hz0 (by rw [hrs, h, div_zero])
  have hr : aeval f r ≠ 0 := fun h => hz0 (by rw [hrs, h, zero_div])
  have hs0 : s ≠ 0 := fun h => hs (by rw [h, map_zero])
  have hr0 : r ≠ 0 := fun h => hr (by rw [h, map_zero])
  obtain ⟨c₁, a, u₁, hu₁, h₁, hm₁⟩ := exists_isUnit_eq_aeval_sumElim vK vL x hx y hy r hr0
  obtain ⟨c₂, b, u₂, hu₂, h₂, hm₂⟩ := exists_isUnit_eq_aeval_sumElim vK vL x hx y hy s hs0
  have hv₁ := (isUnit_valuationSubring_iff vL u₁).mp hu₁
  have hv₂ := (isUnit_valuationSubring_iff vL u₂).mp hu₂
  have hzs : (z : L) * aeval f s = aeval f r := by rw [hrs, div_mul_cancel₀ _ hs]
  have hv : vL (algebraMap K L c₁ * a.prod fun i n => (x i : L) ^ n) =
      vL (algebraMap K L c₂ * b.prod fun i n => (x i : L) ^ n) := by
    have := congrArg vL hzs
    rw [map_mul, hz1, one_mul, h₁, h₂, map_mul, map_mul _ _ (u₁ : L), hv₁, hv₂, mul_one,
      mul_one] at this
    exact this.symm
  have hab : a = b := eq_of_valuation_mul_prod_eq vL x hx hv
  subst hab
  set X := a.prod fun i n => (x i : L) ^ n with hX_def
  have hX : X ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (x i).ne_zero
  have hc₂ : algebraMap K L (c₂ : K) ≠ 0 := (map_ne_zero _).mpr c₂.ne_zero
  have h' : vL (algebraMap K L c₁) = vL (algebraMap K L c₂) := by
    rw [map_mul, map_mul] at hv
    exact mul_right_cancel₀ ((Valuation.ne_zero_iff vL).mpr hX) hv
  have h'' : vK c₁ = vK c₂ := (Valuation.HasExtension.val_map_eq_iff (vR := vK) (vA := vL) _ _).mp h'
  set t : K := (c₁ : K) * (c₂ : K)⁻¹ with ht_def
  have hvt : vK t = 1 := by
    rw [ht_def, map_mul, map_inv₀, h'', mul_inv_cancel₀ ((Valuation.ne_zero_iff vK).mpr c₂.ne_zero)]
  set t₀ : vK.valuationSubring := ⟨t, (vK.mem_valuationSubring_iff _).mpr hvt.le⟩
  have key : z * u₂ = algebraMap vK.valuationSubring vL.valuationSubring t₀ * u₁ := by
    apply Subtype.ext
    show (z : L) * u₂ = algebraMap K L t * u₁
    have hzu : (z : L) * (algebraMap K L c₂ * X * u₂) = algebraMap K L c₁ * X * u₁ := by
      rw [← h₁, ← h₂]
      exact hzs
    apply mul_right_cancel₀ (mul_ne_zero hc₂ hX)
    calc (z : L) * u₂ * (algebraMap K L c₂ * X) = (z : L) * (algebraMap K L c₂ * X * u₂) := by
          ring
      _ = algebraMap K L c₁ * X * u₁ := hzu
      _ = algebraMap K L t * u₁ * (algebraMap K L c₂ * X) := by
          rw [ht_def, map_mul, map_inv₀,
            show algebraMap K L c₁ * (algebraMap K L c₂)⁻¹ * u₁ * (algebraMap K L c₂ * X) =
              algebraMap K L c₁ * X * u₁ * ((algebraMap K L c₂)⁻¹ * algebraMap K L c₂) by ring,
            inv_mul_cancel₀ hc₂, mul_one]
  have hres := congrArg (residue vL.valuationSubring) key
  rw [map_mul, map_mul, ← IsLocalRing.ResidueField.algebraMap_residue] at hres
  have hu₂r : residue _ u₂ ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr hu₂
  have hzeq : residue _ z = algebraMap (ResidueField vK.valuationSubring)
      (ResidueField vL.valuationSubring) (residue _ t₀) * residue _ u₁ * (residue _ u₂)⁻¹ := by
    rw [← hres, mul_inv_cancel_right₀ hu₂r]
  rw [hzeq]
  exact E.mul_mem (E.mul_mem (E.algebraMap_mem _) (hA hm₁)) (E.inv_mem (hA hm₂))

/-- The residues of the elements of the valuation ring of `vL` that are in an intermediate field
`F` of `L/K`, as an intermediate field of the residue field extension. -/
noncomputable def residueIntermediateField (F : IntermediateField K L) :
    IntermediateField (ResidueField vK.valuationSubring) (ResidueField vL.valuationSubring) where
  carrier := {w | ∃ z : vL.valuationSubring, (z : L) ∈ F ∧ residue _ z = w}
  mul_mem' := by
    rintro _ _ ⟨z₁, h₁, rfl⟩ ⟨z₂, h₂, rfl⟩
    exact ⟨z₁ * z₂, F.mul_mem h₁ h₂, map_mul _ _ _⟩
  one_mem' := ⟨1, F.one_mem, map_one _⟩
  add_mem' := by
    rintro _ _ ⟨z₁, h₁, rfl⟩ ⟨z₂, h₂, rfl⟩
    exact ⟨z₁ + z₂, F.add_mem h₁ h₂, map_add _ _ _⟩
  zero_mem' := ⟨0, F.zero_mem, map_zero _⟩
  algebraMap_mem' := by
    intro w
    obtain ⟨a, rfl⟩ := residue_surjective w
    refine ⟨algebraMap vK.valuationSubring vL.valuationSubring a, ?_,
      (IsLocalRing.ResidueField.algebraMap_residue a).symm⟩
    rw [Valuation.HasExtension.coe_algebraMap_valuationSubring_eq]
    exact F.algebraMap_mem _
  inv_mem' := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hu : IsUnit z
    · refine ⟨(hu.unit⁻¹ : (vL.valuationSubring)ˣ), ?_, ?_⟩
      · have h : (z : L) * ((hu.unit⁻¹ : (vL.valuationSubring)ˣ) : vL.valuationSubring) = 1 :=
          congrArg Subtype.val hu.mul_val_inv
        rw [eq_inv_of_mul_eq_one_right h]
        exact F.inv_mem hz
      · apply eq_inv_of_mul_eq_one_right
        rw [← map_mul, IsUnit.mul_val_inv, map_one]
    · have hz0 : residue vL.valuationSubring z = 0 :=
        (residue_eq_zero_iff z).mpr ((mem_maximalIdeal _).mpr hu)
      refine ⟨0, F.zero_mem, ?_⟩
      rw [map_zero, hz0, inv_zero]

/-- Volume 3, Lemma 2.2.1 of the handbook, the residue field part `K_0 w_0 = Kv(ȳ_1, ..., ȳ_s)`.
The residues of the elements of the valuation ring of `vL` that are in `K_0 = K(x, y)` are exactly
the elements of the field `Kv(ȳ_1, ..., ȳ_s)`. -/
theorem residueIntermediateField_adjoin_eq {ι κ : Type*} (x : ι → Lˣ)
    (hx : LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk' (vL.comap (algebraMap K L) : K →*₀ Γ₁).valueGroup
        (Units.map (vL : L →* Γ₁) (x i)))))
    (y : κ → vL.valuationSubring)
    (hy : AlgebraicIndependent (ResidueField vK.valuationSubring) (fun j => residue _ (y j))) :
    residueIntermediateField vK vL (IntermediateField.adjoin K
      (Set.range (Sum.elim (fun i => (x i : L)) (fun j => (y j : L))))) =
      IntermediateField.adjoin (ResidueField vK.valuationSubring)
        (Set.range fun j => residue _ (y j)) := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact residue_mem_adjoin_of_hasExtension vK vL x hx y hy z hz
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact ⟨y j, IntermediateField.subset_adjoin _ _ ⟨Sum.inr j, rfl⟩, rfl⟩

end AbhyankarResidue

end Singularity
