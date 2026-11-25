/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.LocalUniformizationMonomial

/-!
# Monomial valuations over a larger ground field

Let `k` be a field of any characteristic. This file proves three results of the handbook on monomial valuations and on the ground field.

1. Volume 5, Lemma 2.1.2, parts 1 and 2. Let `V` be a monomial valuation of `K = k(x_1, ..., x_n)` (`Singularity.IsMonomialValuation`). Then the value group of `V` is free with basis `v(x_1), ..., v(x_n)`, and the residue field of `V` is `k`.
2. Volume 5, Lemma 1.4.2, the part on the ground field. Let `F` be a subfield of `K` that contains `k`, is finitely generated over `k`, and lies in `V`. If `V` has local uniformization as a valuation of `K/F`, then `V` has local uniformization as a valuation of `K/k`. Also, if `y_1, ..., y_m ∈ V` have residues that are algebraically independent over `k`, then the `y_i` are algebraically independent over `k` and `k(y_1, ..., y_m) ⊆ V`.
3. Volume 5, Corollary 2.1.6. Let `K = k(y_1, ..., y_t, x_1, ..., x_r)`, and let `V` be a valuation that is trivial on `k(y)` and is a monomial valuation of `K = k(y)(x_1, ..., x_r)` over the field `k(y)`. Then `V` has local uniformization as a valuation of `K/k`, `V` is an Abhyankar valuation of `K/k`, and the residue field of `V` is `k(ȳ_1, ..., ȳ_t)`, where the residues `ȳ_i` are algebraically independent over `k`.

## Two ground fields

An affine model of `K/k(y)` is a finitely generated `k(y)`-algebra. It is not a finitely generated `k`-algebra, so local uniformization over `k(y)` and local uniformization over `k` are different statements. The proof of the theorem of Knaf-Kuhlmann (Volume 5, Theorem 2.2.1) needs local uniformization over `k`, because the lifting theorem (Volume 5, Theorem 1.3.4) takes local uniformization of `K_0/k` as its hypothesis. So Corollary 2.1.6 here gives `HasLocalUniformization k V`. Its proof applies the monomial case over the field `k(y)` (`Singularity.hasLocalUniformization_of_isMonomialValuation`) and then goes down from `k(y)` to `k` with `Singularity.HasLocalUniformization.of_intermediateField`.

## The change of ground field

Let `A'` be an affine model of `K/F` with `s ⊆ A' ⊆ V` whose local ring at the center of `V` is regular. Let `t` generate `F` over `k` as a field, and let `g` generate `A'` over `F` as an algebra. Let `B = k[t, g, s]`. Then `B ⊆ A' ⊆ V`. For a subring `R` of `K` let `T_R` be the set of `z ∈ K` with `z c ∈ R` for some `c ∈ R` with `v(c) = 1` (`Singularity.centerSubring`). This subring is the localization of `R` at the center of `V` (`Singularity.isRegularLocalRing_localization_iff`). A nonzero element of `F` has value 1, so `F ⊆ T_B`, and then `A' ⊆ T_B`. Thus `T_B = T_{A'}`, and the local ring of `B` at the center of `V` is regular.

## Main results

* `Singularity.IsMonomialValuation.existsUnique_valuation_eq`, `Singularity.IsMonomialValuation.valueHom_bijective`, `Singularity.IsMonomialValuation.valueGroupBasis`: the value group of a monomial valuation is free with basis the values of the `x_i` (Lemma 2.1.2, part 1).
* `Singularity.IsMonomialValuation.algebraMap_residueField_bijective`: the residue field of a monomial valuation is `k` (Lemma 2.1.2, part 2).
* `Singularity.HasLocalUniformization.of_intermediateField`: local uniformization over a larger ground field inside `V` gives local uniformization over `k` (Lemma 1.4.2).
* `Singularity.algebraicIndependent_of_residue`, `Singularity.mem_of_mem_adjoin_residue`: the first claims of Lemma 1.4.2.
* `Singularity.hasLocalUniformization_of_isMonomialValuation_adjoin`, `Singularity.IsMonomialValuation.isAbhyankarValuation_adjoin`, `Singularity.IsMonomialValuation.adjoin_residue_eq_top`, `Singularity.algebraicIndependent_residue`: Corollary 2.1.6.
-/

open IsLocalRing MvPolynomial

namespace Singularity

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### The local ring at the center as a subring of `K` -/

section CenterSubring

variable (V : ValuationSubring K)

/-- The subring `T_R` of `K` of the elements `z` with `z c ∈ R` for some `c ∈ R` with `v(c) = 1`. If `R ⊆ V`, then it is the localization of `R` at the center `m_V ∩ R`. -/
def centerSubring (R : Subring K) : Subring K where
  carrier := {z | ∃ a ∈ R, ∃ c ∈ R, V.valuation c = 1 ∧ z * c = a}
  mul_mem' := by
    rintro z w ⟨a, ha, c, hc, hc1, hz⟩ ⟨b, hb, d, hd, hd1, hw⟩
    refine ⟨a * b, R.mul_mem ha hb, c * d, R.mul_mem hc hd, by rw [map_mul, hc1, hd1, one_mul], ?_⟩
    rw [← hz, ← hw]
    ring
  one_mem' := ⟨1, R.one_mem, 1, R.one_mem, map_one _, one_mul 1⟩
  add_mem' := by
    rintro z w ⟨a, ha, c, hc, hc1, hz⟩ ⟨b, hb, d, hd, hd1, hw⟩
    refine ⟨a * d + b * c, R.add_mem (R.mul_mem ha hd) (R.mul_mem hb hc), c * d, R.mul_mem hc hd,
      by rw [map_mul, hc1, hd1, one_mul], ?_⟩
    rw [← hz, ← hw]
    ring
  zero_mem' := ⟨0, R.zero_mem, 1, R.one_mem, map_one _, zero_mul 1⟩
  neg_mem' := by
    rintro z ⟨a, ha, c, hc, hc1, hz⟩
    refine ⟨-a, R.neg_mem ha, c, hc, hc1, ?_⟩
    rw [← hz]
    ring

variable {V}

theorem mem_centerSubring {R : Subring K} {z : K} :
    z ∈ centerSubring V R ↔ ∃ a ∈ R, ∃ c ∈ R, V.valuation c = 1 ∧ z * c = a :=
  Iff.rfl

theorem le_centerSubring (R : Subring K) : R ≤ centerSubring V R :=
  fun z hz => ⟨z, hz, 1, R.one_mem, map_one _, mul_one z⟩

theorem inv_mem_centerSubring {R : Subring K} {z : K} (hz : z ∈ centerSubring V R)
    (hz1 : V.valuation z = 1) : z⁻¹ ∈ centerSubring V R := by
  obtain ⟨a, ha, c, hc, hc1, hzc⟩ := mem_centerSubring.mp hz
  have hz0 : z ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hz1
    exact zero_ne_one hz1
  refine ⟨c, hc, a, ha, ?_, ?_⟩
  · rw [← hzc, map_mul, hz1, hc1, one_mul]
  · rw [← hzc, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]

/-- If `S ⊆ T_R`, then `T_S ⊆ T_R`. -/
theorem centerSubring_le {R S : Subring K} (h : S ≤ centerSubring V R) :
    centerSubring V S ≤ centerSubring V R := by
  intro z hz
  obtain ⟨a, ha, c, hc, hc1, hzc⟩ := mem_centerSubring.mp hz
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hc1
    exact zero_ne_one hc1
  have hza : z = a * c⁻¹ := by rw [← hzc, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
  rw [hza]
  exact Subring.mul_mem _ (h ha) (inv_mem_centerSubring (h hc) hc1)

theorem centerSubring_mono {R S : Subring K} (h : R ≤ S) : centerSubring V R ≤ centerSubring V S :=
  centerSubring_le (h.trans (le_centerSubring S))

/-- Let `A ⊆ V` be a subalgebra of `K`. Then the localization of `A` at the center of `V` is regular if and only if the subring `T_A` of `K` is regular. The ring `T_A` is this localization. -/
theorem isRegularLocalRing_localization_iff (A : Subalgebra k K) (h : ∀ a : A, (a : K) ∈ V) :
    IsRegularLocalRing (Localization.AtPrime (valuationCenter V A h)) ↔
      IsRegularLocalRing (centerSubring V A.toSubring) := by
  set T := centerSubring V A.toSubring
  set q := valuationCenter V A h
  have hmemq : ∀ a : A, a ∈ q ↔ V.valuation a < 1 := fun a => V.valuation_lt_one_iff ⟨a, h a⟩
  have hAT : ∀ a : A, (a : K) ∈ T := fun a => le_centerSubring A.toSubring a.2
  let j : A →+* T := (A.val : A →+* K).codRestrict T hAT
  let _ : Algebra A T := j.toAlgebra
  have hloc : IsLocalization q.primeCompl T := by
    refine (isLocalization_iff q.primeCompl T).mpr ⟨fun a => ?_, fun z => ?_, fun {a b} hab => ⟨1, ?_⟩⟩
    · have ha1 : V.valuation (a : A) = 1 := by
        have h2 := a.2
        rw [Ideal.mem_primeCompl_iff, hmemq] at h2
        exact le_antisymm (V.valuation_le_one ⟨_, h a⟩) (not_lt.mp h2)
      have ha0 : ((a : A) : K) ≠ 0 := fun h0 => by
        rw [h0, map_zero] at ha1
        exact zero_ne_one ha1
      have hinv : ((a : A) : K)⁻¹ ∈ T := inv_mem_centerSubring (hAT a) ha1
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
      change ((a : A) : K) * ((a : A) : K)⁻¹ = 1
      exact mul_inv_cancel₀ ha0
    · obtain ⟨b, hb, c, hc, hc1, hz⟩ := mem_centerSubring.mp z.2
      have hcq : (⟨c, hc⟩ : A) ∈ q.primeCompl := by
        rw [Ideal.mem_primeCompl_iff, hmemq]
        change ¬ V.valuation c < 1
        rw [hc1]
        exact lt_irrefl _
      exact ⟨(⟨b, hb⟩, ⟨_, hcq⟩), Subtype.ext hz⟩
    · have hab' : (a : K) = b := congrArg (fun t : T => (t : K)) hab
      rw [Subtype.ext hab']
  constructor
  · intro hreg
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) T).toRingEquiv
  · intro hreg
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).toRingEquiv

end CenterSubring

/-! ### Change of the ground field -/

section GroundField

variable {V : ValuationSubring K}

/-- A nonzero element of a subfield `F` of `K` with `F ⊆ V` has value 1. -/
theorem valuation_eq_one_of_mem {F : IntermediateField k K} (hFV : ∀ c ∈ F, c ∈ V) {c : K}
    (hc : c ∈ F) (hc0 : c ≠ 0) : V.valuation c = 1 :=
  (V.valuation_eq_one_iff ⟨c, hFV c hc⟩).mp (isUnit_iff_exists_inv.mpr
    ⟨⟨c⁻¹, hFV _ (F.inv_mem hc)⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩)

variable (V) in
/-- A subfield `F` of `K` with `F ⊆ V` makes `V` an `F`-algebra. -/
abbrev subfieldAlgebra (F : IntermediateField k K) (hFV : ∀ c ∈ F, c ∈ V) : Algebra F V :=
  ((algebraMap F K).codRestrict V fun c => hFV c c.2).toAlgebra

theorem subfieldAlgebra_isScalarTower (F : IntermediateField k K) (hFV : ∀ c ∈ F, c ∈ V) :
    letI := subfieldAlgebra V F hFV
    IsScalarTower F V K :=
  letI := subfieldAlgebra V F hFV
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- **Change of the ground field** (Volume 5, Lemma 1.4.2 of the handbook). Let `F` be a subfield of `K` that contains `k`, is finitely generated over `k`, and lies in `V`. Let `s` be a finite set. If `V` has a regular center on an affine model of `K/F` that contains `s`, then `V` has a regular center on an affine model of `K/k` that contains `s`. -/
theorem HasRegularCenter.of_intermediateField {F : IntermediateField k K} (hF : F.FG)
    (hFV : ∀ c ∈ F, c ∈ V) {s : Finset K} (hs : HasRegularCenter F V (s : Set K)) :
    HasRegularCenter k V (s : Set K) := by
  classical
  obtain ⟨A', hA'V, ⟨⟨g, hg⟩, hfrac⟩, hsA', hreg⟩ := hs
  obtain ⟨t, ht⟩ := hF
  set B : Subalgebra k K := Algebra.adjoin k ((t ∪ g ∪ s : Finset K) : Set K) with hB
  have hmemB : ∀ w, w ∈ t ∨ w ∈ g ∨ w ∈ s → w ∈ B := by
    intro w hw
    refine Algebra.subset_adjoin ?_
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    tauto
  have hFA' : ∀ c ∈ F, c ∈ A' := fun c hc => A'.algebraMap_mem (⟨c, hc⟩ : F)
  have hgA' : ∀ w ∈ g, w ∈ A' := fun w hw => by
    have h1 : w ∈ Algebra.adjoin F (g : Set K) := Algebra.subset_adjoin hw
    rwa [hg] at h1
  have htA' : ∀ w ∈ t, w ∈ A' := fun w hw => by
    have h1 : w ∈ IntermediateField.adjoin k (t : Set K) := IntermediateField.subset_adjoin k _ hw
    rw [ht] at h1
    exact hFA' w h1
  have hBA' : B.toSubring ≤ A'.toSubring := by
    have hle : B ≤ A'.restrictScalars k := by
      refine Algebra.adjoin_le fun w hw => ?_
      change w ∈ A'
      rw [Finset.coe_union, Finset.coe_union, Set.mem_union, Set.mem_union] at hw
      rcases hw with (hw | hw) | hw
      · exact htA' w hw
      · exact hgA' w hw
      · exact hsA' hw
    exact fun z hz => hle hz
  have hBV : ∀ b : B, (b : K) ∈ V := fun b => hA'V ⟨b, hBA' b.2⟩
  -- The subfield `F` lies in `T_B`.
  have hFT : ∀ c ∈ F, c ∈ centerSubring V B.toSubring := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0]
      exact Subring.zero_mem _
    have hc' := hc
    rw [← ht] at hc'
    obtain ⟨p, hp, q, hq, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hc'
    have htB : Algebra.adjoin k (t : Set K) ≤ B := Algebra.adjoin_le fun w hw => hmemB w (Or.inl hw)
    have hq0 : q ≠ 0 := fun h0 => hc0 (by rw [h0, div_zero])
    have hqF : q ∈ F := by
      have h2 : q ∈ IntermediateField.adjoin k (t : Set K) :=
        IntermediateField.algebra_adjoin_le_adjoin k _ hq
      rwa [ht] at h2
    exact ⟨p, htB hp, q, htB hq, valuation_eq_one_of_mem hFV hqF hq0, div_mul_cancel₀ p hq0⟩
  -- The model `A'` lies in `T_B`.
  have hA'T : A'.toSubring ≤ centerSubring V B.toSubring := by
    let TF : Subalgebra F K :=
      { centerSubring V B.toSubring with algebraMap_mem' := fun c => hFT c c.2 }
    have hle : A' ≤ TF := by
      rw [← hg]
      refine Algebra.adjoin_le fun w hw => ?_
      exact le_centerSubring B.toSubring (show w ∈ B from hmemB w (Or.inr (Or.inl hw)))
    exact fun z hz => hle hz
  have hT : centerSubring V B.toSubring = centerSubring V A'.toSubring :=
    le_antisymm (centerSubring_mono hBA') (centerSubring_le hA'T)
  refine ⟨B, hBV, ⟨⟨t ∪ g ∪ s, rfl⟩, ?_⟩, fun z hz => hmemB z (Or.inr (Or.inr hz)), ?_⟩
  · -- `K` is the fraction field of `B`.
    refine IsFractionRing.of_field B K fun z => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A' z
    have hb0 : (b : K) ≠ 0 := fun h0 => nonZeroDivisors.ne_zero hb (Subtype.ext h0)
    obtain ⟨a₁, ha₁, c₁, hc₁, hc₁1, h₁⟩ := mem_centerSubring.mp (hA'T a.2)
    obtain ⟨a₂, ha₂, c₂, hc₂, hc₂1, h₂⟩ := mem_centerSubring.mp (hA'T b.2)
    have hc₁0 : c₁ ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hc₁1
      exact zero_ne_one hc₁1
    have hc₂0 : c₂ ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hc₂1
      exact zero_ne_one hc₂1
    have ha₂0 : a₂ ≠ 0 := by
      rw [← h₂]
      exact mul_ne_zero hb0 hc₂0
    refine ⟨⟨a₁ * c₂, B.mul_mem ha₁ hc₂⟩, ⟨a₂ * c₁, B.mul_mem ha₂ hc₁⟩, ?_⟩
    change (a : K) / b = a₁ * c₂ / (a₂ * c₁)
    rw [div_eq_div_iff hb0 (mul_ne_zero ha₂0 hc₁0), ← h₁, ← h₂]
    ring
  · -- The local ring of `B` at the center of `V` is regular.
    have h1 := (isRegularLocalRing_localization_iff A' hA'V).mp hreg
    exact (isRegularLocalRing_localization_iff B hBV).mpr
      (IsRegularLocalRing.of_ringEquiv (RingEquiv.subringCongr hT.symm))

/-- **Change of the ground field** (Volume 5, Lemma 1.4.2 of the handbook). Let `F` be a subfield of `K` that contains `k`, is finitely generated over `k`, and lies in `V`. If `V` has local uniformization as a valuation of `K/F`, then `V` has local uniformization as a valuation of `K/k`. -/
theorem HasLocalUniformization.of_intermediateField {F : IntermediateField k K} (hF : F.FG)
    (hFV : ∀ c ∈ F, c ∈ V) (h : HasLocalUniformization F V) : HasLocalUniformization k V :=
  fun s hs => HasRegularCenter.of_intermediateField hF hFV (h s hs)

variable [Algebra k V] [IsScalarTower k V K] {κ : Type*}

omit [Algebra k K] [IsScalarTower k V K] in
theorem aeval_residue (y : κ → V) (p : MvPolynomial κ k) :
    residue V (aeval y p) = aeval (fun i => residue V (y i)) p :=
  MvPolynomial.comp_aeval_apply y (IsScalarTower.toAlgHom k V (ResidueField V)) p

theorem coe_aeval (y : κ → V) (p : MvPolynomial κ k) :
    ((aeval y p : V) : K) = aeval (fun i => (y i : K)) p :=
  MvPolynomial.comp_aeval_apply y (IsScalarTower.toAlgHom k V K) p

/-- **Lifts of independent residues** (Volume 5, Lemma 1.4.2 of the handbook, first claim). Let `y_1, ..., y_m ∈ V` have residues that are algebraically independent over `k`. Then the `y_i` are algebraically independent over `k`. -/
theorem algebraicIndependent_of_residue {y : κ → V}
    (hy : AlgebraicIndependent k fun i => residue V (y i)) :
    AlgebraicIndependent k fun i => (y i : K) := by
  have h1 : AlgebraicIndependent k y :=
    AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom k V (ResidueField V)) hy
  exact h1.map' (f := IsScalarTower.toAlgHom k V K) fun a b hab => Subtype.ext hab

/-- **Lifts of independent residues** (Volume 5, Lemma 1.4.2 of the handbook, second claim). Let `y_1, ..., y_m ∈ V` have residues that are algebraically independent over `k`. Then `k(y_1, ..., y_m) ⊆ V`, so `V` is trivial on `k(y_1, ..., y_m)`. -/
theorem mem_of_mem_adjoin_residue {y : κ → V}
    (hy : AlgebraicIndependent k fun i => residue V (y i)) {c : K}
    (hc : c ∈ IntermediateField.adjoin k (Set.range fun i => (y i : K))) : c ∈ V := by
  obtain ⟨p, hp, q, hq, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hc
  rw [Algebra.adjoin_range_eq_range_aeval] at hp hq
  obtain ⟨P, rfl⟩ := hp
  obtain ⟨Q, rfl⟩ := hq
  by_cases hQ : Q = 0
  · rw [hQ, map_zero, div_zero]
    exact V.zero_mem
  have hres : residue V (aeval y Q) ≠ 0 := by
    rw [aeval_residue]
    intro h0
    exact hQ (hy (h0.trans (map_zero _).symm))
  have hunit : IsUnit (aeval y Q) := (residue_ne_zero_iff_isUnit _).mp hres
  have hQ1 : V.valuation (aeval (fun i => (y i : K)) Q) = 1 := by
    rw [← coe_aeval]
    exact (V.valuation_eq_one_iff _).mp hunit
  refine (V.valuation_le_one_iff _).mp ?_
  change V.valuation (aeval (fun i => (y i : K)) P / aeval (fun i => (y i : K)) Q) ≤ 1
  rw [map_div₀, hQ1, div_one, ← coe_aeval]
  exact V.valuation_le_one _

/-- Let `y_1, ..., y_m ∈ K` be algebraically independent over `k` with `k(y_1, ..., y_m) ⊆ V`. Then the residues of the `y_i` are algebraically independent over `k`. This is the converse of `Singularity.algebraicIndependent_of_residue`. -/
theorem algebraicIndependent_residue {y : κ → K} (hy : AlgebraicIndependent k y)
    (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ V) :
    AlgebraicIndependent k fun i =>
      residue V ⟨y i, hyV _ (IntermediateField.subset_adjoin k _ (Set.mem_range_self i))⟩ := by
  set y' : κ → V := fun i => ⟨y i, hyV _ (IntermediateField.subset_adjoin k _ (Set.mem_range_self i))⟩
  intro P Q hPQ
  rw [← sub_eq_zero]
  by_contra h0
  have hPQ' : aeval (fun i => residue V (y' i)) (P - Q) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hPQ
  have hne : aeval y (P - Q) ≠ 0 := fun h => h0 (hy (h.trans (map_zero _).symm))
  have hmem : aeval y (P - Q) ∈ IntermediateField.adjoin k (Set.range y) :=
    IntermediateField.algebra_adjoin_le_adjoin k _
      ((Algebra.adjoin_range_eq_range_aeval k y).symm ▸ ⟨P - Q, rfl⟩)
  have h1 := valuation_eq_one_of_mem hyV hmem hne
  have hcoe : ((aeval y' (P - Q) : V) : K) = aeval y (P - Q) := coe_aeval y' (P - Q)
  rw [← hcoe, ← V.valuation_eq_one_iff] at h1
  have h2 := (residue_ne_zero_iff_isUnit _).mpr h1
  rw [aeval_residue] at h2
  exact h2 hPQ'

end GroundField

/-! ### Lemma 2.1.2, parts 1 and 2 -/

open MonomialValuation

namespace MonomialValuation

variable {ι : Type*} [Fintype ι] {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- Let `V` be a monomial valuation in `x_1, ..., x_n`, and let `z ≠ 0`. Then `z (1 + G) = c x^a (1 + F)` with `c ∈ k` nonzero and `v(F) < 1`, `v(G) < 1`. -/
theorem exists_eq_mul_one_add {x : ι → K} (hV : IsMonomialValuation k V x) {z : K} (hz0 : z ≠ 0) :
    ∃ (c : k) (a : ι → ℤ) (F G : K), c ≠ 0 ∧ V.valuation F < 1 ∧ V.valuation G < 1 ∧
      z * (1 + G) = algebraMap k K c * laurentMonomial x a * (1 + F) := by
  have hzK : z ∈ IntermediateField.adjoin k (Set.range x) := by
    rw [hV.adjoin_eq_top]
    exact IntermediateField.mem_top
  obtain ⟨f₀, hf₀, g₀, hg₀, hfg⟩ := IntermediateField.mem_adjoin_iff_div.mp hzK
  rw [Algebra.adjoin_range_eq_range_aeval] at hf₀ hg₀
  obtain ⟨P, rfl⟩ := hf₀
  obtain ⟨Q, rfl⟩ := hg₀
  replace hfg : z = aeval x P / aeval x Q := hfg
  have hP : P ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hfg
    exact hz0 hfg
  have hQ : Q ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero] at hfg
    exact hz0 hfg
  obtain ⟨c, α, -, F, hc, hPe, -, -, hF⟩ := exists_leadingTerm hV.ne_zero hV.independent hP
  obtain ⟨d, β, -, G, hd, hQe, -, -, hG⟩ := exists_leadingTerm hV.ne_zero hV.independent hQ
  have hG1 : V.valuation (1 + G) = 1 := Valuation.map_one_add_of_lt _ hG
  have hG0 : 1 + G ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hG1
    exact zero_ne_one hG1
  have hxβ : laurentMonomial x β ≠ 0 := laurentMonomial_ne_zero hV.ne_zero β
  have hd' : algebraMap k K d ≠ 0 := (map_ne_zero _).mpr hd
  refine ⟨c / d, α - β, F, G, div_ne_zero hc hd, hF, hG, ?_⟩
  rw [hfg, hPe, hQe, laurentMonomial_sub hV.ne_zero, map_div₀]
  field_simp

/-- Let `V` be a monomial valuation in `x_1, ..., x_n`. Each nonzero `z` has the value of a Laurent monomial `x^a`. -/
theorem exists_valuation_eq {x : ι → K} (hV : IsMonomialValuation k V x) {z : K} (hz0 : z ≠ 0) :
    ∃ a : ι → ℤ, V.valuation z = V.valuation (laurentMonomial x a) := by
  obtain ⟨c, a, F, G, hc, hF, hG, h⟩ := exists_eq_mul_one_add hV hz0
  refine ⟨a, ?_⟩
  have h2 := congrArg V.valuation h
  rwa [map_mul, map_mul, map_mul, Valuation.map_one_add_of_lt _ hF,
    Valuation.map_one_add_of_lt _ hG, mul_one, mul_one, valuation_algebraMap_eq_one hc,
    one_mul] at h2

end MonomialValuation

variable {ι : Type*} [Fintype ι] {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- **The value group of a monomial valuation** (Volume 5, Lemma 2.1.2 of the handbook, part 1). Let `V` be a monomial valuation of `K = k(x_1, ..., x_n)` in the elements `x_i`. Then the map `a ↦ v(x^a)` from `ℤ^n` to the value group is bijective. So the value group is the free abelian group on `v(x_1), ..., v(x_n)`. -/
theorem IsMonomialValuation.valueHom_bijective {x : ι → K} (hV : IsMonomialValuation k V x) :
    Function.Bijective (valueHom (V := V) hV.ne_zero) := by
  refine ⟨?_, fun γ => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    apply hV.independent a
    have h2 := congrArg (fun g => ((Additive.toMul g : V.ValueGroupˣ) : V.ValueGroup)) ha
    simpa [valueHom] using h2
  · obtain ⟨z, hz⟩ := V.valuation_surjective ((Additive.toMul γ : V.ValueGroupˣ) : V.ValueGroup)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [map_zero] at hz
      exact (Additive.toMul γ).ne_zero hz.symm
    obtain ⟨a, ha⟩ := exists_valuation_eq hV hz0
    refine ⟨a, ?_⟩
    change Additive.ofMul (Units.mk0 _ _) = Additive.ofMul (Additive.toMul γ)
    congr 1
    ext
    rw [Units.val_mk0, ← ha, hz]

/-- **The value group of a monomial valuation** (Volume 5, Lemma 2.1.2 of the handbook, part 1). Let `V` be a monomial valuation of `K = k(x_1, ..., x_n)` in the elements `x_i`. Then each element `γ` of the value group is the value `v(x^a)` of exactly one Laurent monomial `x^a`. -/
theorem IsMonomialValuation.existsUnique_valuation_eq {x : ι → K} (hV : IsMonomialValuation k V x)
    (γ : V.ValueGroupˣ) : ∃! a : ι → ℤ, V.valuation (laurentMonomial x a) = γ := by
  obtain ⟨z, hz⟩ := V.valuation_surjective (γ : V.ValueGroup)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact γ.ne_zero hz.symm
  obtain ⟨a, ha⟩ := exists_valuation_eq hV hz0
  refine ⟨a, ha.symm.trans hz, fun b hb => ?_⟩
  have hb : V.valuation (laurentMonomial x b) = γ := hb
  have h1 : V.valuation (laurentMonomial x (b - a)) = 1 := by
    rw [laurentMonomial_sub hV.ne_zero, map_div₀, hb, ← ha, hz, div_self γ.ne_zero]
  exact sub_eq_zero.mp (hV.independent _ h1)

/-- The isomorphism `a ↦ v(x^a)` from `ℤ^n` to the value group of a monomial valuation (Volume 5, Lemma 2.1.2 of the handbook, part 1). -/
noncomputable def IsMonomialValuation.valueGroupEquiv {x : ι → K} (hV : IsMonomialValuation k V x) :
    (ι → ℤ) ≃+ Additive V.ValueGroupˣ :=
  AddEquiv.ofBijective (valueHom hV.ne_zero) hV.valueHom_bijective

/-- The basis `v(x_1), ..., v(x_n)` of the value group of a monomial valuation (Volume 5, Lemma 2.1.2 of the handbook, part 1). -/
noncomputable def IsMonomialValuation.valueGroupBasis [DecidableEq ι] {x : ι → K}
    (hV : IsMonomialValuation k V x) : Module.Basis ι ℤ (Additive V.ValueGroupˣ) :=
  (Pi.basisFun ℤ ι).map hV.valueGroupEquiv.toIntLinearEquiv

theorem IsMonomialValuation.valueGroupBasis_apply [DecidableEq ι] {x : ι → K}
    (hV : IsMonomialValuation k V x) (i : ι) :
    hV.valueGroupBasis i =
      Additive.ofMul (Units.mk0 (V.valuation (x i)) ((Valuation.ne_zero_iff _).mpr (hV.ne_zero i))) := by
  rw [valueGroupBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  apply Additive.toMul.injective
  ext
  change V.valuation (laurentMonomial x (Pi.single i 1)) = V.valuation (x i)
  rw [laurentMonomial_single]

/-- **The residue field of a monomial valuation** (Volume 5, Lemma 2.1.2 of the handbook, part 2). Let `V` be a monomial valuation of `K = k(x_1, ..., x_n)` in the elements `x_i`. Then the map from `k` to the residue field of `V` is bijective. So the residue field is `k`.

Let `z ∈ V` with `v(z) = 1`. Then `z (1 + G) = c x^a (1 + F)` with `v(F), v(G) < 1`, and `v(x^a) = 1`, so `a = 0`. Thus the residue of `z` is the residue of `c`. -/
theorem IsMonomialValuation.algebraMap_residueField_bijective {x : ι → K}
    (hV : IsMonomialValuation k V x) : Function.Bijective (algebraMap k (ResidueField V)) := by
  refine ⟨(algebraMap k (ResidueField V)).injective, fun w => ?_⟩
  obtain ⟨z, rfl⟩ := residue_surjective w
  by_cases hz1 : V.valuation (z : K) < 1
  · refine ⟨0, ?_⟩
    rw [map_zero, eq_comm, residue_eq_zero_iff, V.valuation_lt_one_iff]
    exact hz1
  have hz1' : V.valuation (z : K) = 1 := le_antisymm (V.valuation_le_one z) (not_lt.mp hz1)
  have hz0 : (z : K) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hz1'
    exact zero_ne_one hz1'
  obtain ⟨c, a, F, G, hc, hF, hG, h⟩ := exists_eq_mul_one_add hV hz0
  have ha : a = 0 := by
    apply hV.independent a
    have h2 := congrArg V.valuation h
    rwa [map_mul, map_mul, map_mul, Valuation.map_one_add_of_lt _ hF,
      Valuation.map_one_add_of_lt _ hG, mul_one, mul_one, valuation_algebraMap_eq_one hc, one_mul,
      hz1', eq_comm] at h2
  rw [ha, laurentMonomial_zero, mul_one] at h
  refine ⟨c, ?_⟩
  have hFV : F ∈ V := (V.valuation_le_one_iff F).mp hF.le
  have hGV : G ∈ V := (V.valuation_le_one_iff G).mp hG.le
  have hFm : residue V ⟨F, hFV⟩ = 0 := (residue_eq_zero_iff _).mpr ((V.valuation_lt_one_iff _).mpr hF)
  have hGm : residue V ⟨G, hGV⟩ = 0 := (residue_eq_zero_iff _).mpr ((V.valuation_lt_one_iff _).mpr hG)
  have hcK : ((algebraMap k V c : V) : K) = algebraMap k K c :=
    (IsScalarTower.algebraMap_apply k V K c).symm
  have hV' : z * (1 + ⟨G, hGV⟩) = algebraMap k V c * (1 + ⟨F, hFV⟩) := by
    apply Subtype.ext
    change (z : K) * (1 + G) = ((algebraMap k V c : V) : K) * (1 + F)
    rw [hcK]
    exact h
  have h3 := congrArg (residue V) hV'
  rw [map_mul, map_mul, map_add, map_add, map_one, hFm, hGm, add_zero, mul_one, mul_one] at h3
  rw [h3, IsScalarTower.algebraMap_apply k V (ResidueField V), ResidueField.algebraMap_eq]

/-- The isomorphism of `k` onto the residue field of a monomial valuation (Volume 5, Lemma 2.1.2 of the handbook, part 2). -/
noncomputable def IsMonomialValuation.residueFieldEquiv {x : ι → K}
    (hV : IsMonomialValuation k V x) : k ≃ₐ[k] ResidueField V :=
  AlgEquiv.ofBijective (Algebra.ofId k (ResidueField V)) hV.algebraMap_residueField_bijective

/-! ### Corollary 2.1.6 -/

section Corollary

variable {κ : Type*} [Fintype κ]

/-- **Monomial valuations over `k(y)`, local uniformization** (Volume 5, Corollary 2.1.6 of the handbook). Let `y_1, ..., y_t ∈ K`, and let `V` be a valuation that is trivial on `k(y)`, that is, `k(y) ⊆ V`. Assume that `V` is a monomial valuation of `K = k(y)(x_1, ..., x_r)` over the field `k(y)`. Then `V` has local uniformization as a valuation of `K/k`.

The affine models here are finitely generated `k`-algebras, not `k(y)`-algebras. This is the form that the proof of the theorem of Knaf-Kuhlmann needs. -/
theorem hasLocalUniformization_of_isMonomialValuation_adjoin {V : ValuationSubring K} {y : κ → K}
    {x : ι → K} (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ V)
    (hV : IsMonomialValuation (IntermediateField.adjoin k (Set.range y)) V x) :
    HasLocalUniformization k V := by
  classical
  let _ := subfieldAlgebra V _ hyV
  have _ := subfieldAlgebra_isScalarTower _ hyV
  refine HasLocalUniformization.of_intermediateField ⟨Finset.univ.image y, ?_⟩ hyV
    (hasLocalUniformization_of_isMonomialValuation hV)
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- **Monomial valuations over `k(y)`, the Abhyankar property** (Volume 5, Corollary 2.1.6 of the handbook). Let `y_1, ..., y_t ∈ K` be algebraically independent over `k`, and let `V` be a valuation of `K/k` that is trivial on `k(y)` and is a monomial valuation of `K = k(y)(x_1, ..., x_r)` over `k(y)`. Then `V` is an Abhyankar valuation of `K/k`.

The value group has rank `r` (`Singularity.IsMonomialValuation.valueGroupBasis` over `k(y)`). The residues of the `y_i` are algebraically independent over `k`, so the residue field has transcendence degree at least `t`. The field `K` is generated by `r + t` elements. The inequality of Abhyankar gives equality. -/
theorem IsMonomialValuation.isAbhyankarValuation_adjoin {y : κ → K} {x : ι → K}
    (hy : AlgebraicIndependent k y) (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ V)
    (hV : IsMonomialValuation (IntermediateField.adjoin k (Set.range y)) V x) :
    IsAbhyankarValuation k V := by
  classical
  have htop : IntermediateField.adjoin k (Set.range y ∪ Set.range x) = ⊤ := by
    rw [← IntermediateField.adjoin_adjoin_left, hV.adjoin_eq_top,
      IntermediateField.restrictScalars_top]
  let _ := subfieldAlgebra V _ hyV
  have _ := subfieldAlgebra_isScalarTower _ hyV
  have hrank : Module.rank ℤ (Additive V.ValueGroupˣ) = Fintype.card ι :=
    rank_eq_card_basis hV.valueGroupBasis
  have hres : (Fintype.card κ : Cardinal) ≤ Algebra.trdeg k (ResidueField V) := by
    simpa using (algebraicIndependent_residue hy hyV).lift_cardinalMk_le_trdeg
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range y ∪ Set.range x)) K :=
    ⟨fun z => by
      have hz : z ∈ IntermediateField.adjoin k (Set.range y ∪ Set.range x) := by
        rw [htop]
        trivial
      exact isAlgebraic_algebraMap
        (⟨z, hz⟩ : IntermediateField.adjoin k (Set.range y ∪ Set.range x))⟩
  have halg' := IntermediateField.isAlgebraic_adjoin_iff_top.mp halg
  have htr : Algebra.trdeg k K ≤ (Fintype.card κ : Cardinal) + Fintype.card ι := by
    refine (Algebra.IsAlgebraic.trdeg_le_cardinalMk k (Set.range y ∪ Set.range x)).trans ?_
    refine (Cardinal.mk_union_le _ _).trans (add_le_add ?_ ?_)
    · simpa using Cardinal.mk_range_le_lift (f := y)
    · simpa using Cardinal.mk_range_le_lift (f := x)
  refine le_antisymm (abhyankar_inequality V) ?_
  rw [(TensorProduct.isBaseChange ℤ (Additive V.ValueGroupˣ) ℚ).rank_eq, hrank]
  exact htr.trans ((add_comm _ _).le.trans (add_le_add le_rfl hres))

omit [Fintype κ] in
/-- **Monomial valuations over `k(y)`, the residue field** (Volume 5, Corollary 2.1.6 of the handbook). Let `V` be a valuation of `K/k` that is trivial on `k(y_1, ..., y_t)` and is a monomial valuation of `K = k(y)(x_1, ..., x_r)` over `k(y)`. Then the residue field of `V` is generated over `k` by the residues `ȳ_1, ..., ȳ_t`. If the `y_i` are algebraically independent over `k`, then so are the `ȳ_i` (`Singularity.algebraicIndependent_residue`), so the residue field is the field of rational functions `k(ȳ_1, ..., ȳ_t)`. -/
theorem IsMonomialValuation.adjoin_residue_eq_top {y : κ → K} {x : ι → K}
    (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ V)
    (hV : IsMonomialValuation (IntermediateField.adjoin k (Set.range y)) V x) :
    IntermediateField.adjoin k (Set.range fun i =>
      residue V ⟨y i, hyV _ (IntermediateField.subset_adjoin k _ (Set.mem_range_self i))⟩) = ⊤ := by
  classical
  set y' : κ → V := fun i => ⟨y i, hyV _ (IntermediateField.subset_adjoin k _ (Set.mem_range_self i))⟩
  set L := IntermediateField.adjoin k (Set.range fun i => residue V (y' i))
  let _ := subfieldAlgebra V _ hyV
  have _ := subfieldAlgebra_isScalarTower _ hyV
  have hbij := hV.algebraMap_residueField_bijective
  rw [eq_top_iff]
  rintro w -
  obtain ⟨c, rfl⟩ := hbij.2 w
  have hc : algebraMap (IntermediateField.adjoin k (Set.range y)) (ResidueField V) c =
      residue V ⟨(c : K), hyV c c.2⟩ := by
    rw [IsScalarTower.algebraMap_apply (IntermediateField.adjoin k (Set.range y)) V (ResidueField V),
      ResidueField.algebraMap_eq]
    rfl
  rw [hc]
  -- The residues of the polynomials in `y` lie in `L`.
  have hpoly : ∀ P : MvPolynomial κ k, residue V (aeval y' P) ∈ L := fun P => by
    rw [aeval_residue]
    have h1 : aeval (fun i => residue V (y' i)) P ∈
        Algebra.adjoin k (Set.range fun i => residue V (y' i)) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨P, rfl⟩
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  have hcoe : ∀ P : MvPolynomial κ k, ((aeval y' P : V) : K) = aeval y P := fun P => coe_aeval y' P
  obtain ⟨p, hp, q, hq, hpq⟩ := IntermediateField.mem_adjoin_iff_div.mp c.2
  rw [Algebra.adjoin_range_eq_range_aeval] at hp hq
  obtain ⟨P, rfl⟩ := hp
  obtain ⟨Q, rfl⟩ := hq
  replace hpq : (c : K) = aeval y P / aeval y Q := hpq
  by_cases hq0 : aeval y Q = 0
  · have hc0 : (⟨(c : K), hyV c c.2⟩ : V) = 0 := Subtype.ext (by
      change (c : K) = 0
      rw [hpq, hq0, div_zero])
    rw [hc0, map_zero]
    exact L.zero_mem
  have hqF : aeval y Q ∈ IntermediateField.adjoin k (Set.range y) :=
    IntermediateField.algebra_adjoin_le_adjoin k _
      ((Algebra.adjoin_range_eq_range_aeval k y).symm ▸ ⟨Q, rfl⟩)
  have hq1 := valuation_eq_one_of_mem hyV hqF hq0
  rw [← hcoe, ← V.valuation_eq_one_iff] at hq1
  have hqres : residue V (aeval y' Q) ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr hq1
  have hmul : (⟨(c : K), hyV c c.2⟩ : V) * aeval y' Q = aeval y' P := by
    apply Subtype.ext
    change (c : K) * ((aeval y' Q : V) : K) = ((aeval y' P : V) : K)
    rw [hcoe, hcoe, hpq, div_mul_cancel₀ _ hq0]
  have h3 := congrArg (residue V) hmul
  rw [map_mul] at h3
  rw [eq_div_of_mul_eq hqres h3]
  exact L.div_mem (hpoly P) (hpoly Q)

end Corollary

end Singularity
