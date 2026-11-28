/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.WeakLogMonomialization
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The normal form of a monomial modulo p-th powers

Let `R` be a local ring, let `x_1, ..., x_n` be elements of `R`, let `u` be a unit of `R`, let `a ∈ ℕ ^ n` and let `i` be an index with `p ∤ a_i`. Let `f = h ^ p + u x ^ a`. This file proves part 2 of Volume 5, Lemma 4.3.7 of the handbook. There are units `v` and `w` of `R` with `u = v ^ (a_i) w ^ p`. Put `x_i' = v x_i` and `x_j' = x_j` for `j ≠ i`. Then `f = h ^ p + w ^ p x' ^ a`, the family `x'` generates the same ideal as `x`, and `x'` is a regular system of parameters if `x` is one. If `z ^ p = f` in a field `L` of characteristic `p`, then `z' = (z - h) / w` satisfies `z' ^ p = x' ^ a`, and `E(z) = E(z')` for each subfield `E` of `L` that contains the image of `R`. For the predicate `IsMonomialModPow` of `Singularity/Valuation/WeakLogMonomialization.lean`, a form of the ramified type becomes a form with the unit `u = 1`.

## Main definitions

* `Singularity.changeParam`: the family `x'` with `x_i' = v x_i` and `x_j' = x_j` for `j ≠ i`.

## Main results

* `Singularity.exists_units_pow_mul_pow_eq`: if `p` and `m` are coprime, then each unit `u` is `v ^ m * w ^ p` for units `v` and `w`.
* `Singularity.IsUnit.exists_pow_mul_pow_eq`: the same statement for an element `u` with `IsUnit u`.
* `Singularity.prod_changeParam_pow`: `x' ^ a = v ^ (a_i) x ^ a`.
* `Singularity.mul_prod_eq_pow_mul_prod_changeParam`: if `u = v ^ (a_i) w ^ p`, then `u x ^ a = w ^ p x' ^ a`.
* `Singularity.span_range_changeParam`: the family `x'` generates the same ideal as `x`.
* `Singularity.IsRegularSystemOfParameters.of_span_eq_of_card_le`: in a Noetherian local ring, a finite set that generates the same ideal as a regular system of parameters and has at most as many elements is a regular system of parameters.
* `Singularity.IsRegularSystemOfParameters.image_changeParam`: if the members of an injective family `x` form a regular system of parameters, then the members of `x'` form one.
* `Singularity.exists_eq_add_pow_mul_prod_changeParam`: the normal form `f = h ^ p + w ^ p x' ^ a`.
* `Singularity.div_pow_eq_of_eq_add`: if `f = h ^ p + w ^ p y` and `z ^ p = f`, then `((z - h) / w) ^ p = y`.
* `Singularity.adjoin_simple_eq_adjoin_simple_div`: `E(z) = E((z - h) / w)`.
* `Singularity.exists_normalForm_adjoin_eq`: the normal form and the field statement together.
* `Singularity.exists_eq_add_prod_of_mem`: a form `f = h ^ p + g ^ p (u ∏ x ^ a x)` over a regular system of parameters `s` with `p ∤ a x_0` becomes `f = h ^ p + g' ^ p ∏ x ^ a' x` over a new regular system of parameters.
* `Singularity.IsMonomialModPow.exists_eq_add_prod_or`: an element that is monomial modulo `p`-th powers has a form with the unit `1`, or a form of the residual type.
* `Singularity.isMonomialModPow_of_eq_add_prod`: a form with the unit `1` is monomial modulo `p`-th powers.

## The proof

Since `p` and `m = a_i` are coprime, there are integers `b` and `c` with `b m + c p = 1`. Put `v = u ^ b` and `w = u ^ c`. These are integer powers of a unit, and `v ^ m w ^ p = u ^ (b m + c p) = u`. The family `x'` is `x_j' = e_j x_j` with `e_i = v` and `e_j = 1` for `j ≠ i`. So `x' ^ a = v ^ (a_i) x ^ a`, and `u x ^ a = w ^ p v ^ (a_i) x ^ a = w ^ p x' ^ a`. Each `x_j'` is a unit times `x_j`, and each `x_j` is a unit times `x_j'`, so the two families generate the same ideal. In a Noetherian local ring the dimension is at most the number of generators of the maximal ideal. So a generating set with at most `dim R` elements has exactly `dim R` elements, and it is a regular system of parameters. In characteristic `p` the equation `(z - h) ^ p = z ^ p - h ^ p = w ^ p x' ^ a` holds, so `((z - h) / w) ^ p = x' ^ a`. The element `z' = (z - h) / w` is in `E(z)`, and `z = w z' + h` is in `E(z')`.

For a regular system of parameters `s` as a finite set, put `s' = (s \ {x_0}) ∪ {v x_0}`. The set `s'` generates the maximal ideal and has at most `card s` elements. So `s'` is a regular system of parameters with `card s' = card s`, and so `v x_0 ∉ s \ {x_0}`. Then the product over `s'` is the product over `s` times `v ^ (a x_0)`.

## What is not proved

This file does not join the normal form to the monomial step `MonomialInseparableStep`. The toric case of the monomial step, where two or more exponents are not divisible by `p`, is not proved. The predicate `IsRegularSystemOfParameters` is on finite sets. So the statement for a family `x` asks that `x` is injective and that the image of `x` is a regular system of parameters. The statements on regular systems of parameters ask that `R` is Noetherian.

## References

* Volume 5, Lemma 4.3.7 of the handbook.
* Volume 5, Chapter 4 of the handbook.
-/

open IsLocalRing IntermediateField

namespace Singularity

section Units

variable {M : Type*} [CommMonoid M]

/-- **A unit is `v ^ m * w ^ p`.** Let `p` and `m` be coprime natural numbers and let `u` be a unit of a commutative monoid. Then there are units `v` and `w` with `u = v ^ m * w ^ p`. Take integers `b` and `c` with `b m + c p = 1`, and put `v = u ^ b` and `w = u ^ c`. -/
theorem exists_units_pow_mul_pow_eq (u : Mˣ) {p m : ℕ} (h : p.Coprime m) :
    ∃ v w : Mˣ, u = v ^ m * w ^ p := by
  refine ⟨u ^ m.gcdA p, u ^ m.gcdB p, ?_⟩
  have hg : ((m.gcd p : ℕ) : ℤ) = m * m.gcdA p + p * m.gcdB p := Nat.gcd_eq_gcd_ab m p
  rw [Nat.Coprime.gcd_eq_one h.symm, Nat.cast_one] at hg
  have h1 : m.gcdA p * m + m.gcdB p * p = 1 := by linarith
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, h1, zpow_one]

/-- **A unit is `v ^ m * w ^ p`, the form with `IsUnit`.** Let `p` and `m` be coprime natural numbers and let `u` be an element of a commutative monoid with `IsUnit u`. Then there are elements `v` and `w` with `IsUnit v`, `IsUnit w` and `u = v ^ m * w ^ p`. -/
theorem IsUnit.exists_pow_mul_pow_eq {u : M} (hu : IsUnit u) {p m : ℕ} (h : p.Coprime m) :
    ∃ v w : M, IsUnit v ∧ IsUnit w ∧ u = v ^ m * w ^ p := by
  obtain ⟨u, rfl⟩ := hu
  obtain ⟨v, w, hvw⟩ := exists_units_pow_mul_pow_eq u h
  exact ⟨v, w, v.isUnit, w.isUnit, by rw [hvw, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val]⟩

end Units

section ChangeParam

variable {ι R : Type*} [DecidableEq ι]

/-- The change of one parameter. For a family `x : ι → R`, an index `i` and an element `v`, the family `changeParam x i v` has `v * x i` at the index `i` and `x j` at each index `j ≠ i`. -/
def changeParam [Mul R] (x : ι → R) (i : ι) (v : R) : ι → R :=
  Function.update x i (v * x i)

/-- The member of `changeParam x i v` at the index `j` is `e * x j`, with `e = v` if `j = i` and `e = 1` if `j ≠ i`. -/
theorem changeParam_apply [Monoid R] (x : ι → R) (i : ι) (v : R) (j : ι) :
    changeParam x i v j = (if j = i then v else 1) * x j := by
  unfold changeParam
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [hj]

/-- **The monomial in the new parameters.** For the family `x' = changeParam x i v` and exponents `a`, the monomial `∏ j, x' j ^ a j` is `v ^ a i * ∏ j, x j ^ a j`. -/
theorem prod_changeParam_pow [Fintype ι] [CommMonoid R] (x : ι → R) (i : ι) (v : R)
    (a : ι → ℕ) : ∏ j, changeParam x i v j ^ a j = v ^ a i * ∏ j, x j ^ a j := by
  simp_rw [changeParam_apply, mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- **The unit goes into the parameters.** Let `u = v ^ a i * w ^ p`, and let `x' = changeParam x i v`. Then `u * ∏ j, x j ^ a j = w ^ p * ∏ j, x' j ^ a j`. -/
theorem mul_prod_eq_pow_mul_prod_changeParam [Fintype ι] [CommMonoid R] {x : ι → R} {i : ι}
    {a : ι → ℕ} {p : ℕ} {u v w : R} (huvw : u = v ^ a i * w ^ p) :
    u * ∏ j, x j ^ a j = w ^ p * ∏ j, changeParam x i v j ^ a j := by
  rw [prod_changeParam_pow, huvw, mul_comm (v ^ a i), mul_assoc]

/-- **The ideal does not change.** If `v` is a unit, then the family `changeParam x i v` generates the same ideal as `x`. Each member of one family is a unit times the member of the other family at the same index. -/
theorem span_range_changeParam [CommSemiring R] (x : ι → R) (i : ι) {v : R} (hv : IsUnit v) :
    Ideal.span (Set.range (changeParam x i v)) = Ideal.span (Set.range x) := by
  obtain ⟨v, rfl⟩ := hv
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [changeParam_apply]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : x j = (if j = i then ((v⁻¹ : Rˣ) : R) else 1) * changeParam x i v j := by
      rw [changeParam_apply, ← mul_assoc]
      split_ifs <;> simp
    rw [hj]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

end ChangeParam

section Parameters

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **A generating set of the right size is a regular system of parameters.** Let `R` be a Noetherian local ring, let `s` be a regular system of parameters, and let `t` be a finite set that generates the same ideal as `s` with `card t ≤ card s`. Then `t` is a regular system of parameters and `card t = card s`. The dimension of `R` is at most the number of generators of the maximal ideal. -/
theorem IsRegularSystemOfParameters.of_span_eq_of_card_le {s t : Finset R}
    (hs : IsRegularSystemOfParameters s)
    (hspan : Ideal.span (t : Set R) = Ideal.span (s : Set R)) (hcard : t.card ≤ s.card) :
    IsRegularSystemOfParameters t ∧ t.card = s.card := by
  have h1 : (maximalIdeal R).spanFinrank ≤ t.card := by
    rw [← hs.1, ← hspan]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite t.finite_toSet).trans_eq
      (Set.ncard_coe_finset t)
  have h2 : ((s.card : ℕ) : WithBot ℕ∞) ≤ ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    hs.2 ▸ ringKrullDim_le_spanFinrank_maximalIdeal R
  have h3 : s.card ≤ (maximalIdeal R).spanFinrank := by exact_mod_cast h2
  have heq : t.card = s.card := by omega
  exact ⟨⟨hspan.trans hs.1, by rw [heq]; exact hs.2⟩, heq⟩

/-- **The change of one parameter keeps a regular system of parameters.** Let `R` be a Noetherian local ring, let `x : ι → R` be injective, and let the image of `x` be a regular system of parameters. If `v` is a unit, then the image of `changeParam x i v` is a regular system of parameters. -/
theorem IsRegularSystemOfParameters.image_changeParam {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq R] {x : ι → R} (hx : IsRegularSystemOfParameters (Finset.univ.image x))
    (hinj : Function.Injective x) (i : ι) {v : R} (hv : IsUnit v) :
    IsRegularSystemOfParameters (Finset.univ.image (changeParam x i v)) := by
  refine (hx.of_span_eq_of_card_le ?_ ?_).1
  · simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact span_range_changeParam x i hv
  · rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_image_le

end Parameters

section NormalForm

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- **The normal form of a monomial modulo `p`-th powers** (Volume 5, Lemma 4.3.7 of the handbook, part 2). Let `f = h ^ p + u * ∏ j, x j ^ a j` with `u` a unit, and let `p` and `a i` be coprime. Then there are units `v` and `w` with `u = v ^ a i * w ^ p`, and with `x' = changeParam x i v` the equation `f = h ^ p + w ^ p * ∏ j, x' j ^ a j` holds. The family `x'` generates the same ideal as `x`. -/
theorem exists_eq_add_pow_mul_prod_changeParam {p : ℕ} {x : ι → R} {a : ι → ℕ} {i : ι}
    (hpa : p.Coprime (a i)) {f h u : R} (hu : IsUnit u) (hf : f = h ^ p + u * ∏ j, x j ^ a j) :
    ∃ v w : R, IsUnit v ∧ IsUnit w ∧ u = v ^ a i * w ^ p ∧
      f = h ^ p + w ^ p * ∏ j, changeParam x i v j ^ a j ∧
      Ideal.span (Set.range (changeParam x i v)) = Ideal.span (Set.range x) := by
  obtain ⟨v, w, hv, hw, huvw⟩ := IsUnit.exists_pow_mul_pow_eq hu hpa
  exact ⟨v, w, hv, hw, huvw, by rw [hf, mul_prod_eq_pow_mul_prod_changeParam huvw],
    span_range_changeParam x i hv⟩

/-- **The `p`-th root of the new monomial.** Let `L` be a field of characteristic `p` with a map from `R`, let `f = h ^ p + w ^ p * y` with `w` a unit, and let `z ^ p = f` in `L`. Then `((z - h) / w) ^ p = y` in `L`, because `(z - h) ^ p = z ^ p - h ^ p`. -/
theorem div_pow_eq_of_eq_add {L : Type*} [Field L] [Algebra R L] {p : ℕ} [ExpChar L p]
    {f h w y : R} (hw : IsUnit w) (hf : f = h ^ p + w ^ p * y) {z : L}
    (hz : z ^ p = algebraMap R L f) :
    ((z - algebraMap R L h) / algebraMap R L w) ^ p = algebraMap R L y := by
  have hw' : algebraMap R L w ≠ 0 := (hw.map (algebraMap R L)).ne_zero
  rw [div_pow, sub_pow_expChar, hz, hf, map_add, map_mul, map_pow, map_pow, add_sub_cancel_left,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hw')]

/-- **The field does not change.** Let `E ⊆ L` be fields with compatible maps from `R`, let `w` be a unit of `R` and let `z ∈ L`. Then `E(z) = E((z - h) / w)`. The element `(z - h) / w` is in `E(z)`, and `z = w ((z - h) / w) + h` is in `E((z - h) / w)`. -/
theorem adjoin_simple_eq_adjoin_simple_div {E L : Type*} [Field E] [Field L] [Algebra R E]
    [Algebra R L] [Algebra E L] [IsScalarTower R E L] (h : R) {w : R} (hw : IsUnit w) (z : L) :
    E⟮z⟯ = E⟮(z - algebraMap R L h) / algebraMap R L w⟯ := by
  have hw' : algebraMap R L w ≠ 0 := (hw.map (algebraMap R L)).ne_zero
  have hh : algebraMap R L h = algebraMap E L (algebraMap R E h) :=
    IsScalarTower.algebraMap_apply R E L h
  have hw2 : algebraMap R L w = algebraMap E L (algebraMap R E w) :=
    IsScalarTower.algebraMap_apply R E L w
  refine le_antisymm (adjoin_simple_le_iff.2 ?_) (adjoin_simple_le_iff.2 ?_)
  · have hz : z = (z - algebraMap R L h) / algebraMap R L w * algebraMap R L w +
        algebraMap R L h := by
      rw [div_mul_cancel₀ _ hw', sub_add_cancel]
    have hmem : (z - algebraMap R L h) / algebraMap R L w * algebraMap R L w +
        algebraMap R L h ∈ E⟮(z - algebraMap R L h) / algebraMap R L w⟯ := by
      refine add_mem (mul_mem (mem_adjoin_simple_self E _) ?_) ?_
      · rw [hw2]
        exact IntermediateField.algebraMap_mem _ _
      · rw [hh]
        exact IntermediateField.algebraMap_mem _ _
    rwa [← hz] at hmem
  · refine div_mem (sub_mem (mem_adjoin_simple_self E z) ?_) ?_
    · rw [hh]
      exact IntermediateField.algebraMap_mem _ _
    · rw [hw2]
      exact IntermediateField.algebraMap_mem _ _

/-- **The normal form and the field** (Volume 5, Lemma 4.3.7 of the handbook, part 2). Let `f = h ^ p + u * ∏ j, x j ^ a j` with `u` a unit, and let `p` and `a i` be coprime. Let `E ⊆ L` be fields with compatible maps from `R`, where `L` has characteristic `p`, and let `z ∈ L` with `z ^ p = f`. Then there are units `v` and `w` of `R` with `u = v ^ a i * w ^ p` such that, for `x' = changeParam x i v` and `z' = (z - h) / w`, the following hold: `f = h ^ p + w ^ p * ∏ j, x' j ^ a j`, the family `x'` generates the same ideal as `x`, `z' ^ p = ∏ j, x' j ^ a j` in `L`, and `E(z) = E(z')`. -/
theorem exists_normalForm_adjoin_eq {E L : Type*} [Field E] [Field L] [Algebra R E] [Algebra R L]
    [Algebra E L] [IsScalarTower R E L] {p : ℕ} [ExpChar L p] {x : ι → R} {a : ι → ℕ} {i : ι}
    (hpa : p.Coprime (a i)) {f h u : R} (hu : IsUnit u) (hf : f = h ^ p + u * ∏ j, x j ^ a j)
    {z : L} (hz : z ^ p = algebraMap R L f) :
    ∃ v w : R, IsUnit v ∧ IsUnit w ∧ u = v ^ a i * w ^ p ∧
      f = h ^ p + w ^ p * ∏ j, changeParam x i v j ^ a j ∧
      Ideal.span (Set.range (changeParam x i v)) = Ideal.span (Set.range x) ∧
      ((z - algebraMap R L h) / algebraMap R L w) ^ p =
        algebraMap R L (∏ j, changeParam x i v j ^ a j) ∧
      E⟮z⟯ = E⟮(z - algebraMap R L h) / algebraMap R L w⟯ := by
  obtain ⟨v, w, hv, hw, huvw, hf', hspan⟩ := exists_eq_add_pow_mul_prod_changeParam hpa hu hf
  exact ⟨v, w, hv, hw, huvw, hf', hspan, div_pow_eq_of_eq_add hw hf' hz,
    adjoin_simple_eq_adjoin_simple_div h hw z⟩

end NormalForm

section MonomialModPow

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **The normal form over a regular system of parameters as a finite set.** Let `R` be a Noetherian local ring, let `p` be a prime, let `s` be a regular system of parameters, and let `f = h ^ p + g ^ p * (u * ∏ x ∈ s, x ^ a x)` with `u` a unit and `g ≠ 0`. Let `x₀ ∈ s` with `p ∤ a x₀`. Then there are `g' ≠ 0`, a regular system of parameters `s'` and exponents `a'` with `f = h ^ p + g' ^ p * ∏ x ∈ s', x ^ a' x` and `p ∤ a' x` for some `x ∈ s'`.

Write `u = v ^ (a x₀) * w ^ p` with units `v` and `w`. Put `g' = g w` and `s' = (s \ {x₀}) ∪ {v x₀}`, with the exponent `a x₀` at `v x₀` and the exponent `a x` at the other members. -/
theorem exists_eq_add_prod_of_mem [IsNoetherianRing R] {p : ℕ} (hp : p.Prime) {f h g u : R}
    {s : Finset R} {a : R → ℕ} (hs : IsRegularSystemOfParameters s) (hu : IsUnit u) (hg : g ≠ 0)
    (hf : f = h ^ p + g ^ p * (u * ∏ x ∈ s, x ^ a x)) {x₀ : R} (hx₀ : x₀ ∈ s)
    (ha : ¬ p ∣ a x₀) :
    ∃ (g' : R) (s' : Finset R) (a' : R → ℕ), IsRegularSystemOfParameters s' ∧ g' ≠ 0 ∧
      f = h ^ p + g' ^ p * ∏ x ∈ s', x ^ a' x ∧ ∃ x ∈ s', ¬ p ∣ a' x := by
  classical
  obtain ⟨v, w, hv, hw, huvw⟩ := IsUnit.exists_pow_mul_pow_eq hu (hp.coprime_iff_not_dvd.2 ha)
  obtain ⟨s', hs'⟩ : ∃ s' : Finset R, s' = insert (v * x₀) (s.erase x₀) := ⟨_, rfl⟩
  set a' : R → ℕ := fun y => if y = v * x₀ then a x₀ else a y with ha'
  have hspan : Ideal.span (s' : Set R) = Ideal.span (s : Set R) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      intro y hy
      rw [hs', Finset.coe_insert, Set.mem_insert_iff] at hy
      rcases hy with rfl | hy
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span hx₀)
      · exact Ideal.subset_span (Finset.mem_of_mem_erase hy)
    · rw [Ideal.span_le]
      intro y hy
      by_cases hyx : y = x₀
      · subst hyx
        obtain ⟨v, rfl⟩ := hv
        have : y = ((v⁻¹ : Rˣ) : R) * (v * y) := by rw [← mul_assoc, Units.inv_mul, one_mul]
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (hs' ▸ Finset.mem_insert_self _ _))
      · exact Ideal.subset_span (hs' ▸ Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hyx, hy⟩))
  have hpos : 0 < s.card := Finset.card_pos.2 ⟨x₀, hx₀⟩
  have herase : (s.erase x₀).card = s.card - 1 := Finset.card_erase_of_mem hx₀
  have hcard : s'.card ≤ s.card := by
    have := Finset.card_insert_le (v * x₀) (s.erase x₀)
    rw [hs']
    omega
  obtain ⟨hs'reg, hcard'⟩ := hs.of_span_eq_of_card_le hspan hcard
  have hnot : v * x₀ ∉ s.erase x₀ := by
    intro hmem
    have := Finset.card_insert_of_mem hmem
    rw [hs'] at hcard'
    omega
  have hprod : ∏ x ∈ s', x ^ a' x = (v * x₀) ^ a x₀ * ∏ x ∈ s.erase x₀, x ^ a x := by
    rw [hs', Finset.prod_insert hnot]
    congr 1
    · simp [ha']
    · refine Finset.prod_congr rfl fun y hy => ?_
      have hy' : y ≠ v * x₀ := fun h' => hnot (h' ▸ hy)
      simp [ha', hy']
  refine ⟨g * w, s', a', hs'reg, fun h0 => hg (hw.mul_left_eq_zero.1 h0), ?_,
    ⟨v * x₀, hs' ▸ Finset.mem_insert_self _ _, by simpa [ha'] using ha⟩⟩
  rw [hprod, hf, ← Finset.mul_prod_erase s (fun x => x ^ a x) hx₀, huvw]
  ring

/-- **A form with the unit `1`** (Volume 5, Lemma 4.3.7 of the handbook, part 2). Let `R` be a Noetherian local ring, let `p` be a prime, and let `f` be monomial modulo `p`-th powers (`IsMonomialModPow p f`). Then one of two cases holds. In the first case `f = h ^ p + g ^ p * ∏ x ∈ s, x ^ a x` with `g ≠ 0`, a regular system of parameters `s` and some exponent `a x` with `x ∈ s` not divisible by `p`. This is the ramified type with the unit `1`. In the second case `f = h ^ p + g ^ p * u` with `g ≠ 0` and `u` a unit whose class in the residue field is not a `p`-th power. This is the residual type.

The predicate `IsMonomialModPow` has the regular system of parameters under an existential quantifier. So the first case is the statement "`IsMonomialModPow p f` holds with `u = 1` and a form of the ramified type". The change of the parameters is in `exists_eq_add_prod_of_mem`. The second case cannot have the unit `1`, because the class of `1` is a `p`-th power. -/
theorem IsMonomialModPow.exists_eq_add_prod_or [IsNoetherianRing R] {p : ℕ} (hp : p.Prime)
    {f : R} (hf : IsMonomialModPow p f) :
    (∃ (h g : R) (s : Finset R) (a : R → ℕ), IsRegularSystemOfParameters s ∧ g ≠ 0 ∧
      f = h ^ p + g ^ p * ∏ x ∈ s, x ^ a x ∧ ∃ x ∈ s, ¬ p ∣ a x) ∨
    (∃ h g u : R, IsUnit u ∧ g ≠ 0 ∧ f = h ^ p + g ^ p * u ∧
      ∀ c : ResidueField R, c ^ p ≠ residue R u) := by
  obtain ⟨h, g, u, s, a, hs, hu, hg, hf, ⟨x₀, hx₀, ha⟩ | ⟨ha, hres⟩⟩ := hf
  · obtain ⟨g', s', a', hs', hg', hf', hx⟩ := exists_eq_add_prod_of_mem hp hs hu hg hf hx₀ ha
    exact Or.inl ⟨h, g', s', a', hs', hg', hf', hx⟩
  · have h1 : ∏ x ∈ s, x ^ a x = 1 := Finset.prod_eq_one fun x hx => by rw [ha x hx, pow_zero]
    rw [h1, mul_one] at hf
    exact Or.inr ⟨h, g, u, hu, hg, hf, hres⟩

/-- **A form with the unit `1` is monomial modulo `p`-th powers.** If `f = h ^ p + g ^ p * ∏ x ∈ s, x ^ a x` with `g ≠ 0`, a regular system of parameters `s` and some exponent `a x` with `x ∈ s` not divisible by `p`, then `IsMonomialModPow p f` holds with `u = 1`. -/
theorem isMonomialModPow_of_eq_add_prod {p : ℕ} {f h g : R} {s : Finset R} {a : R → ℕ}
    (hs : IsRegularSystemOfParameters s) (hg : g ≠ 0) (hf : f = h ^ p + g ^ p * ∏ x ∈ s, x ^ a x)
    (ha : ∃ x ∈ s, ¬ p ∣ a x) : IsMonomialModPow p f :=
  ⟨h, g, 1, s, a, hs, isUnit_one, hg, by rw [one_mul]; exact hf, Or.inl ha⟩

end MonomialModPow

end Singularity
