/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.InertiaField
import Singularity.Valuation.EtaleGenerator
import Singularity.Valuation.DegreePTowers
import Mathlib.FieldTheory.Minpoly.IsConjRoot

/-!
# Local uniformization from the base field to the decomposition field

Step 4 of the reduction of Cossart-Piltant (Volume 6, Proposition 2.2.1 of the handbook, [CP19, Proposition 4.10]) uses the ramification theory of valuations [ZS2, Chapter VI]. Let `L/K` be a finite Galois extension with group `G`, let `W` be a valuation subring of `L`, and let `A = W ∩ K`. The decomposition group `D` is the stabilizer of `W` in `G`, and the decomposition field `K^Z` is its fixed field. This file proves that local uniformization goes up from `A` to `W ∩ K^Z`. The file `Singularity.Valuation.InertiaField` proves the next part of Step 4, from `K^Z` to the inertia field.

The proof of [CP19] embeds `K^Z` in the henselization of `K`. The library does not have the henselization. This file constructs an étale generator of `K^Z/K` directly. The proof has these parts.

(a) `Singularity.exists_isIntegral_mul_eq_one`. Let `W'` be a valuation subring of `L` with `W' ∩ K = A`, and let `β ∈ W'`. Then there is an element `u` of `L` with `w'(u) = 1` such that `u` and `u β` are integral over `A`. This is the argument of Kronecker in Volume 5, Lemma 1.3.3 of the handbook.

(b) `Singularity.exists_isIntegral_sub_one_of_ne`. Let `W₁ ≠ W₂` be valuation subrings of `L` with `W₁ ∩ K = W₂ ∩ K = A`. Then there is an element `a` of `L` that is integral over `A`, with `w₁(a - 1) < 1` and `w₂(a) < 1`. Let `B` be the integral closure of `A` in `L`, and let `M_i` be the center of `W_i` on `B`. The ideals `M_i` are maximal, because `B` is integral over `A`. By (a), `W_i` is the localization of `B` at `M_i`, so `M₁ ≠ M₂`. Then `M₁ + M₂ = B`.

(c) `Singularity.exists_mem_fixedField_decompositionSubgroup`. There is an element `z` of `K^Z` that is integral over `A` with `w(z - 1) < 1` and `w(σ z) < 1` for each `σ ∉ D`. Let `y` be the product of the elements of (b) for the pairs `(W, τ W)` with `τ W ≠ W`, and let `z = ∏_{δ ∈ D} δ(y)`.

(d) `Singularity.isEtaleGenerator_decompositionField`. An element `z` as in (c) generates `K^Z` over `K`, the coefficients of its minimal polynomial `P` are in `A`, and `P'(z)` is a unit of `W`. The roots of `P` other than `z` are the conjugates `σ z` with `σ ∉ D`, and `P'(z) = ∏ (z - σ z)` with `w(z - σ z) = 1`.

(e) `Singularity.hasLocalUniformization_of_etaleGenerator_of_algebra` and `Singularity.hasLocalUniformization_of_etaleGenerator_of_intermediateField`: the lifting theorem `Singularity.hasLocalUniformization_of_etaleGenerator` for an extension that is given as an algebra or as an intermediate field of `L/K`.

(f) `Singularity.hasLocalUniformization_decompositionField`. If `W ∩ K` has local uniformization over `k`, then `W ∩ K^Z` has local uniformization over `k`. `Singularity.hasLocalUniformization_inertiaField_of_base` combines this with `Singularity.hasLocalUniformization_inertiaField_decompositionField`: local uniformization goes up from `W ∩ K` to `W ∩ K^T`, where `K^T` is the inertia field of `W` over `K^Z`.

The proof does not use that `G` acts transitively on the extensions of `A` to `L`, and it does not use the henselization.

## What is not proved

The results of this file are unconditional. They do not complete Step 4. The tame part from the inertia field to the ramification field, the passage down from `K^r` to `K`, Steps 1 and 2 of the reduction, and the Galois steps of degree `p` are not in this file.

## References

* [CP19] V. Cossart and O. Piltant, *Resolution of singularities of arithmetical threefolds*, J. Algebra 529 (2019).
* [ZS2] O. Zariski and P. Samuel, *Commutative Algebra*, Volume II.
-/

open IntermediateField IsLocalRing Polynomial
open scoped Pointwise

namespace Singularity

section Values

variable {K L : Type*} [Field K] [Field L]

/-- An element `x` has value less than `1` for `W` if and only if `x = 0` or `x⁻¹ ∉ W`. -/
theorem valuation_lt_one_iff_eq_zero_or_inv_notMem (W : ValuationSubring L) (x : L) :
    W.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ W := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]

/-- The valuation of the inverse image `W.comap f` takes a value less than `1` at `x` if and only if the valuation of `W` takes a value less than `1` at `f x`. -/
theorem valuation_comap_lt_one_iff (W : ValuationSubring L) (f : K →+* L) (x : K) :
    (W.comap f).valuation x < 1 ↔ W.valuation (f x) < 1 := by
  rw [valuation_lt_one_iff_eq_zero_or_inv_notMem, valuation_lt_one_iff_eq_zero_or_inv_notMem,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff f f.injective]

/-- A product of elements `f i` with `w(f i - 1) < 1` has the same property. -/
theorem valuation_prod_sub_one_lt_one {ι : Type*} (W : ValuationSubring L) (s : Finset ι)
    (f : ι → L) (hf : ∀ i ∈ s, W.valuation (f i - 1) < 1) :
    W.valuation (∏ i ∈ s, f i - 1) < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfa : W.valuation (f a) ≤ 1 := by
      have : f a = (f a - 1) + 1 := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le h1.le (by simp))
    have : f a * ∏ i ∈ s, f i - 1 = f a * (∏ i ∈ s, f i - 1) + (f a - 1) := by ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ h1)
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hfa) h2

variable [Algebra K L]

/-- The inverse image of `σ⁻¹ W` in `L`: `x ∈ σ⁻¹ W` has value less than `1` if and only if `σ x` has value less than `1` for `W`. -/
theorem valuation_inv_smul_lt_one_iff (σ : L ≃ₐ[K] L) (W : ValuationSubring L) (x : L) :
    (σ⁻¹ • W).valuation x < 1 ↔ W.valuation (σ x) < 1 := by
  rw [valuation_lt_one_iff_eq_zero_or_inv_notMem, valuation_lt_one_iff_eq_zero_or_inv_notMem,
    ValuationSubring.mem_inv_pointwise_smul_iff, AlgEquiv.smul_def, map_inv₀,
    map_eq_zero_iff σ σ.injective]

/-- A `K`-automorphism `σ` does not change the intersection with `K`: `σ W ∩ K = W ∩ K`. -/
theorem comap_pointwise_smul (σ : L ≃ₐ[K] L) (W : ValuationSubring L) :
    (σ • W).comap (algebraMap K L) = W.comap (algebraMap K L) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.commutes]

/-- An element `δ` of the decomposition group maps `W` onto `W`. -/
theorem apply_mem_iff_of_mem_decompositionSubgroup {W : ValuationSubring L} {δ : L ≃ₐ[K] L}
    (hδ : δ ∈ W.decompositionSubgroup K) (x : L) : δ x ∈ W ↔ x ∈ W := by
  have h : δ⁻¹ • W = W := MulAction.mem_stabilizer_iff.1 (inv_mem hδ)
  have := ValuationSubring.mem_inv_pointwise_smul_iff (g := δ) (S := W) (x := x)
  rw [h] at this
  exact this.symm

end Values

section Integral

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {A : ValuationSubring K} [Algebra A L]
  [IsScalarTower A K L]

/-- An element of `L` that is integral over `A` lies in each valuation subring `W'` of `L` with `W' ∩ K = A`, because `W'` is integrally closed. -/
theorem mem_of_isIntegral {W : ValuationSubring L} (hW : W.comap (algebraMap K L) = A) {x : L}
    (hx : IsIntegral A x) : x ∈ W := by
  have hAW : ∀ a : A, algebraMap A L a ∈ W := fun a => by
    rw [IsScalarTower.algebraMap_apply A K L, ← ValuationSubring.mem_comap, hW]
    exact a.2
  let φ : A →+* W := (algebraMap A L).codRestrict W hAW
  have hφ : (algebraMap W L).comp φ = (RingHom.id L).comp (algebraMap A L) := by
    ext a
    rfl
  have hxW : IsIntegral W x := IsIntegral.map_of_comp_eq φ (RingHom.id L) hφ hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxW
  rw [← hy]
  exact y.2

theorem mem_maximalIdeal_iff_of_comap_eq {W : ValuationSubring L}
    (hW : W.comap (algebraMap K L) = A) (a : A) :
    a ∈ maximalIdeal A ↔ W.valuation (algebraMap K L a) < 1 := by
  subst hW
  rw [ValuationSubring.valuation_lt_one_iff, valuation_comap_lt_one_iff]

variable [FiniteDimensional K L]

/-- **Kronecker** (Volume 5, Lemma 1.3.3 of the handbook, first part). Let `W'` be a valuation subring of `L` with `W' ∩ K = A`, and let `β ∈ W'`. Then there is an element `u` of `L` with `w'(u) = 1` such that `u` and `u β` are integral over `A`. Divide the minimal polynomial of `β` by a coefficient of largest value, and let `j` be the largest index with a coefficient of value `1`. The element `u = ∑_{i ≥ j} b_i β^(i - j)` has these properties. -/
theorem exists_isIntegral_mul_eq_one {W : ValuationSubring L}
    (hW : W.comap (algebraMap K L) = A) {x : L} (hx : x ∈ W) :
    ∃ u : L, IsIntegral A u ∧ IsIntegral A (u * x) ∧ W.valuation u = 1 := by
  classical
  have hA : ∀ c : K, c ∈ A ↔ algebraMap K L c ∈ W := fun c => by
    rw [← hW]
    rfl
  have hxi : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  set f := minpoly K x with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero hxi
  obtain ⟨t, ht, htmax⟩ := Finset.exists_max_image f.support
    (fun i => W.valuation (algebraMap K L (f.coeff i))) (support_nonempty.mpr hf0)
  set a := f.coeff t
  have ha0 : a ≠ 0 := mem_support_iff.mp ht
  have ha0' : algebraMap K L a ≠ 0 := (_root_.map_ne_zero _).2 ha0
  have hva : ∀ i, W.valuation (algebraMap K L (f.coeff i)) ≤ W.valuation (algebraMap K L a) := by
    intro i
    by_cases hi : i ∈ f.support
    · exact htmax i hi
    · rw [notMem_support_iff.mp hi]
      simp
  set g := C a⁻¹ * f with hg
  have hgc : ∀ i, algebraMap K L (g.coeff i) =
      (algebraMap K L a)⁻¹ * algebraMap K L (f.coeff i) := by
    intro i
    rw [hg, coeff_C_mul, map_mul, map_inv₀]
  have hvg : ∀ i, W.valuation (algebraMap K L (g.coeff i)) ≤ 1 := by
    intro i
    rw [hgc, map_mul]
    calc W.valuation (algebraMap K L a)⁻¹ * W.valuation (algebraMap K L (f.coeff i))
        ≤ W.valuation (algebraMap K L a)⁻¹ * W.valuation (algebraMap K L a) := by
          gcongr
          exact hva i
      _ = 1 := by rw [← map_mul, inv_mul_cancel₀ ha0', map_one]
  have hgt : W.valuation (algebraMap K L (g.coeff t)) = 1 := by
    rw [hgc, inv_mul_cancel₀ ha0', map_one]
  set J := g.support.filter (fun i => W.valuation (algebraMap K L (g.coeff i)) = 1) with hJ
  have htJ : t ∈ J := by
    refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, hgt⟩
    rw [h0] at hgt
    simp at hgt
  set j := J.max' ⟨t, htJ⟩
  have hj1 : W.valuation (algebraMap K L (g.coeff j)) = 1 :=
    (Finset.mem_filter.mp (J.max'_mem _)).2
  have hjgt : ∀ i, j < i → W.valuation (algebraMap K L (g.coeff i)) < 1 := by
    intro i hi
    refine lt_of_le_of_ne (hvg i) fun h1 => ?_
    have hiJ : i ∈ J := by
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, h1⟩
      rw [h0] at h1
      simp at h1
    exact absurd (J.le_max' i hiJ) (not_le.mpr hi)
  -- The polynomial `g` over `A`.
  obtain ⟨G, hG⟩ := (mem_lifts g).mp ((lifts_iff_coeff_lifts (f := algebraMap A K) g).mpr
    fun n => ⟨⟨_, (hA _).mpr ((W.valuation_le_one_iff _).mp (hvg n))⟩, rfl⟩)
  have hGc : ∀ i, algebraMap A L (G.coeff i) = algebraMap K L (g.coeff i) := by
    intro i
    rw [← hG, coeff_map, IsScalarTower.algebraMap_apply A K L]
  have hGx : aeval x G = 0 := by
    rw [← aeval_map_algebraMap K, hG, hg, map_mul, hf, minpoly.aeval, mul_zero]
  -- The value of `u = e_j` is `1`.
  have hej : W.valuation (aeval x (divX^[j] G)) = 1 := by
    have hsmall : W.valuation (aeval x (divX^[j + 1] G) * x) <
        W.valuation (algebraMap A L (G.coeff j)) := by
      rw [hGc, hj1, map_mul]
      refine lt_of_le_of_lt (mul_le_of_le_one_right' ((W.valuation_le_one_iff x).mpr hx)) ?_
      exact valuation_aeval_divX_iterate_lt_one W G hx (j + 1) fun i hi => by
        rw [hGc]
        exact hjgt i (by omega)
    rw [aeval_divX_iterate_succ G x j, Valuation.map_add_eq_of_lt_right _ hsmall, hGc, hj1]
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, Function.iterate_zero_apply, hGx, map_zero] at hej
    exact zero_ne_one hej
  refine ⟨aeval x (divX^[j] G), isIntegral_aeval_divX_iterate hGx j, ?_, hej⟩
  have h1 := aeval_divX_iterate_succ G x (j - 1)
  rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)] at h1
  have h2 : aeval x (divX^[j] G) * x =
      aeval x (divX^[j - 1] G) - algebraMap A L (G.coeff (j - 1)) := by
    rw [h1]
    ring
  rw [h2]
  exact (isIntegral_aeval_divX_iterate hGx (j - 1)).sub isIntegral_algebraMap

/-- **Separation of two extensions.** Let `W₁ ≠ W₂` be valuation subrings of `L` with `W₁ ∩ K = W₂ ∩ K = A`. Then there is an element `a` of `L` that is integral over `A`, with `w₁(a - 1) < 1` and `w₂(a) < 1`.

Let `B` be the integral closure of `A` in `L`, and let `M_i ⊆ B` be the center of `W_i`. The ideal `M_i` is maximal, because `B` is integral over `A` and `M_i ∩ A` is the maximal ideal of `A`. If `M₁ = M₂`, then `W₁ = W₂` by `Singularity.exists_isIntegral_mul_eq_one`: each element `β` of `W_i` is the quotient of `u β ∈ B` by an element `u ∈ B \ M_i`. So there is `c ∈ M₁ \ M₂`, and `d c + a = 1` for some `d ∈ B` and `a ∈ M₂`. -/
theorem exists_isIntegral_sub_one_of_ne {W₁ W₂ : ValuationSubring L}
    (h₁ : W₁.comap (algebraMap K L) = A) (h₂ : W₂.comap (algebraMap K L) = A) (hne : W₁ ≠ W₂) :
    ∃ a : L, IsIntegral A a ∧ W₁.valuation (a - 1) < 1 ∧ W₂.valuation a < 1 := by
  classical
  set B := integralClosure A L
  have hBW : ∀ {V : ValuationSubring L}, V.comap (algebraMap K L) = A → ∀ b : B, (b : L) ∈ V :=
    fun hV b => mem_of_isIntegral hV b.2
  let φ : ∀ V : ValuationSubring L, V.comap (algebraMap K L) = A → B →+* V := fun V hV =>
    (B.val : B →+* L).codRestrict V (hBW hV)
  let M : ∀ V : ValuationSubring L, V.comap (algebraMap K L) = A → Ideal B := fun V hV =>
    (maximalIdeal V).comap (φ V hV)
  have hM : ∀ V hV (b : B), b ∈ M V hV ↔ V.valuation (b : L) < 1 := fun V hV b =>
    (ValuationSubring.valuation_lt_one_iff V (φ V hV b)).trans Iff.rfl
  have hMmax : ∀ V hV, (M V hV).IsMaximal := by
    intro V hV
    have : (M V hV).IsPrime := Ideal.comap_isPrime _ _
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) (M V hV) ?_
    have : (M V hV).under A = maximalIdeal A := by
      ext a
      rw [Ideal.under, Ideal.mem_comap, hM V hV, mem_maximalIdeal_iff_of_comap_eq hV]
      have e : ((algebraMap A B a : B) : L) = algebraMap K L (a : K) := by
        exact IsScalarTower.algebraMap_apply A K L a
      rw [e]
    rw [this]
    exact maximalIdeal.isMaximal A
  -- If the centers are equal, then the valuation rings are equal.
  have key : ∀ (V V' : ValuationSubring L) (hV : V.comap (algebraMap K L) = A)
      (hV' : V'.comap (algebraMap K L) = A), M V hV = M V' hV' → V ≤ V' := by
    intro V V' hV hV' hMM x hx
    obtain ⟨u, hu, hux, hu1⟩ := exists_isIntegral_mul_eq_one hV hx
    have hu' : ¬ V'.valuation u < 1 := by
      intro hlt
      have : (⟨u, hu⟩ : B) ∈ M V' hV' := (hM V' hV' _).2 hlt
      rw [← hMM, hM V hV] at this
      exact lt_irrefl _ (hu1 ▸ this)
    have hu'' : V'.valuation u = 1 :=
      le_antisymm ((V'.valuation_le_one_iff _).2 (mem_of_isIntegral hV' hu)) (not_lt.1 hu')
    have hux' : V'.valuation (u * x) ≤ 1 :=
      (V'.valuation_le_one_iff _).2 (mem_of_isIntegral hV' hux)
    rw [map_mul, hu'', one_mul] at hux'
    exact (V'.valuation_le_one_iff _).1 hux'
  have hle : ¬ M W₁ h₁ ≤ M W₂ h₂ := by
    intro hle
    have heq := (hMmax W₁ h₁).eq_of_le (hMmax W₂ h₂).ne_top hle
    exact hne (le_antisymm (key _ _ h₁ h₂ heq) (key _ _ h₂ h₁ heq.symm))
  obtain ⟨c, hc₁, hc₂⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  obtain ⟨d, i, hi, hdi⟩ := (hMmax W₂ h₂).exists_inv hc₂
  refine ⟨i, i.2, ?_, (hM W₂ h₂ i).1 hi⟩
  have hdi' : (d : L) * c + i = 1 := by
    have := congrArg (fun b : B => (b : L)) hdi
    simpa using this
  have hsub : (i : L) - 1 = -((d : L) * c) := by
    linear_combination hdi'
  rw [hsub, Valuation.map_neg, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((W₁.valuation_le_one_iff _).2 (hBW h₁ d)))
    ((hM W₁ h₁ c).1 hc₁)

end Integral

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **An element of the decomposition field that separates the conjugates of `W`.** Let `L/K` be a finite Galois extension, let `W` be a valuation subring of `L`, and let `D` be the decomposition group of `W`. There is an element `z` of the fixed field of `D` such that the coefficients of the minimal polynomial of `z` over `K` lie in `W`, `w(z - 1) < 1`, and `w(σ z) < 1` for each `σ ∉ D`.

Let `A = W ∩ K`. For each `τ` with `τ W ≠ W`, `Singularity.exists_isIntegral_sub_one_of_ne` gives an element `a_τ` that is integral over `A` with `w(a_τ - 1) < 1` and `a_τ` of value less than `1` for `τ W`. Let `y` be the product of the `a_τ`, and let `z = ∏_{δ ∈ D} δ(y)`. Then `z` is fixed by `D` and integral over `A`, so the coefficients of its minimal polynomial are in `A`. For `σ ∉ D`, the factor `y` of `z` has value less than `1` for `σ⁻¹ W`, so `w(σ z) < 1`. -/
theorem exists_mem_fixedField_decompositionSubgroup (W : ValuationSubring L) :
    ∃ z : L, z ∈ fixedField (W.decompositionSubgroup K) ∧
      (∀ i, algebraMap K L ((minpoly K z).coeff i) ∈ W) ∧ W.valuation (z - 1) < 1 ∧
      ∀ σ : L ≃ₐ[K] L, σ ∉ W.decompositionSubgroup K → W.valuation (σ z) < 1 := by
  classical
  set D := W.decompositionSubgroup K with hD
  set A := W.comap (algebraMap K L) with hA
  letI : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcomap : ∀ σ : L ≃ₐ[K] L, (σ • W).comap (algebraMap K L) = A := fun σ =>
    comap_pointwise_smul σ W
  -- The element `y`.
  have ha : ∀ σ : L ≃ₐ[K] L, ∃ a : L, IsIntegral A a ∧ W.valuation (a - 1) < 1 ∧
      (σ • W ≠ W → (σ • W).valuation a < 1) := by
    intro σ
    by_cases hσ : σ • W = W
    · exact ⟨1, isIntegral_one, by simp, fun h => absurd hσ h⟩
    · obtain ⟨a, ha, ha1, ha2⟩ := exists_isIntegral_sub_one_of_ne rfl (hcomap σ) (Ne.symm hσ)
      exact ⟨a, ha, ha1, fun _ => ha2⟩
  choose a ha ha1 ha2 using ha
  set y := ∏ σ, a σ with hy
  have hyi : IsIntegral A y := IsIntegral.prod _ fun σ _ => ha σ
  have hy1 : W.valuation (y - 1) < 1 := valuation_prod_sub_one_lt_one W _ _ fun σ _ => ha1 σ
  have hy2 : ∀ σ : L ≃ₐ[K] L, σ • W ≠ W → (σ • W).valuation y < 1 := by
    intro σ hσ
    rw [hy, ← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ σ), map_mul]
    have hrest : ∏ τ ∈ Finset.univ.erase σ, a τ ∈ σ • W :=
      prod_mem fun τ _ => mem_of_isIntegral (hcomap σ) (ha τ)
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (((σ • W).valuation_le_one_iff _).2 hrest))
      (ha2 σ hσ)
  -- The element `z`.
  have hδi : ∀ δ : L ≃ₐ[K] L, IsIntegral A (δ y) := fun δ =>
    hyi.map ((δ : L →ₐ[K] L).restrictScalars A)
  set z := ∏ δ : D, (δ : L ≃ₐ[K] L) y with hz
  have hzD : z ∈ fixedField D := by
    rw [mem_fixedField_iff]
    intro σ hσ
    rw [hz, map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft ⟨σ, hσ⟩) _ _ fun _ => rfl
  have hzi : IsIntegral A z := IsIntegral.prod _ fun δ _ => hδi δ
  refine ⟨z, hzD, fun i => ?_, ?_, fun σ hσ => ?_⟩
  · rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hzi, coeff_map]
    exact ((minpoly A z).coeff i).2
  · refine valuation_prod_sub_one_lt_one W _ _ fun δ _ => ?_
    have h := (valuation_apply_lt_one_iff K (apply_mem_iff_of_mem_decompositionSubgroup δ.2)
      (y - 1)).2 hy1
    rwa [map_sub, map_one] at h
  · have hσ' : σ⁻¹ • W ≠ W := fun h => hσ (by
      have : σ⁻¹ ∈ D := MulAction.mem_stabilizer_iff.2 h
      simpa using inv_mem this)
    rw [← valuation_inv_smul_lt_one_iff, hz,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : D)), map_mul]
    have hrest : ∏ δ ∈ Finset.univ.erase (1 : D), (δ : L ≃ₐ[K] L) y ∈ σ⁻¹ • W :=
      prod_mem fun δ _ => mem_of_isIntegral (hcomap σ⁻¹) (hδi δ)
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (((σ⁻¹ • W).valuation_le_one_iff _).2 hrest))
      (hy2 σ⁻¹ hσ')

/-- **An étale generator of the decomposition field.** Let `L/K` be a finite Galois extension, let `W` be a valuation subring of `L`, and let `D` be the decomposition group of `W`. Let `z` be an element of the fixed field `K^Z` of `D` such that the coefficients of the minimal polynomial `P` of `z` over `K` lie in `W`, `w(z - 1) < 1`, and `w(σ z) < 1` for each `σ ∉ D`. Then `z ∈ W`, `K(z) = K^Z`, and `P'(z)` is a unit of `W`.

An automorphism `σ ∉ D` does not fix `z`, because `w(σ z) < 1 = w(z)`. So the fixing group of `K(z)` is `D`, and `K(z) = K^Z`. The roots of `P` other than `z` are the conjugates `σ z` with `σ ∉ D`, and `P'(z)` is the product of the elements `z - σ z`, which have value `1`. -/
theorem isEtaleGenerator_decompositionField {W : ValuationSubring L} {z : L}
    (hzD : z ∈ fixedField (W.decompositionSubgroup K))
    (hz1 : W.valuation (z - 1) < 1)
    (hzσ : ∀ σ : L ≃ₐ[K] L, σ ∉ W.decompositionSubgroup K → W.valuation (σ z) < 1) :
    z ∈ W ∧ K⟮z⟯ = fixedField (W.decompositionSubgroup K) ∧
      W.valuation (aeval z (derivative (minpoly K z))) = 1 := by
  classical
  set D := W.decompositionSubgroup K with hD
  have hzv : W.valuation z = 1 := by
    have : z = (z - 1) + 1 := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]
  have hne : ∀ σ : L ≃ₐ[K] L, σ ∉ D → σ z ≠ z := fun σ hσ h => by
    have := hzσ σ hσ
    rw [h, hzv] at this
    exact lt_irrefl _ this
  have hdiff : ∀ σ : L ≃ₐ[K] L, σ ∉ D → W.valuation (z - σ z) = 1 := by
    intro σ hσ
    have hsmall : W.valuation (z - 1 - σ z) < W.valuation (1 : L) := by
      rw [map_one]
      exact (Valuation.map_sub _ _ _).trans_lt (max_lt hz1 (hzσ σ hσ))
    have : z - σ z = (z - 1 - σ z) + 1 := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ hsmall, map_one]
  refine ⟨(W.valuation_le_one_iff z).1 hzv.le, ?_, ?_⟩
  · refine le_antisymm (adjoin_simple_le_iff.2 hzD) ?_
    rw [← IsGalois.fixedField_fixingSubgroup K⟮z⟯]
    refine IntermediateField.fixedField_le fun σ hσ => ?_
    by_contra hσD
    exact hne σ hσD (hσ ⟨z, mem_adjoin_simple_self K z⟩)
  · have hzint : IsIntegral K z := Algebra.IsIntegral.isIntegral z
    set Q := (minpoly K z).map (algebraMap K L) with hQ
    have hQs : Q.Splits := Normal.splits inferInstance z
    have hQm : Q.Monic := (minpoly.monic hzint).map _
    have hQ0 : Q ≠ 0 := hQm.ne_zero
    have hzQ : z ∈ Q.roots := by
      rw [mem_roots hQ0, IsRoot, hQ, eval_map_algebraMap, minpoly.aeval]
    have hnd : Q.roots.Nodup :=
      (nodup_aroots_iff_of_splits (minpoly.ne_zero hzint) hQs).2
        (Algebra.IsSeparable.isSeparable K z)
    have hder : aeval z (derivative (minpoly K z)) = eval z (derivative Q) := by
      rw [hQ, derivative_map, eval_map_algebraMap]
    rw [hder, hQs.eval_root_derivative hQm hzQ, map_multiset_prod, Multiset.map_map]
    refine Multiset.prod_eq_one fun x hx => ?_
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨hbz, hbQ⟩ := hnd.mem_erase_iff.1 hb
    have hb0 : aeval b (minpoly K z) = 0 := by
      rw [mem_roots hQ0, IsRoot, hQ, eval_map_algebraMap] at hbQ
      exact hbQ
    obtain ⟨σ, hσ⟩ := (isConjRoot_of_aeval_eq_zero hzint hb0).symm.exists_algEquiv
    have hσD : σ ∉ D := fun h => hbz (by rw [← hσ]; exact (mem_fixedField_iff _ _).1 hzD σ h)
    rw [Function.comp_apply, ← hσ]
    exact hdiff σ hσD

end Galois

section Lift

variable {k E E' : Type*} [Field k] [Field E] [Field E'] [Algebra k E] [Algebra k E']
  [Algebra E E'] [IsScalarTower k E E']

/-- **Lifting along an étale generator, for an algebra `E'/E`.** This is `Singularity.hasLocalUniformization_of_etaleGenerator` for an extension `E'/E` that is given as an algebra, not as an intermediate field. Let `V` be a valuation subring of `E'`, and let `z ∈ V` with `E' = E(z)`, such that the coefficients of the minimal polynomial `P` of `z` over `E` lie in `V` and `P'(z)` is a unit of `V`. If `V ∩ E` has local uniformization over `k`, then `V` has local uniformization over `k`.

The image `K₀` of `E` in `E'` is an intermediate field of `E'/k`, and `E ≃ K₀` over `k`. This isomorphism carries the minimal polynomial of `z` over `E` to the minimal polynomial of `z` over `K₀`. -/
theorem hasLocalUniformization_of_etaleGenerator_of_algebra {V : ValuationSubring E'} {z : E'}
    (hz : z ∈ V) (hadj : IntermediateField.adjoin E {z} = ⊤)
    (hc : ∀ i, algebraMap E E' ((minpoly E z).coeff i) ∈ V)
    (hd : V.valuation (aeval z (derivative (minpoly E z))) = 1)
    (h : HasLocalUniformization k (V.comap (algebraMap E E'))) :
    HasLocalUniformization k V := by
  have hzi : IsIntegral E z := by
    by_contra hni
    rw [minpoly.eq_zero hni, derivative_zero, map_zero, map_zero] at hd
    exact zero_ne_one hd
  have hadjA : Algebra.adjoin E {z} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hzi.isAlgebraic, hadj,
      IntermediateField.top_toSubalgebra]
  have : FiniteDimensional E E' :=
    ⟨by rw [← Algebra.top_toSubmodule, ← hadjA]; exact hzi.fg_adjoin_singleton⟩
  let K₀ : IntermediateField k E' := (IsScalarTower.toAlgHom k E E').fieldRange
  let e : E ≃ₐ[k] K₀ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E E')
  have hEK : (algebraMap K₀ E').comp (e.toRingEquiv : E →+* K₀) = algebraMap E E' :=
    RingHom.ext fun _ => rfl
  have hmin : (minpoly E z).map (e.toRingEquiv : E →+* K₀) = minpoly K₀ z :=
    minpoly.map_eq_of_equiv_equiv (g := RingEquiv.refl E') (RingHom.ext fun _ => rfl) z
  have haeval : ∀ p : E[X], aeval z (p.map (e.toRingEquiv : E →+* K₀)) = aeval z p := by
    intro p
    rw [aeval_def, aeval_def, eval₂_map, hEK]
  have hgen : IsEtaleGenerator K₀ V z := by
    refine ⟨hz, ?_, fun i => ?_, ?_⟩
    · rw [eq_top_iff]
      intro x _
      have hx : x ∈ Algebra.adjoin E {z} := hadjA ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
      obtain ⟨p, rfl⟩ := hx
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← haeval]
      exact IntermediateField.algebra_adjoin_le_adjoin K₀ {z} (aeval_mem_adjoin_singleton K₀ z)
    · rw [← hmin, coeff_map]
      exact hc i
    · rw [← hmin, derivative_map, haeval]
      exact hd
  refine hasLocalUniformization_of_etaleGenerator hgen (HasLocalUniformization.of_algEquiv e ?_)
  have hcomap : (V.comap (algebraMap K₀ E')).comap (e : E →+* K₀) = V.comap (algebraMap E E') := by
    ext a
    rfl
  rwa [hcomap]

attribute [local instance] isScalarTower_intermediateField

/-- **Lifting along an étale generator, for an intermediate field.** Let `L/K` be an extension of extensions of `k`, let `F` be an intermediate field of `L/K`, and let `W` be a valuation subring of `L`. Let `z ∈ W` with `K(z) = F`, such that the coefficients of the minimal polynomial `P` of `z` over `K` lie in `W` and `P'(z)` is a unit of `W`. If `W ∩ K` has local uniformization over `k`, then `W ∩ F` has local uniformization over `k`. -/
theorem hasLocalUniformization_of_etaleGenerator_of_intermediateField {K L : Type*} [Field K]
    [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    {F : IntermediateField K L} {W : ValuationSubring L} {z : L} (hz : z ∈ W) (hzF : K⟮z⟯ = F)
    (hc : ∀ i, algebraMap K L ((minpoly K z).coeff i) ∈ W)
    (hd : W.valuation (aeval z (derivative (minpoly K z))) = 1)
    (h : HasLocalUniformization k (W.comap (algebraMap K L))) :
    HasLocalUniformization k (W.comap (algebraMap F L)) := by
  have hzmem : z ∈ F := hzF ▸ mem_adjoin_simple_self K z
  set z' : F := ⟨z, hzmem⟩
  have hmin : minpoly K z' = minpoly K z := IntermediateField.minpoly_eq z'
  refine hasLocalUniformization_of_etaleGenerator_of_algebra (E := K) (z := z') hz ?_ (fun i => ?_)
    ?_ ?_
  · apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    exact hzF
  · rw [hmin, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hc i
  · rw [hmin, valuation_comap_eq_one_iff, ← aeval_algebraMap_apply]
    exact hd
  · have hcomap : (W.comap (algebraMap F L)).comap (algebraMap K F) = W.comap (algebraMap K L) := by
      ext a
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ValuationSubring.mem_comap,
        ← IsScalarTower.algebraMap_apply]
    rwa [hcomap]

end Lift

section Uniformization

attribute [local instance] isScalarTower_intermediateField

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Local uniformization goes up to the decomposition field** (part of Step 4 of the reduction of Cossart-Piltant, Volume 6, Proposition 2.2.1 of the handbook). Let `L/K` be a finite Galois extension of extensions of `k`, let `W` be a valuation subring of `L`, and let `K^Z` be the decomposition field of `W`, the fixed field of the stabilizer of `W` in `Gal(L/K)`. If `W ∩ K` has local uniformization over `k`, then `W ∩ K^Z` has local uniformization over `k`.

By `Singularity.exists_mem_fixedField_decompositionSubgroup` and `Singularity.isEtaleGenerator_decompositionField`, there is an étale generator of `K^Z/K` at `W ∩ K^Z`, and local uniformization lifts along it. -/
theorem hasLocalUniformization_decompositionField (W : ValuationSubring L)
    (h : HasLocalUniformization k (W.comap (algebraMap K L))) :
    HasLocalUniformization k
      (W.comap (algebraMap (fixedField (W.decompositionSubgroup K)) L)) := by
  obtain ⟨z, hzD, hc, hz1, hzσ⟩ := exists_mem_fixedField_decompositionSubgroup (K := K) W
  obtain ⟨hz, hzF, hd⟩ := isEtaleGenerator_decompositionField hzD hz1 hzσ
  exact hasLocalUniformization_of_etaleGenerator_of_intermediateField hz hzF hc hd h

/-- **Local uniformization goes up from the base field to the inertia field** (part of Step 4 of the reduction of Cossart-Piltant, Volume 6, Proposition 2.2.1 of the handbook). Let `L/K` be a finite Galois extension of extensions of `k`, let `W` be a valuation subring of `L`, let `K^Z` be the decomposition field of `W`, and let `K^T` be the inertia field of `W` over `K^Z`. If `W ∩ K` has local uniformization over `k`, then `W ∩ K^T` has local uniformization over `k`. This combines `Singularity.hasLocalUniformization_decompositionField` with `Singularity.hasLocalUniformization_inertiaField_decompositionField`. -/
theorem hasLocalUniformization_inertiaField_of_base (W : ValuationSubring L)
    (h : HasLocalUniformization k (W.comap (algebraMap K L))) :
    HasLocalUniformization k
      (W.comap (algebraMap (inertiaField (fixedField (W.decompositionSubgroup K)) W) L)) :=
  hasLocalUniformization_inertiaField_decompositionField W
    (hasLocalUniformization_decompositionField W h)

end Uniformization

end Singularity
