/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.EtaleGenerator
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Existence of an étale generator when the residue degree is the degree

Let `K₀ ⊆ K` be fields with `[K : K₀] = n` finite, let `v` be a valuation of `K`, and let `v₀` be a valuation of `K₀` that `v` extends. This file proves the existence of an étale generator of `K/K₀` at `v` in one case of the second part of Lemma 1.3.3 of Volume 5 of the handbook (node SG0000004Y). The case is the case where the residue extension `Kv/K₀v₀` is separable of degree `f = n`.

By the fundamental inequality `e f g ≤ n`, the condition `f = n` forces `e = 1`, `g = 1` and `d = 1`: the valuation `v` is the only extension of `v₀` to `K`, the value groups are equal, and the extension is defectless. So this is the case of one extension in Lemma 1.3.3. The proof needs neither the henselization nor these consequences. The general case, with `g` extensions of `v₀`, is not in this file.

## The proof

1. Choose a primitive element `θ` of the residue extension. Its minimal polynomial `μ` over `K₀v₀` has degree `n` and is separable. Choose `z` in the valuation ring of `v` with residue `θ`.
2. Let `p ∈ K₀[X]` be nonzero of degree `< n`, and let `c` be a coefficient of `p` of largest value. Then `c⁻¹ p` has coefficients in the valuation ring of `v₀`, and its reduction is a nonzero polynomial of degree `< n`. So the reduction does not vanish at `θ`, and `v(p(z)) = v(c)` (`Singularity.exists_valuation_aeval_eq_of_natDegree_lt`). In particular `p(z) ≠ 0`.
3. Thus the minimal polynomial `P` of `z` over `K₀` has degree `n`, and `K = K₀(z)`. Write `P = X^n + r` with `deg r < n`. By step 2, the largest value of a coefficient of `r` is `v(r(z)) = v(z^n) ≤ 1`. So `P` has coefficients in the valuation ring of `v₀`.
4. The reduction of `P` is monic of degree `n` and vanishes at `θ`, so it is `μ`. The residue of `P'(z)` is `μ'(θ) ≠ 0`, because `μ` is separable. So `v(P'(z)) = 1`.

## Main results

* `Singularity.exists_valuation_aeval_eq_of_natDegree_lt`: step 2.
* `Singularity.exists_isEtaleGenerator_of_finrank_residueField_eq`: if `Kv/K₀v₀` is separable of degree `[K : K₀]`, then `K/K₀` is separable and there is an étale generator of `K/K₀` at `v` (Lemma 1.3.3, second part, in the case of one extension).
-/

open Polynomial IsLocalRing

namespace Singularity

section Reduction

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ₀ Γ₁ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  (vK : Valuation K Γ₀) (vL : Valuation L Γ₁) [vK.HasExtension vL]

/-- The residue of `p(z)` is the value at the residue of `z` of the reduction of `p`. -/
theorem residue_aeval_eq_aeval_map_residue (z : vL.valuationSubring)
    (p : vK.valuationSubring[X]) :
    residue vL.valuationSubring (aeval z p) =
      aeval (residue vL.valuationSubring z) (p.map (residue vK.valuationSubring)) := by
  rw [← ResidueField.algebraMap_eq, ← ResidueField.algebraMap_eq, aeval_map_algebraMap,
    aeval_algebraMap_apply]

/-- An element of the valuation ring of `vL` with a nonzero residue has value 1. -/
theorem valuation_eq_one_of_residue_ne_zero {x : vL.valuationSubring}
    (hx : residue vL.valuationSubring x ≠ 0) : vL (x : L) = 1 := by
  have hu : IsUnit x := by
    by_contra h
    exact hx ((residue_eq_zero_iff x).mpr h)
  exact (Valuation.integer.integers vL).one_of_isUnit hu

theorem coe_aeval_valuationSubring (z : vL.valuationSubring) (p : vK.valuationSubring[X]) :
    ((aeval z p : vL.valuationSubring) : L) =
      aeval (z : L) (p.map (algebraMap vK.valuationSubring K)) := by
  rw [aeval_map_algebraMap]
  exact (aeval_algebraMap_apply L z p).symm

/-- **Step 2.** Let `z` be in the valuation ring of `vL`, and let the minimal polynomial of the residue of `z` over the residue field of `vK` have degree `> deg p`, where `p ∈ K[X]` is nonzero. Then there is a nonzero coefficient `c` of `p` of largest value, and `vL(p(z)) = vL(c)`. -/
theorem exists_valuation_aeval_eq_of_natDegree_lt (z : vL.valuationSubring) {p : K[X]}
    (hp : p ≠ 0) (hdeg : p.natDegree <
      (minpoly (ResidueField vK.valuationSubring) (residue vL.valuationSubring z)).natDegree) :
    ∃ i, p.coeff i ≠ 0 ∧ (∀ j, vK (p.coeff j) ≤ vK (p.coeff i)) ∧
      vL (aeval (z : L) p) = vL (algebraMap K L (p.coeff i)) := by
  classical
  have hne : p.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hp)
  obtain ⟨i, hi, hmax⟩ := p.support.exists_max_image (fun j => vK (p.coeff j)) hne
  set c := p.coeff i with hc_def
  have hc : c ≠ 0 := mem_support_iff.mp hi
  have hvc : vK c ≠ 0 := (Valuation.ne_zero_iff vK).mpr hc
  have hmax' : ∀ j, vK (p.coeff j) ≤ vK c := by
    intro j
    by_cases hj : j ∈ p.support
    · exact hmax j hj
    · rw [notMem_support_iff.mp hj, map_zero]
      exact zero_le
  refine ⟨i, hc, hmax', ?_⟩
  set q := C c⁻¹ * p with hq_def
  have hq : ∀ j, vK (q.coeff j) ≤ 1 := by
    intro j
    rw [hq_def, coeff_C_mul, map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.mpr hvc)]
    exact hmax' j
  have hql : q ∈ lifts (algebraMap vK.valuationSubring K) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    exact ⟨⟨q.coeff j, (vK.mem_valuationSubring_iff _).mpr (hq j)⟩, rfl⟩
  obtain ⟨q₀, hq₀⟩ := (mem_lifts q).mp hql
  have hq₀i : q₀.coeff i = 1 := by
    apply Subtype.ext
    have h := congrArg (fun r => r.coeff i) hq₀
    simp only [coeff_map] at h
    change (q₀.coeff i : K) = 1
    rw [← ValuationSubring.algebraMap_apply, h, hq_def, coeff_C_mul, ← hc_def, inv_mul_cancel₀ hc]
  set r := q₀.map (residue vK.valuationSubring) with hr_def
  have hr : r ≠ 0 := by
    intro h
    have h' := congrArg (fun s => s.coeff i) h
    simp only [hr_def, coeff_map, hq₀i, map_one, coeff_zero] at h'
    exact one_ne_zero h'
  have hrdeg : r.natDegree < (minpoly (ResidueField vK.valuationSubring)
      (residue vL.valuationSubring z)).natDegree := by
    refine lt_of_le_of_lt (natDegree_map_le) (lt_of_le_of_lt (le_of_eq ?_) hdeg)
    have h1 : q.natDegree = p.natDegree := natDegree_C_mul (inv_ne_zero hc)
    rw [← h1, ← hq₀, natDegree_map_eq_of_injective (fun _ _ h => Subtype.ext h)]
  have hθ : aeval (residue vL.valuationSubring z) r ≠ 0 := by
    intro h0
    have := natDegree_le_natDegree (minpoly.degree_le_of_ne_zero _ _ hr h0)
    omega
  have h1 : vL (aeval (z : L) q) = 1 := by
    rw [← hq₀, ← coe_aeval_valuationSubring vK vL]
    apply valuation_eq_one_of_residue_ne_zero
    rw [residue_aeval_eq_aeval_map_residue vK vL]
    exact hθ
  have hpq : p = C c * q := by
    rw [hq_def, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  rw [show aeval (z : L) p = algebraMap K L c * aeval (z : L) q by rw [hpq, map_mul, aeval_C],
    map_mul, h1, mul_one]

end Reduction

section Existence

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Existence of an étale generator, the case of one extension** (Volume 5, Lemma 1.3.3 of the handbook, second part, in the case `f = [K : K₀]`). Let `K₀` be a subfield of `K` with `[K : K₀]` finite, let `v` be a valuation of `K`, and let `v₀` be a valuation of `K₀` that `v` extends. Assume that the residue extension `Kv/K₀v₀` is separable of degree `[K : K₀]`. Then `K/K₀` is separable, and there is an étale generator of `K/K₀` for the valuation ring of `v`.

By the fundamental inequality, the hypothesis means that `v` is the only extension of `v₀` to `K`, with ramification index 1, residue degree `[K : K₀]` and defect 1. So this is the case `g = 1` of the lemma. The lemma in the handbook allows `g` extensions of `v₀` to `K`, and its proof uses the henselization. That general case is not proved here. -/
theorem exists_isEtaleGenerator_of_finrank_residueField_eq {K₀ : IntermediateField k K}
    {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ]
    (v₀ : Valuation K₀ Γ₀) (v : Valuation K Γ) [v₀.HasExtension v] [FiniteDimensional K₀ K]
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      Module.finrank K₀ K) :
    Algebra.IsSeparable K₀ K ∧ ∃ z, IsEtaleGenerator K₀ v.valuationSubring z := by
  classical
  set κ₀ := ResidueField v₀.valuationSubring
  set κ := ResidueField v.valuationSubring
  set n := Module.finrank K₀ K with hn_def
  have hn : 0 < n := Module.finrank_pos
  have : FiniteDimensional κ₀ κ := Module.finite_of_finrank_pos (hf ▸ hn)
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element κ₀ κ
  have hμdeg : (minpoly κ₀ θ).natDegree = n :=
    ((Field.primitive_element_iff_minpoly_natDegree_eq κ₀ θ).mp hθ).trans hf
  obtain ⟨z, rfl⟩ := residue_surjective θ
  set P := minpoly K₀ (z : K) with hP_def
  have hzi : IsIntegral K₀ (z : K) := Algebra.IsIntegral.isIntegral _
  have hPm : P.Monic := minpoly.monic hzi
  have hPle : P.natDegree ≤ n := minpoly.natDegree_le _
  have hPn : P.natDegree = n := by
    refine le_antisymm hPle (not_lt.mp fun hlt => ?_)
    obtain ⟨i, hi, -, he⟩ := exists_valuation_aeval_eq_of_natDegree_lt v₀ v z hPm.ne_zero
      (hμdeg ▸ hlt)
    rw [minpoly.aeval, map_zero, eq_comm, Valuation.zero_iff, map_eq_zero] at he
    exact hi he
  have hadj : IntermediateField.adjoin K₀ {(z : K)} = ⊤ :=
    (Field.primitive_element_iff_minpoly_natDegree_eq K₀ (z : K)).mpr hPn
  -- The coefficients of `P` lie in the valuation ring of `v₀`.
  have hcoeff : ∀ i, v₀ (P.coeff i) ≤ 1 := by
    set r := P - X ^ n with hr_def
    have hPr : P = X ^ n + r := by rw [hr_def]; ring
    have hrdeg : r.natDegree < n ∨ r = 0 := by
      by_cases hr0 : r = 0
      · exact Or.inr hr0
      left
      have hd : r.degree < P.degree := by
        refine degree_sub_lt_left ?_ hPm.ne_zero ?_
        · rw [degree_X_pow, degree_eq_natDegree hPm.ne_zero, hPn]
        · rw [hPm.leadingCoeff, leadingCoeff_X_pow]
      rw [degree_eq_natDegree hPm.ne_zero, hPn] at hd
      exact (natDegree_lt_iff_degree_lt hr0).mpr hd
    have hr1 : ∀ i, v₀ (r.coeff i) ≤ 1 := by
      rcases hrdeg with hlt | hr0
      · by_cases hr0 : r = 0
        · intro i
          rw [hr0, coeff_zero, map_zero]
          exact zero_le
        obtain ⟨j, -, hjmax, he⟩ := exists_valuation_aeval_eq_of_natDegree_lt v₀ v z hr0
          (hμdeg ▸ hlt)
        have hrz : aeval (z : K) r = -(z : K) ^ n := by
          have h0 := minpoly.aeval K₀ (z : K)
          rw [← hP_def, hPr, map_add, map_pow, aeval_X] at h0
          linear_combination h0
        rw [hrz, Valuation.map_neg, map_pow] at he
        have hz1 : v (z : K) ^ n ≤ 1 := pow_le_one₀ zero_le ((v.mem_valuationSubring_iff _).mp z.2)
        have hj : v₀ (r.coeff j) ≤ 1 :=
          (Valuation.HasExtension.val_map_le_one_iff v₀ v _).mp (he ▸ hz1)
        exact fun i => (hjmax i).trans hj
      · intro i
        rw [hr0, coeff_zero, map_zero]
        exact zero_le
    intro i
    rw [hPr, coeff_add, coeff_X_pow]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ (hr1 i))
    split_ifs
    · rw [map_one]
    · rw [map_zero]
      exact zero_le
  -- The lift `P₀` of `P` to the valuation ring of `v₀`.
  have hPl : P ∈ lifts (algebraMap v₀.valuationSubring K₀) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    exact ⟨⟨P.coeff j, (v₀.mem_valuationSubring_iff _).mpr (hcoeff j)⟩, rfl⟩
  obtain ⟨P₀, hP₀⟩ := (mem_lifts P).mp hPl
  have hinj : Function.Injective (algebraMap v₀.valuationSubring K₀) :=
    fun _ _ h => Subtype.ext h
  have hP₀deg : P₀.natDegree = n := by
    rw [← hPn, ← hP₀, natDegree_map_eq_of_injective hinj]
  have hP₀m : P₀.Monic := by
    rw [Monic.def]
    apply hinj
    rw [leadingCoeff, map_one, ← coeff_map, hP₀, hP₀deg, ← hPn]
    exact hPm.coeff_natDegree
  set R := P₀.map (residue v₀.valuationSubring) with hR_def
  have hRm : R.Monic := hP₀m.map _
  have hRdeg : R.natDegree = n := by rw [hR_def, hP₀m.natDegree_map, hP₀deg]
  have hRθ : aeval (residue v.valuationSubring z) R = 0 := by
    rw [hR_def, ← residue_aeval_eq_aeval_map_residue v₀ v]
    have h0 : aeval z P₀ = 0 := by
      apply Subtype.val_injective
      rw [coe_aeval_valuationSubring v₀ v, hP₀]
      exact minpoly.aeval K₀ (z : K)
    rw [h0, map_zero]
  have hRμ : R = minpoly κ₀ (residue v.valuationSubring z) := by
    refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ?_) hRm
      (minpoly.dvd _ _ hRθ) (by rw [hRdeg, hμdeg])
    exact Algebra.IsIntegral.isIntegral _
  have hsep : IsSeparable κ₀ (residue v.valuationSubring z) := Algebra.IsSeparable.isSeparable κ₀ _
  have hder : v (aeval (z : K) (derivative P)) = 1 := by
    rw [← hP₀, derivative_map, ← coe_aeval_valuationSubring v₀ v]
    apply valuation_eq_one_of_residue_ne_zero
    rw [residue_aeval_eq_aeval_map_residue v₀ v, ← derivative_map, ← hR_def, hRμ]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  have hz : IsEtaleGenerator K₀ v.valuationSubring (z : K) := by
    refine ⟨z.2, hadj, fun i => ?_, ?_⟩
    · rw [Valuation.mem_valuationSubring_iff]
      exact (Valuation.HasExtension.val_map_le_one_iff v₀ v _).mpr (hcoeff i)
    · exact (Valuation.isEquiv_valuation_valuationSubring v).eq_one_iff_eq_one.mp hder
  exact ⟨hz.isSeparable, _, hz⟩

end Existence

end Singularity
