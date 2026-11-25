/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The lattice lemma for real weights

Let `γ_1, ..., γ_n` be real numbers that are linearly independent over `ℤ`, and let `Γ = ℤγ_1 ⊕ ... ⊕ ℤγ_n`, an ordered subgroup of `ℝ`. An element of `Γ` is a vector `a ∈ ℤ^n`, with value `a · γ = ∑ a_i γ_i`. The lattice lemma (Volume 5, Lemma 2.1.4 of the handbook) for this group says: for each finite set `E` of vectors with `a · γ ≥ 0`, there is a basis `b_1, ..., b_n` of `ℤ^n` with `b_l · γ > 0` for each `l`, such that each `a ∈ E` is a combination of the `b_l` with coefficients in `ℕ`. This file proves this case. It is the case of rank 1 of the lattice lemma, because an ordered group of rank 1 is a subgroup of `ℝ`.

The basis is given by two integer matrices `B` and `C` with `B * C = 1` and `C * B = 1`. The rows `b_l` of `B` are the new basis. The coefficients of `a` in this basis are the entries of `a ᵥ* C`, because `a = (a ᵥ* C) ᵥ* B`.

In the application to valuations, `γ_i = ν(x_i)` for a valuation `ν` of `k(x_1, ..., x_n)`, and a vector `a` is the Laurent monomial `x^a`. The rows of `B` give new monomials `u_l = x^{b_l}` with `ν(u_l) > 0`, and each monomial `x^a` with `a ∈ E` is a monomial in the `u_l` with exponents in `ℕ`.

## The proof

The proof works with the columns `c_1, ..., c_n` of `C`, in the dual space. Each `a ∈ ℤ^n` is `∑ (a · c_l) b_l`, and `γ = ∑ (b_l · γ) c_l`. So the conditions are: `γ` is a combination of the `c_l` with positive coefficients, and `a · c_l ≥ 0` for `a ∈ E`. We call an integer matrix `C` with these two conditions and with `det C ≠ 0` a good cone. We do not ask that `C` is invertible over `ℤ`.

1. A first good cone. Let `Q = n + 1`, let `M` be a large natural number, and let `R_r = ⌊M γ_r⌋`. The columns of `C` are `c_l = R + Q e_l`. Then `a · c_l = a · R + Q a_l`, and `a · R` is close to `M (a · γ)`. Since `a · γ > 0` for `a ≠ 0`, this is `≥ 0` for `M` large. The coefficients of `γ` are explicit, and they are positive because `γ_i > 0` and `Q > n`.
2. The index decreases. Let `C` be a good cone with `|det C| > 1`. Then some column `t` of `C⁻¹` is not an integer vector. Let `t'` be the vector of fractional parts of `t`. Then `u = C t'` is an integer vector, and `t'` is not zero. Let `μ` be the coefficients of `γ`. Among the indices with `t'_l > 0`, choose `l` with `μ_l / t'_l` minimal, and replace the column `c_l` by `u`. The new determinant is `t'_l det C`, so its absolute value is smaller. The new coefficients of `γ` are `μ_l / t'_l` and `μ_k - t'_k μ_l / t'_l`, and they are `≥ 0` by the choice of `l`. They are not zero, because `γ` lies on no hyperplane spanned by integer vectors: this is the linear independence of the `γ_i`. The condition on `E` holds, because `a · u = ∑ (a · c_k) t'_k ≥ 0`.
3. When `|det C| = 1`, the matrix `B = (det C) adj C` is the inverse of `C` over `ℤ`, and `B *ᵥ γ` is the vector of coefficients of `γ`, which is positive.

To remove the condition `γ_i > 0`, change the signs of the coordinates.

This is the argument of the handbook in the dual form. The handbook first finds a basis of `ℚ^n` (the cone lemma, Lemma 2.1.3) and then makes the index smaller. For a subgroup of `ℝ`, Step 1 replaces the cone lemma.

## Main results

* `Singularity.LatticeLemma.IsGoodCone`: an integer matrix whose columns give a good cone for `γ` and `E`.
* `Singularity.LatticeLemma.exists_isGoodCone_natAbs_det_lt`: Step 2, the index decreases.
* `Singularity.latticeLemma_real_of_pos`: the lattice lemma for real weights `γ_i > 0`.
* `Singularity.latticeLemma_real`: the lattice lemma for a subgroup of `ℝ` with a basis `γ_1, ..., γ_n`.
-/

open Matrix

namespace Singularity

namespace LatticeLemma

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integer matrix `C` is a good cone for the real weights `γ` and the finite set `E` of integer vectors: `det C ≠ 0`, the vector `γ` is a combination of the columns of `C` with positive real coefficients, and `a ᵥ* C ≥ 0` for each `a ∈ E`. -/
def IsGoodCone (γ : ι → ℝ) (E : Finset (ι → ℤ)) (C : Matrix ι ι ℤ) : Prop :=
  C.det ≠ 0 ∧ (∃ μ : ι → ℝ, C.map (Int.cast : ℤ → ℝ) *ᵥ μ = γ ∧ ∀ l, 0 < μ l) ∧
    ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l

omit [DecidableEq ι] in
/-- The real vector of `a ᵥ* C` is the product of the real vector of `a` with the real matrix of `C`. -/
theorem cast_vecMul (a : ι → ℤ) (C : Matrix ι ι ℤ) :
    (fun i => (a i : ℝ)) ᵥ* C.map (Int.cast : ℤ → ℝ) = fun j => ((a ᵥ* C) j : ℝ) := by
  ext j
  simp [vecMul, dotProduct]

omit [DecidableEq ι] in
/-- The real vector of `C *ᵥ v` is the product of the real matrix of `C` with the real vector of `v`. -/
theorem cast_mulVec (C : Matrix ι ι ℤ) (v : ι → ℤ) :
    C.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (v i : ℝ)) = fun j => ((C *ᵥ v) j : ℝ) := by
  ext j
  simp [mulVec, dotProduct]

/-- The real determinant of an integer matrix. -/
theorem cast_det (C : Matrix ι ι ℤ) : ((C.det : ℤ) : ℝ) = (C.map (Int.cast : ℤ → ℝ)).det := by
  have h := (Int.castRingHom ℝ).map_det C
  simpa using h

/-- Let `C` be an integer matrix with `det C ≠ 0`, and write `γ = C μ`. If the `γ_i` are linearly independent over `ℤ`, then no coefficient `μ_l` is zero. The row `l` of the adjugate of `C` is a nonzero integer vector `a` with `a · γ = (det C) μ_l`. -/
theorem coord_ne_zero {γ : ι → ℝ} (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0)
    {C : Matrix ι ι ℤ} (hC : C.det ≠ 0) {μ : ι → ℝ}
    (hμ : C.map (Int.cast : ℤ → ℝ) *ᵥ μ = γ) (l : ι) : μ l ≠ 0 := by
  intro h0
  set a : ι → ℤ := adjugate C l
  have haC : ∀ j, (a ᵥ* C) j = if l = j then C.det else 0 := by
    intro j
    have h := congrFun (congrFun (adjugate_mul C) l) j
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      mul_apply] at h
    simpa [vecMul, dotProduct, a] using h
  have hsum : ∑ i, (a i : ℝ) * γ i = (C.det : ℝ) * μ l := by
    have h1 : ∑ i, (a i : ℝ) * γ i = (fun i => (a i : ℝ)) ⬝ᵥ γ := rfl
    rw [h1, ← hμ, dotProduct_mulVec, cast_vecMul]
    simp [dotProduct, haC]
  have ha : a = 0 := hind a (by rw [hsum, h0, mul_zero])
  have := haC l
  rw [ha, zero_vecMul, ite_eq_left rfl] at this
  exact hC this.symm

/-- **Step 2: the index decreases.** Let `C` be a good cone with `|det C| > 1`. Then there is a good cone `C'` with `|det C'| < |det C|`. The new matrix replaces one column of `C` by an integer point `C t'` of the fundamental parallelepiped of the columns. -/
theorem exists_isGoodCone_natAbs_det_lt {γ : ι → ℝ}
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0) {E : Finset (ι → ℤ)}
    {C : Matrix ι ι ℤ} (hC : IsGoodCone γ E C) (h1 : 1 < C.det.natAbs) :
    ∃ C' : Matrix ι ι ℤ, IsGoodCone γ E C' ∧ C'.det.natAbs < C.det.natAbs := by
  obtain ⟨hdet, ⟨μ, hμ, hμpos⟩, hE⟩ := hC
  set d := C.det with hd
  -- Some entry of the adjugate is not divisible by `d`.
  have hnd : ∃ l0 i, ¬ d ∣ adjugate C l0 i := by
    by_contra hall
    push Not at hall
    choose B hB using hall
    have hBC : Matrix.of B * C = 1 := by
      have h2 : d • (Matrix.of B * C) = d • (1 : Matrix ι ι ℤ) := by
        rw [← adjugate_mul C, ← Matrix.smul_mul]
        congr 1
        ext l i
        simp [hB l i]
      exact smul_right_injective _ hdet h2
    have h3 := congrArg det hBC
    rw [det_mul, det_one, mul_comm] at h3
    have := Int.isUnit_iff_natAbs_eq.mp (IsUnit.of_mul_eq_one _ h3)
    omega
  obtain ⟨l0, i, hl0⟩ := hnd
  have hdR : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hdet
  set CR := C.map (Int.cast : ℤ → ℝ) with hCR
  -- The column `t` of `C⁻¹`, and its fractional part `t'`.
  set t : ι → ℝ := fun l => ((adjugate C l i : ℤ) : ℝ) / d with ht
  set t' : ι → ℝ := fun l => Int.fract (t l) with ht'
  have ht'0 : 0 < t' l0 := by
    rcases (Int.fract_nonneg (t l0)).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hl0
      refine ⟨⌊t l0⌋, ?_⟩
      have h2 : t l0 = ⌊t l0⌋ := by
        have := Int.floor_add_fract (t l0)
        rw [← h] at this
        linarith
      have h3 : ((adjugate C l0 i : ℤ) : ℝ) = d * ⌊t l0⌋ := by
        rw [← h2, ht]
        field_simp
      exact_mod_cast h3
  have hCt : CR *ᵥ t = Pi.single i 1 := by
    ext r
    have h := congrFun (congrFun (mul_adjugate C) r) i
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_apply] at h
    have h' : ∑ l, ((C r l : ℤ) : ℝ) * ((adjugate C l i : ℤ) : ℝ) =
        (d : ℝ) * (if r = i then 1 else 0) := by
      exact_mod_cast h
    simp only [mulVec, dotProduct, hCR, map_apply, ht, Pi.single_apply]
    simp_rw [mul_div_assoc']
    rw [← Finset.sum_div, h']
    field_simp
  -- The integer point `u = C t'`.
  set u : ι → ℤ := Pi.single i 1 - C *ᵥ (fun l => ⌊t l⌋) with hu
  have huR : (fun r => (u r : ℝ)) = CR *ᵥ t' := by
    have h2 : t' = t - fun l => ((⌊t l⌋ : ℤ) : ℝ) := funext fun l => rfl
    rw [h2, mulVec_sub, hCt, hCR, cast_mulVec]
    ext r
    simp [hu, Pi.single_apply]
  -- The choice of the column `l`.
  set S := Finset.univ.filter (fun l => 0 < t' l) with hS
  have hSne : S.Nonempty := ⟨l0, by simp [hS, ht'0]⟩
  obtain ⟨l, hlS, hlmin⟩ := S.exists_min_image (fun l => μ l / t' l) hSne
  have htl : 0 < t' l := (Finset.mem_filter.mp hlS).2
  set c := μ l / t' l with hc
  set C' := C.updateCol l u with hC'
  set N : Matrix ι ι ℝ := (1 : Matrix ι ι ℝ).updateCol l t' with hN
  have hC'R : C'.map (Int.cast : ℤ → ℝ) = CR * N := by
    rw [hN, mul_updateCol, Matrix.mul_one, hC', map_updateCol, ← huR]
    rfl
  have hdetN : N.det = t' l := by
    rw [hN, ← cramer_apply, cramer_eq_adjugate_mulVec, adjugate_one, one_mulVec]
  have hdet' : (C'.det : ℝ) = d * t' l := by
    rw [cast_det, hC'R, det_mul, hdetN, ← cast_det]
  have hdet'0 : C'.det ≠ 0 := by
    intro h0
    have : (C'.det : ℝ) = 0 := by rw [h0, Int.cast_zero]
    rw [hdet'] at this
    exact mul_ne_zero hdR htl.ne' this
  -- The new coefficients of `γ`.
  set μ' : ι → ℝ := fun k => if k = l then c else μ k - t' k * c with hμ'
  have hNμ : N *ᵥ μ' = μ := by
    ext r
    simp only [mulVec, dotProduct, hN, updateCol_apply, one_apply]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    rw [ite_eq_left rfl]
    have h2 : ∀ j ∈ Finset.univ.erase l, (if j = l then t' r else if r = j then (1 : ℝ) else 0) * μ' j =
        if r = j then μ' j else 0 := by
      intro j hj
      rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq]
    by_cases hr : r = l
    · subst hr
      simp only [hμ', hc, ite_true]
      field_simp
      simp
    · have hr' : r ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩
      rw [ite_eq_left hr']
      simp [hμ', hr]
  have hμ'γ : C'.map (Int.cast : ℤ → ℝ) *ᵥ μ' = γ := by
    rw [hC'R, ← mulVec_mulVec, hNμ, hμ]
  have hcpos : 0 < c := div_pos (hμpos l) htl
  have hμ'nonneg : ∀ k, 0 ≤ μ' k := by
    intro k
    by_cases hk : k = l
    · simp [hμ', hk, hcpos.le]
    · simp only [hμ', ite_eq_right hk]
      by_cases htk : 0 < t' k
      · have hkS : k ∈ S := by simp [hS, htk]
        have h2 : c ≤ μ k / t' k := hlmin k hkS
        rw [le_div_iff₀ htk] at h2
        linarith
      · have h0 : t' k = 0 := le_antisymm (not_lt.mp htk) (Int.fract_nonneg _)
        rw [h0, zero_mul, sub_zero]
        exact (hμpos k).le
  refine ⟨C', ⟨hdet'0, ⟨μ', hμ'γ, fun k => ?_⟩, fun a ha j => ?_⟩, ?_⟩
  · exact lt_of_le_of_ne (hμ'nonneg k) (coord_ne_zero hind hdet'0 hμ'γ k).symm
  · by_cases hj : j = l
    · subst hj
      have h2 : (a ᵥ* C') j = ∑ r, a r * u r := by
        simp [vecMul, dotProduct, hC']
      have h3 : ((∑ r, a r * u r : ℤ) : ℝ) = ∑ k, ((a ᵥ* C) k : ℝ) * t' k := by
        push_cast
        have h4 : ∑ r, (a r : ℝ) * (u r : ℝ) = (fun r => (a r : ℝ)) ⬝ᵥ (fun r => (u r : ℝ)) := rfl
        rw [h4, huR, dotProduct_mulVec, hCR, cast_vecMul]
        rfl
      have h5 : (0 : ℝ) ≤ ∑ k, ((a ᵥ* C) k : ℝ) * t' k :=
        Finset.sum_nonneg fun k _ => mul_nonneg (by exact_mod_cast hE a ha k) (Int.fract_nonneg _)
      rw [h2]
      rw [← h3] at h5
      exact_mod_cast h5
    · have h2 : (a ᵥ* C') j = (a ᵥ* C) j := by
        simp [vecMul, dotProduct, hC', hj]
      rw [h2]
      exact hE a ha j
  · have h2 : ((C'.det.natAbs : ℤ) : ℝ) = |(d : ℝ)| * t' l := by
      rw [Int.natCast_natAbs, Int.cast_abs, hdet', abs_mul, abs_of_pos htl]
    have h3 : ((d.natAbs : ℤ) : ℝ) = |(d : ℝ)| := by
      rw [Int.natCast_natAbs, Int.cast_abs]
    have h4 : |(d : ℝ)| * t' l < |(d : ℝ)| :=
      mul_lt_of_lt_one_right (abs_pos.mpr hdR) (Int.fract_lt_one _)
    have h5 : ((C'.det.natAbs : ℤ) : ℝ) < ((d.natAbs : ℤ) : ℝ) := by
      rw [h2, h3]
      exact h4
    exact_mod_cast h5

/-- Repeat Step 2: from a good cone, we reach a good cone with `|det C| = 1`. -/
theorem exists_isGoodCone_natAbs_det_eq_one {γ : ι → ℝ}
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0) {E : Finset (ι → ℤ)} :
    ∀ (m : ℕ) (C : Matrix ι ι ℤ), C.det.natAbs = m → IsGoodCone γ E C →
      ∃ C' : Matrix ι ι ℤ, IsGoodCone γ E C' ∧ C'.det.natAbs = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro C hm hC
    by_cases h1 : 1 < m
    · obtain ⟨C', hC', hlt⟩ := exists_isGoodCone_natAbs_det_lt hind hC (hm ▸ h1)
      exact ih _ (hm ▸ hlt) C' rfl hC'
    · have h0 : C.det.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hC.1
      exact ⟨C, hC, by omega⟩

/-- **Step 3.** A good cone with `|det C| = 1` gives the basis: `B = (det C) adj C` is the inverse of `C` over `ℤ`, and the rows of `B` have positive values. -/
theorem exists_basis_of_isGoodCone {γ : ι → ℝ} {E : Finset (ι → ℤ)} {C : Matrix ι ι ℤ}
    (hC : IsGoodCone γ E C) (h1 : C.det.natAbs = 1) :
    ∃ B : Matrix ι ι ℤ, B * C = 1 ∧ C * B = 1 ∧ (∀ l, 0 < ∑ i, (B l i : ℝ) * γ i) ∧
      ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l := by
  obtain ⟨-, ⟨μ, hμ, hpos⟩, hE⟩ := hC
  have hdd : C.det * C.det = 1 := by
    rcases Int.natAbs_eq_iff.mp h1 with h | h <;> rw [h] <;> norm_num
  have hBC : (C.det • adjugate C) * C = 1 := by
    rw [Matrix.smul_mul, adjugate_mul, smul_smul, hdd, one_smul]
  refine ⟨C.det • adjugate C, hBC, ?_, fun l => ?_, hE⟩
  · rw [Matrix.mul_smul, mul_adjugate, smul_smul, hdd, one_smul]
  · set B := C.det • adjugate C
    have hBCR : B.map (Int.cast : ℤ → ℝ) * C.map (Int.cast : ℤ → ℝ) = 1 := by
      have h2 := Matrix.map_mul (L := B) (M := C) (f := Int.castRingHom ℝ)
      rw [hBC, Matrix.map_one _ (map_zero _) (map_one _)] at h2
      simpa using h2.symm
    have h3 : B.map (Int.cast : ℤ → ℝ) *ᵥ γ = μ := by
      rw [← hμ, mulVec_mulVec, hBCR, one_mulVec]
    have h4 := congrFun h3 l
    simp only [mulVec, dotProduct, map_apply] at h4
    rw [h4]
    exact hpos l

/-- **Step 1: a first good cone.** If `γ_i > 0` for each `i` and the `γ_i` are linearly independent over `ℤ`, then each finite set `E` of vectors with `a · γ ≥ 0` has a good cone. The columns are `R + Q e_l`, where `Q = n + 1`, `R_r = ⌊M γ_r⌋`, and `M` is a large natural number. -/
theorem exists_isGoodCone {γ : ι → ℝ} (hγ : ∀ i, 0 < γ i)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0) (E : Finset (ι → ℤ))
    (hE : ∀ a ∈ E, 0 ≤ ∑ i, (a i : ℝ) * γ i) : ∃ C, IsGoodCone γ E C := by
  set Q : ℕ := Fintype.card ι + 1 with hQ
  set w : (ι → ℤ) → ℝ := fun a => ∑ i, (a i : ℝ) * γ i with hw
  set nrm : (ι → ℤ) → ℝ := fun a => ∑ i, |(a i : ℝ)| with hnrm
  obtain ⟨M, hM⟩ := exists_nat_gt (∑ a ∈ E, ((Q : ℝ) + 1) * nrm a / w a)
  set R : ι → ℤ := fun r => ⌊(M : ℝ) * γ r⌋ with hR
  set C : Matrix ι ι ℤ := Matrix.of fun r l => R r + if r = l then (Q : ℤ) else 0 with hC
  have hR0 : ∀ r, 0 ≤ R r := fun r =>
    Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (hγ r).le)
  have hCv : ∀ (v : ι → ℤ) r, (C *ᵥ v) r = R r * ∑ l, v l + Q * v r := by
    intro v r
    simp [hC, mulVec, dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum, ite_mul]
  have haC : ∀ (a : ι → ℤ) l, (a ᵥ* C) l = ∑ r, a r * R r + a l * Q := by
    intro a l
    simp [hC, vecMul, dotProduct, mul_add, Finset.sum_add_distrib, mul_ite]
  -- The determinant is not zero.
  have hdet : C.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hv' : ∀ r, R r * ∑ l, v l + Q * v r = 0 := fun r => by
      rw [← hCv]; exact congrFun hv r
    have hsum : (∑ r, R r + Q) * ∑ l, v l = 0 := by
      have := Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) => hv' r)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const_zero] at this
      linarith
    have hpos : 0 < ∑ r, R r + Q := by
      have := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) => hR0 r)
      omega
    have hs : ∑ l, v l = 0 := (mul_eq_zero.mp hsum).resolve_left hpos.ne'
    apply hv0
    ext r
    have := hv' r
    rw [hs, mul_zero, zero_add] at this
    have hQ0 : (Q : ℤ) ≠ 0 := by omega
    exact (mul_eq_zero.mp this).resolve_left hQ0
  -- The coefficients of `γ`.
  set S : ℝ := ∑ i, γ i with hS
  set ρ : ℝ := ∑ r, (R r : ℝ) with hρ
  have hρ0 : 0 ≤ ρ := Finset.sum_nonneg fun r _ => by exact_mod_cast hR0 r
  have hQpos : (0 : ℝ) < Q := by positivity
  have hQρ : 0 < (Q : ℝ) + ρ := by linarith
  set s : ℝ := S / (Q + ρ) with hs
  set μ : ι → ℝ := fun l => (γ l - s * R l) / Q with hμ
  have hsum : ∑ l, μ l = s := by
    simp only [hμ]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hS, ← hρ, hs]
    field_simp
    ring
  have hCμ : C.map (Int.cast : ℤ → ℝ) *ᵥ μ = γ := by
    ext r
    have h2 : (C.map (Int.cast : ℤ → ℝ) *ᵥ μ) r = (R r : ℝ) * ∑ l, μ l + Q * μ r := by
      simp only [mulVec, dotProduct, map_apply, hC, of_apply]
      push_cast
      simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [h2, hsum, hμ]
    field_simp
    ring
  -- The fractional parts `η_r = M γ_r - R_r`.
  have hη : ∀ r, (R r : ℝ) = M * γ r - Int.fract ((M : ℝ) * γ r) := fun r => by
    show ((⌊(M : ℝ) * γ r⌋ : ℤ) : ℝ) = _
    rw [Int.fract]
    ring
  have hηsum : ∑ r, Int.fract ((M : ℝ) * γ r) < Q := by
    have : ∑ r, Int.fract ((M : ℝ) * γ r) ≤ ∑ _r : ι, (1 : ℝ) :=
      Finset.sum_le_sum fun r _ => (Int.fract_lt_one _).le
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [hQ]
    push_cast
    linarith
  have hμpos : ∀ l, 0 < μ l := by
    intro l
    simp only [hμ]
    apply div_pos _ hQpos
    rw [sub_pos, hs, div_mul_eq_mul_div, div_lt_iff₀ hQρ]
    have hρ' : ρ = M * S - ∑ r, Int.fract ((M : ℝ) * γ r) := by
      rw [hρ, Finset.sum_congr rfl fun r _ => hη r, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hρ', hη l]
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (hγ i).le
    have h2 : 0 ≤ S * Int.fract ((M : ℝ) * γ l) := mul_nonneg hS0 (Int.fract_nonneg _)
    have h3 : 0 < γ l * (Q - ∑ r, Int.fract ((M : ℝ) * γ r)) := mul_pos (hγ l) (by linarith)
    nlinarith
  -- The condition on `E`.
  have hEC : ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l := by
    intro a ha l
    by_cases ha0 : a = 0
    · rw [ha0, zero_vecMul]
      rfl
    have hwa : 0 < w a := lt_of_le_of_ne (hE a ha) (fun h => ha0 (hind a h.symm))
    have hnrm0 : 0 ≤ nrm a := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hMa : ((Q : ℝ) + 1) * nrm a < M * w a := by
      have h2 : ((Q : ℝ) + 1) * nrm a / w a ≤ ∑ a ∈ E, ((Q : ℝ) + 1) * nrm a / w a :=
        Finset.single_le_sum (f := fun a => ((Q : ℝ) + 1) * nrm a / w a)
          (fun b hb => div_nonneg (mul_nonneg (by positivity)
            (Finset.sum_nonneg fun i _ => abs_nonneg _)) (hE b hb)) ha
      have h3 := lt_of_le_of_lt h2 hM
      rwa [div_lt_iff₀ hwa] at h3
    have h2 : (((a ᵥ* C) l : ℤ) : ℝ) = ∑ r, (a r : ℝ) * R r + a l * Q := by
      rw [haC]
      push_cast
      rfl
    have h3 : ∑ r, (a r : ℝ) * R r ≥ M * w a - nrm a := by
      have h4 : ∀ r, (a r : ℝ) * R r ≥ M * ((a r : ℝ) * γ r) - |(a r : ℝ)| := by
        intro r
        rw [hη r]
        have h5 : (a r : ℝ) * Int.fract ((M : ℝ) * γ r) ≤ |(a r : ℝ)| := by
          calc (a r : ℝ) * Int.fract ((M : ℝ) * γ r) ≤ |(a r : ℝ)| * Int.fract ((M : ℝ) * γ r) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (Int.fract_nonneg _)
            _ ≤ |(a r : ℝ)| * 1 :=
                mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le (abs_nonneg _)
            _ = |(a r : ℝ)| := mul_one _
        nlinarith
      have h6 := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => h4 r
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at h6
      exact h6
    have h4 : (a l : ℝ) * Q ≥ -(nrm a * Q) := by
      have h5 : |(a l : ℝ)| ≤ nrm a :=
        Finset.single_le_sum (f := fun i => |(a i : ℝ)|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ l)
      have h6 : -|(a l : ℝ)| ≤ (a l : ℝ) := neg_abs_le _
      nlinarith
    have h7 : (0 : ℝ) ≤ (((a ᵥ* C) l : ℤ) : ℝ) := by
      rw [h2]
      nlinarith
    exact_mod_cast h7
  exact ⟨C, hdet, ⟨μ, hCμ, hμpos⟩, hEC⟩

end LatticeLemma

open LatticeLemma

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The lattice lemma for positive real weights.** Let `γ_i > 0` be real numbers, linearly independent over `ℤ`, and let `E` be a finite set of integer vectors `a` with `a · γ ≥ 0`. Then there are integer matrices `B` and `C` with `B * C = 1` and `C * B = 1`, such that each row `b_l` of `B` has `b_l · γ > 0`, and each `a ∈ E` has coefficients `a ᵥ* C ≥ 0` in the basis of the rows of `B`. -/
theorem latticeLemma_real_of_pos (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0) (E : Finset (ι → ℤ))
    (hE : ∀ a ∈ E, 0 ≤ ∑ i, (a i : ℝ) * γ i) :
    ∃ B C : Matrix ι ι ℤ, B * C = 1 ∧ C * B = 1 ∧ (∀ l, 0 < ∑ i, (B l i : ℝ) * γ i) ∧
      ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l := by
  obtain ⟨C₀, hC₀⟩ := exists_isGoodCone hγ hind E hE
  obtain ⟨C, hC, h1⟩ := exists_isGoodCone_natAbs_det_eq_one hind _ C₀ rfl hC₀
  obtain ⟨B, hB⟩ := exists_basis_of_isGoodCone hC h1
  exact ⟨B, C, hB⟩

/-- **The lattice lemma for a subgroup of `ℝ`** (Volume 5, Lemma 2.1.4 of the handbook, in rank 1). Let `γ_1, ..., γ_n` be real numbers that are linearly independent over `ℤ`, so that `Γ = ⊕ ℤ γ_i` is an ordered group isomorphic to `ℤ^n`. Let `E` be a finite set of integer vectors `a` with `a · γ ≥ 0`. Then there is a basis of `ℤ^n`, the rows `b_l` of an integer matrix `B` with inverse `C`, such that `b_l · γ > 0` for each `l`, and each `a ∈ E` is the combination `a = ∑ (a ᵥ* C)_l b_l` with coefficients `(a ᵥ* C)_l ≥ 0`. -/
theorem latticeLemma_real (γ : ι → ℝ)
    (hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0) (E : Finset (ι → ℤ))
    (hE : ∀ a ∈ E, 0 ≤ ∑ i, (a i : ℝ) * γ i) :
    ∃ B C : Matrix ι ι ℤ, B * C = 1 ∧ C * B = 1 ∧ (∀ l, 0 < ∑ i, (B l i : ℝ) * γ i) ∧
      ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l := by
  classical
  -- Change the signs of the coordinates with `γ_i < 0`.
  set σ : ι → ℤ := fun i => if 0 < γ i then 1 else -1 with hσ
  have hσσ : ∀ i, σ i * σ i = 1 := fun i => by simp only [hσ]; split_ifs <;> norm_num
  set D : Matrix ι ι ℤ := diagonal σ with hD
  have hDD : D * D = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    exact hσσ i
  have hγ0 : ∀ i, γ i ≠ 0 := by
    intro i h0
    have := hind (Pi.single i 1) (by simp [Pi.single_apply, h0])
    have h2 := congrFun this i
    simp at h2
  set γ' : ι → ℝ := fun i => σ i * γ i with hγ'
  have hγ'pos : ∀ i, 0 < γ' i := by
    intro i
    simp only [hγ', hσ]
    split_ifs with h
    · simpa using h
    · have : γ i < 0 := lt_of_le_of_ne (not_lt.mp h) (hγ0 i)
      push_cast
      linarith
  have hw : ∀ a : ι → ℤ, ∑ i, ((a ᵥ* D) i : ℝ) * γ' i = ∑ i, (a i : ℝ) * γ i := by
    intro a
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 : (a ᵥ* D) i = a i * σ i := by simp [hD, vecMul_diagonal]
    have h3 : ((σ i : ℤ) : ℝ) * (σ i : ℝ) = 1 := by exact_mod_cast hσσ i
    rw [h2, hγ']
    push_cast
    calc (a i : ℝ) * σ i * (σ i * γ i) = (a i : ℝ) * (σ i * σ i) * γ i := by ring
      _ = (a i : ℝ) * γ i := by rw [h3, mul_one]
  have hind' : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ' i = 0 → a = 0 := by
    intro a ha
    have h2 : a ᵥ* D ᵥ* D = a := by rw [vecMul_vecMul, hDD, vecMul_one]
    have h3 := hind (a ᵥ* D) (by rw [← hw, h2]; exact ha)
    rw [← h2, h3, zero_vecMul]
  obtain ⟨B, C, hBC, hCB, hpos, hE'⟩ := latticeLemma_real_of_pos γ' hγ'pos hind'
    (E.image fun a => a ᵥ* D) (by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      rw [hw]
      exact hE a ha)
  refine ⟨B * D, D * C, ?_, ?_, fun l => ?_, fun a ha l => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc D, hDD, Matrix.one_mul, hBC]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, hCB, Matrix.one_mul, hDD]
  · have h2 : ∀ i, (B * D) l i = B l i * σ i := fun i => by simp [hD, mul_diagonal]
    have h3 : ∑ i, ((B * D) l i : ℝ) * γ i = ∑ i, (B l i : ℝ) * γ' i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h2, hγ']
      push_cast
      ring
    rw [h3]
    exact hpos l
  · rw [← vecMul_vecMul]
    exact hE' _ (Finset.mem_image_of_mem _ ha) l

end Singularity
