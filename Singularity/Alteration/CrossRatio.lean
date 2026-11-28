/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Surface.NormalRationalCores
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Separable

/-!
# The cross-ratio, and general position over an infinite field

This file proves algebraic cores of Example 2.2.3 and Lemmas 2.3.3 and 2.3.4 of Volume 8 of the
handbook, and the easy direction of Remark 2.1.4 of Volume 4.

A point of the projective line over a field `K` is given by a nonzero vector `p : Fin 2 → K`,
up to a nonzero scalar. Two vectors give the same point if and only if their bracket
`p 0 * q 1 - p 1 * q 0` is `0`. The point `z` of `K` is `![z, 1]`, and `∞` is `![1, 0]`.

Example 2.2.3 (four points on a line).

* `Singularity.p1Bracket`: the bracket `[p, q]` of two vectors of `K²`.
* `Singularity.crossRatio`: the cross-ratio `[d, a][b, c] / ([b, a][d, c])` of four points. It
  takes the value `λ` on the four points `0, 1, ∞, λ` (`Singularity.crossRatio_std`).
* `Singularity.p1Bracket_std_ne_zero_iff`: the four points `0, 1, ∞, λ` are distinct if and only
  if `λ ≠ 0` and `λ ≠ 1`. This is the base `U = P¹ \ {0, 1, ∞}` of the example.
* `Singularity.crossRatio_smul`: the cross-ratio does not change when the vectors are scaled, so
  it is a function of four points of `P¹`.
* `Singularity.crossRatio_mulVec`: the cross-ratio is invariant under `GL₂(K)`, hence under
  `PGL₂(K)`.
* `Singularity.crossRatio_ne_zero`, `Singularity.crossRatio_ne_one`,
  `Singularity.crossRatio_den_ne_zero`: for four distinct points the cross-ratio avoids `0`, `1`
  and `∞`.
* `Singularity.exists_mulVec_std`: four distinct points are moved by an element of `GL₂(K)` to
  the points `0, 1, ∞, λ`, with `λ` the cross-ratio.
* `Singularity.exists_mulVec_of_crossRatio_eq`: two quadruples of distinct points with the same
  cross-ratio are in the same orbit of `PGL₂(K)`. So the cross-ratio identifies the quadruples
  of distinct points modulo `PGL₂(K)` with `P¹ \ {0, 1, ∞}`.
* `Singularity.crossRatio_swap_zero_one`, `Singularity.crossRatio_swap_zero_two`,
  `Singularity.crossRatio_swap_zero_three` and the Klein four-group invariance
  `Singularity.crossRatio_klein_one` (and `_two`, `_three`): the action of transpositions.
* `Singularity.crossRatio_comp_perm_mem`: for each permutation `σ` of the four points, the
  cross-ratio of the permuted points lies in the orbit
  `{λ, 1 - λ, λ⁻¹, (1 - λ)⁻¹, λ / (λ - 1), (λ - 1) / λ}`.

The scheme part of Example 2.2.3 is not proved: the blowup `X` of `P¹ × P¹` in three points, its
fibres, and the stability and flatness of `X → P¹` are not constructed in Lean.

Lemmas 2.3.3 and 2.3.4 (general position), the counting cores.

* `Singularity.exists_forall_notMem_of_ne_top`: over an infinite field, a vector space is not a
  finite union of proper subspaces.
* `Singularity.exists_injOn_linear`: over an infinite field, a general linear form on `K^σ` is
  injective on a given finite set. So a general linear projection to a line separates finitely
  many given points.
* `Singularity.exists_forall_eval_ne_zero`: over an infinite field, a finite union of zero sets of
  nonzero polynomials is not all of `K^σ`. This is the choice of a general closed point `p`
  outside `B ∪ π(Z)` in the proof of Lemma 2.3.3.
* `Singularity.finite_setOf_eval_line_eq_zero`: if `f(p) ≠ 0`, then each line through `p` meets
  the zero set of `f` in finitely many points. This is the step "the line `ℓ_t` through `p` is not
  contained in `W`, so `W ∩ ℓ_t` is finite" in part 3 of Lemma 2.3.3, for a hypersurface `W`.
* `Singularity.le_card_rootSet_of_separable`: a separable split polynomial of degree at least `n`
  has at least `n` roots. This is the count "a transversal hyperplane meets a curve of degree at
  least `3` in at least `3` distinct points" in the sketch of Lemma 2.3.4.

The geometry of Lemmas 2.3.3 and 2.3.4 is not proved: the projections `X → P^d`, the blowup of a
point, the fibration in curves, the Bertini statements (B) and the dimension count for
hyperplanes are not in Lean.

Remark 2.1.4 of Volume 4 (one resolution or all normal modifications).

* `Singularity.r1PushforwardVanishes_of_hasRationalSingularities` and
  `Singularity.r1PushforwardVanishes_of_isRationalSingularity`: if `X` (or `Spec A`) has rational
  singularities in the sense of Definition 2.1.3, then `R¹ f_* O_Y = 0` for each resolution `f`,
  since a resolution is a normal modification. This direction is immediate from the definition.

The converse direction of Remark 2.1.4 is not proved. It needs the existence of resolutions
(Theorem 2.2.1 of Volume 4), the comparison of `H¹(Y, O_Y)` with `R¹ f_* O_Y` over an affine
base, and the Leray spectral sequence. None of these is in Lean.
-/

namespace Singularity

/-! ### Example 2.2.3, the cross-ratio -/

section CrossRatio

variable {K : Type*} [Field K]

/-- The bracket `[p, q] = p₀ q₁ - p₁ q₀` of two vectors of `K²`. Two nonzero vectors give the same
point of `P¹` if and only if their bracket is `0`. -/
def p1Bracket (p q : Fin 2 → K) : K := p 0 * q 1 - p 1 * q 0

/-- The cross-ratio `[d, a][b, c] / ([b, a][d, c])` of four points of `P¹`. For points of the
affine line it is `(d - a)(b - c) / ((b - a)(d - c))`. -/
noncomputable def crossRatio (a b c d : Fin 2 → K) : K :=
  p1Bracket d a * p1Bracket b c / (p1Bracket b a * p1Bracket d c)

theorem p1Bracket_swap (p q : Fin 2 → K) : p1Bracket q p = -p1Bracket p q := by
  simp only [p1Bracket]; ring

theorem p1Bracket_swap_ne_zero {p q : Fin 2 → K} (h : p1Bracket p q ≠ 0) :
    p1Bracket q p ≠ 0 := by
  rw [p1Bracket_swap]; exact neg_ne_zero.mpr h

/-- The cross-ratio of `0, 1, ∞, λ` is `λ`. -/
theorem crossRatio_std (l : K) : crossRatio ![0, 1] ![1, 1] ![1, 0] ![l, 1] = l := by
  simp [crossRatio, p1Bracket]

/-- Example 2.2.3. The four points `0, 1, ∞, λ` are pairwise distinct if and only if `λ` lies in
`U = P¹ \ {0, 1, ∞}`, that is `λ ≠ 0` and `λ ≠ 1`. -/
theorem p1Bracket_std_ne_zero_iff (l : K) :
    (∀ i j : Fin 4, i ≠ j →
      p1Bracket (![![0, 1], ![1, 1], ![1, 0], ![l, 1]] i)
        (![![0, 1], ![1, 1], ![1, 0], ![l, 1]] j) ≠ 0) ↔ l ≠ 0 ∧ l ≠ 1 := by
  constructor
  · intro h
    have h03 := h 0 3 (by decide)
    have h13 := h 1 3 (by decide)
    simp only [p1Bracket] at h03 h13
    simp at h03 h13
    exact ⟨h03, fun h1 => h13 (by rw [h1]; ring)⟩
  · rintro ⟨h0, h1⟩ i j hij
    have h1' : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have h1'' : l - 1 ≠ 0 := sub_ne_zero.mpr h1
    fin_cases i <;> fin_cases j <;> simp_all [p1Bracket]

/-- The cross-ratio depends only on the four points of `P¹`: scaling the vectors by nonzero
scalars does not change it. -/
theorem crossRatio_smul (a b c d : Fin 2 → K) {r s t u : K} (hr : r ≠ 0) (hs : s ≠ 0)
    (ht : t ≠ 0) (hu : u ≠ 0) :
    crossRatio (r • a) (s • b) (t • c) (u • d) = crossRatio a b c d := by
  have hk : r * s * t * u ≠ 0 := by simp [hr, hs, ht, hu]
  have hN : p1Bracket (u • d) (r • a) * p1Bracket (s • b) (t • c) =
      (r * s * t * u) * (p1Bracket d a * p1Bracket b c) := by
    simp only [p1Bracket, Pi.smul_apply, smul_eq_mul]; ring
  have hD : p1Bracket (s • b) (r • a) * p1Bracket (u • d) (t • c) =
      (r * s * t * u) * (p1Bracket b a * p1Bracket d c) := by
    simp only [p1Bracket, Pi.smul_apply, smul_eq_mul]; ring
  rw [crossRatio, hN, hD, mul_div_mul_left _ _ hk, crossRatio]

/-- A matrix multiplies the bracket by its determinant. -/
theorem p1Bracket_mulVec (M : Matrix (Fin 2) (Fin 2) K) (p q : Fin 2 → K) :
    p1Bracket (M.mulVec p) (M.mulVec q) = M.det * p1Bracket p q := by
  simp only [p1Bracket, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- The cross-ratio is invariant under `GL₂(K)`, so under `PGL₂(K)`. -/
theorem crossRatio_mulVec (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0)
    (a b c d : Fin 2 → K) :
    crossRatio (M.mulVec a) (M.mulVec b) (M.mulVec c) (M.mulVec d) = crossRatio a b c d := by
  have hk : M.det * M.det ≠ 0 := mul_ne_zero hM hM
  simp only [crossRatio, p1Bracket_mulVec]
  rw [show M.det * p1Bracket d a * (M.det * p1Bracket b c) =
      (M.det * M.det) * (p1Bracket d a * p1Bracket b c) by ring,
    show M.det * p1Bracket b a * (M.det * p1Bracket d c) =
      (M.det * M.det) * (p1Bracket b a * p1Bracket d c) by ring, mul_div_mul_left _ _ hk]

/-- The Plücker relation between the six brackets of four vectors. -/
theorem p1Bracket_plucker (a b c d : Fin 2 → K) :
    p1Bracket a b * p1Bracket c d - p1Bracket a c * p1Bracket b d +
      p1Bracket a d * p1Bracket b c = 0 := by
  simp only [p1Bracket]; ring

/-- The cross-ratio of four distinct points is finite: its denominator is not `0`. -/
theorem crossRatio_den_ne_zero {a b c d : Fin 2 → K} (hab : p1Bracket a b ≠ 0)
    (hcd : p1Bracket c d ≠ 0) : p1Bracket b a * p1Bracket d c ≠ 0 := by
  exact mul_ne_zero (p1Bracket_swap_ne_zero hab) (p1Bracket_swap_ne_zero hcd)

/-- The cross-ratio of four distinct points is not `0`. -/
theorem crossRatio_ne_zero {a b c d : Fin 2 → K} (hab : p1Bracket a b ≠ 0)
    (had : p1Bracket a d ≠ 0) (hbc : p1Bracket b c ≠ 0) (hcd : p1Bracket c d ≠ 0) :
    crossRatio a b c d ≠ 0 := by
  have hda : p1Bracket d a ≠ 0 := by rw [p1Bracket_swap]; exact neg_ne_zero.mpr had
  exact div_ne_zero (mul_ne_zero hda hbc) (crossRatio_den_ne_zero hab hcd)

/-- The formula `1 - cr(a, b, c, d) = [b, d][a, c] / ([b, a][d, c])`. -/
theorem one_sub_crossRatio {a b c d : Fin 2 → K} (hab : p1Bracket a b ≠ 0)
    (hcd : p1Bracket c d ≠ 0) :
    1 - crossRatio a b c d = p1Bracket b d * p1Bracket a c / (p1Bracket b a * p1Bracket d c) := by
  have hD := crossRatio_den_ne_zero hab hcd
  rw [crossRatio, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, one_mul]
  simp only [p1Bracket]; ring

/-- The cross-ratio of four distinct points is not `1`. -/
theorem crossRatio_ne_one {a b c d : Fin 2 → K} (hab : p1Bracket a b ≠ 0)
    (hac : p1Bracket a c ≠ 0) (hbd : p1Bracket b d ≠ 0) (hcd : p1Bracket c d ≠ 0) :
    crossRatio a b c d ≠ 1 := by
  intro h
  have h1 := one_sub_crossRatio hab hcd
  rw [h, sub_self] at h1
  exact div_ne_zero (mul_ne_zero hbd hac) (crossRatio_den_ne_zero hab hcd) h1.symm

/-- Four distinct points are moved by an element `M` of `GL₂(K)` to `0, 1, ∞, λ`, where `λ` is
their cross-ratio. -/
theorem exists_mulVec_std {a b c d : Fin 2 → K} (hab : p1Bracket a b ≠ 0)
    (hac : p1Bracket a c ≠ 0) (_had : p1Bracket a d ≠ 0) (hbc : p1Bracket b c ≠ 0)
    (hcd : p1Bracket c d ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 2) K, M.det ≠ 0 ∧
      ∃ s : Fin 4 → K, (∀ i, s i ≠ 0) ∧ M.mulVec a = s 0 • ![0, 1] ∧
        M.mulVec b = s 1 • ![1, 1] ∧ M.mulVec c = s 2 • ![1, 0] ∧
        M.mulVec d = s 3 • ![crossRatio a b c d, 1] := by
  have hba : p1Bracket b a ≠ 0 := by rw [p1Bracket_swap]; exact neg_ne_zero.mpr hab
  have hca : p1Bracket c a ≠ 0 := by rw [p1Bracket_swap]; exact neg_ne_zero.mpr hac
  have hdc : p1Bracket d c ≠ 0 := by rw [p1Bracket_swap]; exact neg_ne_zero.mpr hcd
  refine ⟨!![p1Bracket b c * a 1, -(p1Bracket b c * a 0);
    p1Bracket b a * c 1, -(p1Bracket b a * c 0)], ?_,
    ![p1Bracket b a * p1Bracket a c, p1Bracket b c * p1Bracket b a,
      p1Bracket b c * p1Bracket c a, p1Bracket b a * p1Bracket d c], ?_, ?_, ?_, ?_, ?_⟩
  · have : (!![p1Bracket b c * a 1, -(p1Bracket b c * a 0);
        p1Bracket b a * c 1, -(p1Bracket b a * c 0)]).det =
        p1Bracket b c * p1Bracket b a * p1Bracket a c := by
      rw [Matrix.det_fin_two_of]; simp only [p1Bracket]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hbc hba) hac
  · intro i
    fin_cases i <;> simp [hba, hac, hbc, hca, hdc]
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, p1Bracket] <;> ring
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, p1Bracket] <;> ring
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, p1Bracket] <;> ring
  · have hs : p1Bracket b a * p1Bracket d c * crossRatio a b c d =
        p1Bracket d a * p1Bracket b c := mul_div_cancel₀ _ (mul_ne_zero hba hdc)
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [p1Bracket] at hs ⊢
      linear_combination -hs
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, p1Bracket]
      ring

theorem mulVec_inv_mulVec {M : Matrix (Fin 2) (Fin 2) K} (hM : M.det ≠ 0) (v : Fin 2 → K) :
    M⁻¹.mulVec (M.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM),
    Matrix.one_mulVec]

/-- Two quadruples of distinct points with the same cross-ratio are in the same orbit of
`PGL₂(K)`: some `M` in `GL₂(K)` maps each point of the first to a nonzero multiple of the
corresponding point of the second. -/
theorem exists_mulVec_of_crossRatio_eq {a b c d a' b' c' d' : Fin 2 → K}
    (hab : p1Bracket a b ≠ 0) (hac : p1Bracket a c ≠ 0) (had : p1Bracket a d ≠ 0)
    (hbc : p1Bracket b c ≠ 0) (hcd : p1Bracket c d ≠ 0)
    (hab' : p1Bracket a' b' ≠ 0) (hac' : p1Bracket a' c' ≠ 0) (had' : p1Bracket a' d' ≠ 0)
    (hbc' : p1Bracket b' c' ≠ 0) (hcd' : p1Bracket c' d' ≠ 0)
    (h : crossRatio a b c d = crossRatio a' b' c' d') :
    ∃ M : Matrix (Fin 2) (Fin 2) K, M.det ≠ 0 ∧ ∃ r : Fin 4 → K, (∀ i, r i ≠ 0) ∧
      M.mulVec a = r 0 • a' ∧ M.mulVec b = r 1 • b' ∧ M.mulVec c = r 2 • c' ∧
        M.mulVec d = r 3 • d' := by
  obtain ⟨M, hM, s, hs, ha, hb, hc, hd⟩ := exists_mulVec_std hab hac had hbc hcd
  obtain ⟨N, hN, t, ht, ha', hb', hc', hd'⟩ := exists_mulVec_std hab' hac' had' hbc' hcd'
  have key : ∀ (x y e : Fin 2 → K) (i : Fin 4), M.mulVec x = s i • e →
      N.mulVec y = t i • e → (N⁻¹ * M).mulVec x = (s i / t i) • y := by
    intro x y e i hx hy
    have he : e = N.mulVec ((t i)⁻¹ • y) := by
      rw [Matrix.mulVec_smul, hy, smul_smul, inv_mul_cancel₀ (ht i), one_smul]
    rw [← Matrix.mulVec_mulVec, hx, he, Matrix.mulVec_smul, mulVec_inv_mulVec hN, smul_smul,
      div_eq_mul_inv]
  refine ⟨N⁻¹ * M, ?_, fun i => s i / t i, fun i => div_ne_zero (hs i) (ht i),
    key a a' _ 0 ha ha', key b b' _ 1 hb hb', key c c' _ 2 hc hc', key d d' _ 3 hd (h ▸ hd')⟩
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero (inv_ne_zero hN) hM

/-- The transposition of the first two points maps the cross-ratio `λ` to `1 - λ`. -/
theorem crossRatio_swap_zero_one {a b c d : Fin 2 → K} (hab : p1Bracket a b ≠ 0)
    (hcd : p1Bracket c d ≠ 0) : crossRatio b a c d = 1 - crossRatio a b c d := by
  rw [one_sub_crossRatio hab hcd, crossRatio, p1Bracket_swap d b, p1Bracket_swap a b,
    neg_mul, neg_mul, neg_div_neg_eq]

/-- The transposition of the first and the third point maps the cross-ratio `λ` to `λ⁻¹`. -/
theorem crossRatio_swap_zero_two (a b c d : Fin 2 → K) :
    crossRatio c b a d = (crossRatio a b c d)⁻¹ := by
  rw [crossRatio, crossRatio, inv_div, mul_comm (p1Bracket d c), mul_comm (p1Bracket b c)]

/-- The transposition of the first and the fourth point maps the cross-ratio `λ` to
`1 - (1 - λ)⁻¹`, that is to `λ / (λ - 1)`. -/
theorem crossRatio_swap_zero_three {a b c d : Fin 2 → K} (hab : p1Bracket a b ≠ 0)
    (hac : p1Bracket a c ≠ 0) (hbd : p1Bracket b d ≠ 0) (hcd : p1Bracket c d ≠ 0) :
    crossRatio d b c a = 1 - (1 - crossRatio a b c d)⁻¹ := by
  have hD : p1Bracket b d * p1Bracket a c ≠ 0 := mul_ne_zero hbd hac
  rw [one_sub_crossRatio hab hcd, inv_div, crossRatio, eq_sub_iff_add_eq, ← add_div,
    div_eq_one_iff_eq hD]
  simp only [p1Bracket]; ring

/-- The Klein four-group fixes the cross-ratio: the double transposition `(01)(23)`. -/
theorem crossRatio_klein_one (a b c d : Fin 2 → K) :
    crossRatio b a d c = crossRatio a b c d := by
  simp only [crossRatio, p1Bracket]; congr 1 <;> ring

/-- The Klein four-group fixes the cross-ratio: the double transposition `(02)(13)`. -/
theorem crossRatio_klein_two (a b c d : Fin 2 → K) :
    crossRatio c d a b = crossRatio a b c d := by
  simp only [crossRatio, p1Bracket]; congr 1 <;> ring

/-- The Klein four-group fixes the cross-ratio: the double transposition `(03)(12)`. -/
theorem crossRatio_klein_three (a b c d : Fin 2 → K) :
    crossRatio d c b a = crossRatio a b c d := by
  simp only [crossRatio, p1Bracket]; congr 1 <;> ring

/-- The orbit `{λ, 1 - λ, λ⁻¹, (1 - λ)⁻¹, λ / (λ - 1), (λ - 1) / λ}` of the cross-ratio under the
permutations of the four points. -/
def crossRatioOrbit (x : K) : Set K := {x, 1 - x, x⁻¹, (1 - x)⁻¹, x / (x - 1), (x - 1) / x}

/-- For `λ ≠ 0, 1`, the orbit of `λ` is closed under `y ↦ 1 - y` and `y ↦ y⁻¹`. -/
theorem crossRatioOrbit_closed {x y : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hy : y ∈ crossRatioOrbit x) : 1 - y ∈ crossRatioOrbit x ∧ y⁻¹ ∈ crossRatioOrbit x := by
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have h2 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [crossRatioOrbit, Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨Or.inl (by ring), Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))), Or.inl (inv_inv _)⟩
    field_simp
  · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))), Or.inr (Or.inl (inv_inv _))⟩
    field_simp; try ring
  · refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ?_))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
    · field_simp; try ring
    · rw [inv_div]
  · refine ⟨Or.inr (Or.inr (Or.inl ?_)), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
    · field_simp; try ring
    · rw [inv_div]

/-- A transposition of the four points maps the cross-ratio `λ` to `1 - λ`, to `λ⁻¹` or to
`1 - (1 - λ)⁻¹`. -/
theorem crossRatio_comp_swap (q : Fin 4 → Fin 2 → K)
    (hq : ∀ i j, i ≠ j → p1Bracket (q i) (q j) ≠ 0) (x y : Fin 4) (hxy : x ≠ y) :
    crossRatio (q (Equiv.swap x y 0)) (q (Equiv.swap x y 1)) (q (Equiv.swap x y 2))
        (q (Equiv.swap x y 3)) = 1 - crossRatio (q 0) (q 1) (q 2) (q 3) ∨
      crossRatio (q (Equiv.swap x y 0)) (q (Equiv.swap x y 1)) (q (Equiv.swap x y 2))
        (q (Equiv.swap x y 3)) = (crossRatio (q 0) (q 1) (q 2) (q 3))⁻¹ ∨
      crossRatio (q (Equiv.swap x y 0)) (q (Equiv.swap x y 1)) (q (Equiv.swap x y 2))
        (q (Equiv.swap x y 3)) = 1 - (1 - crossRatio (q 0) (q 1) (q 2) (q 3))⁻¹ := by
  have s01 := crossRatio_swap_zero_one (hq 0 1 (by decide)) (hq 2 3 (by decide))
  have s02 := crossRatio_swap_zero_two (q 0) (q 1) (q 2) (q 3)
  have s03 := crossRatio_swap_zero_three (hq 0 1 (by decide)) (hq 0 2 (by decide))
    (hq 1 3 (by decide)) (hq 2 3 (by decide))
  have s12 : crossRatio (q 0) (q 2) (q 1) (q 3) = crossRatio (q 3) (q 1) (q 2) (q 0) :=
    (crossRatio_klein_three _ _ _ _).symm
  have s13 : crossRatio (q 0) (q 3) (q 2) (q 1) = crossRatio (q 2) (q 1) (q 0) (q 3) :=
    (crossRatio_klein_two _ _ _ _).symm
  have s23 : crossRatio (q 0) (q 1) (q 3) (q 2) = crossRatio (q 1) (q 0) (q 2) (q 3) :=
    (crossRatio_klein_one _ _ _ _).symm
  fin_cases x <;> fin_cases y <;> simp (config := { decide := true }) only [Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk, Equiv.swap_apply_def, ite_true, ite_false] at hxy ⊢
  all_goals first
    | exact Or.inl s01
    | exact Or.inr (Or.inl s02)
    | exact Or.inr (Or.inr s03)
    | exact Or.inr (Or.inr (s12.trans s03))
    | exact Or.inr (Or.inl (s13.trans s02))
    | exact Or.inl (s23.trans s01)

/-- The action of the permutation group on the cross-ratio. For four distinct points and each
permutation `σ`, the cross-ratio of the permuted points lies in the orbit
`{λ, 1 - λ, λ⁻¹, (1 - λ)⁻¹, λ / (λ - 1), (λ - 1) / λ}` of the cross-ratio `λ`. -/
theorem crossRatio_comp_perm_mem (p : Fin 4 → Fin 2 → K)
    (hp : ∀ i j, i ≠ j → p1Bracket (p i) (p j) ≠ 0) (σ : Equiv.Perm (Fin 4)) :
    crossRatio (p (σ 0)) (p (σ 1)) (p (σ 2)) (p (σ 3)) ∈
      crossRatioOrbit (crossRatio (p 0) (p 1) (p 2) (p 3)) := by
  have hc0 := crossRatio_ne_zero (hp 0 1 (by decide)) (hp 0 3 (by decide))
    (hp 1 2 (by decide)) (hp 2 3 (by decide))
  have hc1 := crossRatio_ne_one (hp 0 1 (by decide)) (hp 0 2 (by decide))
    (hp 1 3 (by decide)) (hp 2 3 (by decide))
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => exact Or.inl rfl
  | mul_swap f x y hxy ih =>
    have hq : ∀ i j, i ≠ j → p1Bracket (p (f i)) (p (f j)) ≠ 0 :=
      fun i j h => hp _ _ (f.injective.ne h)
    have hcl := crossRatioOrbit_closed hc0 hc1 ih
    simp only [Equiv.Perm.mul_apply]
    rcases crossRatio_comp_swap (fun i => p (f i)) hq x y hxy with h | h | h
    · exact h ▸ hcl.1
    · exact h ▸ hcl.2
    · exact h ▸ (crossRatioOrbit_closed hc0 hc1 (crossRatioOrbit_closed hc0 hc1 hcl.1).2).1

end CrossRatio

/-! ### Lemmas 2.3.3 and 2.3.4, general position over an infinite field -/

section GeneralPosition

variable {K : Type*} [Field K]

/-- Over an infinite field, a vector space is not a finite union of proper subspaces. -/
theorem exists_forall_notMem_of_ne_top [Infinite K] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} (s : Finset ι) (W : ι → Submodule K V) (hW : ∀ i ∈ s, W i ≠ ⊤) :
    ∃ v : V, ∀ i ∈ s, v ∉ W i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨v, hv⟩ := ih (fun i hi => hW i (Finset.mem_insert_of_mem hi))
    obtain ⟨w, hw⟩ : ∃ w, w ∉ W a := by
      by_contra h
      push Not at h
      exact hW a (Finset.mem_insert_self a s) (eq_top_iff.mpr fun x _ => h x)
    by_cases hva : v ∈ W a
    swap
    · exact ⟨v, fun i hi => (Finset.mem_insert.mp hi).elim (fun h => h ▸ hva) (hv i)⟩
    have key : ∀ i ∈ s, {t : K | v + t • w ∈ W i}.Subsingleton := by
      intro i hi t ht t' ht'
      by_contra hne
      have h1 : (t - t') • w ∈ W i := by
        have := (W i).sub_mem ht ht'
        rwa [add_sub_add_left_eq_sub, ← sub_smul] at this
      have hwi : w ∈ W i := ((W i).smul_mem_iff (sub_ne_zero.mpr hne)).mp h1
      apply hv i hi
      have := (W i).sub_mem ht ((W i).smul_mem t hwi)
      rwa [add_sub_cancel_right] at this
    have hfin : ((⋃ i ∈ s, {t : K | v + t • w ∈ W i}) ∪ {0}).Finite :=
      (Set.Finite.biUnion s.finite_toSet fun i hi => (key i hi).finite).union
        (Set.finite_singleton 0)
    obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, not_or, not_exists] at ht
    refine ⟨v + t • w, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · intro h
      have := (W i).sub_mem h hva
      rw [add_sub_cancel_left] at this
      exact hw (((W i).smul_mem_iff ht.2).mp this)
    · exact ht.1 i hi

/-- Over an infinite field, a general linear form on `K^σ` is injective on a given finite set.
So a general linear projection to a line separates finitely many given points. -/
theorem exists_injOn_linear [Infinite K] {σ : Type*} [Fintype σ] (S : Finset (σ → K)) :
    ∃ l : σ → K, Set.InjOn (fun x : σ → K => ∑ i, l i * x i) S := by
  classical
  let L : (σ → K) × (σ → K) → (σ → K) →ₗ[K] K := fun p =>
    { toFun := fun l => ∑ i, l i * (p.1 i - p.2 i)
      map_add' := fun l l' => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r l => by simp [Finset.mul_sum, mul_assoc] }
  obtain ⟨l, hl⟩ := exists_forall_notMem_of_ne_top S.offDiag (fun p => LinearMap.ker (L p))
    (by
      rintro ⟨x, y⟩ hxy htop
      obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hxy
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have hmem : Pi.single j 1 ∈ LinearMap.ker (L (x, y)) := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at hmem
      simp [L, Pi.single_apply] at hmem
      exact hj (sub_eq_zero.mp hmem))
  refine ⟨l, fun x hx y hy hxy => ?_⟩
  by_contra hne
  apply hl (x, y) (Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩)
  rw [LinearMap.mem_ker]
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk, mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr hxy

/-- Over an infinite field, a finite union of zero sets of nonzero polynomials is not all of
`K^σ`. -/
theorem exists_forall_eval_ne_zero [Infinite K] {σ ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K) (hf : ∀ i ∈ s, f i ≠ 0) :
    ∃ x : σ → K, ∀ i ∈ s, MvPolynomial.eval x (f i) ≠ 0 := by
  classical
  have hP : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr hf
  by_contra h
  push Not at h
  apply hP
  apply MvPolynomial.funext
  intro x
  obtain ⟨i, hi, h0⟩ := h x
  rw [map_prod, map_zero]
  exact Finset.prod_eq_zero hi h0

theorem eval_aeval_line {σ : Type*} (p v : σ → K) (f : MvPolynomial σ K) (t : K) :
    (MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X)
      f).eval t = MvPolynomial.eval (fun i => p i + t * v i) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf => simp [hf, mul_comm (v i) t]

/-- If `f(p) ≠ 0`, then the line through `p` with direction `v` meets the zero set of `f` in
finitely many points. -/
theorem finite_setOf_eval_line_eq_zero {σ : Type*} (f : MvPolynomial σ K) (p v : σ → K)
    (hp : MvPolynomial.eval p f ≠ 0) :
    {t : K | MvPolynomial.eval (fun i => p i + t * v i) f = 0}.Finite := by
  set g := MvPolynomial.aeval
    (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f with hg
  have hg0 : g ≠ 0 := by
    intro h
    apply hp
    have := eval_aeval_line p v f 0
    rw [← hg, h, Polynomial.eval_zero] at this
    simpa using this.symm
  refine (Polynomial.finite_setOfPred_isRoot hg0).subset fun t ht => ?_
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def] at ht ⊢
  rw [hg, eval_aeval_line, ht]

/-- A separable polynomial of degree at least `n` that splits in `L` has at least `n` roots in
`L`. With `n = 3`: a hyperplane that meets a curve of degree at least `3` transversally meets it
in at least `3` distinct points. -/
theorem le_card_rootSet_of_separable {F L : Type*} [Field F] [Field L] [Algebra F L]
    {q : Polynomial F} (hsep : q.Separable) (hsplit : (q.map (algebraMap F L)).Splits)
    {n : ℕ} (hn : n ≤ q.natDegree) : n ≤ Fintype.card (q.rootSet L) := by
  rw [Polynomial.card_rootSet_eq_natDegree hsep hsplit]
  exact hn

end GeneralPosition

/-! ### Remark 2.1.4 of Volume 4, the easy direction -/

section RationalRemark

open AlgebraicGeometry CategoryTheory

universe u

/-- Remark 2.1.4 of Volume 4, the easy direction. If `X` has rational singularities, then
`R¹ f_* O_Y = 0` for each resolution `f : Y → X`, since a resolution is a normal modification.
-/
theorem r1PushforwardVanishes_of_hasRationalSingularities {X Y : Scheme.{u}}
    (hX : HasRationalSingularities X) {f : Y ⟶ X} (hf : IsNormalModification f) :
    R1PushforwardVanishes f :=
  hX Y f hf

/-- Remark 2.1.4 of Volume 4, the easy direction for a ring. If `A` has a rational singularity,
then `R¹ f_* O_Y = 0` for each resolution `f : Y → Spec A`. -/
theorem r1PushforwardVanishes_of_isRationalSingularity {A : Type u} [CommRing A]
    (hA : IsRationalSingularity A) {Y : Scheme.{u}} {f : Y ⟶ Spec (CommRingCat.of A)}
    (hf : IsNormalModification f) : R1PushforwardVanishes f :=
  hA Y f hf

end RationalRemark

end Singularity
