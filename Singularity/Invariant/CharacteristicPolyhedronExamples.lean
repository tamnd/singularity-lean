/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.CharacteristicPolyhedronClean
import Singularity.Invariant.Tschirnhausen
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Algebra.Field.ZMod

/-!
# Tschirnhausen, purely inseparable equations, and the examples of Section 3.1

This file proves algebraic parts of Section 3.1 of Volume 6 of the handbook. The setting is the
one of `Singularity.charPolyhedron`: a polynomial `f` in `z` over `k[[x]]`.

## Main results

* Corollary 3.1.6, the first two claims. Let `f` be monic of degree `m ≥ 1`, and let `m` be a unit
  in `k`. After `z ↦ z - f_{m-1}/m`, the coefficient of `z^(m-1)` is `0`
  (`coeff_pred_taylor_tschirnhausen`), and then no vertex is solvable
  (`not_isSolvableVertex_of_coeff_pred_eq_zero`, `tschirnhausen_not_isSolvableVertex`). The last
  claim of the corollary, that the polyhedron is then the characteristic polyhedron, uses the hard
  direction of Theorem 3.1.5(2). It is not proved here.
* Lemma 3.1.10(2). In characteristic `p`, the vertex `v` of `z^p + F` is solvable with the constant
  `c` exactly when the coefficient of `x^(p v)` in `F` is `c^p`
  (`isSolvableVertex_X_pow_add_C_iff`).
  Part 3 of the lemma is `taylor_X_pow_add_C`.
* A criterion (`charPolyhedron_X_pow_add_C_of_forall`): if no `φ^p` can cancel a monomial of `F`,
  then `z` attains the characteristic polyhedron of `z^p + F`. This is the direct argument at the
  end of Example 3.1.11.
* Example 3.1.7: in characteristic `2`, `z ↦ z + x` sends `z^2 + x^2 + y^3` to `z^2 + y^3`, and
  the characteristic polyhedron is `(0, 3/2) + ℝ_{≥0}^2`.
* Example 3.1.8: the identity `θ^2 (1 + x^2) = x^2` for `θ (1 + x) = x` in characteristic `2`, and
  the one step translation.
* Example 3.1.9: the expansions of `(z + 6)^3 - 54` and `(z - 3)^3 - 54` and the `3`-adic orders of
  their coefficients.
* Example 3.1.11: for `F = t x^p + y^(p+1)` with `t` not a `p`-th power, the vertex `(1, 0)` is not
  solvable, and `z` attains the characteristic polyhedron. The element `t = X` of `𝔽_p(X)` is not a
  `p`-th power.
-/

open Polynomial Pointwise

namespace Singularity

variable {σ k : Type*}

/-! ### Corollary 3.1.6 -/

section Tschirnhausen

/-- For a monic `f` of degree `m ≥ 1`, the coefficient of `z^(m-1)` in `f(z + d)` is
`f_{m-1} + m d`. -/
theorem coeff_pred_taylor_of_monic {A : Type*} [CommRing A] {f : A[X]} (hf : f.Monic)
    (hm : 1 ≤ f.natDegree) (d : A) :
    (taylor d f).coeff (f.natDegree - 1) = f.coeff (f.natDegree - 1) + f.natDegree * d := by
  have h := coeff_pred_X_add_C hm f.coeff d
  rw [← coeff_taylor_X_pow_add_sum, ← hf.as_sum] at h
  exact h

/-- The Tschirnhausen translation. Let `f` be monic of degree `m ≥ 1`, and let `u` be an inverse
of `m`. Then the coefficient of `z^(m-1)` in `f(z - f_{m-1} u)` is `0`. Volume 6,
Corollary 3.1.6 of the handbook, the claim `f_{1, Z} = 0`. -/
theorem coeff_pred_taylor_tschirnhausen {A : Type*} [CommRing A] {f : A[X]} (hf : f.Monic)
    (hm : 1 ≤ f.natDegree) {u : A} (hu : (f.natDegree : A) * u = 1) :
    (taylor (-(f.coeff (f.natDegree - 1) * u)) f).coeff (f.natDegree - 1) = 0 := by
  rw [coeff_pred_taylor_of_monic hf hm]
  linear_combination (-(f.coeff (f.natDegree - 1))) * hu

/-- If the degree `m ≥ 1` of `f` is a unit in `k` and the coefficient of `z^(m-1)` is `0`, then no
vertex of `Δ(f; x; z)` is solvable. The coefficient of `Z^(m-1)` in `(Z + c)^m` is `m c`, and in
the initial polynomial it is `0`. So `c = 0`, and the initial polynomial is not `Z^m`. Volume 6,
Corollary 3.1.6 of the handbook, the claim that `Δ(h; u; Z)` has no solvable vertex. -/
theorem not_isSolvableVertex_of_coeff_pred_eq_zero [CommRing k] {f : (MvPowerSeries σ k)[X]}
    (hm : 1 ≤ f.natDegree) (hunit : IsUnit (f.natDegree : k))
    (h1 : f.coeff (f.natDegree - 1) = 0) {v : σ →₀ ℕ}
    (hv : expToReal v ∈ (projPolyhedron f).extremePoints ℝ) (c : k) :
    ¬ IsSolvableVertex f v c := by
  intro hs
  have hs' : vertexPoly f v = (X + C c) ^ f.natDegree := hs
  obtain ⟨n, hn⟩ : ∃ n, f.natDegree = n + 1 := ⟨f.natDegree - 1, by omega⟩
  rw [hn, Nat.add_sub_cancel] at h1
  rw [hn] at hunit
  have hc : (vertexPoly f v).coeff n = ((X + C c) ^ f.natDegree).coeff n := by rw [hs']
  rw [coeff_vertexPoly, hn, if_pos (Nat.le_add_right n 1), h1, map_zero, coeff_X_add_C_pow,
    Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right] at hc
  have hc0 : c = 0 := (hunit.mul_left_eq_zero).mp hc.symm
  rw [hc0, map_zero, add_zero] at hs'
  exact vertexPoly_ne_X_pow hv hs'

/-- Corollary 3.1.6, the first two claims together. Let `f` be monic of degree `m ≥ 1` over
`k[[x]]`, and let `u` be an inverse of `m` in `k`. Let `g = f(z - f_{m-1} u)`. Then no vertex of
`Δ(g; x; z)` is solvable. Volume 6, Corollary 3.1.6 of the handbook. The last claim, that
`Δ(g; x; z)` is the characteristic polyhedron, is not proved. -/
theorem tschirnhausen_not_isSolvableVertex [CommRing k] {f : (MvPowerSeries σ k)[X]}
    (hf : f.Monic) (hm : 1 ≤ f.natDegree) {u : k} (hu : (f.natDegree : k) * u = 1)
    {v : σ →₀ ℕ}
    (hv : expToReal v ∈ (projPolyhedron
      (taylor (-(f.coeff (f.natDegree - 1) * MvPowerSeries.C u)) f)).extremePoints ℝ) (c : k) :
    ¬ IsSolvableVertex (taylor (-(f.coeff (f.natDegree - 1) * MvPowerSeries.C u)) f) v c := by
  have hu' : (f.natDegree : MvPowerSeries σ k) * MvPowerSeries.C u = 1 := by
    rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := k)) f.natDegree, ← map_mul, hu, map_one]
  have h0 := coeff_pred_taylor_tschirnhausen hf hm hu'
  refine not_isSolvableVertex_of_coeff_pred_eq_zero ?_ ?_ ?_ hv c
  · rw [natDegree_taylor]
    exact hm
  · rw [natDegree_taylor]
    exact IsUnit.of_mul_eq_one _ hu
  · rw [natDegree_taylor]
    exact h0

end Tschirnhausen

/-! ### Lemma 3.1.10 -/

section Inseparable

/-- The initial polynomial of `z^n + F` at `v` is `Z^n + c`, where `c` is the coefficient of
`x^(n v)` in `F`. -/
theorem vertexPoly_X_pow_add_C [CommRing k] [Nontrivial k] {n : ℕ} (hn : 1 ≤ n)
    (F : MvPowerSeries σ k) (v : σ →₀ ℕ) :
    vertexPoly (X ^ n + C F) v = X ^ n + C (MvPowerSeries.coeff (n • v) F) := by
  ext d
  rw [coeff_vertexPoly, natDegree_X_pow_add_C]
  rcases eq_or_ne d n with hdn | hdn
  · rw [hdn]
    have hn0 : n ≠ 0 := by omega
    simp [coeff_X_pow, coeff_C, hn0, MvPowerSeries.coeff_one]
  · rcases eq_or_ne d 0 with rfl | hd0
    · simp [coeff_X_pow, coeff_C, hdn]
    · simp [coeff_X_pow, coeff_C, hdn, hd0]

variable [CommRing k] [Nontrivial k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- In characteristic `p`, the vertex `v` of `z^p + F` is solvable with the constant `c` exactly
when the coefficient of `x^(p v)` in `F` is `c^p`. Volume 6, Lemma 3.1.10(2) of the handbook. Here
the vertex is given as `v ∈ ℕ^σ`, so the condition `y ∈ ℕ^n` of the handbook is built in, and
the handbook writes `(Z - λ U^y)^p` where this file writes `(Z + c)^p`. -/
theorem isSolvableVertex_X_pow_add_C_iff (F : MvPowerSeries σ k) (v : σ →₀ ℕ) (c : k) :
    IsSolvableVertex (X ^ p + C F) v c ↔ MvPowerSeries.coeff (p • v) F = c ^ p := by
  rw [IsSolvableVertex, vertexPoly_X_pow_add_C (Fact.out : p.Prime).one_lt.le,
    natDegree_X_pow_add_C, add_pow_char, ← C_pow, add_right_inj, C_inj]

/-- In characteristic `p`, the coefficient of `x^(p α)` in `φ^p` is the `p`-th power of the
coefficient of `x^α` in `φ`. -/
theorem coeff_smul_pow_char (φ : MvPowerSeries σ k) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff (p • α) (φ ^ p) = MvPowerSeries.coeff α φ ^ p := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← MvPowerSeries.map_frobenius_expand p hp, MvPowerSeries.coeff_map,
    MvPowerSeries.coeff_expand_smul, frobenius_def]

/-- In characteristic `p`, if no `φ^p` cancels a monomial of `F`, then the coordinate `z`
attains the characteristic polyhedron of `z^p + F`. This is the direct argument at the end of
Volume 6, Example 3.1.11 of the handbook. -/
theorem charPolyhedron_X_pow_add_C_of_forall {F : MvPowerSeries σ k}
    (hF : ∀ (φ : MvPowerSeries σ k) (α : σ →₀ ℕ), MvPowerSeries.coeff α F ≠ 0 →
      MvPowerSeries.coeff α (φ ^ p + F) ≠ 0) :
    charPolyhedron (X ^ p + C F) = projPolyhedron (X ^ p + C F) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  refine subset_antisymm (charPolyhedron_subset_projPolyhedron _)
    (Set.subset_iInter₂ fun φ _ => ?_)
  have ht := taylor_X_pow_add_C p 1 φ F
  simp only [pow_one] at ht
  rw [ht, projPolyhedron, projPolyhedron, projPoints_X_pow_add_C hp1,
    projPoints_X_pow_add_C hp1]
  refine Set.add_subset_add (convexHull_mono ?_) subset_rfl
  rintro _ ⟨α, hα, rfl⟩
  exact ⟨α, hF φ α hα, rfl⟩

end Inseparable

/-! ### Example 3.1.7 and Example 3.1.8 -/

section CharTwo

variable [CommRing k] [CharP k 2]

theorem two_eq_zero_mvPowerSeries : (2 : MvPowerSeries σ k) = 0 := by
  rw [← map_ofNat (MvPowerSeries.C (σ := σ) (R := k)) 2, CharTwo.two_eq_zero, map_zero]

/-- In characteristic `2`, `z ↦ z + φ` sends `z^2 + (φ^2 + G)` to `z^2 + G`. Volume 6,
Examples 3.1.7 and 3.1.8 of the handbook, the translation step. -/
theorem taylor_X_sq_add_C_sq_add (φ G : MvPowerSeries σ k) :
    taylor φ (X ^ 2 + C (φ ^ 2 + G)) = X ^ 2 + C G := by
  have h := taylor_X_pow_add_C 2 1 φ (φ ^ 2 + G)
  simp only [pow_one] at h
  rw [h, show φ ^ 2 + (φ ^ 2 + G) = G by
    linear_combination φ ^ 2 * (two_eq_zero_mvPowerSeries (σ := σ) (k := k))]

/-- In characteristic `2`, `z ↦ z + x` sends `z^2 + x^2 + y^3` to `z^2 + y^3`. Volume 6,
Example 3.1.7 of the handbook, with `x, y = X 0, X 1`. -/
theorem taylor_example_3_1_7 :
    taylor (MvPowerSeries.X 0) (X ^ 2 + C (MvPowerSeries.X 0 ^ 2 + MvPowerSeries.X 1 ^ 3) :
      (MvPowerSeries (Fin 2) k)[X]) = X ^ 2 + C (MvPowerSeries.X 1 ^ 3) :=
  taylor_X_sq_add_C_sq_add _ _

/-- In characteristic `2`, the characteristic polyhedron of `z^2 + x^2 + y^3` is
`(1/2) N(y^3)`. Volume 6, Example 3.1.7 of the handbook. -/
theorem charPolyhedron_example_3_1_7 [Nontrivial k] :
    charPolyhedron (X ^ 2 + C (MvPowerSeries.X 0 ^ 2 + MvPowerSeries.X 1 ^ 3) :
      (MvPowerSeries (Fin 2) k)[X]) =
      (2 : ℝ)⁻¹ • newtonPolyhedron (MvPolynomial.X 1 ^ 3 : MvPolynomial (Fin 2) k) := by
  have hclean : IsClean (2 ^ 1) (MvPolynomial.X 1 ^ 3 : MvPolynomial (Fin 2) k) := by
    intro d hd hall
    rw [MvPolynomial.support_X_pow, Finset.mem_singleton] at hd
    subst hd
    have h1 := hall 1
    rw [Finsupp.single_eq_same] at h1
    exact absurd h1 (by decide)
  have hcoe : (MvPowerSeries.X 1 ^ 3 : MvPowerSeries (Fin 2) k) =
      ((MvPolynomial.X 1 ^ 3 : MvPolynomial (Fin 2) k) : MvPowerSeries (Fin 2) k) := by
    rw [MvPolynomial.coe_pow, MvPolynomial.coe_X]
  have h := charPolyhedron_X_pow_add_C_eq_smul_newtonPolyhedron 2 1 hclean
  simp only [pow_one, Nat.cast_ofNat] at h
  rw [← charPolyhedron_taylor _ (MvPowerSeries.constantCoeff_X (R := k) (0 : Fin 2)),
    taylor_example_3_1_7, hcoe, h]

/-- In characteristic `2`, the characteristic polyhedron of `z^2 + x^2 + y^3` is
`(0, 3/2) + ℝ_{≥0}^2`. Volume 6, Example 3.1.7 of the handbook. -/
theorem charPolyhedron_example_3_1_7_eq [Nontrivial k] :
    charPolyhedron (X ^ 2 + C (MvPowerSeries.X 0 ^ 2 + MvPowerSeries.X 1 ^ 3) :
      (MvPowerSeries (Fin 2) k)[X]) =
      {(2 : ℝ)⁻¹ • expToReal (Finsupp.single (1 : Fin 2) 3)} + orthant (Fin 2) := by
  rw [charPolyhedron_example_3_1_7, MvPolynomial.X_pow_eq_monomial,
    newtonPolyhedron_monomial one_ne_zero, smul_add, Set.smul_set_singleton,
    smul_orthant (c := (2 : ℝ)⁻¹) (by norm_num)]

/-- In characteristic `2`, `θ (1 + x) = x` gives `θ^2 (1 + x^2) = x^2`. Volume 6, Example 3.1.8 of
the handbook, the identity `θ^2 = x^2/(1 + x^2)`. -/
theorem sq_mul_one_add_sq_of_mul_one_add {R : Type*} [CommRing R] [CharP R 2] {x θ : R}
    (h : θ * (1 + x) = x) : θ ^ 2 * (1 + x ^ 2) = x ^ 2 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination (θ * (1 + x) + x) * h - x * θ ^ 2 * h2

end CharTwo

/-! ### Example 3.1.9 -/

section Mixed

/-- `(z + 6)^3 - 54 = z^3 + 18 z^2 + 108 z + 162`. Volume 6, Example 3.1.9 of the handbook. -/
theorem example_3_1_9_expand :
    ((X + 6) ^ 3 - 54 : ℤ[X]) = X ^ 3 + 18 * X ^ 2 + 108 * X + 162 := by
  ring

/-- `(z - 3)^3 - 54 = z^3 - 9 z^2 + 27 z - 81`. Volume 6, Example 3.1.9 of the handbook. -/
theorem example_3_1_9_expand' :
    ((X - 3) ^ 3 - 54 : ℤ[X]) = X ^ 3 - 9 * X ^ 2 + 27 * X - 81 := by
  ring

/-- The `3`-adic orders of `54`, `18`, `108`, `162`, `9`, `27`, `81` are `3`, `2`, `3`, `4`, `2`,
`3`, `4`. Volume 6, Example 3.1.9 of the handbook. -/
theorem example_3_1_9_orders :
    (3 ^ 3 ∣ (54 : ℕ) ∧ ¬ 3 ^ 4 ∣ (54 : ℕ)) ∧ (3 ^ 2 ∣ (18 : ℕ) ∧ ¬ 3 ^ 3 ∣ (18 : ℕ)) ∧
      (3 ^ 3 ∣ (108 : ℕ) ∧ ¬ 3 ^ 4 ∣ (108 : ℕ)) ∧ (3 ^ 4 ∣ (162 : ℕ) ∧ ¬ 3 ^ 5 ∣ (162 : ℕ)) ∧
      (3 ^ 2 ∣ (9 : ℕ) ∧ ¬ 3 ^ 3 ∣ (9 : ℕ)) ∧ (3 ^ 3 ∣ (27 : ℕ) ∧ ¬ 3 ^ 4 ∣ (27 : ℕ)) ∧
      (3 ^ 4 ∣ (81 : ℕ) ∧ ¬ 3 ^ 5 ∣ (81 : ℕ)) := by
  decide

/-- The points `2/1`, `3/2`, `4/3` of Example 3.1.9 have the minimum `4/3`. Volume 6,
Example 3.1.9 of the handbook. -/
theorem example_3_1_9_min : min (min (2 : ℚ) (3 / 2)) (4 / 3) = 4 / 3 := by
  norm_num

end Mixed

/-! ### Example 3.1.11 -/

section Imperfect

variable [CommRing k] [Nontrivial k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The series `F = t x^p + y^(p+1)` of Example 3.1.11, with `x, y = X 0, X 1`. -/
noncomputable def imperfectF (t : k) : MvPowerSeries (Fin 2) k :=
  MvPowerSeries.monomial (Finsupp.single 0 p) t +
    MvPowerSeries.monomial (Finsupp.single 1 (p + 1)) 1

theorem coeff_imperfectF (t : k) (α : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff α (imperfectF p t) =
      (if α = Finsupp.single 0 p then t else 0) +
        (if α = Finsupp.single 1 (p + 1) then 1 else 0) := by
  rw [imperfectF, map_add, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]

theorem single_zero_ne_single_one :
    (Finsupp.single 0 p : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 (p + 1) := by
  intro h
  have h1 := DFunLike.congr_fun h 1
  simp [Finsupp.single_apply] at h1 <;> omega

theorem smul_single_zero_one : p • (Finsupp.single 0 1 : Fin 2 →₀ ℕ) = Finsupp.single 0 p := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- If `t` is not a `p`-th power in `k`, then the vertex `(1, 0)` of `z^p + t x^p + y^(p+1)` is not
solvable. Volume 6, Example 3.1.11 of the handbook. -/
theorem not_isSolvableVertex_imperfect {t : k} (ht : ∀ c : k, c ^ p ≠ t) (c : k) :
    ¬ IsSolvableVertex (X ^ p + C (imperfectF p t)) (Finsupp.single 0 1) c := by
  rw [isSolvableVertex_X_pow_add_C_iff p, smul_single_zero_one, coeff_imperfectF, if_pos rfl,
    if_neg (single_zero_ne_single_one p), add_zero]
  exact fun h => ht c h.symm

/-- If `t` is not a `p`-th power in `k`, then the coordinate `z` attains the characteristic
polyhedron of `z^p + t x^p + y^(p+1)`. Volume 6, Example 3.1.11 of the handbook. -/
theorem charPolyhedron_imperfect {t : k} (ht : ∀ c : k, c ^ p ≠ t) :
    charPolyhedron (X ^ p + C (imperfectF p t)) =
      projPolyhedron (X ^ p + C (imperfectF p t)) := by
  refine charPolyhedron_X_pow_add_C_of_forall p fun φ α hα => ?_
  rw [coeff_imperfectF] at hα
  rw [map_add, coeff_imperfectF]
  by_cases h0 : α = Finsupp.single 0 p
  · subst h0
    rw [if_pos rfl, if_neg (single_zero_ne_single_one p), add_zero, ← smul_single_zero_one p,
      coeff_smul_pow_char]
    intro h
    apply ht (-(MvPowerSeries.coeff (Finsupp.single 0 1) φ))
    rw [neg_pow, neg_one_pow_char]
    linear_combination -h
  · rw [if_neg h0, zero_add] at hα ⊢
    have h1 : α = Finsupp.single 1 (p + 1) := by
      by_contra h1
      rw [if_neg h1] at hα
      exact hα rfl
    subst h1
    have hd : ¬ ∀ i, p ^ 1 ∣ (Finsupp.single 1 (p + 1) : Fin 2 →₀ ℕ) i := by
      intro hall
      have h2 := hall 1
      rw [pow_one, Finsupp.single_eq_same] at h2
      have h3 := (Nat.dvd_add_right (dvd_refl p)).mp h2
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h3)
    have hz := coeff_pow_expChar_pow_eq_zero p 1 φ hd
    rw [pow_one] at hz
    rw [hz, zero_add, if_pos rfl]
    exact one_ne_zero

/-- The variable `X` of `K(X)` is not an `n`-th power for `n ≥ 2`, since its degree is `1`. -/
theorem ratFunc_pow_ne_X {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (g : RatFunc K) :
    g ^ n ≠ RatFunc.X := by
  intro h
  have hg : g ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at h
    exact RatFunc.X_ne_zero h.symm
  have hd : ∀ m : ℕ, RatFunc.intDegree (g ^ m) = m * RatFunc.intDegree g := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero m hg) hg, ih]
      push_cast
      ring
  have h1 := hd n
  rw [h, RatFunc.intDegree_X] at h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1.symm with h2 | h2 <;> omega

end Imperfect

/-- Over `k = 𝔽_p(t)`, the vertex `(1, 0)` of `z^p + t x^p + y^(p+1)` is not solvable, and the
coordinate `z` attains the characteristic polyhedron. Volume 6, Example 3.1.11 of the handbook. -/
theorem example_3_1_11 (p : ℕ) [Fact p.Prime] :
    (∀ c, ¬ IsSolvableVertex (X ^ p + C (imperfectF p (RatFunc.X : RatFunc (ZMod p))))
      (Finsupp.single 0 1) c) ∧
    charPolyhedron (X ^ p + C (imperfectF p (RatFunc.X : RatFunc (ZMod p)))) =
      projPolyhedron (X ^ p + C (imperfectF p (RatFunc.X : RatFunc (ZMod p)))) := by
  have ht : ∀ c : RatFunc (ZMod p), c ^ p ≠ RatFunc.X :=
    ratFunc_pow_ne_X (Fact.out : p.Prime).two_le
  exact ⟨not_isSolvableVertex_imperfect p ht, charPolyhedron_imperfect p ht⟩

end Singularity
