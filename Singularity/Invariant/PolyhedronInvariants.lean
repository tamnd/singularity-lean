/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.ProjPolyhedronWeight
import Singularity.Invariant.CharacteristicPolyhedronClean
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.CharP.Lemmas

/-!
# Initial forms and the invariants delta and epsilon of Cossart and Piltant

This file proves parts of Volume 6 of the handbook. The setting is the one of
`Singularity.Invariant.CharacteristicPolyhedron`. Here `f` is a polynomial of degree `m` in `z`
over `k[[x_i : i ∈ σ]]`, and `Δ(f; x; z)` is `projPolyhedron f`.

## Main definitions and results

* `weightPart`: the part `[g]_c` of a power series `g` of `w`-weight exactly `c`.
* `weightPart_mul`: the product rule `[g g']_(c + d) = [g]_c [g']_d` for `c ≤ μ_w(g)` and
  `d ≤ μ_w(g')`.
* `polyDelta`: the number `δ_w(f) = inf {|x|_w : x ∈ Δ(f; x; z)}`.
* `weightInitialForm`: the initial form `in_w f` of Volume 6, Definition 3.1.3.
* `initialFormAt_isHomogeneous`: `in_w f` is homogeneous of degree `m δ` if `z` has degree `δ`.
* `coeff_weightInitialForm_of_isUniqueMinimizer`: if `v` is the only point of `Δ(f; x; z)` where
  `|·|_w` is minimal, then `in_w f = z^m + ∑_i c_i x^(i v) z^(m-i)`. So `in_w f` does not depend
  on `w`, and it is the initial polynomial `vertexPoly f v` of the repository.
* `isSolvableVertex_iff_weightInitialForm`: the vertex `v` is solvable in the sense of the
  repository if and only if `in_w f = (z + c x^v)^m`, as in Definition 3.1.3.
* `IsMinimalCoord`, `charDelta`: minimal coordinates and the invariant `δ(x)` of
  Definition 3.2.1. The lemmas `charDelta_eq_polyDelta` and `charDelta_taylor` give the formula
  of Definition 3.2.1 and the independence of the choice of `z`.
* `isGreatest_polyDelta_taylor`: Proposition 3.2.2 (1), the maximum formula over the
  translations `z ↦ z + φ`.
* `polyDelta_pos_iff_of_isMinimalCoord`: the algebraic core of Proposition 3.2.2 (2). For minimal
  coordinates, `δ(x) > 0` if and only if `h mod m_S` is `(z + c)^m` for some `c ∈ k`.
* `one_le_polyDelta_iff_order`: the algebraic core of Proposition 3.2.2 (3). We have `δ ≥ 1` if
  and only if each monomial `x^a z^d` of `h` has `|a| + d ≥ m`.
* `divisorDelta`, `residualEpsilon`, `residualEpsilon_nonneg`: Definition 3.2.3 and `ε(x) ≥ 0`.
* `ex411_*`: Example 4.1.1. The coordinates are minimal, and `δ = (p + 1)/p`, `d_1 = d_2 = 0`,
  `ε = p + 1`, and the initial form is `U_1^p U_3` with `∂/∂U_3 ≠ 0`. The first blowup is a ring
  identity, and at the new point `δ = (p + 2)/p`, `d_1 = 0`, `d_2 = 1/p`, `ε = p + 1`, with the
  initial form `U_1^p U_2 U_3`.
* `ex127_*`: Example 1.2.7. The partial derivatives of `h = z^2 + x^3 + y^3 + w^3`, and its
  singular points (all partial derivatives and `h` vanish) when `2, 3 ≠ 0`, in characteristic 3,
  and in characteristic 2. In characteristic 3, `h = z^2 + (x + y + w)^3`, and `h` does not change
  under a translation by a point of the plane `x + y + w = 0`.

## What is not proved

* Definition 3.1.3: the existence of a weight `w` for which a given vertex is the only minimum
  point is not proved. It is a hypothesis of the vertex results.
* Definition 3.2.1 and Proposition 3.2.2: the existence of minimal coordinates (the theorem of
  Hironaka) is not proved. The independence of the regular system of parameters `u` is not
  proved. The translation between the fiber `η⁻¹(m_S)` and the polynomial `h mod m_S`, and
  between the multiplicity at `(m_S, z)` and the monomials of `h`, is not formalized. Only the
  statements about `δ` and the coefficients are proved.
* Definition 3.2.3: the identification of `d_j` with `δ` at the generic point of a component of
  the divisor is not proved.
* Example 4.1.1: the invariant `ω` is not defined here. We prove only the facts on the initial
  form and its derivative that give `ω`. The locus of multiplicity `p`, the arc, and the formula
  for `h_r` with `r ≥ 2` are not formalized.
* Corollary 4.3.2 is not formalized. It rests on Theorem 3.2.6, which has no proof in the
  handbook or in Lean.
* Example 1.2.7: the Jacobian criterion and the resolution by the coefficient ideal are not
  formalized. Singular points are defined by the vanishing of `h` and of its partial derivatives.
-/

open Polynomial Pointwise

namespace Singularity

/-! ### The weighted part and the initial form (Definition 3.1.3) -/

section InitialForm

variable {σ k : Type*} [CommRing k] [Fintype σ]

/-- The part `[g]_c` of a power series `g` of `w`-weight exactly `c`. -/
noncomputable def weightPart (w : σ → ℝ) (c : ℝ) (g : MvPowerSeries σ k) : MvPowerSeries σ k :=
  fun a => if linWeight w (expToReal a) = c then MvPowerSeries.coeff a g else 0

theorem coeff_weightPart (w : σ → ℝ) (c : ℝ) (g : MvPowerSeries σ k) (a : σ →₀ ℕ) :
    MvPowerSeries.coeff a (weightPart w c g) =
      if linWeight w (expToReal a) = c then MvPowerSeries.coeff a g else 0 := rfl

theorem linWeight_expToReal_add (w : σ → ℝ) (a b : σ →₀ ℕ) :
    linWeight w (expToReal (a + b)) = linWeight w (expToReal a) + linWeight w (expToReal b) := by
  rw [map_add]
  exact (isLinearMap_linWeight w).map_add _ _

omit [Fintype σ] in
theorem expToReal_injective : Function.Injective (expToReal : (σ →₀ ℕ) → σ → ℝ) := by
  intro a b h
  refine Finsupp.ext fun j => ?_
  have := congrFun h j
  simp only [expToReal_apply] at this
  exact_mod_cast this

/-- The product rule for the weighted part. If every monomial of `g` has weight at least `c`
and every monomial of `g'` has weight at least `d`, then `[g g']_(c + d) = [g]_c [g']_d`. -/
theorem weightPart_mul {w : σ → ℝ} {c d : ℝ} {g g' : MvPowerSeries σ k}
    (hg : ∀ a, MvPowerSeries.coeff a g ≠ 0 → c ≤ linWeight w (expToReal a))
    (hg' : ∀ a, MvPowerSeries.coeff a g' ≠ 0 → d ≤ linWeight w (expToReal a)) :
    weightPart w (c + d) (g * g') = weightPart w c g * weightPart w d g' := by
  classical
  ext a
  rw [coeff_weightPart, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  split_ifs with ha
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    rw [coeff_weightPart, coeff_weightPart]
    have hsum : linWeight w (expToReal x.1) + linWeight w (expToReal x.2) = c + d := by
      rw [← linWeight_expToReal_add, hx, ha]
    by_cases h1 : MvPowerSeries.coeff x.1 g = 0
    · simp [h1]
    by_cases h2 : MvPowerSeries.coeff x.2 g' = 0
    · simp [h2]
    have e1 := hg _ h1
    have e2 := hg' _ h2
    rw [ite_eq_left (by linarith), ite_eq_left (by linarith)]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_antidiagonal] at hx
    rw [coeff_weightPart, coeff_weightPart]
    by_cases h1 : MvPowerSeries.coeff x.1 g = 0
    · simp [h1]
    by_cases h2 : MvPowerSeries.coeff x.2 g' = 0
    · simp [h2]
    have e1 := hg _ h1
    have hsum : linWeight w (expToReal x.1) + linWeight w (expToReal x.2) =
        linWeight w (expToReal a) := by
      rw [← linWeight_expToReal_add, hx]
    rcases lt_or_eq_of_le e1 with h | h
    · rw [ite_eq_right (ne_of_gt h), zero_mul]
    · rw [ite_eq_left h.symm, ite_eq_right (fun h' => ha (by linarith)), mul_zero]

/-- The initial form `z^m + ∑_i [a_i]_(i δ) z^(m-i)` for the weight `w` and the number `δ`.
Here `a_i` is the coefficient of `z^(m-i)` in `f` and `m = f.natDegree`. -/
noncomputable def initialFormAt (w : σ → ℝ) (δ : ℝ) (f : (MvPowerSeries σ k)[X]) :
    (MvPowerSeries σ k)[X] :=
  X ^ f.natDegree + ∑ i ∈ Finset.Icc 1 f.natDegree,
    C (weightPart w (i * δ) (f.coeff (f.natDegree - i))) * X ^ (f.natDegree - i)

/-- The number `δ_w(f)`: the infimum of `|·|_w` on `Δ(f; x; z)`. -/
noncomputable def polyDelta (w : σ → ℝ) (f : (MvPowerSeries σ k)[X]) : ℝ :=
  sInf (linWeight w '' projPolyhedron f)

/-- Volume 6, Definition 3.1.3. The initial form `in_w f` of `f` for the weight `w`, with
`δ = δ_w(f)`. -/
noncomputable def weightInitialForm (w : σ → ℝ) (f : (MvPowerSeries σ k)[X]) :
    (MvPowerSeries σ k)[X] :=
  initialFormAt w (polyDelta w f) f

theorem coeff_initialFormAt_of_lt (w : σ → ℝ) (δ : ℝ) (f : (MvPowerSeries σ k)[X]) {d : ℕ}
    (hd : d < f.natDegree) :
    (initialFormAt w δ f).coeff d = weightPart w ((f.natDegree - d : ℕ) * δ) (f.coeff d) := by
  rw [initialFormAt, coeff_add, coeff_X_pow, ite_eq_right hd.ne, zero_add, finsetSum_coeff,
    Finset.sum_eq_single (f.natDegree - d)]
  · rw [coeff_C_mul_X_pow, ite_eq_left (by omega), Nat.sub_sub_self hd.le]
  · intro i hi hne
    rw [Finset.mem_Icc] at hi
    rw [coeff_C_mul_X_pow, ite_eq_right (by omega)]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) h

theorem coeff_initialFormAt_self (w : σ → ℝ) (δ : ℝ) (f : (MvPowerSeries σ k)[X]) :
    (initialFormAt w δ f).coeff f.natDegree = 1 := by
  rw [initialFormAt, coeff_add, coeff_X_pow, ite_eq_left rfl, finsetSum_coeff,
    Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [coeff_C_mul_X_pow, ite_eq_right (by omega)]

theorem coeff_initialFormAt_of_gt (w : σ → ℝ) (δ : ℝ) (f : (MvPowerSeries σ k)[X]) {d : ℕ}
    (hd : f.natDegree < d) : (initialFormAt w δ f).coeff d = 0 := by
  rw [initialFormAt, coeff_add, coeff_X_pow, ite_eq_right hd.ne', zero_add, finsetSum_coeff,
    Finset.sum_eq_zero]
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [coeff_C_mul_X_pow, ite_eq_right (by omega)]

/-- The initial form is homogeneous of degree `m δ` if `z` has degree `δ`: each monomial
`x^a z^d` with `d < m` has `|a|_w + d δ = m δ`. -/
theorem initialFormAt_isHomogeneous (w : σ → ℝ) (δ : ℝ) (f : (MvPowerSeries σ k)[X]) {d : ℕ}
    (hd : d < f.natDegree) {a : σ →₀ ℕ}
    (ha : MvPowerSeries.coeff a ((initialFormAt w δ f).coeff d) ≠ 0) :
    linWeight w (expToReal a) + d * δ = f.natDegree * δ := by
  rw [coeff_initialFormAt_of_lt w δ f hd, coeff_weightPart] at ha
  split_ifs at ha with h
  · rw [h, Nat.cast_sub hd.le]
    ring
  · exact absurd rfl ha

/-- The point `y` is the only point of `P` where `|·|_w` is minimal. -/
def IsUniqueMinimizer (w : σ → ℝ) (P : Set (σ → ℝ)) (y : σ → ℝ) : Prop :=
  y ∈ P ∧ ∀ x ∈ P, linWeight w y ≤ linWeight w x ∧ (linWeight w x = linWeight w y → x = y)

theorem polyDelta_eq_of_isUniqueMinimizer {w : σ → ℝ} {f : (MvPowerSeries σ k)[X]}
    {y : σ → ℝ} (hy : IsUniqueMinimizer w (projPolyhedron f) y) :
    polyDelta w f = linWeight w y :=
  IsLeast.csInf_eq ⟨⟨y, hy.1, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact (hy.2 x hx).1⟩

/-- If `y` is the only minimum point of `|·|_w` on `Δ(f; x; z)`, then a monomial `x^a` of `a_i`
of weight `i δ` has `a = i y`. -/
theorem expToReal_eq_smul_of_isUniqueMinimizer {w : σ → ℝ} {f : (MvPowerSeries σ k)[X]}
    {y : σ → ℝ} (hy : IsUniqueMinimizer w (projPolyhedron f) y) {i : ℕ} (hi1 : 1 ≤ i)
    (him : i ≤ f.natDegree) {a : σ →₀ ℕ}
    (ha : MvPowerSeries.coeff a (f.coeff (f.natDegree - i)) ≠ 0)
    (hw : linWeight w (expToReal a) = i * linWeight w y) :
    expToReal a = (i : ℝ) • y := by
  have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmem := projPoints_subset_projPolyhedron f ⟨i, hi1, him, a, ha, rfl⟩
  have hlin : linWeight w ((i : ℝ)⁻¹ • expToReal a) = linWeight w y := by
    rw [(isLinearMap_linWeight w).map_smul, smul_eq_mul, hw, ← mul_assoc, inv_mul_cancel₀ hi0,
      one_mul]
  have := (hy.2 _ hmem).2 hlin
  rw [← this, smul_inv_smul₀ hi0]

omit [Fintype σ] in
theorem expToReal_nsmul (i : ℕ) (v : σ →₀ ℕ) : expToReal (i • v) = (i : ℝ) • expToReal v := by
  rw [map_nsmul, Nat.cast_smul_eq_nsmul]

/-- At a vertex `v` that is the only minimum point of `|·|_w`, the part `[a_i]_(i δ)` is the
monomial `c_i x^(i v)`, where `c_i` is the coefficient of `x^(i v)` in `a_i`. -/
theorem weightPart_eq_monomial_of_isUniqueMinimizer {w : σ → ℝ} {f : (MvPowerSeries σ k)[X]}
    {v : σ →₀ ℕ} (hv : IsUniqueMinimizer w (projPolyhedron f) (expToReal v)) {i : ℕ}
    (hi1 : 1 ≤ i) (him : i ≤ f.natDegree) :
    weightPart w (i * polyDelta w f) (f.coeff (f.natDegree - i)) =
      MvPowerSeries.monomial (i • v)
        (MvPowerSeries.coeff (i • v) (f.coeff (f.natDegree - i))) := by
  classical
  rw [polyDelta_eq_of_isUniqueMinimizer hv]
  ext a
  rw [coeff_weightPart, MvPowerSeries.coeff_monomial]
  by_cases hav : a = i • v
  · subst hav
    rw [ite_eq_left rfl, ite_eq_left (by
      rw [expToReal_nsmul, (isLinearMap_linWeight w).map_smul, smul_eq_mul])]
  · rw [ite_eq_right hav]
    split_ifs with hw
    · by_contra hc
      exact hav (expToReal_injective (by
        rw [expToReal_eq_smul_of_isUniqueMinimizer hv hi1 him hc hw, expToReal_nsmul]))
    · rfl

/-- Volume 6, Definition 3.1.3, the formula for `in_y h`. Let `f` be monic and let `v` be the
only minimum point of `|·|_w` on `Δ(f; x; z)`. Then the coefficient of `z^d` in `in_w f` is
`c_d x^((m-d) v)`, where `c_d` is the coefficient of `Z^d` in the initial polynomial
`vertexPoly f v`. So `in_w f` does not depend on `w`. -/
theorem coeff_weightInitialForm_of_isUniqueMinimizer {w : σ → ℝ} {f : (MvPowerSeries σ k)[X]}
    (hf : f.Monic) {v : σ →₀ ℕ} (hv : IsUniqueMinimizer w (projPolyhedron f) (expToReal v))
    (d : ℕ) :
    (weightInitialForm w f).coeff d =
      MvPowerSeries.monomial ((f.natDegree - d) • v) ((vertexPoly f v).coeff d) := by
  classical
  rw [weightInitialForm, coeff_vertexPoly]
  rcases lt_trichotomy d f.natDegree with hd | hd | hd
  · rw [coeff_initialFormAt_of_lt _ _ _ hd, ite_eq_left hd.le]
    have h := weightPart_eq_monomial_of_isUniqueMinimizer hv (i := f.natDegree - d) (by omega)
      (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self hd.le] at h
  · subst hd
    rw [coeff_initialFormAt_self, ite_eq_left le_rfl, Nat.sub_self, zero_smul, hf.coeff_natDegree,
      MvPowerSeries.coeff_one, ite_eq_left rfl]
    ext a
    rw [MvPowerSeries.coeff_one, MvPowerSeries.coeff_monomial]
  · rw [coeff_initialFormAt_of_gt _ _ _ hd, ite_eq_right (by omega), map_zero]

/-- Volume 6, Definition 3.1.3, solvable vertices. Let `f` be monic and let `v` be the only
minimum point of `|·|_w` on `Δ(f; x; z)`. Then `v` is solvable with the constant `c` in the
sense of `IsSolvableVertex` if and only if `in_w f = (z + c x^v)^m`. The handbook writes
`λ = -c`. -/
theorem isSolvableVertex_iff_weightInitialForm {w : σ → ℝ} {f : (MvPowerSeries σ k)[X]}
    (hf : f.Monic) {v : σ →₀ ℕ} (hv : IsUniqueMinimizer w (projPolyhedron f) (expToReal v))
    (c : k) :
    IsSolvableVertex f v c ↔
      weightInitialForm w f = (X + C (MvPowerSeries.monomial v c)) ^ f.natDegree := by
  classical
  have key : ∀ d, ((X + C (MvPowerSeries.monomial v c)) ^ f.natDegree).coeff d =
      MvPowerSeries.monomial ((f.natDegree - d) • v)
        (((X + C c) ^ f.natDegree : k[X]).coeff d) := by
    intro d
    rw [coeff_X_add_C_pow, coeff_X_add_C_pow, MvPowerSeries.monomial_pow]
    ext a
    rw [mul_comm, MvPowerSeries.coeff_natCast_mul, MvPowerSeries.coeff_monomial,
      MvPowerSeries.coeff_monomial]
    split_ifs <;> simp [mul_comm]
  constructor
  · intro hs
    refine Polynomial.ext fun d => ?_
    rw [coeff_weightInitialForm_of_isUniqueMinimizer hf hv, key, ← hs]
  · intro h
    refine Polynomial.ext fun d => ?_
    have := congrArg (fun P => MvPowerSeries.coeff ((f.natDegree - d) • v) (P.coeff d)) h
    simp only [coeff_weightInitialForm_of_isUniqueMinimizer hf hv, key,
      MvPowerSeries.coeff_monomial_same] at this
    exact this

end InitialForm

/-! ### The invariant delta (Definition 3.2.1 and Proposition 3.2.2) -/

section Delta

variable {σ k : Type*} [CommRing k] [Fintype σ]

/-- The coordinate `z` is minimal if no translation `z ↦ z + φ` with `φ` a power series makes
`Δ(f; x; z)` smaller. -/
def IsMinimalCoord (f : (MvPowerSeries σ k)[X]) : Prop :=
  ∀ φ : MvPowerSeries σ k, projPolyhedron f ⊆ projPolyhedron (taylor φ f)

omit [Fintype σ] in
theorem charPolyhedron_eq_of_isMinimalCoord {f : (MvPowerSeries σ k)[X]}
    (h : IsMinimalCoord f) : charPolyhedron f = projPolyhedron f :=
  subset_antisymm (charPolyhedron_subset_projPolyhedron f) (Set.subset_iInter₂ fun φ _ => h φ)

/-- Volume 6, Definition 3.2.1. The invariant `δ(x)`: the infimum of `x_1 + ... + x_n` on the
characteristic polyhedron. -/
noncomputable def charDelta (f : (MvPowerSeries σ k)[X]) : ℝ :=
  sInf (linWeight (fun _ => 1) '' charPolyhedron f)

/-- Volume 6, Definition 3.2.1. In minimal coordinates, `δ(x) = δ_1(h; u; z)`, and it is the
infimum of the numbers `|a| / i` over the monomials `x^a` of `a_i`, that is
`min_i ord(a_i) / i`. -/
theorem charDelta_eq_polyDelta {f : (MvPowerSeries σ k)[X]} (h : IsMinimalCoord f)
    (hne : (projPolyhedron f).Nonempty) :
    charDelta f = polyDelta (fun _ => 1) f ∧
      charDelta f = sInf (projWeights f fun _ => 1) := by
  have h1 : charDelta f = polyDelta (fun _ => 1) f := by
    rw [charDelta, polyDelta, charPolyhedron_eq_of_isMinimalCoord h]
  exact ⟨h1, h1.trans (sInf_linWeight_projPolyhedron f (fun _ => zero_le_one) hne)⟩

/-- The invariant `δ(x)` does not depend on the choice of `z`: it does not change under a
translation `z ↦ z + ψ` with `ψ` in the maximal ideal. -/
theorem charDelta_taylor (f : (MvPowerSeries σ k)[X]) {ψ : MvPowerSeries σ k}
    (hψ : MvPowerSeries.constantCoeff ψ = 0) : charDelta (taylor ψ f) = charDelta f := by
  rw [charDelta, charDelta, charPolyhedron_taylor f hψ]

omit [Fintype σ] in
/-- Two minimal coordinates have the same polyhedron, so the same `δ`. -/
theorem projPolyhedron_taylor_eq_of_isMinimalCoord {f : (MvPowerSeries σ k)[X]}
    {ψ : MvPowerSeries σ k} (h : IsMinimalCoord f) (h' : IsMinimalCoord (taylor ψ f)) :
    projPolyhedron (taylor ψ f) = projPolyhedron f := by
  refine subset_antisymm ?_ (h ψ)
  have := h' (-ψ)
  rwa [taylor_taylor, neg_add_cancel, taylor_zero] at this

theorem bddBelow_linWeight_projPolyhedron (f : (MvPowerSeries σ k)[X]) {w : σ → ℝ}
    (hw : ∀ j, 0 ≤ w j) : BddBelow (linWeight w '' projPolyhedron f) :=
  ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact linWeight_nonneg hw (projPolyhedron_subset_orthant f hx)⟩

theorem polyDelta_le {f : (MvPowerSeries σ k)[X]} {w : σ → ℝ} (hw : ∀ j, 0 ≤ w j)
    {x : σ → ℝ} (hx : x ∈ projPolyhedron f) : polyDelta w f ≤ linWeight w x :=
  csInf_le (bddBelow_linWeight_projPolyhedron f hw) ⟨x, hx, rfl⟩

/-- Volume 6, Proposition 3.2.2 (1). In minimal coordinates, `δ(x)` is the largest of the
numbers `δ_1(h; u; z + φ) = min_i ord(a_i(φ)) / i` over all power series `φ`. -/
theorem isGreatest_polyDelta_taylor {f : (MvPowerSeries σ k)[X]} (h : IsMinimalCoord f)
    (hne : (projPolyhedron f).Nonempty) :
    IsGreatest (Set.range fun φ : MvPowerSeries σ k => polyDelta (fun _ => 1) (taylor φ f))
      (charDelta f) := by
  rw [(charDelta_eq_polyDelta h hne).1]
  refine ⟨⟨0, by simp only [taylor_zero]⟩, ?_⟩
  rintro _ ⟨φ, rfl⟩
  exact csInf_le_csInf (bddBelow_linWeight_projPolyhedron _ fun _ => zero_le_one)
    (hne.image _) (Set.image_mono (h φ))

omit [Fintype σ] in
theorem one_le_natDegree_of_nonempty {f : (MvPowerSeries σ k)[X]}
    (hne : (projPolyhedron f).Nonempty) : 1 ≤ f.natDegree := by
  by_contra h0
  have : projPolyhedron f = ∅ :=
    (projPolyhedron_eq_empty_iff f).mpr fun i hi1 him => absurd (hi1.trans him) h0
  exact hne.ne_empty this

theorem linWeight_one_expToReal (a : σ →₀ ℕ) :
    linWeight (fun _ => 1) (expToReal a) = ((∑ j, a j : ℕ) : ℝ) := by
  simp [linWeight]

/-- The algebraic core of Volume 6, Proposition 3.2.2 (2), first half. We have `δ_1 > 0` if and
only if each coefficient `a_i` lies in the maximal ideal. -/
theorem polyDelta_pos_iff {f : (MvPowerSeries σ k)[X]} (hne : (projPolyhedron f).Nonempty) :
    0 < polyDelta (fun _ => 1) f ↔ ∀ i, 1 ≤ i → i ≤ f.natDegree →
      MvPowerSeries.constantCoeff (f.coeff (f.natDegree - i)) = 0 := by
  constructor
  · intro hpos i hi1 him
    by_contra hc
    have hmem := projPoints_subset_projPolyhedron f ⟨i, hi1, him, 0,
      by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply], rfl⟩
    have := polyDelta_le (fun _ => zero_le_one) hmem
    simp [linWeight] at this
    linarith
  · intro h0
    have hm := one_le_natDegree_of_nonempty hne
    have hmpos : (0 : ℝ) < f.natDegree := by exact_mod_cast hm
    have hlow : (1 / f.natDegree : ℝ) ≤ polyDelta (fun _ => 1) f := by
      refine le_csInf (hne.image _) ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ((le_linWeight_projPolyhedron_iff f (fun _ => zero_le_one) _).mpr ?_) x hx
      intro i hi1 him a ha
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0 i hi1 him] at ha
        exact ha rfl
      obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
        by_contra hall
        simp only [ne_eq, not_exists, not_not] at hall
        exact ha0 (Finsupp.ext hall)
      have h1 : (1 : ℝ) ≤ linWeight (fun _ => 1) (expToReal a) := by
        rw [linWeight_one_expToReal]
        have : a j ≤ ∑ l, a l := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hj).trans this
      have h2 : (i : ℝ) * (1 / f.natDegree) ≤ 1 := by
        rw [mul_one_div, div_le_one hmpos]
        exact_mod_cast him
      linarith
    exact lt_of_lt_of_le (by positivity) hlow

omit [Fintype σ] in
/-- If each coefficient `a_i` lies in the maximal ideal and `f` is monic, then the image of `f`
in `k[z]` is `z^m`. -/
theorem map_constantCoeff_eq_X_pow {f : (MvPowerSeries σ k)[X]} (hf : f.Monic)
    (h0 : ∀ i, 1 ≤ i → i ≤ f.natDegree →
      MvPowerSeries.constantCoeff (f.coeff (f.natDegree - i)) = 0) :
    f.map MvPowerSeries.constantCoeff = X ^ f.natDegree := by
  ext d
  rw [coeff_map, coeff_X_pow]
  rcases lt_trichotomy d f.natDegree with hd | hd | hd
  · rw [ite_eq_right hd.ne]
    have := h0 (f.natDegree - d) (by omega) (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self hd.le] at this
  · rw [ite_eq_left hd, hd, hf.coeff_natDegree, map_one]
  · rw [ite_eq_right hd.ne', coeff_eq_zero_of_natDegree_lt hd, map_zero]

omit [Fintype σ] in
/-- The initial polynomial at the point `0` is the image of `f` in `k[z]`. -/
theorem vertexPoly_zero_eq_map (f : (MvPowerSeries σ k)[X]) :
    vertexPoly f 0 = f.map MvPowerSeries.constantCoeff := by
  ext d
  rw [coeff_vertexPoly, coeff_map, smul_zero]
  split_ifs with hd
  · exact MvPowerSeries.coeff_zero_eq_constantCoeff_apply _
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

omit [Fintype σ] in
/-- If `0` lies in `Δ(f; x; z)`, then it is a vertex, since the polyhedron lies in the
orthant. -/
theorem zero_mem_extremePoints_projPolyhedron {f : (MvPowerSeries σ k)[X]}
    (h0 : (0 : σ → ℝ) ∈ projPolyhedron f) : (0 : σ → ℝ) ∈ (projPolyhedron f).extremePoints ℝ := by
  refine ⟨h0, ?_⟩
  intro x hx y hy hseg
  obtain ⟨a, b, ha, hb, -, hxy⟩ := hseg
  funext j
  have hj := congrFun hxy j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
  have hxj := projPolyhedron_subset_orthant f hx j
  have hyj := projPolyhedron_subset_orthant f hy j
  nlinarith [mul_nonneg ha.le hxj, mul_nonneg hb.le hyj]

omit [Fintype σ] in
/-- The algebraic core of Volume 6, Proposition 3.2.2 (2), second half. In minimal coordinates,
if the image of `f` in `k[z]` is `(z + c)^m`, then each `a_i` lies in the maximal ideal.
Otherwise the vertex `0` would be solvable, and Lemma 3.1.4 would give a smaller polyhedron. -/
theorem constantCoeff_eq_zero_of_isMinimalCoord {f : (MvPowerSeries σ k)[X]}
    (hmin : IsMinimalCoord f) {c : k}
    (hc : f.map MvPowerSeries.constantCoeff = (X + C c) ^ f.natDegree) :
    ∀ i, 1 ≤ i → i ≤ f.natDegree →
      MvPowerSeries.constantCoeff (f.coeff (f.natDegree - i)) = 0 := by
  intro i hi1 him
  by_contra hne
  have hmem := projPoints_subset_projPolyhedron f ⟨i, hi1, him, 0,
    by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply], rfl⟩
  have h0 : expToReal (0 : σ →₀ ℕ) ∈ projPolyhedron f := by
    simpa only [map_zero, smul_zero] using hmem
  have hext : expToReal (0 : σ →₀ ℕ) ∈ (projPolyhedron f).extremePoints ℝ := by
    rw [map_zero] at h0 ⊢
    exact zero_mem_extremePoints_projPolyhedron h0
  have hs : IsSolvableVertex f 0 c := by
    rw [IsSolvableVertex, vertexPoly_zero_eq_map, hc]
  have hss := projPolyhedron_taylor_ssubset_of_isSolvable hext hs
  exact (ssubset_iff_subset_not_subset.mp hss).2 (hmin _)

/-- The algebraic core of Volume 6, Proposition 3.2.2 (2). Let `f` be monic, let `z` be minimal,
and let `Δ(f; x; z)` be nonempty. Then `δ > 0` if and only if the image of `f` in `k[z]` is
`(z + c)^m` for some `c ∈ k`, that is, the fiber is one rational point. -/
theorem polyDelta_pos_iff_of_isMinimalCoord {f : (MvPowerSeries σ k)[X]} (hf : f.Monic)
    (hmin : IsMinimalCoord f) (hne : (projPolyhedron f).Nonempty) :
    0 < polyDelta (fun _ => 1) f ↔
      ∃ c : k, f.map MvPowerSeries.constantCoeff = (X + C c) ^ f.natDegree := by
  rw [polyDelta_pos_iff hne]
  constructor
  · intro h0
    exact ⟨0, by rw [C_0, add_zero, map_constantCoeff_eq_X_pow hf h0]⟩
  · rintro ⟨c, hc⟩
    exact constantCoeff_eq_zero_of_isMinimalCoord hmin hc

/-- Volume 6, Proposition 3.2.2 (3), in terms of the coefficients. We have `δ_1 ≥ 1` if and only
if each monomial `x^a` of `a_i` has `|a| ≥ i`. -/
theorem one_le_polyDelta_iff {f : (MvPowerSeries σ k)[X]} (hne : (projPolyhedron f).Nonempty) :
    1 ≤ polyDelta (fun _ => 1) f ↔ ∀ i, 1 ≤ i → i ≤ f.natDegree → ∀ a : σ →₀ ℕ,
      MvPowerSeries.coeff a (f.coeff (f.natDegree - i)) ≠ 0 →
        (i : ℝ) ≤ linWeight (fun _ => 1) (expToReal a) := by
  have key := le_linWeight_projPolyhedron_iff f (fun _ => zero_le_one) (1 : ℝ)
  simp only [mul_one] at key
  constructor
  · intro h
    exact key.mp fun x hx => h.trans (polyDelta_le (fun _ => zero_le_one) hx)
  · intro h
    refine le_csInf (hne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact key.mpr h x hx

/-- The algebraic core of Volume 6, Proposition 3.2.2 (3). We have `δ_1 ≥ 1` if and only if each
monomial `x^a z^d` of `f` has total degree `|a| + d ≥ m`, that is, `f` has order at least `m` at
the point `(m_S, z)`. -/
theorem one_le_polyDelta_iff_order {f : (MvPowerSeries σ k)[X]}
    (hne : (projPolyhedron f).Nonempty) :
    1 ≤ polyDelta (fun _ => 1) f ↔ ∀ d, ∀ a : σ →₀ ℕ, MvPowerSeries.coeff a (f.coeff d) ≠ 0 →
      f.natDegree ≤ (∑ j, a j) + d := by
  rw [one_le_polyDelta_iff hne]
  constructor
  · intro h d a ha
    by_cases hd : f.natDegree ≤ d
    · omega
    have h' := h (f.natDegree - d) (by omega) (Nat.sub_le _ _) a
      (by rwa [Nat.sub_sub_self (by omega)])
    rw [linWeight_one_expToReal] at h'
    have : f.natDegree - d ≤ ∑ j, a j := by exact_mod_cast h'
    omega
  · intro h i hi1 him a ha
    have := h _ a ha
    rw [linWeight_one_expToReal]
    have : i ≤ ∑ j, a j := by omega
    exact_mod_cast this

end Delta

/-! ### The invariants of the divisor (Definition 3.2.3) -/

section Divisor

variable {σ k : Type*} [CommRing k] [Fintype σ] [DecidableEq σ]

/-- Volume 6, Definition 3.2.3. The number `d_j = inf {x_j : x ∈ Δ(f; x; z)}`. -/
noncomputable def divisorDelta (f : (MvPowerSeries σ k)[X]) (j : σ) : ℝ :=
  polyDelta (Pi.single j 1) f

/-- Volume 6, Definition 3.2.3. The residual order `ε = m (δ - ∑_(j ∈ E) d_j)`. -/
noncomputable def residualEpsilon (f : (MvPowerSeries σ k)[X]) (E : Finset σ) : ℝ :=
  f.natDegree * (polyDelta (fun _ => 1) f - ∑ j ∈ E, divisorDelta f j)

theorem linWeight_single (j : σ) (x : σ → ℝ) : linWeight (Pi.single j 1) x = x j := by
  simp [linWeight, Pi.single_apply]

omit [Fintype σ] in
theorem single_nonneg (j : σ) : ∀ l, (0 : ℝ) ≤ (Pi.single j (1 : ℝ) : σ → ℝ) l := by
  intro l
  by_cases h : l = j
  · subst h
    simp
  · simp [h]

/-- Each point of `Δ(f; x; z)` has `x_j ≥ d_j`. -/
theorem divisorDelta_le {f : (MvPowerSeries σ k)[X]} {x : σ → ℝ} (hx : x ∈ projPolyhedron f)
    (j : σ) : divisorDelta f j ≤ x j := by
  rw [← linWeight_single j x]
  exact csInf_le ⟨0, by
    rintro _ ⟨y, hy, rfl⟩
    exact linWeight_nonneg (single_nonneg j) (projPolyhedron_subset_orthant f hy)⟩ ⟨x, hx, rfl⟩

/-- `∑_(j ∈ E) d_j ≤ δ`. -/
theorem sum_divisorDelta_le {f : (MvPowerSeries σ k)[X]} (hne : (projPolyhedron f).Nonempty)
    (E : Finset σ) : ∑ j ∈ E, divisorDelta f j ≤ polyDelta (fun _ => 1) f := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxo := projPolyhedron_subset_orthant f hx
  calc ∑ j ∈ E, divisorDelta f j ≤ ∑ j ∈ E, x j :=
        Finset.sum_le_sum fun j _ => divisorDelta_le hx j
    _ ≤ ∑ j, x j := Finset.sum_le_univ_sum_of_nonneg hxo
    _ = linWeight (fun _ => 1) x := by simp [linWeight]

/-- Volume 6, Definition 3.2.3: `ε(x) ≥ 0`. -/
theorem residualEpsilon_nonneg {f : (MvPowerSeries σ k)[X]} (hne : (projPolyhedron f).Nonempty)
    (E : Finset σ) : 0 ≤ residualEpsilon f E :=
  mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (sum_divisorDelta_le hne E))

end Divisor

/-! ### Equations `z^n + G` with two monomials -/

section TwoMonomials

variable {σ k : Type*} [CommRing k] [Nontrivial k] [Fintype σ]

omit [Nontrivial k] [Fintype σ] in
theorem coeff_X_pow_add_C_sub {n i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) (G : MvPowerSeries σ k) :
    (X ^ n + C G : (MvPowerSeries σ k)[X]).coeff (n - i) = if i = n then G else 0 := by
  rw [coeff_add, coeff_X_pow, coeff_C, ite_eq_right (by omega), zero_add]
  rcases eq_or_lt_of_le hin with h | h
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h.ne]

theorem projWeights_X_pow_add_C {n : ℕ} (hn : 1 ≤ n) (G : MvPowerSeries σ k) (w : σ → ℝ) :
    projWeights (X ^ n + C G) w =
      {r | ∃ α, MvPowerSeries.coeff α G ≠ 0 ∧ r = linWeight w (expToReal α) / n} := by
  ext r
  simp only [projWeights, natDegree_X_pow_add_C, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi1, hin, α, hα, rfl⟩
    rw [coeff_X_pow_add_C_sub hi1 hin] at hα
    split_ifs at hα with h
    · subst h
      exact ⟨α, hα, rfl⟩
    · exact absurd (map_zero _) hα
  · rintro ⟨α, hα, rfl⟩
    exact ⟨n, hn, le_rfl, α, by rwa [coeff_X_pow_add_C_sub hn le_rfl, ite_eq_left rfl], rfl⟩

omit [Fintype σ] in
theorem coeff_monomial_add_monomial_ne_zero_iff {a b : σ →₀ ℕ} (hab : a ≠ b) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (MvPowerSeries.monomial a (1 : k) + MvPowerSeries.monomial b 1) ≠ 0 ↔
      α = a ∨ α = b := by
  classical
  rw [map_add, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
  by_cases ha : α = a
  · subst ha
    simp [hab]
  · by_cases hb : α = b
    · simp [hb, Ne.symm hab]
    · simp [ha, hb]

omit [Fintype σ] in
theorem projPolyhedron_X_pow_add_C_nonempty {n : ℕ} (hn : 1 ≤ n) {G : MvPowerSeries σ k}
    {α : σ →₀ ℕ} (hα : MvPowerSeries.coeff α G ≠ 0) :
    (projPolyhedron (X ^ n + C G)).Nonempty := by
  refine ⟨(n : ℝ)⁻¹ • expToReal α, projPoints_subset_projPolyhedron _ ?_⟩
  rw [projPoints_X_pow_add_C hn]
  exact ⟨α, hα, rfl⟩

/-- For `f = z^n + x^a + x^b` with `a ≠ b` and a weight `w ≥ 0`, the number `δ_w(f)` is
`min(|a|_w, |b|_w) / n`. -/
theorem polyDelta_X_pow_add_C_two {n : ℕ} (hn : 1 ≤ n) {a b : σ →₀ ℕ} (hab : a ≠ b)
    {w : σ → ℝ} (hw : ∀ j, 0 ≤ w j) :
    polyDelta w (X ^ n + C (MvPowerSeries.monomial a (1 : k) + MvPowerSeries.monomial b 1)) =
      min (linWeight w (expToReal a) / n) (linWeight w (expToReal b) / n) := by
  have hne := projPolyhedron_X_pow_add_C_nonempty (k := k) hn
    ((coeff_monomial_add_monomial_ne_zero_iff hab a).mpr (Or.inl rfl))
  rw [polyDelta, sInf_linWeight_projPolyhedron _ hw hne, projWeights_X_pow_add_C hn,
    ← csInf_pair]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, coeff_monomial_add_monomial_ne_zero_iff hab, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨α, hα | hα, rfl⟩ <;> subst hα <;> simp
  · rintro (rfl | rfl)
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr rfl, rfl⟩

omit [Nontrivial k] in
theorem weightPart_monomial_add_monomial {a b : σ →₀ ℕ} {w : σ → ℝ} {c : ℝ}
    (ha : linWeight w (expToReal a) ≠ c) (hb : linWeight w (expToReal b) = c) :
    weightPart w c (MvPowerSeries.monomial a (1 : k) + MvPowerSeries.monomial b 1) =
      MvPowerSeries.monomial b 1 := by
  classical
  ext α
  rw [coeff_weightPart]
  by_cases hαb : α = b
  · subst hαb
    have hne : α ≠ a := fun h => ha (h ▸ hb)
    simp [MvPowerSeries.coeff_monomial, hb, hne]
  · by_cases hαa : α = a
    · subst hαa
      simp [MvPowerSeries.coeff_monomial, ha, hαb]
    · simp [MvPowerSeries.coeff_monomial, hαa, hαb]

end TwoMonomials

/-! ### Example 4.1.1 -/

section Example411

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The exponent of `u_2^p u_4 u_3^p`. The variables `u_1, ..., u_4` are `0, ..., 3`. -/
noncomputable def ex411Exp1 : Fin 4 →₀ ℕ :=
  Finsupp.single 1 p + Finsupp.single 3 1 + Finsupp.single 2 p

/-- The exponent of `u_3 u_1^p`. -/
noncomputable def ex411Exp2 : Fin 4 →₀ ℕ := Finsupp.single 2 1 + Finsupp.single 0 p

/-- The series `f = u_2^p u_4 u_3^p + u_3 u_1^p` of Example 4.1.1. -/
noncomputable def ex411F : MvPowerSeries (Fin 4) k :=
  MvPowerSeries.monomial (ex411Exp1 p) 1 + MvPowerSeries.monomial (ex411Exp2 p) 1

omit [Fact p.Prime] [CharP k p] in
theorem ex411F_eq : ex411F (k := k) p =
    MvPowerSeries.X 1 ^ p * MvPowerSeries.X 3 * MvPowerSeries.X 2 ^ p +
      MvPowerSeries.X 2 * MvPowerSeries.X 0 ^ p := by
  rw [ex411F, ex411Exp1, ex411Exp2]
  simp only [MvPowerSeries.X_pow_eq]
  simp only [MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]

/-- The equation `h = Z^p + f` of Example 4.1.1. -/
noncomputable def ex411H : (MvPowerSeries (Fin 4) k)[X] := X ^ p + C (ex411F p)

theorem ex411_two_le : 2 ≤ p := (Fact.out : p.Prime).two_le

omit [Fact p.Prime] in
theorem ex411Exp1_ne : ex411Exp1 p ≠ ex411Exp2 p := by
  intro h
  have := congrArg (fun a => a 3) h
  simp [ex411Exp1, ex411Exp2] at this

omit [CharP k p] in
theorem ex411_clean : ∀ α, MvPowerSeries.coeff α (ex411F (k := k) p) ≠ 0 →
    ¬ ∀ i, p ^ 1 ∣ α i := by
  intro α hα hdvd
  have h2 := ex411_two_le p
  rw [ex411F, coeff_monomial_add_monomial_ne_zero_iff (ex411Exp1_ne p)] at hα
  rcases hα with rfl | rfl
  · have := hdvd 3
    simp [ex411Exp1] at this
    omega
  · have := hdvd 2
    simp [ex411Exp2] at this
    omega

/-- Example 4.1.1: the series `f` is clean, so the coordinates `(u; Z)` are minimal. -/
theorem ex411_isMinimalCoord : IsMinimalCoord (ex411H (k := k) p) := fun φ => by
  have := projPolyhedron_subset_taylor_of_clean p 1 (ex411_clean (k := k) p) φ
  rwa [pow_one] at this

/-- Example 4.1.1: `(u; Z)` attains the characteristic polyhedron. -/
theorem ex411_charPolyhedron :
    charPolyhedron (ex411H (k := k) p) = projPolyhedron (ex411H (k := k) p) :=
  charPolyhedron_eq_of_isMinimalCoord (ex411_isMinimalCoord p)

omit [Fact p.Prime] [CharP k p] in
theorem ex411_natDegree : (ex411H (k := k) p).natDegree = p := natDegree_X_pow_add_C

omit [CharP k p] in
/-- Example 4.1.1: `δ(x) = (p + 1)/p`. -/
theorem ex411_delta : polyDelta (fun _ => 1) (ex411H (k := k) p) = (p + 1) / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast ex411_two_le p
  rw [ex411H, ex411F, polyDelta_X_pow_add_C_two (by have := ex411_two_le p; omega)
    (ex411Exp1_ne p) (fun _ => zero_le_one), linWeight_one_expToReal, linWeight_one_expToReal]
  simp only [ex411Exp1, ex411Exp2, Fin.sum_univ_four, Finsupp.add_apply, Finsupp.single_apply]
  norm_num
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

omit [CharP k p] in
/-- Example 4.1.1: `δ(x) ≥ 1`, so the multiplicity is `p`. -/
theorem ex411_one_le_delta : 1 ≤ polyDelta (fun _ => 1) (ex411H (k := k) p) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast ex411_two_le p
  rw [ex411_delta, le_div_iff₀ (by linarith)]
  linarith

omit [CharP k p] in
/-- Example 4.1.1: `d_1 = 0`. -/
theorem ex411_d1 : divisorDelta (ex411H (k := k) p) 0 = 0 := by
  rw [divisorDelta, ex411H, ex411F, polyDelta_X_pow_add_C_two (by have := ex411_two_le p; omega)
    (ex411Exp1_ne p) (single_nonneg 0), linWeight_single, linWeight_single]
  simp [ex411Exp1, ex411Exp2]
  positivity

omit [CharP k p] in
/-- Example 4.1.1: `d_2 = 0`. -/
theorem ex411_d2 : divisorDelta (ex411H (k := k) p) 1 = 0 := by
  rw [divisorDelta, ex411H, ex411F, polyDelta_X_pow_add_C_two (by have := ex411_two_le p; omega)
    (ex411Exp1_ne p) (single_nonneg 1), linWeight_single, linWeight_single]
  simp [ex411Exp1, ex411Exp2]
  positivity

omit [CharP k p] in
/-- Example 4.1.1: `ε(x) = p + 1` for `E = div(u_1 u_2)`. -/
theorem ex411_epsilon : residualEpsilon (ex411H (k := k) p) {0, 1} = p + 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast ex411_two_le p
  rw [residualEpsilon, ex411_natDegree, ex411_delta, Finset.sum_pair (by decide), ex411_d1,
    ex411_d2]
  field_simp
  ring

omit [CharP k p] in
/-- Example 4.1.1: the initial form of `f` is `U_1^p U_3`. This is the coefficient of `Z^0` in
the initial form `in_1 h` of Definition 3.1.3. -/
theorem ex411_initialForm :
    (weightInitialForm (fun _ => 1) (ex411H (k := k) p)).coeff 0 =
      MvPowerSeries.monomial (ex411Exp2 p) 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast ex411_two_le p
  have hp0 : 0 < (ex411H (k := k) p).natDegree := by
    rw [ex411_natDegree]; exact lt_of_lt_of_le two_pos (ex411_two_le p)
  rw [weightInitialForm, coeff_initialFormAt_of_lt _ _ _ hp0, ex411_natDegree, ex411_delta]
  have hc : (ex411H (k := k) p).coeff 0 = ex411F p := by
    have hp : 0 ≠ p := by have := ex411_two_le p; omega
    rw [ex411H, coeff_add, coeff_X_pow, ite_eq_right hp, coeff_C_zero, zero_add]
  rw [hc, ex411F]
  apply weightPart_monomial_add_monomial
  · rw [linWeight_one_expToReal]
    simp only [ex411Exp1, Fin.sum_univ_four, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    field_simp
    intro h
    linarith
  · rw [linWeight_one_expToReal]
    simp only [ex411Exp2, Fin.sum_univ_four, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    field_simp

omit [Fact p.Prime] [CharP k p] in
/-- Example 4.1.1: the derivative of the initial form `U_1^p U_3` in `U_3` is `U_1^p ≠ 0`. So
`ω(x) = ε(x) - 1 = p`. -/
theorem ex411_pderiv :
    MvPolynomial.pderiv 2 (MvPolynomial.X 2 * MvPolynomial.X 0 ^ p : MvPolynomial (Fin 4) k) =
      MvPolynomial.X 0 ^ p ∧ (MvPolynomial.X 0 ^ p : MvPolynomial (Fin 4) k) ≠ 0 := by
  refine ⟨?_, pow_ne_zero _ (MvPolynomial.X_ne_zero _)⟩
  rw [Derivation.leibniz, Derivation.leibniz_pow, MvPolynomial.pderiv_X_of_ne (by decide),
    MvPolynomial.pderiv_X_self]
  simp

omit [Fact p.Prime] in
/-- Example 4.1.1, the first blowup. With `u_1 = u_2 u_1'`, `u_3 = u_2 u_3'`, `u_4 = u_2 v_4`
and `Z = u_2 T`, we get `h = u_2^p (T^p + u_2 (u_2^p v_4 u_3'^p + u_3' u_1'^p))`. -/
theorem ex411_blowup {R : Type*} [CommRing R] (T u1 u2 u3 v4 : R) :
    (u2 * T) ^ p + u2 ^ p * (u2 * v4) * (u2 * u3) ^ p + u2 * u3 * (u2 * u1) ^ p =
      u2 ^ p * (T ^ p + u2 * (u2 ^ p * v4 * u3 ^ p + u3 * u1 ^ p)) := by
  ring

/-- The exponent of `u_2^(p+1) v_4 u_3'^p`. The variables `u_1', u_2, u_3', v_4` are
`0, ..., 3`. -/
noncomputable def ex411Exp1' : Fin 4 →₀ ℕ :=
  Finsupp.single 1 (p + 1) + Finsupp.single 3 1 + Finsupp.single 2 p

/-- The exponent of `u_2 u_3' u_1'^p`. -/
noncomputable def ex411Exp2' : Fin 4 →₀ ℕ :=
  Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 0 p

/-- The series `f_1 = u_2^(p+1) v_4 u_3'^p + u_2 u_3' u_1'^p` at the point `x_1`. -/
noncomputable def ex411F' : MvPowerSeries (Fin 4) k :=
  MvPowerSeries.monomial (ex411Exp1' p) 1 + MvPowerSeries.monomial (ex411Exp2' p) 1

omit [Fact p.Prime] [CharP k p] in
theorem ex411F'_eq : ex411F' (k := k) p =
    MvPowerSeries.X 1 ^ (p + 1) * MvPowerSeries.X 3 * MvPowerSeries.X 2 ^ p +
      MvPowerSeries.X 1 * MvPowerSeries.X 2 * MvPowerSeries.X 0 ^ p := by
  rw [ex411F', ex411Exp1', ex411Exp2']
  simp only [MvPowerSeries.X_pow_eq]
  simp only [MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]

/-- The strict transform `T_1^p + f_1` at the point `x_1`. -/
noncomputable def ex411H' : (MvPowerSeries (Fin 4) k)[X] := X ^ p + C (ex411F' p)

omit [Fact p.Prime] in
theorem ex411Exp1'_ne : ex411Exp1' p ≠ ex411Exp2' p := by
  intro h
  have := congrArg (fun a => a 3) h
  simp [ex411Exp1', ex411Exp2'] at this

omit [CharP k p] in
theorem ex411_clean' : ∀ α, MvPowerSeries.coeff α (ex411F' (k := k) p) ≠ 0 →
    ¬ ∀ i, p ^ 1 ∣ α i := by
  intro α hα hdvd
  have h2 := ex411_two_le p
  rw [ex411F', coeff_monomial_add_monomial_ne_zero_iff (ex411Exp1'_ne p)] at hα
  rcases hα with rfl | rfl
  · have := hdvd 3
    simp [ex411Exp1'] at this
    omega
  · have := hdvd 2
    simp [ex411Exp2'] at this
    omega

/-- Example 4.1.1: the coordinates at `x_1` are minimal. -/
theorem ex411_isMinimalCoord' : IsMinimalCoord (ex411H' (k := k) p) := fun φ => by
  have := projPolyhedron_subset_taylor_of_clean p 1 (ex411_clean' (k := k) p) φ
  rwa [pow_one] at this

omit [Fact p.Prime] [CharP k p] in
theorem ex411_natDegree' : (ex411H' (k := k) p).natDegree = p := natDegree_X_pow_add_C

omit [CharP k p] in
/-- Example 4.1.1: `δ(x_1) = (p + 2)/p`. -/
theorem ex411_delta' : polyDelta (fun _ => 1) (ex411H' (k := k) p) = (p + 2) / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast ex411_two_le p
  rw [ex411H', ex411F', polyDelta_X_pow_add_C_two (by have := ex411_two_le p; omega)
    (ex411Exp1'_ne p) (fun _ => zero_le_one), linWeight_one_expToReal, linWeight_one_expToReal]
  simp only [ex411Exp1', ex411Exp2', Fin.sum_univ_four, Finsupp.add_apply, Finsupp.single_apply]
  norm_num
  rw [min_eq_right (div_le_div_of_nonneg_right (by linarith) (by linarith))]
  ring

omit [CharP k p] in
/-- Example 4.1.1: `d_1 = 0` at `x_1`. -/
theorem ex411_d1' : divisorDelta (ex411H' (k := k) p) 0 = 0 := by
  rw [divisorDelta, ex411H', ex411F', polyDelta_X_pow_add_C_two
    (by have := ex411_two_le p; omega) (ex411Exp1'_ne p) (single_nonneg 0), linWeight_single,
    linWeight_single]
  simp [ex411Exp1', ex411Exp2']
  positivity

omit [CharP k p] in
/-- Example 4.1.1: `d_2 = 1/p` at `x_1`. -/
theorem ex411_d2' : divisorDelta (ex411H' (k := k) p) 1 = 1 / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast ex411_two_le p
  rw [divisorDelta, ex411H', ex411F', polyDelta_X_pow_add_C_two
    (by have := ex411_two_le p; omega) (ex411Exp1'_ne p) (single_nonneg 1), linWeight_single,
    linWeight_single]
  simp only [ex411Exp1', ex411Exp2']
  norm_num
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

omit [CharP k p] in
/-- Example 4.1.1: `ε(x_1) = p + 1 = ε(x)` for `E_1 = div(u_1' u_2)`. -/
theorem ex411_epsilon' : residualEpsilon (ex411H' (k := k) p) {0, 1} = p + 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast ex411_two_le p
  rw [residualEpsilon, ex411_natDegree', ex411_delta', Finset.sum_pair (by decide), ex411_d1',
    ex411_d2']
  field_simp
  ring

omit [CharP k p] in
/-- Example 4.1.1: the initial form at `x_1` is `U_1^p U_2 U_3`. -/
theorem ex411_initialForm' :
    (weightInitialForm (fun _ => 1) (ex411H' (k := k) p)).coeff 0 =
      MvPowerSeries.monomial (ex411Exp2' p) 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast ex411_two_le p
  have hp0 : 0 < (ex411H' (k := k) p).natDegree := by
    rw [ex411_natDegree']; exact lt_of_lt_of_le two_pos (ex411_two_le p)
  rw [weightInitialForm, coeff_initialFormAt_of_lt _ _ _ hp0, ex411_natDegree', ex411_delta']
  have hc : (ex411H' (k := k) p).coeff 0 = ex411F' p := by
    have hp : 0 ≠ p := by have := ex411_two_le p; omega
    rw [ex411H', coeff_add, coeff_X_pow, ite_eq_right hp, coeff_C_zero, zero_add]
  rw [hc, ex411F']
  apply weightPart_monomial_add_monomial
  · rw [linWeight_one_expToReal]
    simp only [ex411Exp1', Fin.sum_univ_four, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    field_simp
    intro h
    linarith
  · rw [linWeight_one_expToReal]
    simp only [ex411Exp2', Fin.sum_univ_four, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    field_simp
    ring

omit [Fact p.Prime] [CharP k p] in
/-- Example 4.1.1: the derivative of `U_1^p U_2 U_3` in `U_3` is `U_1^p U_2 ≠ 0`. So
`ω(x_1) = p`. -/
theorem ex411_pderiv' :
    MvPolynomial.pderiv 2 (MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 0 ^ p :
      MvPolynomial (Fin 4) k) = MvPolynomial.X 1 * MvPolynomial.X 0 ^ p ∧
      (MvPolynomial.X 1 * MvPolynomial.X 0 ^ p : MvPolynomial (Fin 4) k) ≠ 0 := by
  refine ⟨?_, mul_ne_zero (MvPolynomial.X_ne_zero _) (pow_ne_zero _ (MvPolynomial.X_ne_zero _))⟩
  have h0 : MvPolynomial.pderiv 2 (MvPolynomial.X 0 : MvPolynomial (Fin 4) k) = 0 :=
    MvPolynomial.pderiv_X_of_ne (by decide)
  have h1 : MvPolynomial.pderiv 2 (MvPolynomial.X 1 : MvPolynomial (Fin 4) k) = 0 :=
    MvPolynomial.pderiv_X_of_ne (by decide)
  rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, h0, h1,
    MvPolynomial.pderiv_X_self]
  simp only [smul_eq_mul, mul_one]
  ring

end Example411

/-! ### Example 1.2.7 -/

section Example127

open MvPolynomial

variable {k : Type*} [Field k]

/-- The polynomial `h = z^2 + x^3 + y^3 + w^3` of Example 1.2.7. The variables `z, x, y, w` are
`0, 1, 2, 3`. -/
noncomputable def ex127H : MvPolynomial (Fin 4) k := X 0 ^ 2 + X 1 ^ 3 + X 2 ^ 3 + X 3 ^ 3

/-- A point of `V(h)` where all partial derivatives of `h` vanish. -/
def IsJacobianSingular (h : MvPolynomial (Fin 4) k) (q : Fin 4 → k) : Prop :=
  eval q h = 0 ∧ ∀ i, eval q (pderiv i h) = 0

theorem ex127_pderiv_zero : pderiv 0 (ex127H (k := k)) = 2 * X 0 := by
  simp [ex127H, Derivation.leibniz_pow, pderiv_X]

theorem ex127_pderiv_succ (i : Fin 4) (hi : i ≠ 0) :
    pderiv i (ex127H (k := k)) = 3 * X i ^ 2 := by
  fin_cases i
  · exact absurd rfl hi
  all_goals simp [ex127H, Derivation.leibniz_pow, pderiv_X]

theorem ex127_eval_pderiv (q : Fin 4 → k) :
    eval q (pderiv 0 (ex127H (k := k))) = 2 * q 0 ∧
      ∀ i, i ≠ 0 → eval q (pderiv i (ex127H (k := k))) = 3 * q i ^ 2 := by
  refine ⟨by simp [ex127_pderiv_zero], fun i hi => by simp [ex127_pderiv_succ i hi]⟩

/-- Example 1.2.7, the case `p ≥ 5` (`2` and `3` are units). The only singular point is the
origin. -/
theorem ex127_singular_iff_of_ne (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (q : Fin 4 → k) :
    IsJacobianSingular ex127H q ↔ q = 0 := by
  obtain ⟨hd0, hd⟩ := ex127_eval_pderiv (k := k) q
  constructor
  · rintro ⟨-, hq⟩
    have e0 := hq 0
    rw [hd0] at e0
    have hi : ∀ i, i ≠ 0 → q i = 0 := fun i hi => by
      have := hq i
      rw [hd i hi] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp this).resolve_left h3)
    funext i
    by_cases h : i = 0
    · subst h
      exact (mul_eq_zero.mp e0).resolve_left h2
    · exact hi i h
  · rintro rfl
    refine ⟨by simp [ex127H], fun i => ?_⟩
    by_cases h : i = 0
    · subst h
      rw [hd0]
      simp
    · rw [hd i h]
      simp

/-- Example 1.2.7, the case `p = 3`. The Frobenius map gives `h = z^2 + (x + y + w)^3`. -/
theorem ex127_char3 [CharP k 3] : ex127H (k := k) = X 0 ^ 2 + (X 1 + X 2 + X 3) ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [add_pow_char, add_pow_char, ex127H]
  ring

theorem ex127_two_ne_zero_char3 [CharP k 3] : (2 : k) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff k 3 2).mp (by exact_mod_cast h)
  omega

/-- Example 1.2.7, the case `p = 3`. The singular locus is the plane `V(z, x + y + w)`. -/
theorem ex127_singular_iff_char3 [CharP k 3] (q : Fin 4 → k) :
    IsJacobianSingular ex127H q ↔ q 0 = 0 ∧ q 1 + q 2 + q 3 = 0 := by
  obtain ⟨hd0, hd⟩ := ex127_eval_pderiv (k := k) q
  have h3 : (3 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 3
  have hev : eval q (ex127H (k := k)) = q 0 ^ 2 + (q 1 + q 2 + q 3) ^ 3 := by
    rw [ex127_char3]
    simp
  constructor
  · rintro ⟨he, hq⟩
    have e0 := hq 0
    rw [hd0] at e0
    have hq0 : q 0 = 0 := (mul_eq_zero.mp e0).resolve_left ex127_two_ne_zero_char3
    refine ⟨hq0, ?_⟩
    rw [hev, hq0] at he
    simpa using he
  · rintro ⟨hq0, hs⟩
    refine ⟨by rw [hev, hq0, hs]; ring, fun i => ?_⟩
    by_cases h : i = 0
    · subst h
      rw [hd0, hq0, mul_zero]
    · rw [hd i h, h3, zero_mul]

/-- Example 1.2.7, the case `p = 3`. A translation by a point `v = (0, v_1, v_2, v_3)` of the
plane `x + y + w = 0` does not change `h`. -/
theorem ex127_translate_char3 [CharP k 3] {v : Fin 4 → k} (h0 : v 0 = 0)
    (hv : v 1 + v 2 + v 3 = 0) :
    aeval (fun i => X i + MvPolynomial.C (v i)) (ex127H (k := k)) = ex127H := by
  have hC : (MvPolynomial.C (v 1) + MvPolynomial.C (v 2) + MvPolynomial.C (v 3) :
      MvPolynomial (Fin 4) k) = 0 := by
    rw [← map_add, ← map_add, hv, map_zero]
  rw [ex127_char3]
  simp only [map_add, map_pow, MvPolynomial.aeval_X, h0, map_zero, add_zero]
  congr 2
  linear_combination hC

/-- Example 1.2.7, the case `p = 2`. The derivative of `h` in `z` is `0`, and the derivatives in
`x, y, w` are `x^2, y^2, w^2`. -/
theorem ex127_pderiv_char2 [CharP k 2] :
    pderiv 0 (ex127H (k := k)) = 0 ∧ ∀ i, i ≠ 0 → pderiv i (ex127H (k := k)) = X i ^ 2 := by
  have h2 : (2 : MvPolynomial (Fin 4) k) = 0 := by
    have : ((2 : ℕ) : MvPolynomial (Fin 4) k) = 0 := CharP.cast_eq_zero _ 2
    exact_mod_cast this
  have h3 : (3 : MvPolynomial (Fin 4) k) = 1 := by
    rw [show (3 : MvPolynomial (Fin 4) k) = 2 + 1 by norm_num, h2, zero_add]
  refine ⟨by rw [ex127_pderiv_zero, h2, zero_mul], fun i hi => ?_⟩
  rw [ex127_pderiv_succ i hi, h3, one_mul]

/-- Example 1.2.7, the case `p = 2`. The only singular point is the origin. -/
theorem ex127_singular_iff_char2 [CharP k 2] (q : Fin 4 → k) :
    IsJacobianSingular ex127H q ↔ q = 0 := by
  obtain ⟨-, hd⟩ := ex127_pderiv_char2 (k := k)
  constructor
  · rintro ⟨he, hq⟩
    have hi : ∀ i, i ≠ 0 → q i = 0 := fun i hi => by
      have := hq i
      rw [hd i hi] at this
      simpa using this
    have he' := he
    simp only [ex127H, map_add, map_pow, MvPolynomial.eval_X, hi 1 (by decide), hi 2 (by decide),
      hi 3 (by decide)] at he'
    have hq0 : q 0 = 0 := by simpa using he'
    funext i
    by_cases h : i = 0
    · subst h
      exact hq0
    · exact hi i h
  · rintro rfl
    refine ⟨by simp [ex127H], fun i => ?_⟩
    by_cases h : i = 0
    · subst h
      rw [ex127_pderiv_char2.1]
      simp
    · rw [hd i h]
      simp

end Example127

end Singularity
