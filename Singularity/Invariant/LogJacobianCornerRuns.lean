/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianSurfaceRuns
import Singularity.Invariant.OrderAlong

/-!
# A run with an infinite number of corner steps

This file proves the run of Example 3.13.15 of Volume 7, Section 3.13 of the handbook. The field
is `ZMod p` for a prime `p`. The variables `x, y, z` are the indices `0, 1, 2` of `Fin 3`, and the
divisor is `{y, z}`. At each point of the run,
`g = y^a z^b (x^p + y^m z^l) = x^p y^a z^b + y^(a+m) z^(b+l)`
with `m = μ + p` and `l = λ + p`. The start `P_0` has `(a, b, μ, λ) = (1, 1, 1, 0)`, that is
`g = x^p y z + y^(p+2) z^(p+1)`.

* The origin of the `y`-chart sends the data `(a, b, μ, λ)` to `(a + b, b, μ + λ, λ)`, and the
  origin of the `z`-chart sends them to `(a, a + b, μ, μ + λ)`. No cleaning is necessary.
* The number `b μ - a λ` does not change, so it is `1` at each point
  (`CornerData.IsGood`). Thus `a l - b m ≡ -1 (mod p)` (`cornerSeq_modEq`). So neither
  `x^p y^a z^b` nor `y^(a+m) z^(b+l)` is a `p`-th power (`not_dvd_and_dvd_a_b`,
  `not_dvd_and_dvd_add`), and `g` is clean.
* The log-Jacobian ideal is `J = (x^p, y^m z^l)` (`residualLogJacobian_cornerG`), so `ρ = p`
  (`logJacobianOrder_cornerPoly`), and the order of `G = x^p + y^m z^l` is `p`
  (`ord_residualFactor_cornerPoly`).
* From `P_0`, each sequence of the two charts is an infinite run with distinct points
  (`cornerRun_of_charts`).
* For each `h`, the variable `x` does not divide `g + h^p` (`not_X_dvd_cornerPoly_add_pow`). So the
  clean order of `g` along the surface `V(x)` is `0` (Example 3.13.15, part 3, the second claim).

* Let `Z = V(x_i : i ∈ S)` be a coordinate subvariety. If `S` does not both contain `x` and meet
  `{y, z}`, then `x^p` or `y^m z^l` is a generator of `J` with the order `0` along `Z`. So
  Lemma 3.13.14 gives `ν^G_Z ≤ 1 < p` (`orderGAlong_cornerPoly_le_one`,
  `cornerRun_orderGAlong_lt`). This is part 2 of Example 3.13.15 for coordinate subvarieties,
  with `h` a polynomial in the clean order.

This file does not prove part 2 of Example 3.13.15 for the subvarieties that are not coordinate
subvarieties, or the first claim of part 3.

## Main definitions

* `CornerRuns.CornerData`: the data `(a, b, μ, λ)` of a point.
* `CornerRuns.cornerPoint p D`: the point `({y, z}, g)` of the data `D`.
* `CornerRuns.cornerSeq c`: the data of the run that takes the charts `c`.

## Main results

* `CornerRuns.rhoStep_cornerPoint_y` and `CornerRuns.rhoStep_cornerPoint_z`: the two steps.
* `CornerRuns.residualLogJacobian_cornerG`: the ideal `J = (x^p, y^m z^l)`.
* `CornerRuns.cornerSeq_modEq`: the invariant `a l - b m ≡ -1 (mod p)`.
* `CornerRuns.cornerRun_of_charts`: Example 3.13.15, part 1, each sequence of the charts.
* `CornerRuns.cornerRun`: the run where the charts alternate.
* `CornerRuns.not_X_dvd_cornerPoly_add_pow`: the clean order along `V(x)` is `0`.
* `CornerRuns.cornerRun_orderGAlong_lt`: `ν^G_Z < p` along the coordinate subvarieties of
  part 2.

## References

* Volume 7, Section 3.13 of the handbook: Lemma 3.13.14 and Example 3.13.15.
-/

open MvPolynomial Finsupp

namespace Singularity

namespace CornerRuns

open SurfaceRuns

/-- The data `(a, b, μ, λ)` of a point of Example 3.13.15. The polynomial is
`x^p y^a z^b + y^(a+μ+p) z^(b+λ+p)`. -/
structure CornerData where
  /-- The exponent of `y` in the monomial factor. -/
  a : ℕ
  /-- The exponent of `z` in the monomial factor. -/
  b : ℕ
  /-- The number `μ = m - p`. -/
  mu : ℕ
  /-- The number `λ = l - p`. -/
  lam : ℕ

namespace CornerData

/-- The data of the start `P_0`: `(a, b, μ, λ) = (1, 1, 1, 0)`. -/
def start : CornerData := ⟨1, 1, 1, 0⟩

/-- The data after the origin of the `y`-chart. -/
def y (D : CornerData) : CornerData := ⟨D.a + D.b, D.b, D.mu + D.lam, D.lam⟩

/-- The data after the origin of the `z`-chart. -/
def z (D : CornerData) : CornerData := ⟨D.a, D.a + D.b, D.mu, D.mu + D.lam⟩

/-- The invariant of the run: `b μ = a λ + 1`. -/
def IsGood (D : CornerData) : Prop := D.b * D.mu = D.a * D.lam + 1

theorem isGood_start : start.IsGood := rfl

theorem IsGood.y {D : CornerData} (h : D.IsGood) : D.y.IsGood := by
  unfold IsGood CornerData.y at *
  dsimp only
  rw [mul_add, h]
  ring

theorem IsGood.z {D : CornerData} (h : D.IsGood) : D.z.IsGood := by
  unfold IsGood CornerData.z at *
  dsimp only
  rw [add_mul, h]
  ring

end CornerData

section Point

variable (p : ℕ) [Fact p.Prime]

/-- The monomial `M = y^m z^l` with `m = μ + p` and `l = λ + p`. -/
noncomputable def cornerM (mu lam : ℕ) : MvPolynomial (Fin 3) (ZMod p) :=
  X 1 ^ (mu + p) * X 2 ^ (lam + p)

/-- The residual factor `G = x^p + y^m z^l`. -/
noncomputable def cornerG (mu lam : ℕ) : MvPolynomial (Fin 3) (ZMod p) :=
  X 0 ^ p + cornerM p mu lam

/-- The polynomial `g = x^p y^a z^b + y^(a+m) z^(b+l)` of the data `D`. -/
noncomputable def cornerPoly (D : CornerData) : MvPolynomial (Fin 3) (ZMod p) :=
  X 0 ^ p * X 1 ^ D.a * X 2 ^ D.b + X 1 ^ (D.a + D.mu + p) * X 2 ^ (D.b + D.lam + p)

/-- The point `({y, z}, g)` of the data `D`. -/
noncomputable def cornerPoint (D : CornerData) : Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p) :=
  ({1, 2}, cornerPoly p D)

variable {p}

/-- The exponent of `x^p y^a z^b`. -/
noncomputable def cornerE1 (p : ℕ) (D : CornerData) : Fin 3 →₀ ℕ :=
  single 0 p + single 1 D.a + single 2 D.b

/-- The exponent of `y^(a+m) z^(b+l)`. -/
noncomputable def cornerE2 (p : ℕ) (D : CornerData) : Fin 3 →₀ ℕ :=
  single 1 (D.a + D.mu + p) + single 2 (D.b + D.lam + p)

theorem cornerPoly_eq_monomial (D : CornerData) :
    cornerPoly p D = monomial (cornerE1 p D) 1 + monomial (cornerE2 p D) 1 := by
  simp only [cornerPoly, cornerE1, cornerE2, X_pow_eq_monomial, monomial_mul_monomial, one_mul]

theorem cornerE2_ne_cornerE1 (D : CornerData) : cornerE2 p D ≠ cornerE1 p D := by
  intro h
  have h0 := congrArg (· 0) h
  have hp := (Fact.out : p.Prime).pos
  simp [cornerE1, cornerE2] at h0
  omega

theorem cornerPoly_ne_zero (D : CornerData) : cornerPoly p D ≠ 0 := by
  intro h
  have hc : (cornerPoly p D).coeff (cornerE1 p D) = 1 := by
    rw [cornerPoly_eq_monomial, coeff_add_apply, coeff_monomial, coeff_monomial, ite_eq_left rfl,
      ite_eq_right (cornerE2_ne_cornerE1 D), add_zero]
  rw [h] at hc
  simp at hc

/-- If `b μ = a λ + 1`, then `p` does not divide both `a` and `b`. So `x^p y^a z^b` is not a
`p`-th power. -/
theorem not_dvd_and_dvd_a_b {D : CornerData} (h : D.IsGood) : ¬ (p ∣ D.a ∧ p ∣ D.b) := by
  rintro ⟨ha, hb⟩
  have h1 : p ∣ D.a * D.lam + 1 := h ▸ dvd_mul_of_dvd_left hb D.mu
  have h2 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_left ha D.lam)).mp h1
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h2)

/-- If `b μ = a λ + 1`, then `p` does not divide both `a + m` and `b + l`. So
`y^(a+m) z^(b+l)` is not a `p`-th power. -/
theorem not_dvd_and_dvd_add {D : CornerData} (h : D.IsGood) :
    ¬ (p ∣ D.a + D.mu + p ∧ p ∣ D.b + D.lam + p) := by
  rintro ⟨hA, hB⟩
  have hA' := (ZMod.natCast_eq_zero_iff _ _).mpr hA
  have hB' := (ZMod.natCast_eq_zero_iff _ _).mpr hB
  have hp : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hi : ((D.b * D.mu : ℕ) : ZMod p) = ((D.a * D.lam + 1 : ℕ) : ZMod p) := congrArg _ h
  push_cast at hA' hB' hi
  have h1 : (1 : ZMod p) = 0 := by
    linear_combination (-1 : ZMod p) * hi + (D.mu : ZMod p) * hB' - (D.lam : ZMod p) * hA' -
      ((D.mu : ZMod p) - D.lam) * hp
  exact one_ne_zero h1

/-- If `b μ = a λ + 1`, then `g` is clean. -/
theorem isClean_cornerPoly {D : CornerData} (h : D.IsGood) : IsClean p (cornerPoly p D) := by
  intro d hd hall
  have hc := MvPolynomial.mem_support_iff.mp hd
  rw [cornerPoly_eq_monomial, coeff_add_apply, coeff_monomial, coeff_monomial] at hc
  by_cases h1 : cornerE1 p D = d
  · subst h1
    exact not_dvd_and_dvd_a_b h ⟨by simpa [cornerE1] using hall 1, by simpa [cornerE1] using hall 2⟩
  · by_cases h2 : cornerE2 p D = d
    · subst h2
      exact not_dvd_and_dvd_add h
        ⟨by simpa [cornerE2] using hall 1, by simpa [cornerE2] using hall 2⟩
    · rw [ite_eq_right h1, ite_eq_right h2, add_zero] at hc
      exact hc rfl

theorem le_ord_cornerM (mu lam : ℕ) : (p : ℕ∞) ≤ ord (cornerM p mu lam) := by
  rw [cornerM, ord_mul, ord_X_pow, ord_X_pow]
  norm_cast
  omega

theorem lt_ord_cornerM (mu lam : ℕ) : (p : ℕ∞) < ord (cornerM p mu lam) := by
  have hp := (Fact.out : p.Prime).pos
  rw [cornerM, ord_mul, ord_X_pow, ord_X_pow]
  norm_cast
  omega

theorem le_ord_cornerPoly (D : CornerData) : (p : ℕ∞) ≤ ord (cornerPoly p D) := by
  refine le_ord_add ?_ ?_
  · rw [ord_mul, ord_mul, ord_X_pow, ord_X_pow, ord_X_pow]
    norm_cast
    omega
  · rw [ord_mul, ord_X_pow, ord_X_pow]
    norm_cast
    omega

theorem cornerPoly_eq_mul (D : CornerData) :
    cornerPoly p D = monomial (single 1 D.a + single 2 D.b) 1 * cornerG p D.mu D.lam := by
  have h : (X 1 ^ D.a * X 2 ^ D.b : MvPolynomial (Fin 3) (ZMod p)) =
      monomial (single 1 D.a + single 2 D.b) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  rw [← h, cornerPoly, cornerG, cornerM]
  ring

theorem cornerG_eq (mu lam : ℕ) : cornerG p mu lam =
    monomial (single 0 p) 1 + monomial (single 1 (mu + p) + single 2 (lam + p)) 1 := by
  simp only [cornerG, cornerM, X_pow_eq_monomial, monomial_mul_monomial, one_mul]

theorem corner_hG (mu lam : ℕ) :
    ∀ i ∈ ({1, 2} : Finset (Fin 3)), ∃ d ∈ (cornerG p mu lam).support, d i = 0 := by
  intro i hi
  refine ⟨single 0 p, MvPolynomial.mem_support_iff.mpr ?_, ?_⟩
  · have hne : single 1 (mu + p) + single 2 (lam + p) ≠ (single 0 p : Fin 3 →₀ ℕ) := by
      intro h
      have h1 := congrArg (· 1) h
      have hp := (Fact.out : p.Prime).pos
      simp at h1
      omega
    rw [cornerG_eq, coeff_add_apply, coeff_monomial, coeff_monomial, ite_eq_left rfl,
      ite_eq_right hne, add_zero]
    exact one_ne_zero
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp

theorem divisorExponent_cornerPoly (D : CornerData) :
    divisorExponent {1, 2} (cornerPoly p D) = single 1 D.a + single 2 D.b := by
  rw [cornerPoly_eq_mul]
  exact KangarooCounterexample.divisorExponent_monomial_mul' (surface_hr D.a D.b) (corner_hG _ _)

theorem residualFactor_cornerPoly (D : CornerData) :
    residualFactor {1, 2} (cornerPoly p D) = cornerG p D.mu D.lam := by
  rw [cornerPoly_eq_mul]
  exact residualFactor_monomial_mul (surface_hr D.a D.b) (corner_hG _ _)

/-- The order `d` of `G = x^p + y^m z^l` is `p`. -/
theorem ord_residualFactor_cornerPoly (D : CornerData) :
    ord (residualFactor {1, 2} (cornerPoly p D)) = p := by
  rw [residualFactor_cornerPoly, cornerG, ord_add_of_lt, ord_X_pow]
  rw [ord_X_pow]
  exact lt_ord_cornerM _ _

theorem pderiv_zero_cornerM (mu lam : ℕ) : pderiv 0 (cornerM p mu lam) = 0 := by
  simp [cornerM, pderiv_X]

theorem X_mul_pderiv_one_cornerM (mu lam : ℕ) :
    X 1 * pderiv 1 (cornerM p mu lam) = ((mu + p : ℕ) : MvPolynomial (Fin 3) (ZMod p)) *
      cornerM p mu lam := by
  rw [cornerM, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, pderiv_X_self,
    pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1)]
  rcases Nat.exists_eq_add_of_lt (show 0 < mu + p from by
    have := (Fact.out : p.Prime).pos; omega) with ⟨n, hn⟩
  rw [hn]
  simp only [zero_add, Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, mul_one]
  push_cast
  ring

theorem X_mul_pderiv_two_cornerM (mu lam : ℕ) :
    X 2 * pderiv 2 (cornerM p mu lam) = ((lam + p : ℕ) : MvPolynomial (Fin 3) (ZMod p)) *
      cornerM p mu lam := by
  rw [cornerM, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, pderiv_X_self,
    pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  rcases Nat.exists_eq_add_of_lt (show 0 < lam + p from by
    have := (Fact.out : p.Prime).pos; omega) with ⟨n, hn⟩
  rw [hn]
  simp only [zero_add, Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, mul_one]
  push_cast
  ring

/-- **The ideal `J = (x^p, y^m z^l)`** (Example 3.13.15, part 1). The generators of `J` are
`∂_x G = 0`, `a G + y ∂_y G = a x^p + (a + m) M` and `b G + z ∂_z G = b x^p + (b + l) M`. The
determinant of the coefficients is `a l - b m ≡ -1 (mod p)`, so it is a unit. -/
theorem residualLogJacobian_cornerG {D : CornerData} (h : D.IsGood) :
    residualLogJacobian {1, 2} (single 1 D.a + single 2 D.b) (cornerG p D.mu D.lam) =
      Ideal.span {X 0 ^ p, cornerM p D.mu D.lam} := by
  set M := cornerM p D.mu D.lam with hM
  have e1 : (single 1 D.a + single 2 D.b : Fin 3 →₀ ℕ) 1 = D.a := by simp
  have e2 : (single 1 D.a + single 2 D.b : Fin 3 →₀ ℕ) 2 = D.b := by simp
  have g1 : (((single 1 D.a + single 2 D.b : Fin 3 →₀ ℕ) 1 : ℕ) : ZMod p) •
      cornerG p D.mu D.lam + X 1 * pderiv 1 (cornerG p D.mu D.lam) =
      (D.a : MvPolynomial (Fin 3) (ZMod p)) * X 0 ^ p +
        ((D.a + (D.mu + p) : ℕ) : MvPolynomial (Fin 3) (ZMod p)) * M := by
    rw [e1, cornerG, map_add, mul_add, pderiv_X_zero_pow, mul_zero, zero_add,
      X_mul_pderiv_one_cornerM, smul_eq_C_mul, hM]
    simp only [map_natCast]
    push_cast
    ring
  have g2 : (((single 1 D.a + single 2 D.b : Fin 3 →₀ ℕ) 2 : ℕ) : ZMod p) •
      cornerG p D.mu D.lam + X 2 * pderiv 2 (cornerG p D.mu D.lam) =
      (D.b : MvPolynomial (Fin 3) (ZMod p)) * X 0 ^ p +
        ((D.b + (D.lam + p) : ℕ) : MvPolynomial (Fin 3) (ZMod p)) * M := by
    rw [e2, cornerG, map_add, mul_add, pderiv_X_zero_pow, mul_zero, zero_add,
      X_mul_pderiv_two_cornerM, smul_eq_C_mul, hM]
    simp only [map_natCast]
    push_cast
    ring
  have g0 : pderiv 0 (cornerG p D.mu D.lam) = 0 := by
    rw [cornerG, map_add, pderiv_X_zero_pow, pderiv_zero_cornerM, add_zero]
  have hD : (D.a : MvPolynomial (Fin 3) (ZMod p)) * ((D.b + (D.lam + p) : ℕ) : _) -
      (D.b : MvPolynomial (Fin 3) (ZMod p)) * ((D.a + (D.mu + p) : ℕ) : _) = -1 := by
    have hp : ((p : ℕ) : MvPolynomial (Fin 3) (ZMod p)) = 0 := CharP.cast_eq_zero _ p
    have hi : ((D.b * D.mu : ℕ) : MvPolynomial (Fin 3) (ZMod p)) =
        ((D.a * D.lam + 1 : ℕ) : MvPolynomial (Fin 3) (ZMod p)) := congrArg _ h
    push_cast at hi ⊢
    linear_combination (-1 : MvPolynomial (Fin 3) (ZMod p)) * hi +
      ((D.a : MvPolynomial (Fin 3) (ZMod p)) - D.b) * hp
  apply le_antisymm
  · rw [residualLogJacobian, Ideal.span_le]
    rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl
      · rw [SetLike.mem_coe]
        dsimp only
        rw [g1]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      · rw [SetLike.mem_coe]
        dsimp only
        rw [g2]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · have : i = 0 := by
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_compl_iff,
          Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        fin_cases i <;> simp_all
      subst this
      rw [SetLike.mem_coe]
      dsimp only
      rw [g0]
      exact Ideal.zero_mem _
  · have m1 : (D.a : MvPolynomial (Fin 3) (ZMod p)) * X 0 ^ p +
        ((D.a + (D.mu + p) : ℕ) : MvPolynomial (Fin 3) (ZMod p)) * M ∈
        residualLogJacobian {1, 2} (single 1 D.a + single 2 D.b) (cornerG p D.mu D.lam) := by
      rw [← g1, residualLogJacobian]
      exact Ideal.subset_span (Or.inl ⟨1, by simp, rfl⟩)
    have m2 : (D.b : MvPolynomial (Fin 3) (ZMod p)) * X 0 ^ p +
        ((D.b + (D.lam + p) : ℕ) : MvPolynomial (Fin 3) (ZMod p)) * M ∈
        residualLogJacobian {1, 2} (single 1 D.a + single 2 D.b) (cornerG p D.mu D.lam) := by
      rw [← g2, residualLogJacobian]
      exact Ideal.subset_span (Or.inl ⟨2, by simp, rfl⟩)
    rw [Ideal.span_le]
    rintro s (rfl | rfl)
    · have e : X 0 ^ p = ((D.a + (D.mu + p) : ℕ) : MvPolynomial (Fin 3) (ZMod p)) *
          ((D.b : MvPolynomial (Fin 3) (ZMod p)) * X 0 ^ p +
            ((D.b + (D.lam + p) : ℕ) : MvPolynomial (Fin 3) (ZMod p)) * M) -
          ((D.b + (D.lam + p) : ℕ) : MvPolynomial (Fin 3) (ZMod p)) *
          ((D.a : MvPolynomial (Fin 3) (ZMod p)) * X 0 ^ p +
            ((D.a + (D.mu + p) : ℕ) : MvPolynomial (Fin 3) (ZMod p)) * M) := by
        linear_combination X 0 ^ p * hD
      rw [SetLike.mem_coe, e]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ m2) (Ideal.mul_mem_left _ _ m1)
    · have e : M = (D.b : MvPolynomial (Fin 3) (ZMod p)) *
          ((D.a : MvPolynomial (Fin 3) (ZMod p)) * X 0 ^ p +
            ((D.a + (D.mu + p) : ℕ) : MvPolynomial (Fin 3) (ZMod p)) * M) -
          (D.a : MvPolynomial (Fin 3) (ZMod p)) *
          ((D.b : MvPolynomial (Fin 3) (ZMod p)) * X 0 ^ p +
            ((D.b + (D.lam + p) : ℕ) : MvPolynomial (Fin 3) (ZMod p)) * M) := by
        linear_combination M * hD
      rw [SetLike.mem_coe, e]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ m1) (Ideal.mul_mem_left _ _ m2)

/-- If `b μ = a λ + 1`, then `ρ = p` at `({y, z}, g)`. -/
theorem logJacobianOrder_cornerPoly {D : CornerData} (h : D.IsGood) :
    logJacobianOrder ({1, 2} : Finset (Fin 3)) (cornerPoly p D) = p := by
  rw [logJacobianOrder, divisorExponent_cornerPoly, residualFactor_cornerPoly,
    residualLogJacobian_cornerG h]
  refine idealOrd_span_eq' ?_ (Set.mem_insert _ _) (ord_X_pow 0 p)
  rintro s (rfl | rfl)
  · exact (ord_X_pow 0 p).ge
  · exact le_ord_cornerM _ _

theorem pointChart_cornerPoly_y (D : CornerData) :
    pointChart 1 0 (cornerPoly p D) = X 1 ^ p * cornerPoly p D.y := by
  have hx : pointChart (1 : Fin 3) 0 (X 0 : MvPolynomial (Fin 3) (ZMod p)) = X 1 * X 0 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have hz : pointChart (1 : Fin 3) 0 (X 2 : MvPolynomial (Fin 3) (ZMod p)) = X 1 * X 2 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  simp only [cornerPoly, CornerData.y, map_add, map_mul, map_pow, hx, hz, pointChart_X_self]
  ring

theorem pointChart_cornerPoly_z (D : CornerData) :
    pointChart 2 0 (cornerPoly p D) = X 2 ^ p * cornerPoly p D.z := by
  have hx : pointChart (2 : Fin 3) 0 (X 0 : MvPolynomial (Fin 3) (ZMod p)) = X 2 * X 0 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have hy : pointChart (2 : Fin 3) 0 (X 1 : MvPolynomial (Fin 3) (ZMod p)) = X 2 * X 1 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  simp only [cornerPoly, CornerData.z, map_add, map_mul, map_pow, hx, hy, pointChart_X_self]
  ring

/-- **The `y`-chart of Example 3.13.15.** If `b μ = a λ + 1`, the origin of the `y`-chart sends
the data `(a, b, μ, λ)` to `(a + b, b, μ + λ, λ)`, no cleaning is necessary, and `ρ = p` at both
points. -/
theorem rhoStep_cornerPoint_y {D : CornerData} (h : D.IsGood) :
    RhoStep p p (cornerPoint p D) (cornerPoint p D.y) := by
  refine ⟨1, 0, cornerPoly p D.y, cornerPoly_ne_zero D, isClean_cornerPoly h,
    le_ord_cornerPoly D, pointChart_cornerPoly_y D, ?_, logJacobianOrder_cornerPoly h,
    logJacobianOrder_cornerPoly h.y⟩
  show ((({1, 2} : Finset (Fin 3)), cornerPoly p D.y) :
      Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p)) =
    (blowupDivisor ({1, 2} : Finset (Fin 3)) 1 0, cleanPart p (cornerPoly p D.y))
  rw [blowupDivisor_surface_y, cleanPart_eq_self (isClean_cornerPoly h.y)]

/-- **The `z`-chart of Example 3.13.15.** If `b μ = a λ + 1`, the origin of the `z`-chart sends
the data `(a, b, μ, λ)` to `(a, a + b, μ, μ + λ)`, no cleaning is necessary, and `ρ = p` at both
points. -/
theorem rhoStep_cornerPoint_z {D : CornerData} (h : D.IsGood) :
    RhoStep p p (cornerPoint p D) (cornerPoint p D.z) := by
  refine ⟨2, 0, cornerPoly p D.z, cornerPoly_ne_zero D, isClean_cornerPoly h,
    le_ord_cornerPoly D, pointChart_cornerPoly_z D, ?_, logJacobianOrder_cornerPoly h,
    logJacobianOrder_cornerPoly h.z⟩
  show ((({1, 2} : Finset (Fin 3)), cornerPoly p D.z) :
      Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p)) =
    (blowupDivisor ({1, 2} : Finset (Fin 3)) 2 0, cleanPart p (cornerPoly p D.z))
  rw [blowupDivisor_surface_z, cleanPart_eq_self (isClean_cornerPoly h.z)]

/-- **The clean order along `V(x)` is `0`** (Example 3.13.15, part 3). If `b μ = a λ + 1`, then
for each `h` the variable `x` does not divide `g + h^p`. The reason is that the term
`y^(a+m) z^(b+l)` of `g` is not in `(x)`, and it is not a `p`-th power. -/
theorem not_X_dvd_cornerPoly_add_pow {D : CornerData} (hD : D.IsGood)
    (h : MvPolynomial (Fin 3) (ZMod p)) : ¬ X 0 ∣ cornerPoly p D + h ^ p := by
  rintro ⟨q, hq⟩
  have hc := congrArg (fun F : MvPolynomial (Fin 3) (ZMod p) => F.coeff (cornerE2 p D)) hq
  have hnot : ¬ ∀ i, p ^ 1 ∣ cornerE2 p D i := fun hall => not_dvd_and_dvd_add hD
    ⟨by simpa [cornerE2] using hall 1, by simpa [cornerE2] using hall 2⟩
  have hpow := coeff_pow_eq_zero_of_not_dvd p 1 h hnot
  rw [pow_one] at hpow
  rw [coeff_add_apply, hpow, add_zero, cornerPoly_eq_monomial, coeff_add_apply, coeff_monomial,
    coeff_monomial, ite_eq_left rfl, ite_eq_right (cornerE2_ne_cornerE1 D).symm, zero_add,
    coeff_X_mul', ite_eq_right (by simp [cornerE2])] at hc
  exact one_ne_zero hc

/-- **Example 3.13.15, part 2, for a coordinate subvariety.** Let `Z = V(x_i : i ∈ S)`, where `S`
does not both contain `x` and meet `{y, z}`. Then the order of `G` along `Z` is at most `1`. The
reason is that `J = (x^p, y^m z^l)` has a generator with the order `0` along `Z`, so Lemma 3.13.14
gives the bound. -/
theorem orderGAlong_cornerPoly_le_one {D : CornerData} (h : D.IsGood) (S : Finset (Fin 3))
    (hS : ¬ (0 ∈ S ∧ (1 ∈ S ∨ 2 ∈ S))) : orderGAlong p {1, 2} S (cornerPoly p D) ≤ 1 := by
  refine (orderGAlong_le_idealOrdAlong_add_one p {1, 2} S (cornerPoly p D)).trans ?_
  rw [divisorExponent_cornerPoly, residualFactor_cornerPoly, residualLogJacobian_cornerG h]
  have h0 : idealOrdAlong S (Ideal.span {X 0 ^ p, cornerM p D.mu D.lam}) = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    by_cases h0S : 0 ∈ S
    · have h1 : 1 ∉ S := fun h1 => hS ⟨h0S, Or.inl h1⟩
      have h2 : 2 ∉ S := fun h2 => hS ⟨h0S, Or.inr h2⟩
      refine (idealOrdAlong_le_ordAlong
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))).trans (le_of_eq ?_)
      rw [cornerM, ordAlong_mul, ordAlong_X_pow, ordAlong_X_pow]
      simp [h1, h2]
    · refine (idealOrdAlong_le_ordAlong (Ideal.subset_span (Set.mem_insert _ _))).trans
        (le_of_eq ?_)
      rw [ordAlong_X_pow]
      simp [h0S]
  rw [h0, zero_add]

end Point

/-! ### The runs -/

/-- The data of a run of Example 3.13.15. The run starts at `P_0`. At step `k` it takes the
`y`-chart if `c k` is true, and the `z`-chart if not. -/
def cornerSeq (c : ℕ → Bool) : ℕ → CornerData
  | 0 => CornerData.start
  | k + 1 => if c k then (cornerSeq c k).y else (cornerSeq c k).z

theorem cornerSeq_succ (c : ℕ → Bool) (k : ℕ) :
    cornerSeq c (k + 1) = if c k then (cornerSeq c k).y else (cornerSeq c k).z := rfl

/-- The invariant `b μ = a λ + 1` holds along each run, and `a, b ≥ 1`. -/
theorem cornerSeq_spec (c : ℕ → Bool) (k : ℕ) :
    (cornerSeq c k).IsGood ∧ 1 ≤ (cornerSeq c k).a ∧ 1 ≤ (cornerSeq c k).b := by
  induction k with
  | zero => exact ⟨CornerData.isGood_start, le_rfl, le_rfl⟩
  | succ k ih =>
    obtain ⟨h, ha, hb⟩ := ih
    rw [cornerSeq_succ]
    cases c k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨h.z, ha, by simp only [CornerData.z]; omega⟩
    · simp only [↓reduceIte]
      exact ⟨h.y, by simp only [CornerData.y]; omega, hb⟩

/-- **The invariant of Example 3.13.15.** Along each run, `a l - b m ≡ -1 (mod p)`, with
`m = μ + p` and `l = λ + p`. -/
theorem cornerSeq_modEq (p : ℕ) (c : ℕ → Bool) (k : ℕ) :
    ((cornerSeq c k).a : ℤ) * ((cornerSeq c k).lam + p) -
      (cornerSeq c k).b * ((cornerSeq c k).mu + p) ≡ -1 [ZMOD p] := by
  have hz : ((cornerSeq c k).b : ℤ) * (cornerSeq c k).mu = (cornerSeq c k).a * (cornerSeq c k).lam + 1 := by
    exact_mod_cast (cornerSeq_spec c k).1
  refine Int.modEq_iff_dvd.mpr ⟨((cornerSeq c k).b : ℤ) - (cornerSeq c k).a, ?_⟩
  linear_combination hz

/-- Along each run, neither `x^p y^a z^b` nor `y^(a+m) z^(b+l)` is a `p`-th power. -/
theorem cornerSeq_not_dvd (p : ℕ) [Fact p.Prime] (c : ℕ → Bool) (k : ℕ) :
    ¬ (p ∣ (cornerSeq c k).a ∧ p ∣ (cornerSeq c k).b) ∧
      ¬ (p ∣ (cornerSeq c k).a + (cornerSeq c k).mu + p ∧
        p ∣ (cornerSeq c k).b + (cornerSeq c k).lam + p) :=
  ⟨not_dvd_and_dvd_a_b (cornerSeq_spec c k).1, not_dvd_and_dvd_add (cornerSeq_spec c k).1⟩

theorem cornerSeq_sum_lt (c : ℕ → Bool) (k : ℕ) :
    (cornerSeq c k).a + (cornerSeq c k).b < (cornerSeq c (k + 1)).a + (cornerSeq c (k + 1)).b := by
  obtain ⟨-, ha, hb⟩ := cornerSeq_spec c k
  rw [cornerSeq_succ]
  cases c k
  · simp only [Bool.false_eq_true, ↓reduceIte, CornerData.z]
    omega
  · simp only [↓reduceIte, CornerData.y]
    omega

section Run

variable (p : ℕ) [Fact p.Prime]

/-- The point `P_k` of the run of Example 3.13.15 that takes the charts `c`. -/
noncomputable def cornerRunPoint (c : ℕ → Bool) (k : ℕ) :
    Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p) :=
  cornerPoint p (cornerSeq c k)

variable {p}

theorem rhoStep_cornerRunPoint (c : ℕ → Bool) (k : ℕ) :
    RhoStep p p (cornerRunPoint p c k) (cornerRunPoint p c (k + 1)) := by
  have h := (cornerSeq_spec c k).1
  rw [cornerRunPoint, cornerRunPoint, cornerSeq_succ]
  cases c k
  · exact rhoStep_cornerPoint_z h
  · exact rhoStep_cornerPoint_y h

theorem cornerRunPoint_injective (c : ℕ → Bool) : Function.Injective (cornerRunPoint p c) := by
  have hm : StrictMono fun k => (cornerSeq c k).a + (cornerSeq c k).b :=
    strictMono_nat_of_lt_succ (cornerSeq_sum_lt c)
  intro k l h
  have h1 := congrArg (fun P => divisorExponent P.1 P.2 1) h
  have h2 := congrArg (fun P => divisorExponent P.1 P.2 2) h
  simp only [cornerRunPoint, cornerPoint, divisorExponent_cornerPoly] at h1 h2
  simp at h1 h2
  exact hm.injective (by simp only [h1, h2])

/-- **Example 3.13.15, part 1, each sequence of the charts.** Let `p` be a prime, `Δ = {y, z}`
and `g = x^p y z + y^(p+2) z^(p+1)`. Each sequence of the `y`-chart and the `z`-chart at the
origin is an infinite run, `ρ = p` at each point, and the points are distinct. -/
theorem cornerRun_of_charts (c : ℕ → Bool) :
    (∀ k, RhoStep p p (cornerRunPoint p c k) (cornerRunPoint p c (k + 1))) ∧
    (∀ k, logJacobianOrder (cornerRunPoint p c k).1 (cornerRunPoint p c k).2 = p) ∧
    Function.Injective (cornerRunPoint p c) :=
  ⟨rhoStep_cornerRunPoint c, fun k => logJacobianOrder_cornerPoly (cornerSeq_spec c k).1,
    cornerRunPoint_injective c⟩

/-- **Example 3.13.15** (Volume 7, Section 3.13 of the handbook). Let `p` be a prime,
`Δ = {y, z}` and `g = x^p y z + y^(p+2) z^(p+1)`. The `y`-chart and the `z`-chart at the origin
alternate, so each step from the second step on is a corner step. The sequence is an infinite
run, `ρ = p` at each point, and the points are distinct. -/
theorem cornerRun :
    (∀ k, RhoStep p p (cornerRunPoint p alternate k) (cornerRunPoint p alternate (k + 1))) ∧
    (∀ k, logJacobianOrder (cornerRunPoint p alternate k).1
      (cornerRunPoint p alternate k).2 = p) ∧
    Function.Injective (cornerRunPoint p alternate) :=
  cornerRun_of_charts alternate

/-- **Example 3.13.15, part 2, for coordinate subvarieties.** At each point of a run, let
`Z = V(x_i : i ∈ S)`, where `S` does not both contain `x` and meet `{y, z}`. Then the order of
`G` along `Z` is less than `p`. -/
theorem cornerRun_orderGAlong_lt (c : ℕ → Bool) (k : ℕ) (S : Finset (Fin 3))
    (hS : ¬ (0 ∈ S ∧ (1 ∈ S ∨ 2 ∈ S))) :
    orderGAlong p (cornerRunPoint p c k).1 S (cornerRunPoint p c k).2 < p :=
  (orderGAlong_cornerPoly_le_one (cornerSeq_spec c k).1 S hS).trans_lt
    (by exact_mod_cast (Fact.out : p.Prime).one_lt)

end Run

/-- **Example 3.13.15 for `p = 2`.** -/
theorem cornerRun_two :
    (∀ k, RhoStep 2 2 (cornerRunPoint 2 alternate k) (cornerRunPoint 2 alternate (k + 1))) ∧
    (∀ k, logJacobianOrder (cornerRunPoint 2 alternate k).1
      (cornerRunPoint 2 alternate k).2 = 2) ∧
    Function.Injective (cornerRunPoint 2 alternate) :=
  cornerRun

end CornerRuns

end Singularity
