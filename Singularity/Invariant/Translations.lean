/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianCornerCurves
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Multiplicity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Runs with free translations: an example and the combinatorial facts

This file proves Example 3.15.18 of Volume 7 of the handbook, and the combinatorial facts that
Section 3.16 of Volume 7 uses: the primitive vectors before Theorem 3.16.10, and the facts of
Lucas type of Lemma 3.16.4 and Remark 3.16.15.

## Example 3.15.18

The field is `ZMod p` for a prime `p ≥ 3`. The variables `x, y, z` are the indices `0, 1, 2` of
`Fin 3`, the divisor is `Δ = {y, z}`, and `g = x^2 y^(p-2) z^(p-2)` (`exPoly`). The point `g` is
clean, `ord g = 2p - 2 ≥ p`, `G = x^2`, `d = 2`, `ρ = 1` and `deg_x g = 2 < p`
(`example_3_15_18`). The origin of the `y`-chart and the origin of the `z`-chart send `g` to
`y^p g` and `z^p g`, and the new divisor is `{y, z}` (`pointChart_exPoly_y`,
`pointChart_exPoly_z`). So each step at the origin of one of the two charts is a step with
`ρ = 1` at both points (`rhoStep_exPoint_y`, `rhoStep_exPoint_z`), and each sequence of the two
charts at the origin is an infinite run with all translations `0` and `ρ = 1` at each point
(`exRun_of_charts`).

## The primitive vectors

A word in the two charts is a sequence `ch : ℕ → Bool`, where `true` is the `y`-chart and
`false` is the `z`-chart. The `y`-chart sends `(y_m, z_m)` to `(y_{m+1}, y_{m+1} z_{m+1})`, and
the `z`-chart sends `(y_m, z_m)` to `(y_{m+1} z_{m+1}, z_{m+1})`. The exponent matrix of a chart
(`chartMat`) has determinant `1` (`det_chartMat`). The rows of `expMat ch m` are the exponent
vectors `u, w` of `y_m` and `z_m` in `y_N, z_N`. The step multiplies it by the inverse of the
exponent matrix of the chart (`chartMat_mul_expMat_succ`), so its determinant is `1`
(`det_expMat`). The vector `n_m = -(u + w)` (`nVec`) is the exponent of
`N_m = M_m / (y_N z_N) = 1 / (y_m z_m)` (`nVec_eq_mVec_sub`), and it is primitive at each step of
each word (`isCoprime_nVec`, `gcd_nVec`). If `k n = k' n'` for primitive vectors `n, n'` and
positive integers `k, k'`, then `k = k'` and `n = n'` (`eq_of_smul_eq_smul_of_isCoprime`,
`nVec_smul_inj`).

## Lucas type facts

* `(p^a s choose p^a) ≡ s (mod p)` (`choose_pow_mul_pow_modEq`). This is the step of the proof of
  Lemma 3.16.4. So `(i choose p^a) ≠ 0` in a field of characteristic `p` for `i = p^a s` with
  `p ∤ s` (`choose_pow_mul_pow_ne_zero`).
* `(p^e choose l) = 0` in characteristic `p` for `0 < l < p^e` (`choose_prime_pow_eq_zero`).
* The lemma of Lucas type of Remark 3.16.15. Let `S(U) = Σ_{i ∈ I} c_i ((U + Z)^i - U^i)`, with
  `Z` a variable (`lucasPoly`). If each `i ∈ I` is a power of `p`, then `S` is constant
  (`lucasPoly_eq_C_of_forall_pow`). If `i₀ = p^a s ∈ I` with `s ≥ 2`, `p ∤ s` and `c_{i₀} ≠ 0`,
  then the coefficient of `U^(p^a)` is not `0` (`coeff_lucasPoly_ne_zero`). So for `0 ∉ I` and
  all `c_i ≠ 0`, `S` is constant if and only if each `i ∈ I` is a power of `p`
  (`lucasPoly_isConstant_iff`). Here `Z` is a variable, and the handbook takes for `Z` an element
  that is transcendental over `K`. The two forms are the same by the substitution `Z ↦ Z`.

## References

* Volume 7, Section 3.15 of the handbook: Example 3.15.18.
* Volume 7, Section 3.16 of the handbook: Lemma 3.16.4, the primitive vectors before Theorem
  3.16.10, and Remark 3.16.15.
-/

namespace Singularity

namespace Translations

/-! ### Example 3.15.18 -/

section Example

open MvPolynomial Finsupp CornerCurves SurfaceRuns

variable (p : ℕ) [Fact p.Prime]

/-- The polynomial `g = x^2 y^(p-2) z^(p-2)` of Example 3.15.18 of Volume 7 of the handbook. -/
noncomputable def exPoly : MvPolynomial (Fin 3) (ZMod p) :=
  curvePoly p 2 (p - 2) (p - 2)

/-- The point `({y, z}, x^2 y^(p-2) z^(p-2))` of Example 3.15.18 of Volume 7 of the handbook. -/
noncomputable def exPoint : Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p) :=
  ({1, 2}, exPoly p)

/-- The variable of the chart: `y` for `true` and `z` for `false`. -/
def chartVar (b : Bool) : Fin 3 := if b then 1 else 2

variable {p}

omit [Fact p.Prime] in
theorem not_dvd_two (hp : 3 ≤ p) : ¬ p ∣ 2 := fun h => by
  have := Nat.le_of_dvd two_pos h
  omega

theorem isClean_exPoly (hp : 3 ≤ p) : IsClean p (exPoly p) :=
  isClean_curvePoly (not_dvd_two hp) _ _

theorem exPoly_ne_zero : exPoly p ≠ 0 := curvePoly_ne_zero _ _ _

theorem ord_exPoly (hp : 3 ≤ p) : ord (exPoly p) = ((2 * p - 2 : ℕ) : ℕ∞) := by
  rw [exPoly, curvePoly_eq_monomial, ord_monomial one_ne_zero, map_add, map_add, degree_single,
    degree_single, degree_single]
  congr 1
  omega

theorem le_ord_exPoly (hp : 3 ≤ p) : (p : ℕ∞) ≤ ord (exPoly p) := by
  rw [ord_exPoly hp]
  exact_mod_cast (by omega : p ≤ 2 * p - 2)

theorem residualFactor_exPoly : residualFactor {1, 2} (exPoly p) = X 0 ^ 2 :=
  residualFactor_curvePoly _ _ _

theorem logJacobianOrder_exPoly (hp : 3 ≤ p) :
    logJacobianOrder ({1, 2} : Finset (Fin 3)) (exPoly p) = 1 := by
  rw [exPoly, logJacobianOrder_curvePoly (not_dvd_two hp)]
  norm_num

theorem degreeOf_exPoly : degreeOf 0 (exPoly p) = 2 := by
  rw [exPoly, curvePoly_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero]
  simp

/-- **The `y`-chart of Example 3.15.18.** The origin of the `y`-chart, `x = y x'`, `z = y z'`,
sends `x^2 y^(p-2) z^(p-2)` to `y^p x'^2 y^(p-2) z'^(p-2)`. -/
theorem pointChart_exPoly_y (hp : 3 ≤ p) :
    pointChart 1 0 (exPoly p) = X 1 ^ p * exPoly p := by
  have hx : pointChart (1 : Fin 3) 0 (X 0 : MvPolynomial (Fin 3) (ZMod p)) = X 1 * X 0 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have hz : pointChart (1 : Fin 3) 0 (X 2 : MvPolynomial (Fin 3) (ZMod p)) = X 1 * X 2 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  obtain ⟨m, hm⟩ : ∃ m, p - 2 = m := ⟨_, rfl⟩
  have hpm : p = m + 2 := by omega
  have e : (X 1 ^ p : MvPolynomial (Fin 3) (ZMod p)) = X 1 ^ 2 * X 1 ^ m := by
    rw [← pow_add]
    congr 1
    omega
  simp only [exPoly, curvePoly, map_mul, map_pow, hx, hz, pointChart_X_self, hm, e]
  ring

/-- **The `z`-chart of Example 3.15.18.** The origin of the `z`-chart, `x = z x'`, `y = z y'`,
sends `x^2 y^(p-2) z^(p-2)` to `z^p x'^2 y'^(p-2) z^(p-2)`. -/
theorem pointChart_exPoly_z (hp : 3 ≤ p) :
    pointChart 2 0 (exPoly p) = X 2 ^ p * exPoly p := by
  have hx : pointChart (2 : Fin 3) 0 (X 0 : MvPolynomial (Fin 3) (ZMod p)) = X 2 * X 0 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have hy : pointChart (2 : Fin 3) 0 (X 1 : MvPolynomial (Fin 3) (ZMod p)) = X 2 * X 1 := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  obtain ⟨m, hm⟩ : ∃ m, p - 2 = m := ⟨_, rfl⟩
  have hpm : p = m + 2 := by omega
  have e : (X 2 ^ p : MvPolynomial (Fin 3) (ZMod p)) = X 2 ^ 2 * X 2 ^ m := by
    rw [← pow_add]
    congr 1
    omega
  simp only [exPoly, curvePoly, map_mul, map_pow, hx, hy, pointChart_X_self, hm, e]
  ring

theorem pointChart_exPoly (hp : 3 ≤ p) (b : Bool) :
    pointChart (chartVar b) 0 (exPoly p) = X (chartVar b) ^ p * exPoly p := by
  cases b
  · exact pointChart_exPoly_z hp
  · exact pointChart_exPoly_y hp

theorem blowupDivisor_chartVar (b : Bool) :
    blowupDivisor ({1, 2} : Finset (Fin 3)) (chartVar b) (0 : Fin 3 → ZMod p) = {1, 2} := by
  cases b
  · exact blowupDivisor_surface_z
  · exact blowupDivisor_surface_y

/-- **The step of the `y`-chart** (Example 3.15.18). The origin of the `y`-chart sends the point
`({y, z}, x^2 y^(p-2) z^(p-2))` to itself, and `ρ = 1` at both points. -/
theorem rhoStep_exPoint_y (hp : 3 ≤ p) : RhoStep p 1 (exPoint p) (exPoint p) := by
  refine ⟨1, 0, exPoly p, exPoly_ne_zero, isClean_exPoly hp, le_ord_exPoly hp,
    pointChart_exPoly_y hp, ?_, logJacobianOrder_exPoly hp, logJacobianOrder_exPoly hp⟩
  show ((({1, 2} : Finset (Fin 3)), exPoly p) : Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p)) =
    (blowupDivisor ({1, 2} : Finset (Fin 3)) 1 0, cleanPart p (exPoly p))
  rw [blowupDivisor_surface_y, cleanPart_eq_self (isClean_exPoly hp)]

/-- **The step of the `z`-chart** (Example 3.15.18). The origin of the `z`-chart sends the point
`({y, z}, x^2 y^(p-2) z^(p-2))` to itself, and `ρ = 1` at both points. -/
theorem rhoStep_exPoint_z (hp : 3 ≤ p) : RhoStep p 1 (exPoint p) (exPoint p) := by
  refine ⟨2, 0, exPoly p, exPoly_ne_zero, isClean_exPoly hp, le_ord_exPoly hp,
    pointChart_exPoly_z hp, ?_, logJacobianOrder_exPoly hp, logJacobianOrder_exPoly hp⟩
  show ((({1, 2} : Finset (Fin 3)), exPoly p) : Finset (Fin 3) × MvPolynomial (Fin 3) (ZMod p)) =
    (blowupDivisor ({1, 2} : Finset (Fin 3)) 2 0, cleanPart p (exPoly p))
  rw [blowupDivisor_surface_z, cleanPart_eq_self (isClean_exPoly hp)]

/-- **Example 3.15.18, the point** (Volume 7 of the handbook). Let `p ≥ 3` be a prime,
`Δ = {y, z}` and `g = x^2 y^(p-2) z^(p-2)`. Then `g` is clean, `ord g = 2p - 2 ≥ p`, `G = x^2`,
`d = ord G = 2`, `ρ = 1` and `deg_x g = 2 < p`. -/
theorem example_3_15_18 (hp : 3 ≤ p) :
    IsClean p (exPoly p) ∧ ord (exPoly p) = ((2 * p - 2 : ℕ) : ℕ∞) ∧ (p : ℕ∞) ≤ ord (exPoly p) ∧
      residualFactor {1, 2} (exPoly p) = X 0 ^ 2 ∧ ord (residualFactor {1, 2} (exPoly p)) = 2 ∧
      logJacobianOrder ({1, 2} : Finset (Fin 3)) (exPoly p) = 1 ∧
      degreeOf 0 (exPoly p) = 2 ∧ 2 < p := by
  refine ⟨isClean_exPoly hp, ord_exPoly hp, le_ord_exPoly hp, residualFactor_exPoly, ?_,
    logJacobianOrder_exPoly hp, degreeOf_exPoly, by omega⟩
  simp [residualFactor_exPoly, ord_X_pow]

/-- **Example 3.15.18, the runs** (Volume 7 of the handbook). Let `p ≥ 3` be a prime,
`Δ = {y, z}` and `g = x^2 y^(p-2) z^(p-2)`. For each sequence `ch` of the two charts, the step
`k` is the origin of the `y`-chart if `ch k` is true and of the `z`-chart if not. Each step sends
`g` to `x_j^p g`, with the translation `0`, keeps the divisor `{y, z}`, and is a step with `ρ = 1`
at both points. So each such sequence, for example one in which both charts occur an infinite
number of times, is an infinite run with all translations `0` and `ρ = 1` at each point. -/
theorem exRun_of_charts (hp : 3 ≤ p) (ch : ℕ → Bool) :
    ∀ k, pointChart (chartVar (ch k)) 0 (exPoly p) = X (chartVar (ch k)) ^ p * exPoly p ∧
      blowupDivisor ({1, 2} : Finset (Fin 3)) (chartVar (ch k)) (0 : Fin 3 → ZMod p) = {1, 2} ∧
      RhoStep p 1 (exPoint p) (exPoint p) ∧
      logJacobianOrder (exPoint p).1 (exPoint p).2 = 1 :=
  fun k => ⟨pointChart_exPoly hp (ch k), blowupDivisor_chartVar (ch k), rhoStep_exPoint_y hp,
    logJacobianOrder_exPoly hp⟩

end Example

/-! ### The primitive vectors of Section 3.16 -/

section Primitive

open Matrix

/-- The exponent matrix of a chart (Volume 7, Section 3.16 of the handbook). The rows are the
exponent vectors of `y_m` and `z_m` in `y_{m+1}, z_{m+1}`. The `y`-chart (`true`) has
`y_m = y_{m+1}` and `z_m = y_{m+1} z_{m+1}`, and the `z`-chart (`false`) has
`y_m = y_{m+1} z_{m+1}` and `z_m = z_{m+1}`. -/
def chartMat (b : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  if b then !![1, 0; 1, 1] else !![1, 1; 0, 1]

/-- The inverse of the exponent matrix of a chart. -/
def chartInv (b : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  if b then !![1, 0; -1, 1] else !![1, -1; 0, 1]

/-- **The exponent matrix of a chart has determinant `1`** (Volume 7, Section 3.16 of the
handbook). -/
theorem det_chartMat (b : Bool) : (chartMat b).det = 1 := by
  cases b <;> simp [chartMat, det_fin_two_of]

theorem det_chartInv (b : Bool) : (chartInv b).det = 1 := by
  cases b <;> simp [chartInv, det_fin_two_of]

theorem chartMat_mul_chartInv (b : Bool) : chartMat b * chartInv b = 1 := by
  cases b <;> simp [chartMat, chartInv, one_fin_two]

theorem chartInv_mul_chartMat (b : Bool) : chartInv b * chartMat b = 1 := by
  cases b <;> simp [chartMat, chartInv, one_fin_two]

/-- The exponent matrix of the point `P_m` of the word `ch`, with `P_0 = P_N`. The rows are the
exponent vectors `u` and `w` of `y_m` and `z_m` in `y_N, z_N`. -/
def expMat (ch : ℕ → Bool) : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => 1
  | m + 1 => chartInv (ch m) * expMat ch m

/-- The exponents at `P_m` come from the exponents at `P_{m+1}` by the exponent matrix of the
chart: `expMat ch m = chartMat (ch m) * expMat ch (m + 1)`. -/
theorem chartMat_mul_expMat_succ (ch : ℕ → Bool) (m : ℕ) :
    chartMat (ch m) * expMat ch (m + 1) = expMat ch m := by
  rw [expMat, ← Matrix.mul_assoc, chartMat_mul_chartInv, Matrix.one_mul]

/-- **The exponent vectors of `y_m, z_m` in `y_N, z_N` have determinant `1`** (Volume 7,
Section 3.16 of the handbook), at each step of each word. -/
theorem det_expMat (ch : ℕ → Bool) (m : ℕ) : (expMat ch m).det = 1 := by
  induction m with
  | zero => simp [expMat]
  | succ m ih => rw [expMat, det_mul, det_chartInv, ih, one_mul]

/-- The exponent vector `M_m` in `y_N, z_N` of the product of the exceptional variables: `M_0 = 1`
and `M_{m+1} = M_m y_{m+1}` for the `y`-chart and `M_m z_{m+1}` for the `z`-chart. -/
def mVec (ch : ℕ → Bool) : ℕ → Fin 2 → ℤ
  | 0 => 0
  | m + 1 => mVec ch m + expMat ch (m + 1) (if ch m then 0 else 1)

/-- The vector `n_m = -(u + w)`, the exponent of `N_m = 1 / (y_m z_m)` in `y_N, z_N`. -/
def nVec (ch : ℕ → Bool) (m : ℕ) : Fin 2 → ℤ := -(expMat ch m 0 + expMat ch m 1)

theorem expMat_succ_row (ch : ℕ → Bool) (m : ℕ) :
    (expMat ch (m + 1) 0 = if ch m then expMat ch m 0 else expMat ch m 0 - expMat ch m 1) ∧
    (expMat ch (m + 1) 1 = if ch m then expMat ch m 1 - expMat ch m 0 else expMat ch m 1) := by
  have e : expMat ch (m + 1) = chartInv (ch m) * expMat ch m := rfl
  rw [e]
  cases ch m <;> constructor <;> funext j <;>
    simp [chartInv, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **`M_m y_m z_m = y_N z_N`** (Lemma 3.13.24, part 3, of Volume 7 of the handbook, in
exponents). -/
theorem mVec_add_rows (ch : ℕ → Bool) (m : ℕ) :
    mVec ch m + expMat ch m 0 + expMat ch m 1 = 1 := by
  induction m with
  | zero =>
    funext j
    fin_cases j <;> simp [mVec, expMat]
  | succ m ih =>
    obtain ⟨h0, h1⟩ := expMat_succ_row ch m
    have e : mVec ch (m + 1) = mVec ch m + expMat ch (m + 1) (if ch m then 0 else 1) := rfl
    rw [e]
    cases hc : ch m <;> simp only [hc, ↓reduceIte, Bool.false_eq_true] at h0 h1 ⊢ <;>
      rw [h0, h1, ← ih] <;> abel

/-- `n_m = M_m - (1, 1)`, that is `N_m = M_m / (y_N z_N)`. -/
theorem nVec_eq_mVec_sub (ch : ℕ → Bool) (m : ℕ) : nVec ch m = mVec ch m - 1 := by
  rw [nVec, ← mVec_add_rows ch m]
  abel

/-- **The vector `n_m` is primitive** (Volume 7, Section 3.16 of the handbook, before Theorem
3.16.10). At each step of each word of the two charts, the entries of `n_m` are coprime. The
reason is that `u_0 (u_1 + w_1) - u_1 (u_0 + w_0) = det = 1`. -/
theorem isCoprime_nVec (ch : ℕ → Bool) (m : ℕ) : IsCoprime (nVec ch m 0) (nVec ch m 1) := by
  have h := det_expMat ch m
  rw [det_fin_two] at h
  refine ⟨expMat ch m 0 1, -expMat ch m 0 0, ?_⟩
  simp only [nVec, Pi.neg_apply, Pi.add_apply]
  linear_combination h

/-- **The vector `n_m` is primitive**, in the form `gcd = 1`. -/
theorem gcd_nVec (ch : ℕ → Bool) (m : ℕ) : Int.gcd (nVec ch m 0) (nVec ch m 1) = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp (isCoprime_nVec ch m)

/-- **Distinct multiples of primitive vectors** (Volume 7, proof of Theorem 3.16.10 of the
handbook). If `k n = k' n'` for primitive vectors `n, n'` and positive integers `k, k'`, then
`k = k'` and `n = n'`. -/
theorem eq_of_smul_eq_smul_of_isCoprime {n n' : Fin 2 → ℤ} (hn : IsCoprime (n 0) (n 1))
    (hn' : IsCoprime (n' 0) (n' 1)) {k k' : ℤ} (hk : 0 < k) (hk' : 0 < k')
    (h : k • n = k' • n') : k = k' ∧ n = n' := by
  have h0 : k * n 0 = k' * n' 0 := by simpa using congrFun h 0
  have h1 : k * n 1 = k' * n' 1 := by simpa using congrFun h 1
  have d1 : k ∣ k' := by
    obtain ⟨a, b, hab⟩ := hn'
    exact ⟨a * n 0 + b * n 1, by linear_combination (-k') * hab - a * h0 - b * h1⟩
  have d2 : k' ∣ k := by
    obtain ⟨a, b, hab⟩ := hn
    exact ⟨a * n' 0 + b * n' 1, by linear_combination (-k) * hab + a * h0 + b * h1⟩
  have hkk : k = k' := Int.dvd_antisymm hk.le hk'.le d1 d2
  refine ⟨hkk, ?_⟩
  subst hkk
  funext i
  fin_cases i
  · exact mul_left_cancel₀ hk.ne' h0
  · exact mul_left_cancel₀ hk.ne' h1

/-- **The multiples of the vectors `n_m` are distinct** (Volume 7, proof of Theorem 3.16.10 of
the handbook). If `k n_j = k' n'_{j'}` for two points of two words and positive integers `k, k'`,
then `k = k'` and `n_j = n'_{j'}`. -/
theorem nVec_smul_inj (ch ch' : ℕ → Bool) (j j' : ℕ) {k k' : ℕ} (hk : 0 < k) (hk' : 0 < k')
    (h : (k : ℤ) • nVec ch j = (k' : ℤ) • nVec ch' j') : k = k' ∧ nVec ch j = nVec ch' j' := by
  obtain ⟨h1, h2⟩ := eq_of_smul_eq_smul_of_isCoprime (isCoprime_nVec ch j) (isCoprime_nVec ch' j')
    (by exact_mod_cast hk) (by exact_mod_cast hk') h
  exact ⟨by exact_mod_cast h1, h2⟩

end Primitive

/-! ### The facts of Lucas type -/

section Lucas

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Lucas's theorem for `p^a s` and `p^a`** (Volume 7, proof of Lemma 3.16.4 of the handbook).
`(p^a s choose p^a) ≡ s (mod p)`. -/
theorem choose_pow_mul_pow_modEq (a s : ℕ) : (p ^ a * s).choose (p ^ a) ≡ s [MOD p] := by
  induction a with
  | zero =>
    simp only [pow_zero, one_mul, Nat.choose_one_right]
    exact Nat.ModEq.refl _
  | succ a ih =>
    have hp0 : 0 < p := hp.out.pos
    refine Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
    have e1 : p ^ (a + 1) * s = p * (p ^ a * s) := by ring
    have e2 : p ^ (a + 1) = p * p ^ a := by ring
    rw [e1, e2, Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hp0,
      Nat.mul_div_cancel_left _ hp0, Nat.choose_self, one_mul]
    exact ih

/-- **`(p^a s choose p^a) = s`** in a ring of characteristic `p` (Volume 7, proof of Lemma 3.16.4
of the handbook). -/
theorem choose_pow_mul_pow_eq (R : Type*) [AddMonoidWithOne R] [CharP R p] (a s : ℕ) :
    (((p ^ a * s).choose (p ^ a) : ℕ) : R) = s :=
  CharP.natCast_eq_natCast' R p (choose_pow_mul_pow_modEq a s)

/-- **Lemma 3.16.4 of Volume 7 of the handbook, the step of Lucas.** If `p ∤ s`, then
`(p^a s choose p^a) ≠ 0` in a ring of characteristic `p`. -/
theorem choose_pow_mul_pow_ne_zero (R : Type*) [AddMonoidWithOne R] [CharP R p] (a : ℕ)
    {s : ℕ} (hs : ¬ p ∣ s) : (((p ^ a * s).choose (p ^ a) : ℕ) : R) ≠ 0 := by
  rw [choose_pow_mul_pow_eq R a s, Ne, CharP.cast_eq_zero_iff R p]
  exact hs

/-- **`(p^e choose l) = 0` for `0 < l < p^e`** in a ring of characteristic `p` (Volume 7,
Remark 3.16.15 of the handbook). -/
theorem choose_prime_pow_eq_zero (R : Type*) [AddMonoidWithOne R] [CharP R p] (e : ℕ) {l : ℕ}
    (hl : l ≠ 0) (hle : l ≠ p ^ e) : (((p ^ e).choose l : ℕ) : R) = 0 :=
  (CharP.cast_eq_zero_iff R p _).mpr (Nat.Prime.dvd_choose_pow hp.out hl hle)

open Polynomial

variable {K : Type*} [Field K]

/-- The polynomial `S(U) = Σ_{i ∈ I} c_i ((U + Z)^i - U^i)` of Remark 3.16.15 of Volume 7 of the
handbook, in the variable `U` over `K[Z]`. -/
noncomputable def lucasPoly (I : Finset ℕ) (c : ℕ → K) : K[X][X] :=
  ∑ i ∈ I, C (C (c i)) * ((X + C X) ^ i - X ^ i)

/-- **Remark 3.16.15 of Volume 7 of the handbook, the powers of `p`.** In characteristic `p`, if
each `i ∈ I` is a power of `p`, then `S(U) = Σ_{i ∈ I} c_i Z^i` is constant in `U`. -/
theorem lucasPoly_eq_C_of_forall_pow [CharP K p] (I : Finset ℕ) (c : ℕ → K)
    (hI : ∀ i ∈ I, ∃ e, i = p ^ e) : lucasPoly I c = C (∑ i ∈ I, C (c i) * X ^ i) := by
  rw [lucasPoly, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨e, rfl⟩ := hI i hi
  rw [add_pow_char_pow, add_sub_cancel_left, ← C_pow, ← C_mul]

theorem coeff_coeff_term (c : K) (i a d : ℕ) (hd : d ≠ 0) :
    ((C (C c) * ((X + C X) ^ i - X ^ i) : K[X][X]).coeff a).coeff d =
      if d = i - a then c * (i.choose a : K) else 0 := by
  have h1 : ((X ^ i : K[X][X]).coeff a).coeff d = 0 := by
    rw [coeff_X_pow]
    split_ifs
    · rw [coeff_one, if_neg hd]
    · rw [coeff_zero]
  rw [coeff_C_mul, coeff_sub, coeff_C_mul, coeff_sub, h1, sub_zero, coeff_X_add_C_pow,
    ← C_eq_natCast, coeff_mul_C, coeff_X_pow]
  split_ifs <;> simp

/-- The coefficient of `U^a Z^d` of `S`, for `d ≠ 0`, is `Σ c_i (i choose a)` over the `i ∈ I`
with `i - a = d`. -/
theorem coeff_coeff_lucasPoly (I : Finset ℕ) (c : ℕ → K) (a d : ℕ) (hd : d ≠ 0) :
    ((lucasPoly I c).coeff a).coeff d =
      ∑ i ∈ I, if d = i - a then c i * (i.choose a : K) else 0 := by
  rw [lucasPoly, finsetSum_coeff, finsetSum_coeff]
  exact Finset.sum_congr rfl fun i _ => coeff_coeff_term (c i) i a d hd

/-- **Remark 3.16.15 of Volume 7 of the handbook, the lemma of Lucas type.** In characteristic
`p`, let `i₀ = p^a s ∈ I` with `s ≥ 2`, `p ∤ s` and `c_{i₀} ≠ 0`. Then the coefficient of
`U^(p^a)` in `S(U) = Σ_{i ∈ I} c_i ((U + Z)^i - U^i)` is not `0`. Its coefficient of
`Z^(i₀ - p^a)` is `c_{i₀} s`. -/
theorem coeff_lucasPoly_ne_zero [CharP K p] (I : Finset ℕ) (c : ℕ → K) {a s : ℕ}
    (hI : p ^ a * s ∈ I) (hs2 : 2 ≤ s) (hs : ¬ p ∣ s) (hc : c (p ^ a * s) ≠ 0) :
    (lucasPoly I c).coeff (p ^ a) ≠ 0 := by
  have hpa : 0 < p ^ a := pow_pos hp.out.pos a
  have hle : p ^ a * 2 ≤ p ^ a * s := Nat.mul_le_mul_left _ hs2
  have hd : p ^ a * s - p ^ a ≠ 0 := by omega
  have hsK : (s : K) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff K p]
  intro h
  have h2 := coeff_coeff_lucasPoly I c (p ^ a) _ hd
  rw [h, coeff_zero, Finset.sum_eq_single (p ^ a * s), if_pos rfl,
    choose_pow_mul_pow_eq K a s] at h2
  · exact mul_ne_zero hc hsK h2.symm
  · intro i _ hi
    rw [if_neg]
    intro he
    apply hi
    omega
  · intro h'
    exact absurd hI h'

/-- **Remark 3.16.15, `S` is not constant.** Under the hypotheses of `coeff_lucasPoly_ne_zero`,
`S(U)` is not a constant in `K[Z]`. -/
theorem lucasPoly_ne_C [CharP K p] (I : Finset ℕ) (c : ℕ → K) {a s : ℕ} (hI : p ^ a * s ∈ I)
    (hs2 : 2 ≤ s) (hs : ¬ p ∣ s) (hc : c (p ^ a * s) ≠ 0) (b : K[X]) : lucasPoly I c ≠ C b := by
  intro h
  apply coeff_lucasPoly_ne_zero I c hI hs2 hs hc
  rw [h, coeff_C, if_neg (pow_pos hp.out.pos a).ne']

/-- **The lemma of Lucas type of Remark 3.16.15 of Volume 7 of the handbook.** In
characteristic `p`, let `0 ∉ I` and `c_i ≠ 0` for each `i ∈ I`. Then
`S(U) = Σ_{i ∈ I} c_i ((U + Z)^i - U^i)` is constant in `U` if and only if each `i ∈ I` is a
power of `p`. -/
theorem lucasPoly_isConstant_iff [CharP K p] (I : Finset ℕ) (c : ℕ → K) (h0 : 0 ∉ I)
    (hc : ∀ i ∈ I, c i ≠ 0) : (∃ b, lucasPoly I c = C b) ↔ ∀ i ∈ I, ∃ e, i = p ^ e := by
  constructor
  · rintro ⟨b, hb⟩ i hi
    by_contra hne
    have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)
    obtain ⟨a, s, hs, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 p hp.out.one_lt.ne'
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hi0
    have hs1 : s ≠ 1 := by
      rintro rfl
      exact hne ⟨a, by simp⟩
    exact lucasPoly_ne_C I c hi (by omega) hs (hc _ hi) b hb
  · intro h
    exact ⟨_, lucasPoly_eq_C_of_forall_pow I c h⟩

end Lucas

end Translations

end Singularity
