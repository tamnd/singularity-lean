/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.OrderBlowup
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.CharP.Lemmas

/-!
# Moh's bound for one point blowup

Let `k` be a field of characteristic `p`, let `q = p^e`, and let `F` be a clean polynomial with `ord F ≥ q`. The `x_j`-chart of the point blowup with translations `t` sends `F` to `x_j^q F'`, and `z^q + F'` is the weak transform of `z^q + F` (`pointChartZ_purelyInseparable`). Let `d` be the residual order of `F` along the divisor `Δ`, and let `d'` be the residual order of `F'` along the transformed divisor `Δ'` (`blowupDivisor`). This file proves the bound of Moh [Moh87], [Hau08, §B], [HP19a, §3]: `d' ≤ d + p^(e-1)`. If `q` does not divide `ord F`, then `d' ≤ d`. The residual orders are measured in the given coordinates, the field need not be algebraically closed, and the hypothesis `ord F' ≥ q` is not needed.

The proof uses differential operators that are diagonal in the monomial basis. Let `F = x^r G` with `r` the divisor exponent along `Δ` and `ord G = d`, and let `m = ord F = |r| + d`.

1. The chart sends `x^r` to `x_j^|r| x^N' U`, with `N'` the part of `r` on the indices `l ≠ j` with `t_l = 0` and `U(0) ≠ 0` (`chartRest_monomial_one`). So `F' = x^N U G'` with `N = (m - q) e_j + N'`, and `N` is supported in `Δ'` (`le_of_mem_support_of_pointChart`). Thus `d' + |N| ≤ ord C`, with `C` the clean part of `F'` (`residualOrderAlong_add_le`).
2. Let `S` be a diagonal operator, `x^β ↦ w(β) x^β`, with `w(α) ≠ 0` for a monomial `x^α` of `F` of degree `m`. Then `ord S F = m`, and `S F = x^r H` with `ord H = d`. The order does not go up under the chart (`ord_le_of_pointChart`), so `ord π(S F) ≤ m + |N'| + d` (`ord_pointChart_diag_le`).
3. If `q ∤ m`, take `n = p^v` with `v < e` and `binom(m, n) ≠ 0` in `k` (`exists_choose_ne_zero`). Take `S = Θ^(n)`, `x^β ↦ binom(|β|, n) x^β`, and on `F'` the operator `θ_j^(n)`, `x^β ↦ binom(β_j, n) x^β`. Then `x_j^q θ_j^(n) F' = π(Θ^(n) F)` (`eulerVar_pointChart`). The operator `θ_j^(n)` kills the monomials in `q ℕ^n` and does not lower the order, so `ord C + q ≤ m + |N'| + d` (`ord_cleanPart_add_le_of_not_dvd`).
4. If `q ∣ m`, the cleanness of `F` gives an index `i ≠ j` with `q ∤ α_i`. Take `n = p^v` with `v < e` and `binom(α_i, n) ≠ 0` in `k`. Take `S = x_i^n D_i^(n)`, `x^β ↦ binom(β_i, n) x^β`, with `D_i^(n)` the Hasse derivative. The chain rule `D_i^(n) π(P) = x_j^n π(D_i^(n) P)` (`hasse_pointChart`) gives `(x_i + t_i)^n x_j^q D_i^(n) F' = π(S F)`. The operator `D_i^(n)` kills the monomials in `q ℕ^n` and lowers the order by at most `n`, so `ord C + q ≤ n + m + |N'| + d` (`ord_cleanPart_add_le_of_ne`).
5. With `|N| = m - q + |N'|`, the two inequalities give `d' ≤ d` in case 3 and `d' ≤ d + p^v ≤ d + p^(e-1)` in case 4.

The binomial coefficients are computed in characteristic `p` with `(1 + s)^(p^v b) = (1 + s^(p^v))^b` (`choose_cast_eq_zero`, `exists_choose_ne_zero`). The operators are coefficients of the substitutions `x_i ↦ x_i + s`, `x_j ↦ x_j (1 + s)` and `x_l ↦ x_l (1 + s)` into `k[x][s]`.

## Main results

* `Singularity.residualOrderAlong_pointChart_le`: Moh's bound `d' ≤ d + p^(e-1)`.
* `Singularity.residualOrderAlong_pointChart_le_of_not_dvd`: if `q ∤ ord F`, then `d' ≤ d`.
* `Singularity.moh_bound_holds`: the proposition `moh_bound` of `Singularity/Invariant/Residual.lean` holds.
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### Binomial coefficients in characteristic `p` -/

section Binomial

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- In characteristic `p`, `(1 + s)^(p^v b) = (1 + s^(p^v))^b`. -/
theorem one_add_X_pow_pow_mul (v b : ℕ) :
    (1 + Polynomial.X : Polynomial k) ^ (p ^ v * b) =
      Polynomial.expand k (p ^ v) ((1 + Polynomial.X) ^ b) := by
  rw [pow_mul, add_pow_char_pow, one_pow, map_pow, map_add, map_one, Polynomial.expand_X]

theorem choose_pow_mul_cast (v b n : ℕ) :
    (((p ^ v * b).choose n : ℕ) : k) =
      if p ^ v ∣ n then ((b.choose (n / p ^ v) : ℕ) : k) else 0 := by
  rw [← Polynomial.coeff_one_add_X_pow k, one_add_X_pow_pow_mul p,
    Polynomial.coeff_expand (pow_pos (Fact.out : p.Prime).pos v), Polynomial.coeff_one_add_X_pow]

/-- If `p^e` divides `a` and does not divide `n`, then `binom(a, n) = 0` in characteristic `p`. -/
theorem choose_cast_eq_zero {e a n : ℕ} (ha : p ^ e ∣ a) (hn : ¬ p ^ e ∣ n) :
    ((a.choose n : ℕ) : k) = 0 := by
  obtain ⟨b, rfl⟩ := ha
  rw [choose_pow_mul_cast p, ite_eq_right hn]

/-- If `p^e` does not divide `a`, then `binom(a, p^v) ≠ 0` in characteristic `p` for some
`v < e`: take for `p^v` the largest power of `p` that divides `a`. -/
theorem exists_choose_ne_zero {e a : ℕ} (ha : ¬ p ^ e ∣ a) :
    ∃ v < e, ((a.choose (p ^ v) : ℕ) : k) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (dvd_zero _)
  obtain ⟨v, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha0 p hp.one_lt.ne'
  refine ⟨v, ?_, ?_⟩
  · by_contra hv
    exact ha (Dvd.dvd.mul_right (pow_dvd_pow p (not_lt.mp hv)) b)
  · rw [choose_pow_mul_cast p, ite_eq_left dvd_rfl, Nat.div_self (pow_pos hp.pos v),
      Nat.choose_one_right]
    rwa [Ne, CharP.cast_eq_zero_iff k p]

end Binomial

/-! ### Operators that are diagonal in the monomial basis -/

section Diagonal

variable {σ k : Type*} [Field k]

/-- The operator `L` multiplies the monomial `x^β` by the scalar `w β`. -/
def IsDiag (L : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (w : (σ →₀ ℕ) → k) : Prop :=
  ∀ β c, L (monomial β c) = monomial β (w β * c)

variable {L : MvPolynomial σ k →ₗ[k] MvPolynomial σ k} {w : (σ →₀ ℕ) → k}

theorem IsDiag.coeff (hL : IsDiag L w) (P : MvPolynomial σ k) (β : σ →₀ ℕ) :
    (L P).coeff β = w β * P.coeff β := by
  classical
  have hL' : ∀ β c, L (monomial β c) = monomial β (w β * c) := hL
  conv_lhs => rw [P.as_sum]
  rw [map_sum, coeff_sum]
  simp_rw [hL', coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, mul_zero]

theorem IsDiag.ord_le (hL : IsDiag L w) (P : MvPolynomial σ k) : ord P ≤ ord (L P) :=
  ENat.forall_natCast_le_iff_le.mp fun n hn => le_ord_iff.mpr fun d hd => by
    rw [hL.coeff, le_ord_iff.mp hn d hd, mul_zero]

theorem IsDiag.mem_support (hL : IsDiag L w) {P : MvPolynomial σ k} {β : σ →₀ ℕ}
    (h : β ∈ (L P).support) : β ∈ P.support := by
  rw [MvPolynomial.mem_support_iff, hL.coeff] at h
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul h)

theorem IsDiag.coeff_ne_zero (hL : IsDiag L w) {P : MvPolynomial σ k} {β : σ →₀ ℕ}
    (hP : P.coeff β ≠ 0) (hw : w β ≠ 0) : (L P).coeff β ≠ 0 := by
  rw [hL.coeff]
  exact mul_ne_zero hw hP

/-- A diagonal operator that kills the monomials in `q ℕ^n` does not see the cleaning. -/
theorem IsDiag.map_cleanPart (hL : IsDiag L w) {q : ℕ} (hw : ∀ β, (∀ i, q ∣ β i) → w β = 0)
    (P : MvPolynomial σ k) : L (cleanPart q P) = L P := by
  ext β
  rw [hL.coeff, hL.coeff, coeff_cleanPart]
  split_ifs with h
  · rw [hw β h, zero_mul, zero_mul]
  · rfl

end Diagonal

/-! ### Taylor and scaling operators -/

section Operators

variable {σ k : Type*} [Field k]

/-- The coefficient of `s^n` in the image of a polynomial under `φ : k[x] → k[x][s]`. -/
noncomputable def opOf (φ : MvPolynomial σ k →ₐ[k] Polynomial (MvPolynomial σ k)) (n : ℕ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k where
  toFun P := (φ P).coeff n
  map_add' P Q := by rw [map_add, Polynomial.coeff_add]
  map_smul' c P := by rw [map_smul, Polynomial.coeff_smul, RingHom.id_apply]

theorem opOf_apply (φ : MvPolynomial σ k →ₐ[k] Polynomial (MvPolynomial σ k)) (n : ℕ)
    (P : MvPolynomial σ k) : opOf φ n P = (φ P).coeff n := rfl

theorem aeval_C_X : (aeval fun l => Polynomial.C (X l) :
    MvPolynomial σ k →ₐ[k] Polynomial (MvPolynomial σ k)) = Polynomial.CAlgHom := by
  refine algHom_ext fun l => ?_
  simp

/-- The image of `c x^β` under `x_l ↦ x_l g_l` is `c x^β ∏ g_l^(β_l)`. -/
theorem aeval_C_mul_monomial (g : σ → Polynomial (MvPolynomial σ k)) (β : σ →₀ ℕ) (c : k) :
    aeval (fun l => Polynomial.C (X l) * g l) (monomial β c) =
      Polynomial.C (monomial β c) * β.prod fun l e => g l ^ e := by
  have h := congrArg (fun φ => φ (monomial β c)) (aeval_C_X (σ := σ) (k := k))
  simp only [aeval_monomial, Polynomial.CAlgHom_apply] at h
  rw [aeval_monomial, ← h]
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul, mul_assoc]

variable [DecidableEq σ]

/-- The Taylor substitution `x_i ↦ x_i + s`. -/
noncomputable def taylorVar (i : σ) : MvPolynomial σ k →ₐ[k] Polynomial (MvPolynomial σ k) :=
  aeval fun l => Polynomial.C (X l) + if l = i then Polynomial.X else 0

/-- The scaling `x_j ↦ x_j (1 + s)`. -/
noncomputable def scaleVar (j : σ) : MvPolynomial σ k →ₐ[k] Polynomial (MvPolynomial σ k) :=
  aeval fun l => Polynomial.C (X l) * if l = j then 1 + Polynomial.X else 1

/-- The scaling `x_l ↦ x_l (1 + s)` of all variables. -/
noncomputable def scaleAll : MvPolynomial σ k →ₐ[k] Polynomial (MvPolynomial σ k) :=
  aeval fun l => Polynomial.C (X l) * (1 + Polynomial.X)

/-- The Hasse derivative `D_i^(n)`: `x^β ↦ binom(β_i, n) x^(β - n e_i)`. -/
noncomputable def hasse (i : σ) (n : ℕ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  opOf (taylorVar i) n

/-- The operator `x_i^n D_i^(n)`: `x^β ↦ binom(β_i, n) x^β`. -/
noncomputable def hasseX (i : σ) (n : ℕ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  (LinearMap.mulLeft k (X i ^ n)).comp (hasse i n)

/-- The operator `x^β ↦ binom(β_j, n) x^β`. -/
noncomputable def eulerVar (j : σ) (n : ℕ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  opOf (scaleVar j) n

/-- The operator `x^β ↦ binom(|β|, n) x^β`. -/
noncomputable def eulerTotal (n : ℕ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  opOf scaleAll n

theorem hasseX_apply (i : σ) (n : ℕ) (P : MvPolynomial σ k) :
    hasseX i n P = X i ^ n * hasse i n P := rfl

theorem scaleVar_monomial (j : σ) (β : σ →₀ ℕ) (c : k) :
    scaleVar j (monomial β c) = Polynomial.C (monomial β c) * (1 + Polynomial.X) ^ β j := by
  rw [scaleVar, aeval_C_mul_monomial, Finsupp.prod]
  congr 1
  simp_rw [ite_pow, one_pow]
  rw [Finset.prod_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h, pow_zero]

omit [DecidableEq σ] in
theorem scaleAll_monomial (β : σ →₀ ℕ) (c : k) :
    scaleAll (monomial β c) =
      Polynomial.C (monomial β c) * (1 + Polynomial.X) ^ degree β := by
  rw [scaleAll, aeval_C_mul_monomial, Finsupp.prod, Finset.prod_pow_eq_pow_sum, degree_apply]

omit [DecidableEq σ] in
theorem natCast_mul_monomial (a : ℕ) (β : σ →₀ ℕ) (c : k) :
    monomial β c * (a : MvPolynomial σ k) = monomial β ((a : k) * c) := by
  rw [← map_natCast (C : k →+* MvPolynomial σ k), mul_comm, C_mul_monomial]

theorem isDiag_eulerVar (j : σ) (n : ℕ) :
    IsDiag (eulerVar (k := k) j n) fun β => ((β j).choose n : k) := fun β c => by
  rw [eulerVar, opOf_apply, scaleVar_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_one_add_X_pow, natCast_mul_monomial]

omit [DecidableEq σ] in
theorem isDiag_eulerTotal (n : ℕ) :
    IsDiag (eulerTotal (σ := σ) (k := k) n) fun β => ((degree β).choose n : k) := fun β c => by
  rw [eulerTotal, opOf_apply, scaleAll_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_one_add_X_pow, natCast_mul_monomial]

theorem taylorVar_monomial (i : σ) (β : σ →₀ ℕ) (c : k) :
    taylorVar i (monomial β c) =
      Polynomial.C (monomial (β.erase i) c) * (Polynomial.C (X i) + Polynomial.X) ^ β i := by
  have hβ : monomial β c = monomial (β.erase i) c * X i ^ β i := by
    rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one, add_comm, Finsupp.single_add_erase]
  have h1 : taylorVar i (monomial (β.erase i) c) =
      aeval (fun l => Polynomial.C (X l)) (monomial (β.erase i) c) := by
    rw [taylorVar, aeval_monomial, aeval_monomial]
    congr 1
    refine Finsupp.prod_congr fun l hl => ?_
    rw [Finsupp.support_erase, Finset.mem_erase] at hl
    rw [ite_eq_right hl.1, add_zero]
  rw [hβ, map_mul, h1, aeval_C_X, Polynomial.CAlgHom_apply, map_pow]
  congr 2
  simp [taylorVar]

theorem isDiag_hasseX (i : σ) (n : ℕ) :
    IsDiag (hasseX (k := k) i n) fun β => ((β i).choose n : k) := fun β c => by
  rw [hasseX_apply, hasse, opOf_apply, taylorVar_monomial, Polynomial.coeff_C_mul, add_comm,
    Polynomial.coeff_X_add_C_pow]
  have hβ : monomial β c = monomial (β.erase i) c * X i ^ β i := by
    rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one, add_comm, Finsupp.single_add_erase]
  rcases le_or_gt n (β i) with h | h
  · rw [← natCast_mul_monomial, hβ, show β i = n + (β i - n) by omega, pow_add]
    simp only [Nat.add_sub_cancel_left]
    ring
  · simp [Nat.choose_eq_zero_of_lt h]

end Operators

/-! ### Chain rules for the chart -/

section Chain

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- The Taylor substitution in `x_i`, `i ≠ j`, after the `x_j`-chart: since the chart sends
`x_i + s` to `x_j (x_i + t_i) + x_j s`, it is the chart after the Taylor substitution, with `s`
replaced by `x_j s`. -/
theorem taylorVar_pointChart {i j : σ} (hij : i ≠ j) (t : σ → k) (P : MvPolynomial σ k) :
    taylorVar i (pointChart j t P) =
      ((taylorVar i P).map (pointChart j t : MvPolynomial σ k →+* MvPolynomial σ k)).comp
        (Polynomial.C (X j) * Polynomial.X) := by
  have h : ((taylorVar i).comp (pointChart j t)).toRingHom =
      ((Polynomial.compRingHom (Polynomial.C (X j) * Polynomial.X)).comp
        (Polynomial.mapRingHom (pointChart j t : MvPolynomial σ k →+* MvPolynomial σ k))).comp
        (taylorVar i).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun l => ?_)
    · simp [taylorVar, pointChart, Polynomial.compRingHom]
    · by_cases hl : l = j
      · subst hl
        simp [taylorVar, pointChart, Polynomial.compRingHom, Ne.symm hij]
      · by_cases hli : l = i
        · subst hli
          simp [taylorVar, pointChart, Polynomial.compRingHom, hl, Ne.symm hl]
          ring
        · simp [taylorVar, pointChart, Polynomial.compRingHom, hl, hli, Ne.symm hij]
  exact RingHom.congr_fun h P

/-- `D_i^(n) π(P) = x_j^n π(D_i^(n) P)` for `i ≠ j`. -/
theorem hasse_pointChart {i j : σ} (hij : i ≠ j) (t : σ → k) (n : ℕ) (P : MvPolynomial σ k) :
    hasse i n (pointChart j t P) = X j ^ n * pointChart j t (hasse i n P) := by
  rw [hasse, opOf_apply, opOf_apply, taylorVar_pointChart hij, Polynomial.comp_C_mul_X_coeff,
    Polynomial.coeff_map, mul_comm]
  rfl

/-- The scaling of `x_j` after the `x_j`-chart is the chart after the scaling of all variables. -/
theorem scaleVar_pointChart (j : σ) (t : σ → k) (P : MvPolynomial σ k) :
    scaleVar j (pointChart j t P) =
      (scaleAll P).map (pointChart j t : MvPolynomial σ k →+* MvPolynomial σ k) := by
  have h : ((scaleVar j).comp (pointChart j t)).toRingHom =
      (Polynomial.mapRingHom (pointChart j t : MvPolynomial σ k →+* MvPolynomial σ k)).comp
        (scaleAll (σ := σ) (k := k)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun l => ?_)
    · simp [scaleVar, scaleAll, pointChart]
    · by_cases hl : l = j
      · subst hl
        simp [scaleVar, scaleAll, pointChart]
      · simp [scaleVar, scaleAll, pointChart, hl]
        ring
  exact RingHom.congr_fun h P

/-- `θ_j^(n) π(P) = π(Θ^(n) P)`. -/
theorem eulerVar_pointChart (j : σ) (t : σ → k) (n : ℕ) (P : MvPolynomial σ k) :
    eulerVar j n (pointChart j t P) = pointChart j t (eulerTotal n P) := by
  rw [eulerVar, eulerTotal, opOf_apply, opOf_apply, scaleVar_pointChart, Polynomial.coeff_map]
  rfl

theorem hasse_X_pow_mul {i j : σ} (hij : i ≠ j) (n a : ℕ) (P : MvPolynomial σ k) :
    hasse i n (X j ^ a * P) = X j ^ a * hasse i n P := by
  have hX : taylorVar i (X j ^ a : MvPolynomial σ k) = Polynomial.C (X j ^ a) := by
    simp [taylorVar, Ne.symm hij]
  rw [hasse, opOf_apply, opOf_apply, map_mul, hX, Polynomial.coeff_C_mul]

theorem eulerVar_X_pow_mul (p : ℕ) [Fact p.Prime] [CharP k p] (j : σ) {e n : ℕ}
    (hn : n < p ^ e) (P : MvPolynomial σ k) :
    eulerVar j n (X j ^ p ^ e * P) = X j ^ p ^ e * eulerVar j n P := by
  have hX : scaleVar j (X j ^ p ^ e : MvPolynomial σ k) =
      Polynomial.C (X j ^ p ^ e) * (1 + Polynomial.X ^ p ^ e) := by
    simp only [map_pow, scaleVar, aeval_X, ite_true, mul_pow, add_pow_char_pow, one_pow]
  rw [eulerVar, opOf_apply, opOf_apply, map_mul, hX, mul_assoc, Polynomial.coeff_C_mul, add_mul,
    one_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega), add_zero]

end Chain

/-! ### Monomial factors -/

section Factor

variable {σ k : Type*} [Field k]

theorem monomial_mul_divMonomial {P : MvPolynomial σ k} {r : σ →₀ ℕ}
    (h : ∀ β ∈ P.support, r ≤ β) : monomial r 1 * divMonomial P r = P := by
  ext β
  rw [coeff_monomial_mul', one_mul]
  split_ifs with hr
  · rw [coeff_divMonomial, add_tsub_cancel_of_le hr]
  · exact (MvPolynomial.notMem_support_iff.mp fun hm => hr (h β hm)).symm

theorem ord_divMonomial_add {P : MvPolynomial σ k} {r : σ →₀ ℕ} (h : ∀ β ∈ P.support, r ≤ β) :
    ord (divMonomial P r) + degree r = ord P := by
  conv_rhs => rw [← monomial_mul_divMonomial h]
  rw [ord_mul, ord_monomial one_ne_zero, add_comm]

theorem le_of_mem_support_monomial_mul {N β : σ →₀ ℕ} {Q : MvPolynomial σ k}
    (h : β ∈ (monomial N 1 * Q).support) : N ≤ β := by
  classical
  rw [MvPolynomial.mem_support_iff, coeff_monomial_mul'] at h
  by_contra hN
  exact h (ite_eq_right hN)

theorem divisorExponent_le {Δ : Finset σ} {P : MvPolynomial σ k} {β : σ →₀ ℕ}
    (hβ : β ∈ P.support) : divisorExponent Δ P ≤ β := fun i => by
  classical
  rw [divisorExponent_apply]
  split_ifs
  · exact Nat.sInf_le ⟨β, hβ, rfl⟩
  · exact Nat.zero_le _

theorem divisorExponent_eq_zero {Δ : Finset σ} {P : MvPolynomial σ k} {i : σ} (hi : i ∉ Δ) :
    divisorExponent Δ P i = 0 := by
  classical
  rw [divisorExponent_apply, ite_eq_right hi]

theorem le_divisorExponent {Δ : Finset σ} {P : MvPolynomial σ k} {N : σ →₀ ℕ} (hP : P ≠ 0)
    (hN : ∀ i, i ∉ Δ → N i = 0) (h : ∀ β ∈ P.support, N ≤ β) : N ≤ divisorExponent Δ P :=
  fun i => by
  classical
  rw [divisorExponent_apply]
  split_ifs with hi
  · obtain ⟨β, hβ⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hP)
    exact le_csInf ⟨_, β, hβ, rfl⟩ (by rintro _ ⟨β', hβ', rfl⟩; exact h β' hβ' i)
  · rw [hN i hi]

theorem degree_mono {N r : σ →₀ ℕ} (h : N ≤ r) : degree N ≤ degree r := by
  rw [← tsub_add_cancel_of_le h, map_add]
  exact Nat.le_add_left _ _

end Factor

/-! ### The chart of a monomial -/

section ChartMonomial

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k]

/-- The exponents of the factors `x_l` of `ρ(x^r)` for `l ≠ j` with `t_l = 0`. -/
noncomputable def chartExponent (j : σ) (t : σ → k) (r : σ →₀ ℕ) : σ →₀ ℕ :=
  r.filter fun l => l ≠ j ∧ t l = 0

/-- The unit factor `∏ (x_l + t_l)^(r_l)` of `ρ(x^r)`, over `l ≠ j` with `t_l ≠ 0`. -/
noncomputable def chartUnit (j : σ) (t : σ → k) (r : σ →₀ ℕ) : MvPolynomial σ k :=
  (r.filter fun l => ¬(l ≠ j ∧ t l = 0)).prod fun l e => (if l = j then 1 else X l + C (t l)) ^ e

theorem chartRest_monomial_one (j : σ) (t : σ → k) (r : σ →₀ ℕ) :
    chartRest j t (monomial r 1) = monomial (chartExponent j t r) 1 * chartUnit j t r := by
  rw [chartRest, aeval_monomial, map_one, one_mul,
    ← Finsupp.prod_filter_mul_prod_filter_not (p := fun l => l ≠ j ∧ t l = 0)]
  congr 1
  rw [chartExponent, ← prod_X_pow_eq_monomial, Finsupp.prod]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Finsupp.support_filter, Finset.mem_filter] at hl
  rw [ite_eq_right hl.2.1, hl.2.2, C_0, add_zero]

theorem ord_chartUnit (j : σ) (t : σ → k) (r : σ →₀ ℕ) : ord (chartUnit j t r) = 0 := by
  refine le_antisymm ?_ (by simp)
  have h : (chartUnit j t r).coeff 0 ≠ 0 := by
    rw [← constantCoeff_eq, chartUnit, Finsupp.prod, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun l hl => ?_
    rw [Finsupp.support_filter, Finset.mem_filter] at hl
    rw [map_pow]
    refine pow_ne_zero _ ?_
    by_cases hlj : l = j
    · simp [hlj]
    · have : t l ≠ 0 := fun h0 => hl.2 ⟨hlj, h0⟩
      simpa [hlj] using this
  simpa using ord_le h

theorem ord_chartRest_monomial_one (j : σ) (t : σ → k) (r : σ →₀ ℕ) :
    ord (chartRest j t (monomial r 1)) = degree (chartExponent j t r) := by
  rw [chartRest_monomial_one, ord_mul, ord_monomial one_ne_zero, ord_chartUnit, add_zero]

/-- Let `r ≤ β` for each monomial `x^β` of `P`, and let `ord P = |r| + d`. Then
`ord π(P) ≤ |r| + |N'| + 2d`, with `N' = chartExponent j t r`. -/
theorem ord_pointChart_le {j : σ} {t : σ → k} {P : MvPolynomial σ k} {r : σ →₀ ℕ} {d : ℕ}
    (hr : ∀ β ∈ P.support, r ≤ β) (hP : ord P = ((degree r + d : ℕ) : ℕ∞)) :
    ord (pointChart j t P) ≤ ((degree r + degree (chartExponent j t r) + d + d : ℕ) : ℕ∞) := by
  have hH := ord_divMonomial_add hr
  rw [hP] at hH
  have hd : ord (divMonomial P r) = d := by
    cases h : ord (divMonomial P r) using ENat.recTopCoe with
    | top => rw [h, top_add] at hH; exact absurd hH (ENat.top_ne_natCast _)
    | coe a =>
      rw [h] at hH
      have : a + degree r = degree r + d := by exact_mod_cast hH
      congr 1
      omega
  obtain ⟨H', hH'⟩ := exists_pointChart_eq_X_pow_mul (j := j) (t := t) hd.ge
  have h1 := ord_le_of_pointChart hd hH'
  rw [← monomial_mul_divMonomial hr, map_mul, pointChart_monomial, hH', ord_mul, ord_mul, ord_mul,
    ord_X_pow, ord_X_pow, ord_chartRest_monomial_one]
  push_cast
  calc _ ≤ ((degree r : ℕ) : ℕ∞) + ((degree (chartExponent j t r) : ℕ) : ℕ∞) + (d + d) := by
        gcongr
    _ = _ := by ring

end ChartMonomial

/-! ### The bound -/

section Bound

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k]

omit [DecidableEq σ] [DecidableEq k] in
theorem mem_support_of_mem_support_cleanPart {q : ℕ} {P : MvPolynomial σ k} {β : σ →₀ ℕ}
    (h : β ∈ (cleanPart q P).support) : β ∈ P.support := by
  rw [MvPolynomial.mem_support_iff, coeff_cleanPart] at h
  split_ifs at h with hq
  · exact absurd rfl h
  · exact MvPolynomial.mem_support_iff.mpr h

/-- Let `F = x^r G` with `r` the divisor exponent along `Δ` and `ord G = d`, and let
`π(F) = x_j^q F'` with `q ≤ |r| + d`. Then every monomial of `F'` is divisible by `x^N` with
`N = (|r| + d - q) e_j + N'`. -/
theorem le_of_mem_support_of_pointChart {Δ : Finset σ} {j : σ} {t : σ → k} {q d : ℕ}
    {F F' : MvPolynomial σ k} (hd : ord (divMonomial F (divisorExponent Δ F)) = d)
    (hq : q ≤ degree (divisorExponent Δ F) + d) (hπ : pointChart j t F = X j ^ q * F')
    {β : σ →₀ ℕ} (hβ : β ∈ F'.support) :
    single j (degree (divisorExponent Δ F) + d - q) +
      chartExponent j t (divisorExponent Δ F) ≤ β := by
  set r := divisorExponent Δ F
  have hr : ∀ β ∈ F.support, r ≤ β := fun β hβ => divisorExponent_le hβ
  obtain ⟨G', hG'⟩ := exists_pointChart_eq_X_pow_mul (j := j) (t := t) hd.ge
  obtain ⟨c, hc⟩ : ∃ c, degree r + d = q + c := ⟨_, (Nat.add_sub_cancel' hq).symm⟩
  have hm : monomial (single j c + chartExponent j t r) (1 : k) =
      X j ^ c * monomial (chartExponent j t r) 1 := by
    rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  have e1 : pointChart j t F = X j ^ q *
      (monomial (single j c + chartExponent j t r) 1 * (chartUnit j t r * G')) := by
    conv_lhs => rw [← monomial_mul_divMonomial hr]
    rw [map_mul, pointChart_monomial, chartRest_monomial_one, hG', hm]
    calc X j ^ degree r * (monomial (chartExponent j t r) 1 * chartUnit j t r) * (X j ^ d * G')
        = X j ^ (degree r + d) * (monomial (chartExponent j t r) 1 * (chartUnit j t r * G')) := by
          ring
      _ = _ := by
          rw [hc, pow_add]
          ring
  have hF' := mul_left_cancel₀ (pow_ne_zero _ (X_ne_zero j)) (hπ.symm.trans e1)
  rw [hF'] at hβ
  rw [show degree r + d - q = c by omega]
  exact le_of_mem_support_monomial_mul hβ

theorem chartN_eq_zero {Δ : Finset σ} {j : σ} {t : σ → k} {r : σ →₀ ℕ}
    (hr : ∀ i, i ∉ Δ → r i = 0) (c : ℕ) {i : σ} (hi : i ∉ blowupDivisor Δ j t) :
    (single j c + chartExponent j t r) i = 0 := by
  rw [blowupDivisor, Finset.mem_insert, Finset.mem_filter, not_or] at hi
  rw [Finsupp.add_apply, Finsupp.single_apply, ite_eq_right fun h => hi.1 h.symm, zero_add,
    chartExponent, Finsupp.filter_apply]
  split_ifs with h
  · exact hr i fun hΔ => hi.2 ⟨hΔ, h⟩
  · rfl

omit [DecidableEq σ] [DecidableEq k] in
/-- The residual side of the bound: if `x^N` divides `F'`, with `N` supported in `Δ'`, then the
residual order of `F'` along `Δ'` is at most `ord C - |N|`, with `C` the clean part of `F'`. -/
theorem residualOrderAlong_add_le {Δ' : Finset σ} {q B : ℕ} {F' : MvPolynomial σ k}
    {N : σ →₀ ℕ} (hN : ∀ i, i ∉ Δ' → N i = 0) (hsupp : ∀ β ∈ F'.support, N ≤ β)
    (hC : ord (cleanPart q F') + q ≤ B) :
    residualOrderAlong Δ' q F' + ((degree N + q : ℕ) : ℕ∞) ≤ B := by
  set C' := cleanPart q F'
  have hC0 : C' ≠ 0 := by
    intro h
    rw [h, ord_zero, top_add] at hC
    exact absurd hC (by simp)
  have hNr : N ≤ divisorExponent Δ' C' :=
    le_divisorExponent hC0 hN fun β hβ => hsupp β (mem_support_of_mem_support_cleanPart hβ)
  have h1 := ord_divMonomial_add (P := C') (r := divisorExponent Δ' C')
    fun β hβ => divisorExponent_le hβ
  calc residualOrderAlong Δ' q F' + ((degree N + q : ℕ) : ℕ∞)
      ≤ ord (divMonomial C' (divisorExponent Δ' C')) +
          ((degree (divisorExponent Δ' C') : ℕ) : ℕ∞) + q := by
        rw [Nat.cast_add, ← add_assoc]
        gcongr
        · exact le_rfl
        · exact degree_mono hNr
    _ = ord C' + q := by rw [h1]
    _ ≤ B := hC

omit [DecidableEq σ] [DecidableEq k] in
/-- The order data of a nonzero `F`: a monomial `x^α` of `F` of degree `ord F`, and the order `d`
of the residual factor, with `|α| = |r| + d`. -/
theorem exists_ord_data {Δ : Finset σ} {F : MvPolynomial σ k} (hF0 : F ≠ 0) :
    ∃ α : σ →₀ ℕ, ∃ d : ℕ, F.coeff α ≠ 0 ∧ ord F = degree α ∧
      ord (divMonomial F (divisorExponent Δ F)) = d ∧
      degree α = degree (divisorExponent Δ F) + d := by
  obtain ⟨α, hα, hαm⟩ := exists_coeff_ne_zero_and_ord_eq hF0
  have hH := ord_divMonomial_add (P := F) (r := divisorExponent Δ F)
    fun β hβ => divisorExponent_le hβ
  rw [hαm] at hH
  cases h : ord (divMonomial F (divisorExponent Δ F)) using ENat.recTopCoe with
  | top =>
    rw [h, top_add] at hH
    exact absurd hH (ENat.top_ne_natCast _)
  | coe d =>
    rw [h] at hH
    refine ⟨α, d, hα, hαm, rfl, ?_⟩
    have : d + degree (divisorExponent Δ F) = degree α := by exact_mod_cast hH
    omega

/-- For a diagonal operator `S` with `w α ≠ 0` at a monomial `x^α` of `F` of degree `ord F`,
`ord π(S F) ≤ |r| + |N'| + 2d`. -/
theorem ord_pointChart_diag_le {Δ : Finset σ} {j : σ} {t : σ → k} {F : MvPolynomial σ k}
    {S : MvPolynomial σ k →ₗ[k] MvPolynomial σ k} {w : (σ →₀ ℕ) → k} (hS : IsDiag S w)
    {α : σ →₀ ℕ} {d : ℕ} (hα : F.coeff α ≠ 0) (hαm : ord F = degree α) (hw : w α ≠ 0)
    (hdeg : degree α = degree (divisorExponent Δ F) + d) :
    ord (pointChart j t (S F)) ≤ ((degree (divisorExponent Δ F) +
      degree (chartExponent j t (divisorExponent Δ F)) + d + d : ℕ) : ℕ∞) := by
  refine ord_pointChart_le (fun β hβ => divisorExponent_le (hS.mem_support hβ)) ?_
  rw [← hdeg]
  refine le_antisymm (ord_le (hS.coeff_ne_zero hα hw)) ?_
  rw [← hαm]
  exact hS.ord_le F

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The case `q ∤ ord F`. Use the operator `θ_j^(n)` on `F'`, with `n = p^v` the largest power
of `p` that divides `ord F`. It kills the monomials in `q ℕ^n`, does not lower the order, and
`x_j^q θ_j^(n) F' = π(Θ^(n) F)`. -/
theorem ord_cleanPart_add_le_of_not_dvd {Δ : Finset σ} {j : σ} {t : σ → k} {e d : ℕ}
    {F F' : MvPolynomial σ k} {α : σ →₀ ℕ} (hα : F.coeff α ≠ 0) (hαm : ord F = degree α)
    (hdeg : degree α = degree (divisorExponent Δ F) + d) (hdvd : ¬ p ^ e ∣ degree α)
    (hπ : pointChart j t F = X j ^ p ^ e * F') :
    ord (cleanPart (p ^ e) F') + ((p ^ e : ℕ) : ℕ∞) ≤ ((degree (divisorExponent Δ F) +
      degree (chartExponent j t (divisorExponent Δ F)) + d + d : ℕ) : ℕ∞) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨v, hv, hc⟩ := exists_choose_ne_zero p (k := k) hdvd
  have hvq : p ^ v < p ^ e := Nat.pow_lt_pow_right hp.one_lt hv
  have hkill : ∀ β : σ →₀ ℕ, (∀ i, p ^ e ∣ β i) → (((β j).choose (p ^ v) : ℕ) : k) = 0 :=
    fun β hβ => choose_cast_eq_zero p (hβ j) fun h => (Nat.le_of_dvd (pow_pos hp.pos v) h).not_gt hvq
  have hK := ord_pointChart_diag_le (j := j) (t := t) (isDiag_eulerTotal (p ^ v)) hα hαm hc hdeg
  have hid : pointChart j t (eulerTotal (p ^ v) F) =
      X j ^ p ^ e * eulerVar j (p ^ v) (cleanPart (p ^ e) F') := by
    rw [← eulerVar_pointChart, hπ, eulerVar_X_pow_mul p j hvq,
      (isDiag_eulerVar j _).map_cleanPart hkill]
  rw [hid, ord_mul, ord_X_pow] at hK
  calc ord (cleanPart (p ^ e) F') + ((p ^ e : ℕ) : ℕ∞)
      ≤ ord (eulerVar j (p ^ v) (cleanPart (p ^ e) F')) + ((p ^ e : ℕ) : ℕ∞) := by
        gcongr
        exact (isDiag_eulerVar j _).ord_le _
    _ ≤ _ := by
        rw [add_comm]
        exact_mod_cast hK

/-- The case of a monomial `x^α` of degree `ord F` and an index `i ≠ j` with `q ∤ α_i`. Use the
Hasse derivative `D_i^(n)` on `F'`, with `n = p^v` the largest power of `p` that divides `α_i`.
It kills the monomials in `q ℕ^n`, lowers the order by at most `n`, and
`(x_i + t_i)^n x_j^q D_i^(n) F' = π(x_i^n D_i^(n) F)`. -/
theorem ord_cleanPart_add_le_of_ne {Δ : Finset σ} {j : σ} {t : σ → k} {e d : ℕ}
    {F F' : MvPolynomial σ k} {α : σ →₀ ℕ} (hα : F.coeff α ≠ 0) (hαm : ord F = degree α)
    (hdeg : degree α = degree (divisorExponent Δ F) + d) {i : σ} (hij : i ≠ j)
    (hi : ¬ p ^ e ∣ α i) (hπ : pointChart j t F = X j ^ p ^ e * F') :
    ∃ v < e, ord (cleanPart (p ^ e) F') + ((p ^ e : ℕ) : ℕ∞) ≤ ((p ^ v +
      (degree (divisorExponent Δ F) + degree (chartExponent j t (divisorExponent Δ F)) + d + d) :
        ℕ) : ℕ∞) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨v, hv, hc⟩ := exists_choose_ne_zero p (k := k) hi
  have hvq : p ^ v < p ^ e := Nat.pow_lt_pow_right hp.one_lt hv
  have hkill : ∀ β : σ →₀ ℕ, (∀ l, p ^ e ∣ β l) → (((β i).choose (p ^ v) : ℕ) : k) = 0 :=
    fun β hβ => choose_cast_eq_zero p (hβ i) fun h => (Nat.le_of_dvd (pow_pos hp.pos v) h).not_gt hvq
  have hK := ord_pointChart_diag_le (j := j) (t := t) (isDiag_hasseX i (p ^ v)) hα hαm hc hdeg
  set C' := cleanPart (p ^ e) F'
  have hcl : hasse i (p ^ v) C' = hasse i (p ^ v) F' := by
    have := (isDiag_hasseX i (p ^ v)).map_cleanPart hkill F'
    rw [hasseX_apply, hasseX_apply] at this
    exact mul_left_cancel₀ (pow_ne_zero _ (X_ne_zero i)) this
  have hid : pointChart j t (hasseX i (p ^ v) F) =
      (X i + C (t i)) ^ p ^ v * (X j ^ p ^ e * hasse i (p ^ v) C') := by
    rw [hasseX_apply, map_mul, map_pow, pointChart_X_of_ne t hij, hcl, ← hasse_X_pow_mul hij,
      ← hπ, hasse_pointChart hij, mul_pow]
    ring
  rw [hid, ord_mul, ord_mul, ord_X_pow] at hK
  have hlow : ord C' ≤ ((p ^ v : ℕ) : ℕ∞) + ord (hasse i (p ^ v) C') := by
    have := (isDiag_hasseX i (p ^ v)).ord_le C'
    rwa [hasseX_apply, ord_mul, ord_X_pow] at this
  refine ⟨v, hv, ?_⟩
  calc ord C' + ((p ^ e : ℕ) : ℕ∞)
      ≤ ((p ^ v : ℕ) : ℕ∞) + ord (hasse i (p ^ v) C') + ((p ^ e : ℕ) : ℕ∞) := by gcongr
    _ = ((p ^ v : ℕ) : ℕ∞) + (((p ^ e : ℕ) : ℕ∞) + ord (hasse i (p ^ v) C')) := by ring
    _ ≤ ((p ^ v : ℕ) : ℕ∞) + (ord ((X i + C (t i)) ^ p ^ v) +
          (((p ^ e : ℕ) : ℕ∞) + ord (hasse i (p ^ v) C'))) :=
        add_le_add le_rfl le_add_self
    _ ≤ _ := by
        rw [Nat.cast_add]
        exact add_le_add le_rfl (by exact_mod_cast hK)

omit [Fact p.Prime] [CharP k p] in
/-- The arithmetic at the end of the proof. -/
theorem residualOrderAlong_le_of_bound {Δ : Finset σ} {j : σ} {t : σ → k} {e d n : ℕ}
    {F F' : MvPolynomial σ k} (hF : IsClean (p ^ e) F)
    (hd : ord (divMonomial F (divisorExponent Δ F)) = d)
    (hq : p ^ e ≤ degree (divisorExponent Δ F) + d) (hπ : pointChart j t F = X j ^ p ^ e * F')
    (hC : ord (cleanPart (p ^ e) F') + ((p ^ e : ℕ) : ℕ∞) ≤ ((n +
      (degree (divisorExponent Δ F) + degree (chartExponent j t (divisorExponent Δ F)) + d + d) :
        ℕ) : ℕ∞)) :
    residualOrderAlong (blowupDivisor Δ j t) (p ^ e) F' ≤
      residualOrderAlong Δ (p ^ e) F + (n : ℕ∞) := by
  set r := divisorExponent Δ F
  have hres : residualOrderAlong Δ (p ^ e) F = d := by
    rw [residualOrderAlong, cleanPart_eq_self hF]
    exact hd
  have h := residualOrderAlong_add_le
    (fun i hi => chartN_eq_zero (fun l hl => divisorExponent_eq_zero hl) (degree r + d - p ^ e) hi)
    (fun β hβ => le_of_mem_support_of_pointChart hd hq hπ hβ) hC
  rw [hres]
  rw [map_add, degree_single] at h
  cases h' : residualOrderAlong (blowupDivisor Δ j t) (p ^ e) F' using ENat.recTopCoe with
  | top =>
    rw [h', top_add] at h
    exact absurd h (by simp)
  | coe a =>
    rw [h'] at h
    have : a + (degree r + d - p ^ e + degree (chartExponent j t r) + p ^ e) ≤
        n + (degree r + degree (chartExponent j t r) + d + d) := by exact_mod_cast h
    exact_mod_cast (show a ≤ d + n by omega)

/-- If all exponents `α_l`, `l ≠ j`, of `x^α` are divisible by `q` and `q ∣ |α|`, then all
exponents of `x^α` are divisible by `q`. -/
theorem dvd_apply_of_dvd_degree {q : ℕ} {α : σ →₀ ℕ} (j : σ) (h : ∀ i, i ≠ j → q ∣ α i)
    (hdeg : q ∣ degree α) (i : σ) : q ∣ α i := by
  by_cases hij : i = j
  · subst hij
    have he : q ∣ degree (α.erase i) := by
      rw [degree_apply]
      refine Finset.dvd_sum fun l hl => ?_
      rw [Finsupp.support_erase, Finset.mem_erase] at hl
      rw [Finsupp.erase_ne hl.1]
      exact h l hl.1
    rw [degree_eq_add_degree_erase i] at hdeg
    exact (Nat.dvd_add_left he).mp hdeg
  · exact h i hij

end Bound

/-! ### Moh's bound -/

section Main

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p]

omit [DecidableEq σ] [DecidableEq k] [Fact p.Prime] [CharP k p] in
theorem residualOrderAlong_zero (Δ : Finset σ) (q : ℕ) :
    residualOrderAlong Δ q (0 : MvPolynomial σ k) = ⊤ := by
  rw [residualOrderAlong, cleanPart_eq_self (isClean_zero _), ord_eq_top_iff]
  ext β
  simp [residualFactor]

/-- **Moh's bound** for one point blowup [Moh87], [Hau08, §B], [HP19a, §3]. Let `k` be a field of
characteristic `p`, let `q = p^e`, and let `F` be clean with `ord F ≥ q`. Let the `x_j`-chart
with translations `t` send `F` to `x_j^q F'`, so that `z^q + F'` is the weak transform of
`z^q + F`. Then the residual order along the transformed divisor goes up by at most `p^(e-1)`.
The residual orders are measured in the given coordinates, and the hypothesis `ord F' ≥ q` is not
needed. -/
theorem residualOrderAlong_pointChart_le (Δ : Finset σ) (j : σ) (t : σ → k) {e : ℕ}
    {F F' : MvPolynomial σ k} (hF : IsClean (p ^ e) F) (hord : ((p ^ e : ℕ) : ℕ∞) ≤ ord F)
    (hπ : pointChart j t F = X j ^ p ^ e * F') :
    residualOrderAlong (blowupDivisor Δ j t) (p ^ e) F' ≤
      residualOrderAlong Δ (p ^ e) F + ((p ^ (e - 1) : ℕ) : ℕ∞) := by
  by_cases hF0 : F = 0
  · rw [hF0, residualOrderAlong_zero, top_add]
    exact le_top
  obtain ⟨α, d, hα, hαm, hd, hdeg⟩ := exists_ord_data (Δ := Δ) hF0
  have hq : p ^ e ≤ degree (divisorExponent Δ F) + d := by
    rw [← hdeg]
    rw [hαm] at hord
    exact_mod_cast hord
  have hp := (Fact.out : p.Prime)
  by_cases hdvd : p ^ e ∣ degree α
  · have hex : ∃ i, i ≠ j ∧ ¬ p ^ e ∣ α i := by
      by_contra h
      simp only [not_exists, not_and, not_not] at h
      exact hF α (MvPolynomial.mem_support_iff.mpr hα) (dvd_apply_of_dvd_degree j h hdvd)
    obtain ⟨i, hij, hi⟩ := hex
    obtain ⟨v, hv, hC⟩ := ord_cleanPart_add_le_of_ne p hα hαm hdeg hij hi hπ
    refine (residualOrderAlong_le_of_bound p hF hd hq hπ hC).trans ?_
    exact add_le_add le_rfl
      (by exact_mod_cast Nat.pow_le_pow_right hp.pos (show v ≤ e - 1 by omega))
  · have hC := ord_cleanPart_add_le_of_not_dvd p (j := j) (t := t) hα hαm hdeg hdvd hπ
    refine (residualOrderAlong_le_of_bound p (n := 0) hF hd hq hπ (by simpa using hC)).trans ?_
    simp

/-- If `q` does not divide `ord F`, then the residual order does not go up under the chart. -/
theorem residualOrderAlong_pointChart_le_of_not_dvd (Δ : Finset σ) (j : σ) (t : σ → k) {e m : ℕ}
    {F F' : MvPolynomial σ k} (hF : IsClean (p ^ e) F) (hord : ((p ^ e : ℕ) : ℕ∞) ≤ ord F)
    (hm : ord F = m) (hdvd : ¬ p ^ e ∣ m) (hπ : pointChart j t F = X j ^ p ^ e * F') :
    residualOrderAlong (blowupDivisor Δ j t) (p ^ e) F' ≤ residualOrderAlong Δ (p ^ e) F := by
  have hF0 : F ≠ 0 := by
    rintro rfl
    rw [ord_zero] at hm
    exact ENat.top_ne_natCast _ hm
  obtain ⟨α, d, hα, hαm, hd, hdeg⟩ := exists_ord_data (Δ := Δ) hF0
  have hαm' : degree α = m := by
    rw [hm] at hαm
    exact_mod_cast hαm.symm
  have hq : p ^ e ≤ degree (divisorExponent Δ F) + d := by
    rw [← hdeg]
    rw [hαm] at hord
    exact_mod_cast hord
  have hC := ord_cleanPart_add_le_of_not_dvd p (j := j) (t := t) hα hαm hdeg (hαm' ▸ hdvd) hπ
  simpa using residualOrderAlong_le_of_bound p (n := 0) hF hd hq hπ (by simpa using hC)

/-- The proposition `moh_bound` holds. -/
theorem moh_bound_holds : moh_bound := fun _ _ _ _ p _ _ _ _ Δ j t _ _ _ hF hord hπ _ =>
  residualOrderAlong_pointChart_le p Δ j t hF hord hπ

end Main

end Singularity
