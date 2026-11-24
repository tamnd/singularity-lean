/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Directrix
import Singularity.Example.Narasimhan

/-!
# The lemma of Tschirnhausen

Let `R` be a commutative ring, and let `R[z, x]` be the polynomial ring in one variable `z = X none` and the variables `x_l = X (some l)` for `l ∈ σ`, as in `Singularity/Invariant/Residual.lean`. A polynomial `f = z^m + ∑_{i < m} a_i(x) z^i` is monic of degree `m` in `z` (`zMonic m a`). It is in *Tschirnhausen form* if `a_{m-1} = 0`. This file proves three facts about this form. They are the positive side of the example of Narasimhan (`Singularity/Example/Narasimhan.lean`), and they need the hypothesis that `m` is a unit.

(a) The Tschirnhausen transformation. The change `z ↦ z + h(x)` sends `f` to a polynomial of the same kind, and the new coefficient of `z^{m-1}` is `a_{m-1} + m h` (`exists_zShift_zMonic`). So if `m` is a unit, then `z ↦ z - a_{m-1}/m` gives the Tschirnhausen form (`tschirnhausen_transformation`).

(b) The points of order `m`. Let `f` be in Tschirnhausen form and let `m` be a unit. If `f` has order at least `m` at a point `b`, then `b_z = 0` (`eq_zero_of_le_ord_translate`). The reason is that the coefficient of `z^{m-1}` in `f(X + b)` is `m b_z`. So the points of order at least `m` lie in the hypersurface `z = 0`, and this hypersurface has maximal contact. More precisely, `f` has order at least `m` at `b` if and only if `b_z = 0` and `a_i` has order at least `m - i` at `b_x` for each `i < m` (`le_ord_translate_zMonic_iff`).

(c) The point blowup. Let `f` be in Tschirnhausen form of order `m` at the origin, so that `a_i` has order at least `m - i` (`le_ord_zMonic_iff`), and let `m ≠ 0` in the field `k`. Blow up the origin of `k^{1+n}` and look at a chart `pointChart c t` of `k[z, x]` (the chart of the variable `c`, with translations `t`). Let `f'` be the weak transform. If `f'` has order at least `m` at the origin of the chart, then the chart is an `x_j`-chart (`c = some j`), the translation of `z` is `0`, and `f'` is again in Tschirnhausen form, with `a_i = x_j^{m-i} a_i'` in the chart of `k[x]` (`tschirnhausen_pointChart`). The new coefficients `a_i'` have order at least `m - i`. So the hypotheses come back after the blowup, and the lemma applies again.

The proof of (c). By the theorem on the directrix (`mem_directrix_of_ord_pointChart_eq`), the vector `v` of the chart lies in the directrix of the initial form `f_m`. The initial form is again in Tschirnhausen form (`homogeneousComponent_zMonic`), and `f_m(x + v) = f_m(x)`. So `f_m` has order `m` at the point `v`, and (b) gives `v_z = 0`. In the `z`-chart `v_z = 1`, and in the `x_j`-chart `v_z = t_z`. In the `x_j`-chart with `t_z = 0`, the chart is `z ↦ x_j z` (`pointChart_some_eq_pointChartZ`), and the computation of the transform is direct (`pointChart_zMonic`).

The hypothesis that `m` is a unit is necessary. In characteristic `2`, the polynomial of Narasimhan is `x^2 + (y z^3 + z w^3 + y^7 w)`, in Tschirnhausen form with `m = 2`. It has order `2` at the point `(1, 1, 1, 1)`, and the coordinate `x = 1` of this point is not `0` (`narasimhan_le_ord_translate`, `not_tschirnhausen_charTwo`).

## Main definitions

* `Singularity.zMonic m a`: the polynomial `z^m + ∑_{i < m} a_i(x) z^i`.
* `Singularity.xTranslate b`: the translation `x ↦ x + b`, with `z` fixed.

## Main results

* `exists_zShift_zMonic`, `tschirnhausen_transformation`: part (a).
* `eq_zero_of_le_ord_translate`, `le_ord_translate_zMonic_iff`: part (b).
* `le_ord_zMonic_iff`: `f` has order at least `m` at the origin if and only if `ord a_i ≥ m - i` for each `i < m`.
* `homogeneousComponent_zMonic`, `pointChart_zMonic`, `tschirnhausen_pointChart`: part (c).
* `narasimhan_le_ord_translate`, `not_tschirnhausen_charTwo`: the hypothesis that `m` is a unit is necessary.

## References

* [Nar83] R. Narasimhan, *Hyperplanarity of the equimultiple locus*, Proc. Amer. Math. Soc. 87 (1983), 403-408.
* [Hau03] H. Hauser, *The Hironaka theorem on resolution of singularities*, Bull. AMS 40 (2003) (the Tschirnhausen transformation and maximal contact).
-/

open MvPolynomial Finsupp

namespace Singularity

section Ring

variable {σ R : Type*} [CommRing R]

/-- The polynomial `z^m + ∑_{i < m} a_i(x) z^i` in `R[z, x]`, with `z = X none` and `x_l = X (Option.some l)`. It is in Tschirnhausen form if `a (m - 1) = 0`. The values `a i` for `i ≥ m` are not used. -/
noncomputable def zMonic (m : ℕ) (a : ℕ → MvPolynomial σ R) : MvPolynomial (Option σ) R :=
  X none ^ m + ∑ i ∈ Finset.range m, rename Option.some (a i) * X none ^ i

theorem optionEquivLeft_rename_some (g : MvPolynomial σ R) :
    optionEquivLeft R σ (rename Option.some g) = Polynomial.C g := by
  induction g using MvPolynomial.induction_on with
  | C r => rw [rename_C, optionEquivLeft_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.C_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, rename_X, optionEquivLeft_X_some, Polynomial.C_mul]

/-- As a polynomial in `z` over `R[x]`, `zMonic m a` is `z^m + ∑_{i < m} a_i z^i`. -/
theorem optionEquivLeft_zMonic (m : ℕ) (a : ℕ → MvPolynomial σ R) :
    optionEquivLeft R σ (zMonic m a) =
      Polynomial.X ^ m + ∑ i ∈ Finset.range m, Polynomial.C (a i) * Polynomial.X ^ i := by
  simp only [zMonic, map_add, map_pow, map_sum, map_mul, optionEquivLeft_X_none,
    optionEquivLeft_rename_some]

theorem coeff_X_pow_add_sum {A : Type*} [CommRing A] (m : ℕ) (a : ℕ → A) (n : ℕ) :
    (Polynomial.X ^ m + ∑ i ∈ Finset.range m, Polynomial.C (a i) * Polynomial.X ^ i).coeff n =
      if n < m then a n else if n = m then 1 else 0 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  by_cases h1 : n < m
  · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by omega), zero_add]
  · rw [ite_eq_right h1, ite_eq_right h1, add_zero]

/-- The coefficients of `zMonic m a`. -/
theorem coeff_zMonic (m : ℕ) (a : ℕ → MvPolynomial σ R) (e : Option σ →₀ ℕ) :
    (zMonic m a).coeff e =
      if e none < m then (a (e none)).coeff e.some
      else if e none = m then (1 : MvPolynomial σ R).coeff e.some else 0 := by
  rw [← optionEquivLeft_coeff_some_coeff_none, optionEquivLeft_zMonic, coeff_X_pow_add_sum]
  split_ifs
  · rfl
  · rfl
  · simp

/-- The total degree of an exponent of `R[z, x]` is the exponent of `z` plus the degree of the
exponent of `x`. -/
theorem degree_eq_none_add_degree_some (e : Option σ →₀ ℕ) :
    degree e = e none + degree e.some := by
  induction e using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg, Finsupp.some_add, map_add, Finsupp.add_apply]; ring
  | single o n =>
    cases o with
    | none => rw [Finsupp.some_single_none, degree_single, map_zero, single_eq_same, add_zero]
    | some l =>
      rw [Finsupp.some_single_some, degree_single, degree_single,
        single_eq_of_ne (Option.some_ne_none l).symm, zero_add]

theorem optionElim_none (i : ℕ) (d : σ →₀ ℕ) : (d.optionElim i) none = i :=
  Finsupp.optionElim_apply_none i d

theorem some_optionElim (i : ℕ) (d : σ →₀ ℕ) : (d.optionElim i).some = d := by
  ext l
  rw [Finsupp.some_apply, Finsupp.optionElim_apply_some]

theorem X_mem_idealOfVars (o : σ) : (X o : MvPolynomial σ R) ∈ idealOfVars σ R :=
  Ideal.subset_span (Set.mem_range_self o)

theorem ord_le_ord_rename_some (g : MvPolynomial σ R) : ord g ≤ ord (rename Option.some g) := by
  have h := ord_le_ord_aeval (fun l => (X (Option.some l) : MvPolynomial (Option σ) R))
    (fun l => constantCoeff_X R (Option.some l)) g
  rwa [show (aeval fun l => (X (Option.some l) : MvPolynomial (Option σ) R)) = rename Option.some
    from (rename_eq_aeval _).symm] at h

/-- **The order of `zMonic` at the origin.** `z^m + ∑_{i < m} a_i z^i` has order at least `m` if and only if `a_i` has order at least `m - i` for each `i < m`. -/
theorem le_ord_zMonic_iff {m : ℕ} {a : ℕ → MvPolynomial σ R} :
    (m : ℕ∞) ≤ ord (zMonic m a) ↔ ∀ i < m, ((m - i : ℕ) : ℕ∞) ≤ ord (a i) := by
  constructor
  · intro h i hi
    refine le_ord_iff.mpr fun d hd => ?_
    have h1 := le_ord_iff.mp h (d.optionElim i) (by
      rw [degree_eq_none_add_degree_some, optionElim_none, some_optionElim]
      omega)
    rwa [coeff_zMonic, optionElim_none, ite_eq_left hi, some_optionElim] at h1
  · intro h
    refine le_ord_iff_mem_pow.mpr (Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun i hi => ?_))
    · exact Ideal.pow_mem_pow (X_mem_idealOfVars none) m
    · have hi' := Finset.mem_range.mp hi
      rw [show m = (m - i) + i by omega, pow_add]
      refine Ideal.mul_mem_mul ?_ (Ideal.pow_mem_pow (X_mem_idealOfVars none) i)
      exact le_ord_iff_mem_pow.mp ((h i hi').trans (ord_le_ord_rename_some (a i)))

/-! ### (a) The Tschirnhausen transformation -/

/-- As a polynomial in `z`, the change `z ↦ z + h(x)` is the Taylor shift by `h`. -/
theorem optionEquivLeft_zShift (h : MvPolynomial σ R) (f : MvPolynomial (Option σ) R) :
    optionEquivLeft R σ (zShift h f) = Polynomial.taylor h (optionEquivLeft R σ f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [zShift, optionEquivLeft_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p o hp =>
    have hX : optionEquivLeft R σ (zShift h (X o)) =
        Polynomial.taylor h (optionEquivLeft R σ (X o)) := by
      cases o with
      | none =>
        rw [show zShift h (X none) = X none + rename Option.some h by simp [zShift], map_add,
          optionEquivLeft_X_none, optionEquivLeft_rename_some, Polynomial.taylor_X]
      | some l =>
        rw [show zShift h (X (Option.some l)) = X (Option.some l) by simp [zShift],
          optionEquivLeft_X_some, Polynomial.taylor_C]
    rw [map_mul (zShift h), map_mul (optionEquivLeft R σ), hp, hX, map_mul (optionEquivLeft R σ),
      Polynomial.taylor_mul]

theorem coeff_taylor_X_pow_add_sum {A : Type*} [CommRing A] (m : ℕ) (a : ℕ → A) (d : A) :
    (Polynomial.taylor d (Polynomial.X ^ m +
      ∑ i ∈ Finset.range m, Polynomial.C (a i) * Polynomial.X ^ i)) =
      (Polynomial.X + Polynomial.C d) ^ m +
        ∑ i ∈ Finset.range m, Polynomial.C (a i) * (Polynomial.X + Polynomial.C d) ^ i := by
  simp [Polynomial.taylor_apply, Polynomial.add_comp, Polynomial.sum_comp,
    Polynomial.mul_comp]

theorem coeff_top_X_add_C {A : Type*} [CommRing A] (m : ℕ) (a : ℕ → A) (d : A) :
    ((Polynomial.X + Polynomial.C d) ^ m +
      ∑ i ∈ Finset.range m, Polynomial.C (a i) * (Polynomial.X + Polynomial.C d) ^ i).coeff m =
      1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_add_C_pow, Polynomial.finsetSum_coeff,
    Finset.sum_eq_zero fun i hi => ?_]
  · simp
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow,
      Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]
    simp

theorem coeff_pred_X_add_C {A : Type*} [CommRing A] {m : ℕ} (hm : 1 ≤ m) (a : ℕ → A) (d : A) :
    ((Polynomial.X + Polynomial.C d) ^ m +
      ∑ i ∈ Finset.range m, Polynomial.C (a i) * (Polynomial.X + Polynomial.C d) ^ i).coeff
        (m - 1) = a (m - 1) + m * d := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Polynomial.coeff_add, Polynomial.coeff_X_add_C_pow, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single n]
  · simp only [Nat.add_sub_cancel, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow,
      Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one,
      show n + 1 - n = 1 by omega, pow_one, Nat.choose_succ_self_right, Nat.cast_add]
    ring
  · intro i hi hne
    have : i < n := by
      have := Finset.mem_range.mp hi
      omega
    rw [Nat.add_sub_cancel, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow,
      Nat.choose_eq_zero_of_lt this]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h

/-- A polynomial in `z` over `R[x]` of degree at most `m`, with the coefficient `1` at `z^m`, is a `zMonic m a`. -/
theorem optionEquivLeft_zMonic_coeff {m : ℕ} {Q : Polynomial (MvPolynomial σ R)}
    (hQ : Q.natDegree ≤ m) (hQm : Q.coeff m = 1) :
    optionEquivLeft R σ (zMonic m fun i => Q.coeff i) = Q := by
  rw [optionEquivLeft_zMonic]
  ext1 n
  rw [coeff_X_pow_add_sum]
  split_ifs with h1 h2
  · rfl
  · rw [h2, hQm]
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- **The change `z ↦ z + h`.** Let `1 ≤ m`. The change `z ↦ z + h(x)` sends `z^m + ∑_{i < m} a_i z^i` to a polynomial `z^m + ∑_{i < m} a_i' z^i` with `a_{m-1}' = a_{m-1} + m h`. -/
theorem exists_zShift_zMonic (h : MvPolynomial σ R) {m : ℕ} (hm : 1 ≤ m)
    (a : ℕ → MvPolynomial σ R) :
    ∃ a' : ℕ → MvPolynomial σ R, zShift h (zMonic m a) = zMonic m a' ∧
      a' (m - 1) = a (m - 1) + m * h := by
  set Q := Polynomial.taylor h (optionEquivLeft R σ (zMonic m a)) with hQ
  have hQ' : Q = (Polynomial.X + Polynomial.C h) ^ m +
      ∑ i ∈ Finset.range m, Polynomial.C (a i) * (Polynomial.X + Polynomial.C h) ^ i := by
    rw [hQ, optionEquivLeft_zMonic, coeff_taylor_X_pow_add_sum]
  have hdeg : Q.natDegree ≤ m := by
    rw [hQ, Polynomial.natDegree_taylor, optionEquivLeft_zMonic]
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
    rw [coeff_X_pow_add_sum, ite_eq_right (by omega), ite_eq_right (by omega)]
  have htop : Q.coeff m = 1 := by rw [hQ', coeff_top_X_add_C]
  refine ⟨fun i => Q.coeff i, (optionEquivLeft R σ).injective ?_, ?_⟩
  · rw [optionEquivLeft_zShift, optionEquivLeft_zMonic_coeff hdeg htop]
  · simp only
    rw [hQ', coeff_pred_X_add_C hm]

/-- **The Tschirnhausen transformation (part (a)).** Let `m` be a unit in `R`. The change `z ↦ z - a_{m-1}/m` sends `z^m + ∑_{i < m} a_i z^i` to a polynomial in Tschirnhausen form `z^m + ∑_{i < m} a_i' z^i` with `a_{m-1}' = 0`. -/
theorem tschirnhausen_transformation {m : ℕ} (hm : IsUnit (m : R)) (a : ℕ → MvPolynomial σ R) :
    ∃ a' : ℕ → MvPolynomial σ R,
      zShift (-(C (↑hm.unit⁻¹ : R) * a (m - 1))) (zMonic m a) = zMonic m a' ∧ a' (m - 1) = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · refine ⟨0, ?_, rfl⟩
    simp [zMonic]
  obtain ⟨a', he, ha'⟩ := exists_zShift_zMonic (-(C (↑hm.unit⁻¹ : R) * a (m - 1))) hm1 a
  refine ⟨a', he, ?_⟩
  have hu : C (m : R) * C (↑hm.unit⁻¹ : R) = (1 : MvPolynomial σ R) := by
    rw [← map_mul, hm.mul_val_inv, map_one]
  rw [ha', ← map_natCast (C : R →+* MvPolynomial σ R)]
  linear_combination (-a (m - 1)) * hu

/-! ### (b) The points of order `m` -/

/-- The translation `x_l ↦ x_l + b_l` of `R[z, x]`, with `z` fixed. -/
noncomputable def xTranslate (b : σ → R) : MvPolynomial (Option σ) R →ₐ[R] MvPolynomial (Option σ) R :=
  aeval fun o => Option.elim o (X none) fun l => X (Option.some l) + C (b l)

theorem xTranslate_rename (b : σ → R) (g : MvPolynomial σ R) :
    xTranslate b (rename Option.some g) = rename Option.some (aeval (fun l => X l + C (b l)) g) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun l => ?_
  simp [xTranslate]

theorem xTranslate_zMonic (b : σ → R) (m : ℕ) (a : ℕ → MvPolynomial σ R) :
    xTranslate b (zMonic m a) = zMonic m fun i => aeval (fun l => X l + C (b l)) (a i) := by
  have hz : xTranslate b (X none) = X none := by simp [xTranslate]
  simp only [zMonic, map_add, map_pow, map_sum, map_mul, hz, xTranslate_rename]

/-- The translation by `b` is the translation of `x` followed by the change `z ↦ z + b_z`. -/
theorem aeval_translate_eq (b : Option σ → R) (f : MvPolynomial (Option σ) R) :
    aeval (fun o => X o + C (b o)) f = zShift (C (b none)) (xTranslate (fun l => b (Option.some l)) f) := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun o => ?_
  cases o with
  | none => simp [zShift, xTranslate]
  | some l => simp [zShift, xTranslate]

theorem zShift_zero_apply (f : MvPolynomial (Option σ) R) : zShift (0 : MvPolynomial σ R) f = f := by
  rw [← AlgHom.id_apply (R := R) f, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun o => ?_
  cases o with
  | none => simp [zShift]
  | some l => simp [zShift]

/-- **The points of order `m` lie in `z = 0` (part (b)).** Let `m` be a unit in `R`, and let `f = z^m + ∑_{i < m} a_i z^i` be in Tschirnhausen form, `a_{m-1} = 0`. If `f` has order at least `m` at the point `b ∈ R^{1+n}`, then `b_z = 0`. No hypothesis on the order of `f` at the origin is necessary. -/
theorem eq_zero_of_le_ord_translate {m : ℕ} (hm : IsUnit (m : R)) {a : ℕ → MvPolynomial σ R}
    (ha : a (m - 1) = 0) (b : Option σ → R)
    (h : (m : ℕ∞) ≤ ord (aeval (fun o => X o + C (b o)) (zMonic m a))) : b none = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · rw [Nat.cast_zero, isUnit_zero_iff] at hm
    rw [← mul_one (b none), ← hm, mul_zero]
  rw [aeval_translate_eq, xTranslate_zMonic] at h
  obtain ⟨a', he, ha'⟩ := exists_zShift_zMonic (C (b none)) hm1
    (fun i => aeval (fun l => X l + C (b (Option.some l))) (a i))
  rw [he] at h
  have h0 := le_ord_iff.mp h (Finsupp.single none (m - 1)) (by rw [degree_single]; omega)
  rw [coeff_zMonic, single_eq_same, ite_eq_left (show m - 1 < m by omega), Finsupp.some_single_none,
    ha', ha, map_zero (aeval _), zero_add, ← map_natCast (C : R →+* MvPolynomial σ R), ← map_mul,
    coeff_zero_C] at h0
  exact (hm.mul_right_eq_zero).mp h0

/-- **The locus of order `m` (part (b), the precise form).** Let `m` be a unit in `R`, and let `f = z^m + ∑_{i < m} a_i z^i` be in Tschirnhausen form. Then `f` has order at least `m` at `b` if and only if `b_z = 0` and, for each `i < m`, `a_i` has order at least `m - i` at the point `(b_l)_{l ∈ σ}` of `R^n`. -/
theorem le_ord_translate_zMonic_iff {m : ℕ} (hm : IsUnit (m : R)) {a : ℕ → MvPolynomial σ R}
    (ha : a (m - 1) = 0) (b : Option σ → R) :
    (m : ℕ∞) ≤ ord (aeval (fun o => X o + C (b o)) (zMonic m a)) ↔
      b none = 0 ∧ ∀ i < m, ((m - i : ℕ) : ℕ∞) ≤
        ord (aeval (fun l => X l + C (b (Option.some l))) (a i)) := by
  have key : b none = 0 → aeval (fun o => X o + C (b o)) (zMonic m a) =
      zMonic m fun i => aeval (fun l => X l + C (b (Option.some l))) (a i) := fun h0 => by
    rw [aeval_translate_eq, h0, map_zero, zShift_zero_apply, xTranslate_zMonic]
  constructor
  · intro h
    have h0 := eq_zero_of_le_ord_translate hm ha b h
    rw [key h0] at h
    exact ⟨h0, le_ord_zMonic_iff.mp h⟩
  · rintro ⟨h0, h⟩
    rw [key h0]
    exact le_ord_zMonic_iff.mpr h

end Ring

/-! ### (c) The point blowup -/

section Field

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- The initial form of `zMonic m a` is `zMonic m a°`, with `a°_i` the part of degree `m - i` of `a_i`. -/
theorem homogeneousComponent_zMonic (m : ℕ) (a : ℕ → MvPolynomial σ k) :
    homogeneousComponent m (zMonic m a) = zMonic m fun i => homogeneousComponent (m - i) (a i) := by
  ext e
  rw [coeff_homogeneousComponent, coeff_zMonic, coeff_zMonic, degree_eq_none_add_degree_some]
  by_cases h1 : e none < m
  · rw [ite_eq_left h1, ite_eq_left h1, coeff_homogeneousComponent]
    by_cases h2 : degree e.some = m - e none
    · rw [ite_eq_left (show e none + degree e.some = m by omega), ite_eq_left h2]
    · rw [ite_eq_right (show ¬ e none + degree e.some = m by omega), ite_eq_right h2]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : e none = m
    · simp only [ite_eq_left h2]
      by_cases h3 : degree e.some = 0
      · rw [ite_eq_left (show e none + degree e.some = m by omega)]
      · rw [ite_eq_right (show ¬ e none + degree e.some = m by omega), coeff_one, ite_eq_right]
        intro h4
        exact h3 (by rw [← h4, map_zero])
    · simp only [ite_eq_right h2, ite_self]

/-- In the chart of `x_j`, the chart of `k[z, x]` acts on `k[x]` as the chart of `k[x]`. -/
theorem pointChart_some_rename (j : σ) (t : Option σ → k) (g : MvPolynomial σ k) :
    pointChart (Option.some j) t (rename Option.some g) = rename Option.some (pointChart j (fun l => t (Option.some l)) g) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun l => ?_
  by_cases hl : l = j
  · subst hl
    simp [pointChart]
  · simp [pointChart, hl]

/-- If the translation of `z` is `0`, the chart of `x_j` of `k[z, x]` is the chart `pointChartZ` of `Singularity/Invariant/Residual.lean`: `z ↦ x_j z`. -/
theorem pointChart_some_eq_pointChartZ (j : σ) {t : Option σ → k} (ht : t none = 0) :
    pointChart (Option.some j) t = pointChartZ j fun l => t (Option.some l) := by
  refine algHom_ext fun o => ?_
  cases o with
  | none => simp [pointChart, pointChartZ, ht]
  | some l =>
    by_cases hl : l = j
    · subst hl
      simp [pointChart, pointChartZ]
    · simp [pointChart, pointChartZ, hl]

/-- **The chart of `x_j` keeps the form.** Let `a_i` have order at least `m - i` for each `i < m`, and let the translation of `z` be `0`. Then the chart of `x_j` sends `z^m + ∑_{i < m} a_i z^i` to `x_j^m (z^m + ∑_{i < m} a_i' z^i)`, where `a_i'` is the transform of `a_i` with `π(a_i) = x_j^{m-i} a_i'` in the chart of `k[x]`. -/
theorem pointChart_zMonic {m : ℕ} {a : ℕ → MvPolynomial σ k}
    (hord : ∀ i < m, ((m - i : ℕ) : ℕ∞) ≤ ord (a i)) (j : σ) {t : Option σ → k}
    (ht : t none = 0) :
    pointChart (Option.some j) t (zMonic m a) = X (Option.some j) ^ m *
      zMonic m (fun i => chartTransform j (fun l => t (Option.some l)) (m - i) (a i)) := by
  have hz : pointChart (Option.some j) t (X none) = X (Option.some j) * X none := by
    rw [pointChart_X_of_ne t (Option.some_ne_none j).symm, ht, C_0, add_zero]
  rw [zMonic, zMonic, map_add, map_pow, hz, map_sum, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [map_mul, map_pow, hz, pointChart_some_rename,
      pointChart_eq_X_pow_mul_chartTransform j _ (hord i hi'), map_mul, map_pow, rename_X,
      show X (Option.some j) ^ m = (X (Option.some j) : MvPolynomial (Option σ) k) ^ (m - i) * X (Option.some j) ^ i by
        rw [← pow_add, Nat.sub_add_cancel hi'.le]]
    ring

/-- **The lemma of Tschirnhausen for a point blowup (part (c)).** Let `k` be a field with `m ≠ 0` in `k`, and let `f = z^m + ∑_{i < m} a_i z^i` be in Tschirnhausen form, `a_{m-1} = 0`, with `ord a_i ≥ m - i` for each `i < m` (so that `ord f = m`). Let the chart `pointChart c t` of the blowup of the origin of `k^{1+n}` send `f` to `X c ^ m * f'`, and let `f'` have order at least `m`. Then:

* the chart is the chart of a variable `x_j` (`c = Option.some j`), and the translation of `z` is `0`;
* `f' = z^m + ∑_{i < m} a_i' z^i` is again in Tschirnhausen form, with `π(a_i) = x_j^{m-i} a_i'` in the chart `pointChart j t` of `k[x]`;
* `ord a_i' ≥ m - i` for each `i < m`.

So the hypotheses hold again for `f'`, and the points of order `m` after the blowup lie on the strict transform of `z = 0`. -/
theorem tschirnhausen_pointChart {m : ℕ} (hm : (m : k) ≠ 0) {a : ℕ → MvPolynomial σ k}
    (ha : a (m - 1) = 0) (hord : ∀ i < m, ((m - i : ℕ) : ℕ∞) ≤ ord (a i)) {c : Option σ}
    {t : Option σ → k} {f' : MvPolynomial (Option σ) k}
    (h : pointChart c t (zMonic m a) = X c ^ m * f') (hf' : (m : ℕ∞) ≤ ord f') :
    ∃ j : σ, c = Option.some j ∧ t none = 0 ∧ ∃ a' : ℕ → MvPolynomial σ k, f' = zMonic m a' ∧
      a' (m - 1) = 0 ∧ (∀ i < m, ((m - i : ℕ) : ℕ∞) ≤ ord (a' i)) ∧
      ∀ i < m, pointChart j (fun l => t (Option.some l)) (a i) = X j ^ (m - i) * a' i := by
  have hu : IsUnit (m : k) := hm.isUnit
  -- The order of `f` is `m`.
  have hfm : ord (zMonic m a) = m := by
    refine le_antisymm ?_ (le_ord_zMonic_iff.mpr hord)
    have h1 : (zMonic m a).coeff (Finsupp.single none m) ≠ 0 := by
      rw [coeff_zMonic, single_eq_same, ite_eq_right (lt_irrefl m), ite_eq_left rfl,
        Finsupp.some_single_none, AddMonoidAlgebra.coeff_one_zero]
      exact one_ne_zero
    exact (ord_le h1).trans_eq (by rw [degree_single])
  have hf'm : ord f' = m := le_antisymm (ord_le_of_pointChart hfm h) hf'
  -- The vector of the chart lies in the directrix of the initial form.
  have hv := mem_directrix_of_ord_pointChart_eq hfm h hf'm
  rw [homogeneousComponent_zMonic] at hv
  set g := zMonic m fun i => homogeneousComponent (m - i) (a i) with hg
  have hg0 : (fun i => homogeneousComponent (m - i) (a i)) (m - 1) = 0 := by
    simp only [ha, map_zero]
  have hgm : (m : ℕ∞) ≤ ord g := by
    rw [hg, ← homogeneousComponent_zMonic]
    refine le_ord_iff.mpr fun d hd => ?_
    rw [coeff_homogeneousComponent, ite_eq_right (by omega)]
  have htr := aeval_add_smul_of_mem_directrix hv 1
  have hvz := eq_zero_of_le_ord_translate hu hg0 (fun o => 1 * chartVector c t o)
    (by rw [htr]; exact hgm)
  rcases c with _ | j
  · simp [chartVector] at hvz
  have ht : t none = 0 := by
    simpa [chartVector] using hvz
  refine ⟨j, rfl, ht, fun i => chartTransform j (fun l => t (Option.some l)) (m - i) (a i), ?_, ?_, ?_,
    fun i hi => pointChart_eq_X_pow_mul_chartTransform j _ (hord i hi)⟩
  · have h2 := pointChart_zMonic hord j ht
    rw [h] at h2
    exact mul_left_cancel₀ (pow_ne_zero m (X_ne_zero _)) h2
  · simp [ha, chartTransform]
  · have h2 := pointChart_zMonic hord j ht
    rw [h] at h2
    rw [mul_left_cancel₀ (pow_ne_zero m (X_ne_zero _)) h2] at hf'
    exact le_ord_zMonic_iff.mp hf'

end Field

/-! ### The hypothesis that `m` is a unit is necessary -/

section Narasimhan

variable (K : Type*) [Field K]

/-- The coefficients of the polynomial of Narasimhan as a polynomial in `x`: `a_0 = y z^3 + z w^3 + y^7 w` and `a_i = 0` for `i ≥ 1`. The variables `y, z, w` are `X 0, X 1, X 2` of `Fin 3`. -/
noncomputable def narasimhanCoeff : ℕ → MvPolynomial (Fin 3) K :=
  fun i => if i = 0 then X 0 * X 1 ^ 3 + X 1 * X 2 ^ 3 + X 0 ^ 7 * X 2 else 0

/-- `zMonic 2 (narasimhanCoeff K)` is the polynomial `Singularity.Examples.narasimhanF` of Narasimhan, with `x = X 0` of `Fin 4` as the variable `z = X none`. -/
theorem zMonic_narasimhanCoeff :
    zMonic 2 (narasimhanCoeff K) = rename (finSuccEquiv 3) (Examples.narasimhanF K) := by
  have h0 : finSuccEquiv 3 0 = none := rfl
  have h1 : finSuccEquiv 3 1 = Option.some 0 := rfl
  have h2 : finSuccEquiv 3 2 = Option.some 1 := rfl
  have h3 : finSuccEquiv 3 3 = Option.some 2 := rfl
  simp only [zMonic, narasimhanCoeff, Examples.narasimhanF, Finset.sum_range_succ,
    Finset.sum_range_zero, map_add, map_mul, map_pow, rename_X, h0, h1, h2, h3]
  try simp
  try ring

theorem two_le_ord_narasimhanCoeff : ∀ i < 2, ((2 - i : ℕ) : ℕ∞) ≤ ord (narasimhanCoeff K i) := by
  intro i hi
  interval_cases i
  · refine le_ord_iff_mem_pow.mpr ?_
    have hX := X_mem_idealOfVars (R := K) (σ := Fin 3)
    have hmem : ∀ p q : Fin 3, ∀ P : MvPolynomial (Fin 3) K,
        X p * X q * P ∈ idealOfVars (Fin 3) K ^ (2 - 0) := fun p q P =>
      Ideal.mul_mem_right _ _ (by rw [Nat.sub_zero, pow_two]; exact Ideal.mul_mem_mul (hX p) (hX q))
    have he : narasimhanCoeff K 0 = X 0 * X 1 * X 1 ^ 2 + X 1 * X 2 * X 2 ^ 2 + X 0 * X 2 * X 0 ^ 6 := by
      simp only [narasimhanCoeff, ↓reduceIte]
      ring
    rw [he]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hmem _ _ _) (hmem _ _ _)) (hmem _ _ _)
  · simp [narasimhanCoeff]

/-- In characteristic `2`, the polynomial of Narasimhan has order at least `2` at the point `(1, 1, 1, 1)`. The four terms of `f(1 + u)` give `4 + 2 u_x + 8 u_y + 4 u_z + 4 u_w` plus terms of degree at least `2`. -/
theorem narasimhan_le_ord_translate [CharP K 2] :
    ((2 : ℕ) : ℕ∞) ≤ ord (aeval (fun o => X o + C ((fun _ => (1 : K)) o))
      (zMonic 2 (narasimhanCoeff K))) := by
  have h2 : (2 : MvPolynomial (Option (Fin 3)) K) = 0 := by
    rw [← map_ofNat (C : K →+* MvPolynomial (Option (Fin 3)) K) 2, CharTwo.two_eq_zero, map_zero]
  set x : MvPolynomial (Option (Fin 3)) K := X none
  set y : MvPolynomial (Option (Fin 3)) K := X (Option.some 0)
  set z : MvPolynomial (Option (Fin 3)) K := X (Option.some 1)
  set w : MvPolynomial (Option (Fin 3)) K := X (Option.some 2)
  have hE : aeval (fun o => X o + C ((fun _ => (1 : K)) o)) (zMonic 2 (narasimhanCoeff K)) =
      (x + 1) ^ 2 + ((y + 1) * (z + 1) ^ 3 + (z + 1) * (w + 1) ^ 3 + (y + 1) ^ 7 * (w + 1)) := by
    simp [zMonic, narasimhanCoeff, Finset.sum_range_succ, x, y, z, w]
  have hQ : (x + 1) ^ 2 + ((y + 1) * (z + 1) ^ 3 + (z + 1) * (w + 1) ^ 3 + (y + 1) ^ 7 * (w + 1)) =
      x * x * 1 + y * z * (3 + 3 * z + z ^ 2) + z * z * (3 + z) + z * w * (3 + 3 * w + w ^ 2) +
        w * w * (3 + w) +
        w * y * (7 + 21 * y + 35 * y ^ 2 + 35 * y ^ 3 + 21 * y ^ 4 + 7 * y ^ 5 + y ^ 6) +
        y * y * (21 + 35 * y + 35 * y ^ 2 + 21 * y ^ 3 + 7 * y ^ 4 + y ^ 5) := by
    linear_combination (2 + x + 4 * y + 2 * z + 2 * w) * h2
  have hX := X_mem_idealOfVars (R := K) (σ := Option (Fin 3))
  have hmem : ∀ p q : Option (Fin 3), ∀ P : MvPolynomial (Option (Fin 3)) K,
      X p * X q * P ∈ idealOfVars (Option (Fin 3)) K ^ 2 := fun p q P =>
    Ideal.mul_mem_right _ _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hX p) (hX q))
  refine le_ord_iff_mem_pow.mpr ?_
  rw [hE, hQ]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.add_mem _ (hmem _ _ _) (hmem _ _ _)) (hmem _ _ _)) (hmem _ _ _)) (hmem _ _ _))
    (hmem _ _ _)) (hmem _ _ _)

/-- **The hypothesis that `m` is a unit is necessary.** Over a field of characteristic `2`, part (b) fails for `m = 2`: the polynomial of Narasimhan `x^2 + (y z^3 + z w^3 + y^7 w)` is in Tschirnhausen form, the coefficient `a_0` has order at least `2`, and the polynomial has order at least `2` at the point `(1, 1, 1, 1)`, whose coordinate `x` is `1 ≠ 0`. -/
theorem not_tschirnhausen_charTwo [CharP K 2] :
    ¬ ∀ (m : ℕ) (a : ℕ → MvPolynomial (Fin 3) K) (b : Option (Fin 3) → K), a (m - 1) = 0 →
      (∀ i < m, ((m - i : ℕ) : ℕ∞) ≤ ord (a i)) →
      (m : ℕ∞) ≤ ord (aeval (fun o => X o + C (b o)) (zMonic m a)) → b none = 0 := by
  intro H
  have := H 2 (narasimhanCoeff K) (fun _ => 1) (by simp [narasimhanCoeff])
    (two_le_ord_narasimhanCoeff K) (narasimhan_le_ord_translate K)
  exact one_ne_zero this

end Narasimhan

end Singularity
