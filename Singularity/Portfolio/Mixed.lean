/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.Perfect
import Singularity.Invariant.RigidLayer

/-!
# Mixed multiplicities and the lifting of a base blowup

This file proves Lemmas 10.3, 10.4 and 10.5 of research note 10. The handbook numbers are not fixed yet.

Let `R` be a commutative ring of characteristic `p`, let `m = p^e m_0` with `p ∤ m_0`, and let `f = z^m + a_1 z^(m-1) + ... + a_m`. Here `a_i` is the coefficient `f.coeff (m - i)` of `z^(m-i)`. The translation `z ↦ z + c` changes `f` into `f.comp (X + C c)`, with the coefficients `a'_i`.

* Lemma 10.3 (Lucas and Tschirnhausen). `a'_(p^e) = a_(p^e) + m_0 c^(p^e) + ∑_(0 < j < p^e) binom(m - j, p^e - j) a_j c^(p^e - j)` (`Portfolio.lucas_tschirnhausen`).
* Lemma 10.4 (the inseparable layer is rigid). For `0 < i < p^e`, `a'_i = a_i + ∑_(0 < j < i) binom(m - j, i - j) a_j c^(i-j)` (`Portfolio.inseparable_layer_rigid`).

The proofs follow the note. The general translation formula is `coeff_taylor_natDegree_sub_eq` of `Singularity/Invariant/RigidLayer.lean`. The theorem of Lucas (`Choose.choose_modEq_choose_mul_prod_range_choose` of Mathlib) gives `binom(p^e m_0, p^e) ≡ m_0` and `binom(p^e m_0, i) ≡ 0` modulo `p` for `0 < i < p^e` (`Portfolio.choose_pow_mul_pow_modEq`, `Portfolio.choose_pow_mul_modEq_zero`). The file `RigidLayer.lean` proves the same two formulas with the Frobenius identity and not with the theorem of Lucas.

* Lemma 10.5 (lifting a base blowup). Let `q = p^e`, let `I ≠ R` be an ideal of `R`, let `g, h ∈ R`, and let `J = (z - h) + I R[z]`. For each `n`, `z^q + g ∈ J^n` if and only if `n ≤ q` and `g + h^q ∈ I^n` (`Portfolio.X_pow_add_C_mem_pow_iff_order`). So the order of `z^q + g` along `J` is the minimum of `q` and the order of `g + h^q` along `I`. In particular `z^q + g ∈ J`, `z^q + g ∈ J^q` and `z^q + g ∉ J^(q+1)` if and only if `g + h^q ∈ I^q` (`Portfolio.lift_base_blowup`). The key step is the description of the powers of `(z) + I R[z]` by the coefficients: `f ∈ ((z) + I R[z])^n` if and only if the coefficient of `z^k` is in `I^(n-k)` for each `k` (`Portfolio.mem_span_X_sup_map_C_pow_iff`). This is the associated graded ring `gr_I(R)[Z]` of the note in an elementary form. In a chart where `I` becomes the principal ideal `(x)`, the substitution `z = h + x z''` sends `z^q + g` to `x^q (z''^q + g'')` with `x^q g'' = g + h^q` (`Portfolio.lift_base_blowup_chart`).

## What is not proved

The order along `J` in this file is the largest `n` with `f ∈ J^n`, with ordinary powers. The note uses the order at the generic point of the centre. The two agree when `R` is regular and `R / I` is regular, but the file does not prove this. The file does not prove that the blowup is permissible (normal flatness, or the order `p` at each point of the centre), and it has no blowup of a scheme. The chart lemma is a ring identity in a ring where `I` becomes principal. It does not prove that the strict transform is `x^(-p) π^*(z^p + g)`.
-/

open Polynomial

namespace Singularity

namespace Portfolio

/-! ### The theorem of Lucas for `binom(p^e m_0, i)` -/

section Lucas

variable {p : ℕ} [hp : Fact p.Prime]

/-- If the base `p` digits of `k` in the places `i < a` are all `0`, then `p^a` divides `k`. -/
theorem pow_dvd_of_forall_div_pow_mod_eq_zero {k a : ℕ} (h : ∀ i < a, k / p ^ i % p = 0) :
    p ^ a ∣ k := by
  induction a with
  | zero => simp
  | succ a ih =>
    obtain ⟨t, rfl⟩ := ih fun i hi => h i (by omega)
    have ht := h a (by omega)
    rw [Nat.mul_div_cancel_left t (pow_pos hp.out.pos a)] at ht
    rw [pow_succ]
    exact Nat.mul_dvd_mul_left _ (Nat.dvd_of_mod_eq_zero ht)

/-- For `i < e`, the base `p` digit of `p^e m_0` in the place `i` is `0`. -/
theorem pow_mul_div_pow_mod_eq_zero {e i : ℕ} (m₀ : ℕ) (hi : i < e) :
    p ^ e * m₀ / p ^ i % p = 0 := by
  rw [show p ^ e * m₀ = p ^ i * (p ^ (e - i) * m₀) by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi.le],
    Nat.mul_div_cancel_left _ (pow_pos hp.out.pos i)]
  exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _)

/-- The theorem of Lucas for `binom(p^e m_0, p^e)`. The base `p` digits of `p^e` are `1` in the place `e` and `0` in the other places, and the digits of `p^e m_0` in the places below `e` are `0`. So `binom(p^e m_0, p^e) ≡ binom(m_0, 1) = m_0` modulo `p`. -/
theorem choose_pow_mul_pow_modEq (e m₀ : ℕ) :
    ((p ^ e * m₀).choose (p ^ e) : ℤ) ≡ m₀ [ZMOD p] := by
  have hq : 0 < p ^ e := pow_pos hp.out.pos e
  refine (Choose.choose_modEq_choose_mul_prod_range_choose (p := p) (n := p ^ e * m₀)
    (k := p ^ e) e).trans ?_
  rw [Nat.mul_div_cancel_left _ hq, Nat.div_self hq, Nat.choose_one_right,
    Finset.prod_eq_one, Nat.cast_one, mul_one]
  intro i hi
  rw [Finset.mem_range] at hi
  have h2 : p ^ e / p ^ i % p = 0 := by
    simpa using pow_mul_div_pow_mod_eq_zero (p := p) 1 hi
  rw [pow_mul_div_pow_mod_eq_zero m₀ hi, h2]
  simp

/-- The theorem of Lucas for `binom(p^e m_0, k)` with `p^e ∤ k`. Some base `p` digit of `k` in a place `i < e` is not `0`, and the digit of `p^e m_0` in this place is `0`. So `binom(p^e m_0, k) ≡ 0` modulo `p`. -/
theorem choose_pow_mul_modEq_zero {e m₀ k : ℕ} (hk : ¬ p ^ e ∣ k) :
    ((p ^ e * m₀).choose k : ℤ) ≡ 0 [ZMOD p] := by
  refine (Choose.choose_modEq_choose_mul_prod_range_choose (p := p) (n := p ^ e * m₀)
    (k := k) e).trans ?_
  obtain ⟨i, hi, hki⟩ : ∃ i < e, k / p ^ i % p ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (pow_dvd_of_forall_div_pow_mod_eq_zero h)
  rw [Finset.prod_eq_zero (Finset.mem_range.2 hi), Nat.cast_zero, mul_zero]
  rw [pow_mul_div_pow_mod_eq_zero m₀ hi, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hki)]

variable {R : Type*} [CommRing R] [CharP R p]

/-- In a ring of characteristic `p`, `binom(p^e m_0, p^e) = m_0`, by the theorem of Lucas. -/
theorem cast_choose_pow_mul_pow_lucas (e m₀ : ℕ) :
    (((p ^ e * m₀).choose (p ^ e) : ℕ) : R) = m₀ := by
  exact_mod_cast (CharP.intCast_eq_intCast R p).2 (choose_pow_mul_pow_modEq (p := p) e m₀)

/-- In a ring of characteristic `p`, `binom(p^e m_0, k) = 0` if `p^e ∤ k`, by the theorem of Lucas. -/
theorem cast_choose_pow_mul_eq_zero_lucas {e m₀ k : ℕ} (hk : ¬ p ^ e ∣ k) :
    (((p ^ e * m₀).choose k : ℕ) : R) = 0 := by
  exact_mod_cast (CharP.intCast_eq_intCast R p).2 (choose_pow_mul_modEq_zero (m₀ := m₀) hk)

end Lucas

/-! ### Lemmas 10.3 and 10.4 -/

section Translation

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

omit hp in
private theorem pos_of_not_dvd {m₀ : ℕ} (hm₀ : ¬ p ∣ m₀) : 0 < m₀ :=
  Nat.pos_of_ne_zero fun h => hm₀ (h ▸ dvd_zero p)

/-- Lemma 10.3 of research note 10 (Lucas and Tschirnhausen). Let `R` have characteristic `p`, let `f` be monic of degree `m = p^e m_0` with `p ∤ m_0`, and let `a_i = f.coeff (m - i)`. Let `a'_i` be the coefficients of `f(z + c)`. Then `a'_(p^e) = a_(p^e) + m_0 c^(p^e) + ∑_(0 < j < p^e) binom(m - j, p^e - j) a_j c^(p^e - j)`. -/
theorem lucas_tschirnhausen {f : R[X]} (hmonic : f.Monic) {e m₀ m : ℕ} (hm : m = p ^ e * m₀)
    (hm₀ : ¬ p ∣ m₀) (hf : f.natDegree = m) (c : R) :
    (f.comp (X + C c)).coeff (m - p ^ e) = f.coeff (m - p ^ e) + m₀ * c ^ p ^ e +
      ∑ j ∈ Finset.Ioo 0 (p ^ e),
        ((m - j).choose (p ^ e - j) : R) * f.coeff (m - j) * c ^ (p ^ e - j) := by
  have hq : 0 < p ^ e := pow_pos hp.out.pos e
  have him : p ^ e ≤ f.natDegree := by
    rw [hf, hm]
    exact Nat.le_mul_of_pos_right _ (pos_of_not_dvd hm₀)
  rw [← taylor_apply, ← hf, coeff_taylor_natDegree_sub_eq f c hq him, hmonic.coeff_natDegree, hf,
    hm, cast_choose_pow_mul_pow_lucas, mul_one]

/-- Lemma 10.3 of research note 10, when `a_1 = ... = a_(p^e - 1) = 0`. Then the translation `z ↦ z + c` adds `m_0 c^(p^e)` to `a_(p^e)`. -/
theorem lucas_tschirnhausen_of_eq_zero {f : R[X]} (hmonic : f.Monic) {e m₀ m : ℕ}
    (hm : m = p ^ e * m₀) (hm₀ : ¬ p ∣ m₀) (hf : f.natDegree = m) (c : R)
    (h : ∀ j, 0 < j → j < p ^ e → f.coeff (m - j) = 0) :
    (f.comp (X + C c)).coeff (m - p ^ e) = f.coeff (m - p ^ e) + m₀ * c ^ p ^ e := by
  rw [lucas_tschirnhausen hmonic hm hm₀ hf c, Finset.sum_eq_zero, add_zero]
  intro j hj
  rw [Finset.mem_Ioo] at hj
  rw [h j hj.1 hj.2, mul_zero, zero_mul]

omit hp in
/-- The factor `m_0` of Lemma 10.3 of research note 10 is not `0` in a nontrivial ring of characteristic `p`. -/
theorem cast_ne_zero_of_not_dvd [Nontrivial R] {m₀ : ℕ} (hm₀ : ¬ p ∣ m₀) : (m₀ : R) ≠ 0 := by
  rwa [Ne, CharP.cast_eq_zero_iff R p]

/-- The cleaning step after Lemma 10.3 of research note 10. Over a perfect field `K` of characteristic `p`, if `a_1 = ... = a_(p^e - 1) = 0`, then a translation `z ↦ z + c` makes `a_(p^e) = 0`. -/
theorem exists_lucas_tschirnhausen_eq_zero {K : Type*} [Field K] [CharP K p] [PerfectRing K p]
    {f : K[X]} (hmonic : f.Monic) {e m₀ m : ℕ} (hm : m = p ^ e * m₀) (hm₀ : ¬ p ∣ m₀)
    (hf : f.natDegree = m) (h : ∀ j, 0 < j → j < p ^ e → f.coeff (m - j) = 0) :
    ∃ c : K, (f.comp (X + C c)).coeff (m - p ^ e) = 0 := by
  have hu : (m₀ : K) ≠ 0 := cast_ne_zero_of_not_dvd hm₀
  refine ⟨(iterateFrobeniusEquiv K p e).symm (-f.coeff (m - p ^ e) / m₀), ?_⟩
  rw [lucas_tschirnhausen_of_eq_zero hmonic hm hm₀ hf _ h, ← iterateFrobeniusEquiv_def,
    RingEquiv.apply_symm_apply, mul_div_cancel₀ _ hu]
  ring

/-- Lemma 10.4 of research note 10 (the inseparable layer is rigid). Let `R` have characteristic `p`, let `f` have degree `m = p^e m_0` with `p ∤ m_0`, and let `a_i = f.coeff (m - i)`. Let `a'_i` be the coefficients of `f(z + c)`. For `0 < i < p^e`, `a'_i = a_i + ∑_(0 < j < i) binom(m - j, i - j) a_j c^(i-j)`. -/
theorem inseparable_layer_rigid {f : R[X]} {e m₀ m : ℕ} (hm : m = p ^ e * m₀) (hm₀ : ¬ p ∣ m₀)
    (hf : f.natDegree = m) (c : R) {i : ℕ} (hi₀ : 0 < i) (hi : i < p ^ e) :
    (f.comp (X + C c)).coeff (m - i) = f.coeff (m - i) +
      ∑ j ∈ Finset.Ioo 0 i, ((m - j).choose (i - j) : R) * f.coeff (m - j) * c ^ (i - j) := by
  have him : i ≤ f.natDegree := by
    rw [hf, hm]
    exact hi.le.trans (Nat.le_mul_of_pos_right _ (pos_of_not_dvd hm₀))
  rw [← taylor_apply, ← hf, coeff_taylor_natDegree_sub_eq f c hi₀ him, hf, hm,
    cast_choose_pow_mul_eq_zero_lucas (Nat.not_dvd_of_pos_of_lt hi₀ hi), zero_mul, zero_mul, add_zero]

/-- Lemma 10.4 of research note 10. If `a_1 = ... = a_(i-1) = 0` and `0 < i < p^e`, then `a'_i = a_i` for each `c`. -/
theorem inseparable_layer_rigid_of_eq_zero {f : R[X]} {e m₀ m : ℕ} (hm : m = p ^ e * m₀)
    (hm₀ : ¬ p ∣ m₀) (hf : f.natDegree = m) (c : R) {i : ℕ} (hi₀ : 0 < i) (hi : i < p ^ e)
    (h : ∀ j, 0 < j → j < i → f.coeff (m - j) = 0) :
    (f.comp (X + C c)).coeff (m - i) = f.coeff (m - i) := by
  rw [inseparable_layer_rigid hm hm₀ hf c hi₀ hi, Finset.sum_eq_zero, add_zero]
  intro j hj
  rw [Finset.mem_Ioo] at hj
  rw [h j hj.1 hj.2, mul_zero, zero_mul]

/-- Lemma 10.4 of research note 10 for `i = 1`. If `e ≥ 1`, then `a'_1 = a_1` for each `c`. -/
theorem inseparable_layer_rigid_one {f : R[X]} {e m₀ m : ℕ} (he : 1 ≤ e) (hm : m = p ^ e * m₀)
    (hm₀ : ¬ p ∣ m₀) (hf : f.natDegree = m) (c : R) :
    (f.comp (X + C c)).coeff (m - 1) = f.coeff (m - 1) :=
  inseparable_layer_rigid_of_eq_zero hm hm₀ hf c one_pos
    (Nat.one_lt_pow (by omega) hp.out.one_lt) fun j hj hj' => by omega

end Translation

/-! ### The powers of the ideal `(z) + I R[z]` -/

section Graded

variable {R : Type*} [CommRing R]

/-- The polynomials whose coefficient of `z^k` is in `I^(n-k)` for each `k`. This is the ideal `((z) + I R[z])^n` (`mem_span_X_sup_map_C_pow_iff`). -/
def coeffPowIdeal (I : Ideal R) (n : ℕ) : Ideal R[X] where
  carrier := {f | ∀ k, f.coeff k ∈ I ^ (n - k)}
  add_mem' := fun ha hb k => by
    rw [coeff_add]
    exact add_mem (ha k) (hb k)
  zero_mem' := fun k => by simp
  smul_mem' := fun r f hf k => by
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun x hx => Ideal.mul_mem_left _ _ ?_
    rw [Finset.mem_antidiagonal] at hx
    exact Ideal.pow_le_pow_right (by omega) (hf x.2)

theorem mem_coeffPowIdeal {I : Ideal R} {n : ℕ} {f : R[X]} :
    f ∈ coeffPowIdeal I n ↔ ∀ k, f.coeff k ∈ I ^ (n - k) :=
  Iff.rfl

theorem coeffPowIdeal_mul_le (I : Ideal R) (a b : ℕ) :
    coeffPowIdeal I a * coeffPowIdeal I b ≤ coeffPowIdeal I (a + b) := by
  rw [Ideal.mul_le]
  intro f hf g hg k
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  refine Ideal.pow_le_pow_right (by omega : a + b - k ≤ (a - x.1) + (b - x.2)) ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul (hf x.1) (hg x.2)

theorem span_X_sup_map_C_le_coeffPowIdeal (I : Ideal R) :
    Ideal.span {X} ⊔ I.map (C : R →+* R[X]) ≤ coeffPowIdeal I 1 := by
  refine sup_le ?_ ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_coeffPowIdeal]
    intro k
    rw [coeff_X]
    split_ifs with h
    · subst h
      simp
    · exact zero_mem _
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_coeffPowIdeal]
    intro k
    rw [coeff_C]
    split_ifs with h
    · subst h
      simpa using ha
    · exact zero_mem _

theorem pow_span_X_sup_map_C_le (I : Ideal R) (n : ℕ) :
    (Ideal.span {X} ⊔ I.map (C : R →+* R[X])) ^ n ≤ coeffPowIdeal I n := by
  induction n with
  | zero =>
    intro f _ k
    simp
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (span_X_sup_map_C_le_coeffPowIdeal I)).trans
      (coeffPowIdeal_mul_le I n 1)

theorem coeffPowIdeal_le_pow (I : Ideal R) (n : ℕ) :
    coeffPowIdeal I n ≤ (Ideal.span {X} ⊔ I.map (C : R →+* R[X])) ^ n := by
  set J := Ideal.span {X} ⊔ I.map (C : R →+* R[X])
  have hX : (X : R[X]) ∈ J := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  intro f hf
  rw [mem_coeffPowIdeal] at hf
  rw [f.as_sum_support]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [← C_mul_X_pow_eq_monomial]
  rcases le_or_gt n k with hk | hk
  · exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow hX k))
  · have hC : C (f.coeff k) ∈ J ^ (n - k) := by
      refine Ideal.pow_right_mono le_sup_right _ ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem C (hf k)
    have h := Ideal.mul_mem_mul hC (Ideal.pow_mem_pow hX k)
    rwa [← pow_add, Nat.sub_add_cancel hk.le] at h

/-- The powers of `(z) + I R[z]`. A polynomial `f` is in `((z) + I R[z])^n` if and only if the coefficient of `z^k` in `f` is in `I^(n-k)` for each `k`. This is the elementary form of the statement that the associated graded ring of `R[z]` for `(z) + I R[z]` is `gr_I(R)[Z]`, used in the proof of Lemma 10.5 of research note 10. -/
theorem mem_span_X_sup_map_C_pow_iff (I : Ideal R) (n : ℕ) (f : R[X]) :
    f ∈ (Ideal.span {X} ⊔ I.map (C : R →+* R[X])) ^ n ↔ ∀ k, f.coeff k ∈ I ^ (n - k) :=
  ⟨fun h => pow_span_X_sup_map_C_le I n h, fun h => coeffPowIdeal_le_pow I n h⟩

/-- The translation `z ↦ z + c` sends `((z - d) + I R[z])^n` into `((z - (d - c)) + I R[z])^n`. -/
theorem taylor_mem_pow (I : Ideal R) (c d : R) {f : R[X]} {n : ℕ}
    (hf : f ∈ (Ideal.span {X - C d} ⊔ I.map (C : R →+* R[X])) ^ n) :
    taylor c f ∈ (Ideal.span {X - C (d - c)} ⊔ I.map (C : R →+* R[X])) ^ n := by
  have hK : (Ideal.span {X - C d} ⊔ I.map (C : R →+* R[X])).map
      (taylorAlgHom c : R[X] →+* R[X]) ≤ Ideal.span {X - C (d - c)} ⊔ I.map C := by
    rw [Ideal.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
      have : (taylorAlgHom c : R[X] →+* R[X]) (X - C d) = X - C (d - c) := by
        simp only [RingHom.coe_coe, map_sub, taylorAlgHom_apply, taylor_X, taylor_C]
        ring
      rw [this]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have : (taylorAlgHom c : R[X] →+* R[X]) (C a) = C a := by
        simp only [RingHom.coe_coe, taylorAlgHom_apply, taylor_C]
      rw [this]
      exact Ideal.mem_sup_right (Ideal.mem_map_of_mem C ha)
  have h := Ideal.mem_map_of_mem (taylorAlgHom c : R[X] →+* R[X]) hf
  rw [Ideal.map_pow] at h
  simpa using Ideal.pow_right_mono hK n h

end Graded

/-! ### Lemma 10.5 -/

section Lift

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]

/-- Lemma 10.5 of research note 10, the order form. Let `q = p^e`, let `I ≠ R` be an ideal, let `g, h ∈ R`, and let `J = (z - h) + I R[z]`. For each `n`, `z^q + g ∈ J^n` if and only if `n ≤ q` and `g + h^q ∈ I^n`. So the order of `z^q + g` along `J` is the minimum of `q` and the order of `g + h^q` along `I`. The proof translates `z = z' + h`. Then the equation is `z'^q + (g + h^q)`, and the powers of `(z') + I R[z']` are described by `mem_span_X_sup_map_C_pow_iff`. -/
theorem X_pow_add_C_mem_pow_iff_order {I : Ideal R} (hI : I ≠ ⊤) (g h : R) (e n : ℕ) :
    X ^ p ^ e + C g ∈ (Ideal.span {X - C h} ⊔ I.map (C : R →+* R[X])) ^ n ↔
      n ≤ p ^ e ∧ g + h ^ p ^ e ∈ I ^ n := by
  have hq : 0 < p ^ e := expChar_pow_pos R p e
  have key : taylor h (X ^ p ^ e + C g) = X ^ p ^ e + C (g + h ^ p ^ e) := by
    rw [map_add, taylor_pow, taylor_X, taylor_C, add_pow_expChar_pow, map_add, map_pow]
    ring
  have hiff : X ^ p ^ e + C g ∈ (Ideal.span {X - C h} ⊔ I.map (C : R →+* R[X])) ^ n ↔
      taylor h (X ^ p ^ e + C g) ∈ (Ideal.span {X} ⊔ I.map (C : R →+* R[X])) ^ n := by
    constructor
    · intro hf
      simpa using taylor_mem_pow I h h hf
    · intro hf
      have h' := taylor_mem_pow I (-h) 0 (by simpa using hf)
      simpa [taylor_taylor] using h'
  rw [hiff, key, mem_span_X_sup_map_C_pow_iff]
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    swap
    · have h0 := H 0
      rw [coeff_add, coeff_X_pow, coeff_C_zero, Nat.sub_zero] at h0
      simpa [hq.ne] using h0
    by_contra hn
    have h1 := H (p ^ e)
    rw [coeff_add, coeff_X_pow_self, coeff_C_of_ne_zero hq.ne', add_zero] at h1
    exact hI ((Ideal.eq_top_iff_one I).2 (Ideal.pow_le_self (by omega) h1))
  · rintro ⟨hn, hg⟩ k
    rw [coeff_add, coeff_X_pow]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [coeff_C_zero, Nat.sub_zero]
      simpa [hq.ne] using hg
    · rw [coeff_C_of_ne_zero hk, add_zero]
      split_ifs with hkq
      · subst hkq
        simp [Nat.sub_eq_zero_of_le hn]
      · exact zero_mem _

/-- Lemma 10.5 of research note 10 (lifting a base blowup). Let `q = p^e`, let `I ≠ R` be the ideal of the centre `C` in the base, let `g, h ∈ R`, and let `J = (z - h) + I R[z]` be the ideal of `C' = V(z - h, I)`. Then `C'` lies in `X = V(z^q + g)` and `z^q + g` has order exactly `q` along `J` if and only if `g + h^q ∈ I^q`. -/
theorem lift_base_blowup {I : Ideal R} (hI : I ≠ ⊤) (g h : R) (e : ℕ) :
    (X ^ p ^ e + C g ∈ Ideal.span {X - C h} ⊔ I.map (C : R →+* R[X]) ∧
      X ^ p ^ e + C g ∈ (Ideal.span {X - C h} ⊔ I.map (C : R →+* R[X])) ^ p ^ e ∧
      X ^ p ^ e + C g ∉ (Ideal.span {X - C h} ⊔ I.map (C : R →+* R[X])) ^ (p ^ e + 1)) ↔
      g + h ^ p ^ e ∈ I ^ p ^ e := by
  have hq : 1 ≤ p ^ e := expChar_pow_pos R p e
  rw [X_pow_add_C_mem_pow_iff_order p hI, X_pow_add_C_mem_pow_iff_order p hI]
  constructor
  · rintro ⟨_, ⟨_, hg⟩, _⟩
    exact hg
  · intro hg
    refine ⟨?_, ⟨le_rfl, hg⟩, ?_⟩
    · rw [← pow_one (Ideal.span {X - C h} ⊔ I.map (C : R →+* R[X])),
        X_pow_add_C_mem_pow_iff_order p hI, pow_one]
      exact ⟨hq, Ideal.pow_le_self (by omega) hg⟩
    · rintro ⟨hn, _⟩
      omega

/-- The chart computation of Lemma 10.5 of research note 10. Let `φ : R → A` be a ring map, for example to the chart of a generator `x` of `I` in the blowup of the base, so that `φ(I) ⊆ (x)`. If `g + h^q ∈ I^q`, then `φ(g + h^q) = x^q g''` for some `g''`, and the substitution `z = h + x z''` sends `z^q + g` to `x^q (z''^q + g'')`. So the transform of `z^q + g` in the chart is `z''^q + g''`. -/
theorem lift_base_blowup_chart {A : Type*} [CommRing A] (φ : R →+* A) {I : Ideal R} {x : A}
    (hx : I.map φ ≤ Ideal.span {x}) (g h : R) (e : ℕ) (hg : g + h ^ p ^ e ∈ I ^ p ^ e) :
    ∃ g'' : A, φ (g + h ^ p ^ e) = x ^ p ^ e * g'' ∧
      (((X ^ p ^ e + C g).comp (X + C h)).map φ).comp (C x * X) =
        C (x ^ p ^ e) * (X ^ p ^ e + C g'') := by
  have hmem : φ (g + h ^ p ^ e) ∈ Ideal.span {x ^ p ^ e} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono hx _ ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem φ hg
  obtain ⟨g'', hg''⟩ := Ideal.mem_span_singleton.1 hmem
  refine ⟨g'', hg'', ?_⟩
  have hcomp : (X ^ p ^ e + C g).comp (X + C h) = X ^ p ^ e + C (g + h ^ p ^ e) := by
    rw [add_comp, X_pow_comp, C_comp, add_pow_expChar_pow, map_add, map_pow]
    ring
  rw [hcomp, Polynomial.map_add, Polynomial.map_pow, map_X, map_C, hg'', add_comp, X_pow_comp,
    C_comp, mul_pow, ← C_pow, map_mul]
  ring

end Lift

end Portfolio

end Singularity
