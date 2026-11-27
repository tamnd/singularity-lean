/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Statement D for planar runs

This file proves the algebraic core of Theorem 3.18.11 of Volume 7 of the handbook (Statement D),
that is, Conjecture T of Remark 3.17.34 for the planar runs and the polynomials of degree less
than `p`.

## The model

The library does not have the corner runs in four variables with their Hahn field. So the file
uses an abstract model that keeps only what the proof of Theorem 3.18.11 uses.

* `K` is a field with a valuation `v : AddValuation K (WithTop ℝ)`, for example the Hahn field
  `𝕂` of Lemma 3.15.6 with `v(y_N^a z_N^b) = a + θ b`.
* `F` is a subring of `K`. In the handbook it is the field `𝔽` of the elements of finite type
  (Lemma 3.18.8). The coefficients of the polynomials and the points `Φ_m` lie in `F`.
* `Φ m : σ → F` are the points `Φ_m` and `Φi : σ → K` is the limit `Φ_∞`. The handbook has
  `σ = Fin 2`, but the proof works for each finite set of variables.
* `IsPlanarTail v F Φ Φi Θ γ` says that the tail `Δ_m = Φ_∞ - Φ_m` has a value at least `γ m`,
  that `γ m → Θ`, and that the conclusion of Lemma 3.18.10 holds: for `α ≠ 0` and `c` with
  entries in `F`,
  `v(c + Σ α_i Δ_i) < min_i v(α_i) + Θ`.
  In the handbook `Θ = 1 + θ` and `γ m = v(M_{m+1})`.

The Hasse derivatives `f^{[k]}` of `f ∈ F[X_i : i ∈ σ]` are `hasse k f`. Their coefficients are
`coeff m f^{[k]} = (Π_i C(m_i + k_i, k_i)) coeff (m + k) f` (`coeff_hasse`). They satisfy
(18.5): `(f^{[k]})^{[j]} = (Π_i C(k_i + j_i, k_i)) f^{[k + j]}` (`hasse_hasse`), and Taylor's
formula `f(a + s) = Σ_k f^{[k]}(a) s^k` (`eval₂_add_eq_sum`).

## Statement D

Let `f ≠ 0` with `deg_{X_i} f < p` for each `i`, and assume that `v(n) = 0` for `0 < n < p`. This
holds in characteristic `p` (`AddValuation.map_natCast_eq_zero`). Then (`statementD`):

1. `f(Φ_∞) ≠ 0`.
2. For each `k ≠ 0` with `f^{[k]} ≠ 0`, `v(f(Φ_∞)) < v(f^{[k]}(Φ_∞)) + |k| Θ`. This is the
   displayed inequality of part 3 of Theorem 3.18.11, and it gives part 1.
3. For `m` large, `v(f(Φ_∞) - f(Φ_m)) > v(f(Φ_∞))`. This is part 2.

The condition on the degree is on each variable, so it is weaker than `deg f < p`. The proof is
the induction of the handbook on the degree, with the chain of Step 1 in the form of Step 1 of
Theorem 3.18.26 for `e = 0`: for `k_i ≥ 1` and `k ≠ e_i`, part 2 for `h = f^{[e_i]}` and
`h^{[k - e_i]} = k_i f^{[k]}` give `v(f^{[e_i]}(Φ_∞)) + Θ < v(f^{[k]}(Φ_∞)) + |k| Θ`.

## What is not proved

The file does not build the planar runs, the Hahn field and the field `𝔽`, so it does not prove
Lemma 3.18.8 and Lemma 3.18.10. Their conclusions are the hypotheses of `IsPlanarTail`. The
chain `λ_{s-1} < λ_s + Θ` of part 3 for all `s` and Theorem 3.18.26 for degrees at least `p` are
not proved.

## References

* Volume 7, Section 3.18 of the handbook: Lemma 3.18.10, Theorem 3.18.11 and Remark 3.18.12.
-/

open MvPolynomial Filter Topology

namespace Singularity

namespace PlanarRuns

/-! ### Hasse derivatives in several variables -/

section Hasse

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

/-- The Hasse derivative `f^{[k]}` of a polynomial in several variables, defined by
`X^e ↦ (Π_i C(e_i, k_i)) X^(e - k)`. -/
noncomputable def hasse (k : σ →₀ ℕ) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ e ∈ f.support, monomial (e - k) ((∏ i, (e i).choose (k i)) • f.coeff e)

/-- The coefficients of a Hasse derivative. -/
theorem coeff_hasse (k m : σ →₀ ℕ) (f : MvPolynomial σ R) :
    (hasse k f).coeff m = (∏ i, (m i + k i).choose (k i)) • f.coeff (m + k) := by
  rw [hasse, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single (m + k)]
  · simp [Finsupp.add_apply]
  · intro e _ hne
    split_ifs with h
    · have hk : ¬ k ≤ e := by
        intro hk
        apply hne
        rw [← h, tsub_add_cancel_of_le hk]
      have : ∃ i, e i < k i := by
        by_contra hc
        push Not at hc
        exact hk (Finsupp.le_def.mpr hc)
      obtain ⟨i, hi⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Nat.choose_eq_zero_of_lt hi), zero_smul]
    · rfl
  · intro h
    rw [notMem_support_iff.mp h, smul_zero]
    simp

theorem hasse_zero (f : MvPolynomial σ R) : hasse 0 f = f := by
  ext m
  rw [coeff_hasse]
  simp

omit [DecidableEq σ] in
theorem hasse_zero_right (k : σ →₀ ℕ) : hasse k (0 : MvPolynomial σ R) = 0 := by
  simp [hasse]

theorem coeff_zero_hasse (k : σ →₀ ℕ) (f : MvPolynomial σ R) :
    (hasse k f).coeff 0 = f.coeff k := by
  rw [coeff_hasse]
  simp

theorem choose_mul_choose_eq (a b c : ℕ) :
    (a + b).choose b * (a + b + c).choose c = (c + b).choose c * (a + (c + b)).choose (c + b) := by
  have h := Nat.choose_mul (n := a + b + c) (k := c + b) (s := c) (by omega)
  rw [show a + b + c - c = a + b by omega, show c + b - c = b by omega] at h
  rw [show a + (c + b) = a + b + c by ring, mul_comm ((c + b).choose c), h, mul_comm]

/-- The identity (18.5): `(f^{[k]})^{[j]} = (Π_i C(k_i + j_i, k_i)) f^{[k + j]}`. -/
theorem hasse_hasse (j k : σ →₀ ℕ) (f : MvPolynomial σ R) :
    hasse j (hasse k f) = (∏ i, (k i + j i).choose (k i)) • hasse (k + j) f := by
  ext m
  rw [coeff_hasse, coeff_hasse, coeff_smul, coeff_hasse, smul_smul, smul_smul,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    show m + j + k = m + (k + j) by rw [add_assoc, add_comm j]]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Finsupp.add_apply]
  exact choose_mul_choose_eq _ _ _

theorem add_mem_support_of_mem_support_hasse {k m : σ →₀ ℕ} {f : MvPolynomial σ R}
    (h : m ∈ (hasse k f).support) : m + k ∈ f.support := by
  rw [mem_support_iff, coeff_hasse] at h
  rw [mem_support_iff]
  intro h0
  rw [h0, smul_zero] at h
  exact h rfl

theorem degreeOf_hasse_le (k : σ →₀ ℕ) (f : MvPolynomial σ R) (i : σ) :
    degreeOf i (hasse k f) ≤ degreeOf i f - k i := by
  rw [degreeOf_le_iff]
  intro m hm
  have := monomial_le_degreeOf i (add_mem_support_of_mem_support_hasse hm)
  rw [Finsupp.add_apply] at this
  omega

theorem le_degreeOf_of_hasse_ne_zero {k : σ →₀ ℕ} {f : MvPolynomial σ R} (h : hasse k f ≠ 0)
    (i : σ) : k i ≤ degreeOf i f := by
  obtain ⟨m, hm⟩ := ne_zero_iff.mp h
  have := monomial_le_degreeOf i (add_mem_support_of_mem_support_hasse (mem_support_iff.mpr hm))
  rw [Finsupp.add_apply] at this
  omega

/-- The case `k = e_i` of (18.5): `(f^{[e_i]})^{[k - e_i]} = k_i f^{[k]}`. -/
theorem hasse_sub_single_hasse_single (k : σ →₀ ℕ) {i : σ} (hi : k i ≠ 0)
    (f : MvPolynomial σ R) :
    hasse (k - Finsupp.single i 1) (hasse (Finsupp.single i 1) f) = k i • hasse k f := by
  have hle : Finsupp.single i 1 ≤ k := Finsupp.single_le_iff.mpr (by omega)
  rw [hasse_hasse, add_tsub_cancel_of_le hle]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp only [Finsupp.single_eq_same, Finsupp.tsub_apply, Nat.choose_one_right]
    omega
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

/-- The finite set of the exponents `k` with `k_i ≤ N` for each `i`. -/
noncomputable def box (σ : Type*) [Fintype σ] [DecidableEq σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  (Fintype.piFinset fun _ : σ => Finset.range (N + 1)).map
    Finsupp.equivFunOnFinite.symm.toEmbedding

theorem mem_box {N : ℕ} {k : σ →₀ ℕ} : k ∈ box σ N ↔ ∀ i, k i ≤ N := by
  simp [box, Finset.mem_map_equiv, Fintype.mem_piFinset]

theorem prod_add_pow_eq_sum {S : Type*} [CommSemiring S] (a s : σ → S) (e : σ →₀ ℕ) {N : ℕ}
    (he : ∀ i, e i ≤ N) :
    ∏ i, (a i + s i) ^ e i = ∑ k ∈ box σ N,
      ((∏ i, (e i).choose (k i) : ℕ) : S) * (∏ i, a i ^ (e i - k i)) * ∏ i, s i ^ k i := by
  have h1 : ∀ i, (a i + s i) ^ e i =
      ∑ j ∈ Finset.range (N + 1), ((e i).choose j : S) * a i ^ (e i - j) * s i ^ j := by
    intro i
    rw [add_comm, add_pow]
    rw [Finset.sum_subset (Finset.range_mono (by have := he i; omega : e i + 1 ≤ N + 1))]
    · exact Finset.sum_congr rfl fun j _ => by ring
    · intro j _ hj
      simp only [Finset.mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum, box, Finset.sum_map]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.coe_toEmbedding, Finsupp.coe_equivFunOnFinite_symm, Nat.cast_prod]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- Taylor's formula `f(a + s) = Σ_k f^{[k]}(a) s^k`. -/
theorem eval₂_add_eq_sum {S : Type*} [CommSemiring S] (φ : R →+* S) (a s : σ → S)
    (f : MvPolynomial σ R) {N : ℕ} (hN : ∀ i, degreeOf i f ≤ N) :
    eval₂ φ (a + s) f = ∑ k ∈ box σ N, eval₂ φ a (hasse k f) * ∏ i, s i ^ k i := by
  rw [eval₂_eq']
  simp_rw [hasse, eval₂_sum, eval₂_monomial, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [Pi.add_apply]
  rw [prod_add_pow_eq_sum a s e (fun i => (monomial_le_degreeOf i he).trans (hN i)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [Finsupp.tsub_apply, nsmul_eq_mul, map_mul, map_natCast]
  ring

end Hasse

/-! ### Values -/

section Values

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

theorem le_map_prod_pow_finset {σ : Type*} (s : Finset σ) {Δ : σ → K} {γ : ℝ}
    (h : ∀ i, (γ : WithTop ℝ) ≤ v (Δ i)) (k : σ →₀ ℕ) :
    ((((∑ i ∈ s, k i : ℕ) : ℝ) * γ : ℝ) : WithTop ℝ) ≤ v (∏ i ∈ s, Δ i ^ k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddValuation.map_mul, AddValuation.map_pow,
      Nat.cast_add, add_mul, WithTop.coe_add]
    refine add_le_add ?_ ih
    rw [← nsmul_eq_mul, WithTop.coe_nsmul]
    exact nsmul_le_nsmul_right (h a) _

theorem le_map_prod_pow {σ : Type*} [Fintype σ] {Δ : σ → K} {γ : ℝ}
    (h : ∀ i, (γ : WithTop ℝ) ≤ v (Δ i)) (k : σ →₀ ℕ) :
    ((((∑ i, k i : ℕ) : ℝ) * γ : ℝ) : WithTop ℝ) ≤ v (∏ i, Δ i ^ k i) :=
  le_map_prod_pow_finset v _ h k

theorem le_map_mul_prod_pow {σ : Type*} [Fintype σ] {Δ : σ → K} {γ : ℝ}
    (h : ∀ i, (γ : WithTop ℝ) ≤ v (Δ i)) (x : K) (k : σ →₀ ℕ) :
    v x + ((((∑ i, k i : ℕ) : ℝ) * γ : ℝ) : WithTop ℝ) ≤ v (x * ∏ i, Δ i ^ k i) := by
  rw [AddValuation.map_mul]
  exact add_le_add_right (le_map_prod_pow v h k) _

theorem map_eq_of_lt_map_sub {x y : K} (h : v x < v (x - y)) : v y = v x := by
  have : y = x + -(x - y) := by ring
  rw [this, AddValuation.map_add_eq_of_lt_left]
  rwa [AddValuation.map_neg]

theorem eventually_lt_add {γ : ℕ → ℝ} {Θ : ℝ} (hγ : Tendsto γ atTop (𝓝 Θ)) {a b : WithTop ℝ}
    (n : ℕ) (h : a < b + (((n : ℝ) * Θ : ℝ) : WithTop ℝ)) :
    ∀ᶠ m in atTop, a < b + (((n : ℝ) * γ m : ℝ) : WithTop ℝ) := by
  induction b with
  | top =>
    simp only [WithTop.top_add] at h ⊢
    exact Eventually.of_forall fun _ => h
  | coe b =>
    induction a with
    | top => simp at h
    | coe a =>
      have h' : a < b + n * Θ := by exact_mod_cast h
      have ht : Tendsto (fun m => b + n * γ m) atTop (𝓝 (b + n * Θ)) :=
        (hγ.const_mul _).const_add _
      filter_upwards [ht.eventually_const_lt h'] with m hm
      exact_mod_cast hm

/-- In characteristic `p`, a valuation with values in `ℝ ∪ {∞}` vanishes on the integers that
are prime to `p`. -/
theorem _root_.AddValuation.map_natCast_eq_zero {p : ℕ} [CharP K p] (hp : p.Prime) {n : ℕ}
    (hn : ¬ p ∣ n) : v (n : K) = 0 := by
  have := Fact.mk hp
  have hz : (n : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have h1 : (n : K) ^ (p - 1) = 1 := by
    have := ZMod.pow_card_sub_one_eq_one hz
    have h2 := congrArg (ZMod.castHom (dvd_refl p) K) this
    simpa using h2
  have hn0 : (n : K) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by have := hp.two_le; omega)] at h1
    exact zero_ne_one h1
  have hv := congrArg v h1
  rw [AddValuation.map_pow, AddValuation.map_one] at hv
  have hne : v (n : K) ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  induction h : v (n : K) with
  | top => exact absurd h hne
  | coe r =>
    rw [h, ← WithTop.coe_nsmul] at hv
    have : (p - 1) • r = 0 := by exact_mod_cast hv
    rw [nsmul_eq_mul] at this
    have hp1 : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
      have := hp.two_le
      exact_mod_cast (by omega : p - 1 ≠ 0)
    exact_mod_cast (mul_eq_zero.mp this).resolve_left hp1

end Values

/-! ### Statement D -/

section StatementD

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

/-- The abstract planar tail. The tail `Φ_∞ - Φ_m` has a value at least `γ m`, `γ m → Θ`, and
the conclusion of Lemma 3.18.10 holds for the coefficients in `F`. -/
structure IsPlanarTail (v : AddValuation K (WithTop ℝ)) (F : Subring K) (Φ : ℕ → σ → F)
    (Φi : σ → K) (Θ : ℝ) (γ : ℕ → ℝ) : Prop where
  tendsto : Tendsto γ atTop (𝓝 Θ)
  le_map : ∀ m i, ((γ m : ℝ) : WithTop ℝ) ≤ v (Φi i - Φ m i)
  map_lt : ∀ m (α : σ → F) (c : F), α ≠ 0 →
    v ((c : K) + ∑ i, (α i : K) * (Φi i - Φ m i)) <
      Finset.univ.inf (fun i => v (α i : K)) + (Θ : WithTop ℝ)

variable {v : AddValuation K (WithTop ℝ)} {F : Subring K} {Φ : ℕ → σ → F} {Φi : σ → K}
  {Θ : ℝ} {γ : ℕ → ℝ}

omit [Fintype σ] [DecidableEq σ] in
theorem coe_eval (x : σ → F) (g : MvPolynomial σ F) :
    ((eval x g : F) : K) = eval₂ F.subtype (fun i => (x i : K)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The order `|k| = Σ_i k_i` of an exponent. -/
def ord (k : σ →₀ ℕ) : ℕ := ∑ i, k i

theorem ord_sub_single (k : σ →₀ ℕ) {i : σ} (hi : k i ≠ 0) :
    ord (k - Finsupp.single i 1) + 1 = ord k := by
  have hle : Finsupp.single i 1 ≤ k := Finsupp.single_le_iff.mpr (by omega)
  have : ord (k - Finsupp.single i 1) + ord (Finsupp.single i 1) = ord k := by
    rw [ord, ord, ord, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finsupp.tsub_apply]
    have := Finsupp.le_def.mp hle l
    omega
  rwa [show ord (Finsupp.single i 1 : σ →₀ ℕ) = 1 by simp [ord, Finsupp.single_apply]] at this

omit [DecidableEq σ] in
theorem exists_ne_zero_of_ne_zero {k : σ →₀ ℕ} (hk : k ≠ 0) : ∃ i, k i ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hk (Finsupp.ext hc)

/-- Statement D (Theorem 3.18.11 of the handbook, parts 1 and 2 and the inequality of part 3),
for the abstract planar tail. -/
theorem statementD (hT : IsPlanarTail v F Φ Φi Θ γ) {p : ℕ}
    (hv : ∀ n : ℕ, 0 < n → n < p → v (n : K) = 0) (f : MvPolynomial σ F) (hf : f ≠ 0)
    (hdeg : ∀ i, degreeOf i f < p) :
    eval₂ F.subtype Φi f ≠ 0 ∧
      (∀ k, k ≠ 0 → hasse k f ≠ 0 →
        v (eval₂ F.subtype Φi f) <
          v (eval₂ F.subtype Φi (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ)) ∧
      ∀ᶠ m in atTop,
        v (eval₂ F.subtype Φi f) < v (eval₂ F.subtype Φi f - (eval (Φ m) f : K)) := by
  set E : MvPolynomial σ F → K := fun g => eval₂ F.subtype Φi g with hE
  set e : σ → σ →₀ ℕ := fun i => Finsupp.single i 1 with he
  suffices H : ∀ n (f : MvPolynomial σ F), ∑ i, degreeOf i f = n → f ≠ 0 →
      (∀ i, degreeOf i f < p) →
      E f ≠ 0 ∧ (∀ k, k ≠ 0 → hasse k f ≠ 0 →
        v (E f) < v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ)) ∧
      ∀ᶠ m in atTop, v (E f) < v (E f - (eval (Φ m) f : K)) from H _ f rfl hf hdeg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn hf hdeg
  -- the derivatives have a smaller degree
  have hlt : ∀ k, k ≠ 0 → hasse k f ≠ 0 → ∑ i, degreeOf i (hasse k f) < n := by
    intro k hk hk0
    obtain ⟨i0, hi0⟩ := exists_ne_zero_of_ne_zero hk
    rw [← hn]
    refine Finset.sum_lt_sum (fun i _ => (degreeOf_hasse_le k f i).trans (Nat.sub_le _ _))
      ⟨i0, Finset.mem_univ _, ?_⟩
    have h1 := degreeOf_hasse_le k f i0
    have h2 := le_degreeOf_of_hasse_ne_zero hk0 i0
    omega
  have IH : ∀ k, k ≠ 0 → hasse k f ≠ 0 →
      E (hasse k f) ≠ 0 ∧ (∀ j, j ≠ 0 → hasse j (hasse k f) ≠ 0 →
        v (E (hasse k f)) <
          v (E (hasse j (hasse k f))) + (((ord j : ℝ) * Θ : ℝ) : WithTop ℝ)) ∧
      ∀ᶠ m in atTop, v (E (hasse k f)) < v (E (hasse k f) - (eval (Φ m) (hasse k f) : K)) :=
    fun k hk hk0 => ih _ (hlt k hk hk0) _ rfl hk0
      (fun i => (degreeOf_hasse_le k f i).trans_lt ((Nat.sub_le _ _).trans_lt (hdeg i)))
  -- the factor `k_i` has value `0`
  have hki : ∀ k, hasse k f ≠ 0 → ∀ i, k i ≠ 0 → v (k i : K) = 0 := fun k hk0 i hi =>
    hv _ (Nat.pos_of_ne_zero hi) ((le_degreeOf_of_hasse_ne_zero hk0 i).trans_lt (hdeg i))
  have hE_nsmul : ∀ (c : ℕ) g, E (c • g) = (c : K) * E g := by
    intro c g
    simp [hE, nsmul_eq_mul]
  have hchain_eval : ∀ k, hasse k f ≠ 0 → ∀ i, k i ≠ 0 →
      E (hasse (k - e i) (hasse (e i) f)) = (k i : K) * E (hasse k f) := by
    intro k _ i hi
    rw [he, hasse_sub_single_hasse_single k hi, hE_nsmul]
  have hval_k : ∀ k, hasse k f ≠ 0 → ∀ i, k i ≠ 0 →
      v (E (hasse (k - e i) (hasse (e i) f))) = v (E (hasse k f)) := by
    intro k hk0 i hi
    rw [hchain_eval k hk0 i hi, AddValuation.map_mul, hki k hk0 i hi, zero_add]
  have hne_top : ∀ x : K, x ≠ 0 → v x ≠ ⊤ := fun x hx => by rwa [Ne, AddValuation.top_iff]
  -- if `f^{[k]} ≠ 0` with `k_i ≠ 0`, then `f^{[e_i]} ≠ 0`
  have hsingle : ∀ k, k ≠ 0 → hasse k f ≠ 0 → ∀ i, k i ≠ 0 →
      hasse (e i) f ≠ 0 ∧ (k ≠ e i → hasse (k - e i) (hasse (e i) f) ≠ 0) := by
    intro k hk hk0 i hi
    have hEk := (IH k hk hk0).1
    have hk_ne : (k i : K) ≠ 0 := by
      intro h0
      have := hki k hk0 i hi
      rw [h0, AddValuation.map_zero] at this
      exact WithTop.top_ne_zero this
    have hpoly : hasse (k - e i) (hasse (e i) f) ≠ 0 := by
      intro h0
      have := hchain_eval k hk0 i hi
      rw [h0] at this
      simp only [hE, eval₂_zero] at this
      exact mul_ne_zero hk_ne hEk this.symm
    refine ⟨fun h0 => hpoly (by rw [h0, hasse_zero_right]), fun _ => hpoly⟩
  by_cases hcase : ∀ i, hasse (e i) f = 0
  · -- `f` is a constant
    have hall : ∀ k, k ≠ 0 → hasse k f = 0 := by
      intro k hk
      by_contra hk0
      obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hk
      exact (hsingle k hk hk0 i hi).1 (hcase i)
    have hfC : f = C (f.coeff 0) := by
      ext d
      rw [coeff_C]
      split_ifs with hd
      · rw [hd]
      · rw [← coeff_zero_hasse, hall d (Ne.symm hd)]
        rfl
    have hc : f.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, C_0] at hfC
      exact hf hfC
    have hEf : E f = (f.coeff 0 : K) := by
      show eval₂ F.subtype Φi f = _
      conv_lhs => rw [hfC]
      rw [eval₂_C]
      rfl
    have hEf0 : E f ≠ 0 := by
      rw [hEf]
      exact_mod_cast hc
    refine ⟨hEf0, fun k hk hk0 => absurd (hall k hk) hk0, Eventually.of_forall fun m => ?_⟩
    have : ((eval (Φ m) f : F) : K) = (f.coeff 0 : K) := by
      conv_lhs => rw [hfC]
      rw [eval_C]
    rw [this, ← hEf, sub_self, AddValuation.map_zero]
    exact lt_top_iff_ne_top.mpr (hne_top _ hEf0)
  push Not at hcase
  obtain ⟨i0, hi0⟩ := hcase
  -- the value `λ₁`
  set lam : WithTop ℝ := Finset.univ.inf fun i => v (E (hasse (e i) f)) with hlam
  have hlam_le : ∀ i, lam ≤ v (E (hasse (e i) f)) := fun i => Finset.inf_le (Finset.mem_univ i)
  have he0 : ∀ i, e i ≠ 0 := fun i => by simp [he]
  have hlam_top : lam ≠ ⊤ := by
    intro h
    have := hlam_le i0
    rw [h, top_le_iff, AddValuation.top_iff] at this
    exact (IH (e i0) (he0 i0) hi0).1 this
  -- the chain
  have hchain : ∀ k, k ≠ 0 → hasse k f ≠ 0 →
      lam + (Θ : WithTop ℝ) ≤ v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) ∧
      ((∀ i, k ≠ e i) →
        lam + (Θ : WithTop ℝ) < v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ)) := by
    intro k hk hk0
    obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hk
    have hstrict : k ≠ e i →
        lam + (Θ : WithTop ℝ) < v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) := by
      intro hke
      obtain ⟨hi1, hi2⟩ := hsingle k hk hk0 i hi
      have hj : k - e i ≠ 0 := by
        intro h0
        apply hke
        have hle : e i ≤ k := Finsupp.single_le_iff.mpr (by omega)
        rw [← tsub_add_cancel_of_le hle, h0, zero_add]
      have h3 := (IH (e i) (he0 i) hi1).2.1 (k - e i) hj (hi2 hke)
      rw [hval_k k hk0 i hi] at h3
      have hord := ord_sub_single k hi
      have hreal : ((ord k : ℝ) * Θ : ℝ) = ((ord (k - e i) : ℝ) * Θ : ℝ) + Θ := by
        rw [← hord]
        push_cast
        ring
      calc lam + (Θ : WithTop ℝ) ≤ v (E (hasse (e i) f)) + (Θ : WithTop ℝ) :=
            add_le_add_left (hlam_le i) _
        _ < v (E (hasse k f)) + (((ord (k - e i) : ℝ) * Θ : ℝ) : WithTop ℝ) + (Θ : WithTop ℝ) :=
            WithTop.add_lt_add_right WithTop.coe_ne_top h3
        _ = v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) := by
            rw [hreal, WithTop.coe_add, add_assoc]
    refine ⟨?_, fun hall => hstrict (hall i)⟩
    by_cases hke : k = e i
    · have hord : ord k = 1 := by
        rw [hke]
        simp [ord, he, Finsupp.single_apply]
      rw [hord, Nat.cast_one, one_mul]
      have := hlam_le i
      rw [← hke] at this
      exact add_le_add_left this _
    · exact (hstrict hke).le
  -- the set of indices
  set N := ∑ i, degreeOf i f with hN
  have hNi : ∀ i, degreeOf i f ≤ N := fun i =>
    Finset.single_le_sum (f := fun i => degreeOf i f) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hN1 : 1 ≤ N := by
    have := le_degreeOf_of_hasse_ne_zero hi0 i0
    simp only [he, Finsupp.single_eq_same] at this
    exact this.trans (hNi i0)
  set S := box σ N with hS
  have hTaylor : ∀ m, E f = ∑ k ∈ S, ((eval (Φ m) (hasse k f) : F) : K) *
      ∏ i, (Φi i - Φ m i) ^ k i := by
    intro m
    have : Φi = (fun i => (Φ m i : K)) + fun i => Φi i - Φ m i := by
      funext i
      simp
    rw [hE]
    dsimp only
    conv_lhs => rw [this]
    rw [eval₂_add_eq_sum _ _ _ _ hNi]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_eval]
  -- eventual values of the derivatives
  have hEv : ∀ᶠ m in atTop, ∀ k ∈ S, k ≠ 0 →
      v ((eval (Φ m) (hasse k f) : F) : K) = v (E (hasse k f)) := by
    rw [Filter.eventually_all_finset]
    intro k _
    by_cases hk : k = 0
    · exact Eventually.of_forall fun m h => absurd hk h
    by_cases hk0 : hasse k f = 0
    · exact Eventually.of_forall fun m _ => by simp [hk0, hE]
    filter_upwards [(IH k hk hk0).2.2] with m hm _
    exact map_eq_of_lt_map_sub v hm
  -- the strict chain, for `m` large
  have hTv : ∀ᶠ m in atTop, ∀ k ∈ S, k ≠ 0 → hasse k f ≠ 0 → (∀ i, k ≠ e i) →
      lam + (Θ : WithTop ℝ) < v (E (hasse k f)) + (((ord k : ℝ) * γ m : ℝ) : WithTop ℝ) := by
    rw [Filter.eventually_all_finset]
    intro k _
    by_cases h : k ≠ 0 ∧ hasse k f ≠ 0 ∧ ∀ i, k ≠ e i
    · filter_upwards [eventually_lt_add hT.tendsto (ord k) ((hchain k h.1 h.2.1).2 h.2.2)]
        with m hm _ _ _
      exact hm
    · exact Eventually.of_forall fun m h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h
  have hS1 : ∀ i, e i ∈ S := fun i => mem_box.mpr fun l => by
    simp only [he, Finsupp.single_apply]
    split_ifs <;> omega
  have hS0 : (0 : σ →₀ ℕ) ∈ S := mem_box.mpr fun _ => Nat.zero_le _
  -- parts 1 and 2
  obtain ⟨m, hm1, hm2⟩ := (hEv.and hTv).exists
  set S1 : Finset (σ →₀ ℕ) := insert 0 (Finset.univ.image e) with hS1def
  have hS1S : S1 ⊆ S := by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_image] at hk
    rcases hk with rfl | ⟨i, _, rfl⟩
    · exact hS0
    · exact hS1 i
  have h0img : (0 : σ →₀ ℕ) ∉ Finset.univ.image e := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro i _ h
    exact he0 i h
  have he_inj : Function.Injective e := fun i j h =>
    Finsupp.single_left_injective one_ne_zero h
  have hS1sum : ∑ k ∈ S1, ((eval (Φ m) (hasse k f) : F) : K) * ∏ i, (Φi i - Φ m i) ^ k i =
      ((eval (Φ m) f : F) : K) +
        ∑ i, ((eval (Φ m) (hasse (e i) f) : F) : K) * (Φi i - Φ m i) := by
    rw [hS1def, Finset.sum_insert h0img, Finset.sum_image (fun i _ j _ h => he_inj h)]
    congr 1
    · simp [hasse_zero]
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [Finset.prod_eq_single i]
      · simp [he]
      · intro l _ hl
        simp [he, Ne.symm hl]
      · simp
  set α : σ → F := fun i => eval (Φ m) (hasse (e i) f) with hα
  have hαv : ∀ i, v (α i : K) = v (E (hasse (e i) f)) := fun i => hm1 (e i) (hS1 i) (he0 i)
  have hα0 : α ≠ 0 := by
    intro h0
    have := hαv i0
    rw [h0, Pi.zero_apply, ZeroMemClass.coe_zero, AddValuation.map_zero] at this
    exact hne_top _ (IH (e i0) (he0 i0) hi0).1 this.symm
  have hB := hT.map_lt m α (eval (Φ m) f) hα0
  have hinf : Finset.univ.inf (fun i => v (α i : K)) = lam :=
    Finset.inf_congr rfl fun i _ => hαv i
  rw [hinf] at hB
  have hne : lam + (Θ : WithTop ℝ) ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hlam_top, WithTop.coe_ne_top⟩
  have hR : lam + (Θ : WithTop ℝ) <
      v (∑ k ∈ S \ S1, ((eval (Φ m) (hasse k f) : F) : K) * ∏ i, (Φi i - Φ m i) ^ k i) := by
    refine AddValuation.map_lt_sum v hne fun k hk => ?_
    rw [Finset.mem_sdiff] at hk
    have hk0 : k ≠ 0 := fun h => hk.2 (by rw [h]; exact Finset.mem_insert_self _ _)
    have hke : ∀ i, k ≠ e i := fun i h => hk.2 (by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    by_cases hkf : hasse k f = 0
    · simp only [hkf, map_zero, ZeroMemClass.coe_zero, zero_mul, AddValuation.map_zero]
      exact lt_top_iff_ne_top.mpr hne
    · calc lam + (Θ : WithTop ℝ)
            < v (E (hasse k f)) + (((ord k : ℝ) * γ m : ℝ) : WithTop ℝ) :=
            hm2 k hk.1 hk0 hkf hke
        _ = v ((eval (Φ m) (hasse k f) : F) : K) + (((ord k : ℝ) * γ m : ℝ) : WithTop ℝ) := by
            rw [hm1 k hk.1 hk0]
        _ ≤ _ := le_map_mul_prod_pow v (hT.le_map m) _ k
  have hEf : E f = (((eval (Φ m) f : F) : K) + ∑ i, (α i : K) * (Φi i - Φ m i)) +
      ∑ k ∈ S \ S1, ((eval (Φ m) (hasse k f) : F) : K) * ∏ i, (Φi i - Φ m i) ^ k i := by
    rw [hTaylor m, ← Finset.sum_sdiff hS1S, hS1sum, add_comm]
  have hlt1 : v (E f) < lam + (Θ : WithTop ℝ) := by
    rw [hEf, AddValuation.map_add_eq_of_lt_left _ (hB.trans hR)]
    exact hB
  have hEf0 : E f ≠ 0 := fun h => by
    rw [h, AddValuation.map_zero] at hlt1
    exact not_top_lt hlt1
  have hpart2 : ∀ k, k ≠ 0 → hasse k f ≠ 0 →
      v (E f) < v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) :=
    fun k hk hk0 => hlt1.trans_le (hchain k hk hk0).1
  refine ⟨hEf0, hpart2, ?_⟩
  -- part 3
  have hUv : ∀ᶠ m in atTop, ∀ k ∈ S, k ≠ 0 → hasse k f ≠ 0 →
      v (E f) < v (E (hasse k f)) + (((ord k : ℝ) * γ m : ℝ) : WithTop ℝ) := by
    rw [Filter.eventually_all_finset]
    intro k _
    by_cases h : k ≠ 0 ∧ hasse k f ≠ 0
    · filter_upwards [eventually_lt_add hT.tendsto (ord k) (hpart2 k h.1 h.2)] with m hm _ _
      exact hm
    · exact Eventually.of_forall fun m h1 h2 => absurd ⟨h1, h2⟩ h
  filter_upwards [hEv, hUv] with m' hm1' hm2'
  have hdiff : E f - ((eval (Φ m') f : F) : K) =
      ∑ k ∈ S.erase 0, ((eval (Φ m') (hasse k f) : F) : K) * ∏ i, (Φi i - Φ m' i) ^ k i := by
    rw [hTaylor m', ← Finset.add_sum_erase S _ hS0]
    simp [hasse_zero]
  rw [hdiff]
  refine AddValuation.map_lt_sum v (hne_top _ hEf0) fun k hk => ?_
  obtain ⟨hk0, hkS⟩ := Finset.mem_erase.mp hk
  by_cases hkf : hasse k f = 0
  · simp only [hkf, map_zero, ZeroMemClass.coe_zero, zero_mul, AddValuation.map_zero]
    exact lt_top_iff_ne_top.mpr (hne_top _ hEf0)
  · calc v (E f) < v (E (hasse k f)) + (((ord k : ℝ) * γ m' : ℝ) : WithTop ℝ) :=
          hm2' k hkS hk0 hkf
      _ = v ((eval (Φ m') (hasse k f) : F) : K) + (((ord k : ℝ) * γ m' : ℝ) : WithTop ℝ) := by
          rw [hm1' k hkS hk0]
      _ ≤ _ := le_map_mul_prod_pow v (hT.le_map m') _ k

/-- Statement D in characteristic `p`. -/
theorem statementD_of_charP {p : ℕ} [CharP K p] (hp : p.Prime) (hT : IsPlanarTail v F Φ Φi Θ γ)
    (f : MvPolynomial σ F) (hf : f ≠ 0) (hdeg : ∀ i, degreeOf i f < p) :
    eval₂ F.subtype Φi f ≠ 0 ∧
      (∀ k, k ≠ 0 → hasse k f ≠ 0 →
        v (eval₂ F.subtype Φi f) <
          v (eval₂ F.subtype Φi (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ)) ∧
      ∀ᶠ m in atTop,
        v (eval₂ F.subtype Φi f) < v (eval₂ F.subtype Φi f - (eval (Φ m) f : K)) :=
  statementD hT (fun n hn hnp => v.map_natCast_eq_zero hp
    (fun h => absurd (Nat.le_of_dvd hn h) (by omega))) f hf hdeg

end StatementD

end PlanarRuns

end Singularity
