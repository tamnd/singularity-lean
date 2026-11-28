/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Factorization.Basic
import Singularity.Invariant.PlanarRunsConjectureP

/-!
# Theorem 3.18.26 in the abstract model

This file proves Theorem 3.18.26 of Volume 7 of the handbook (Statement D for each degree) in
the abstract model of `PlanarRuns.lean`. The hypothesis on the tail is stronger than
`IsPlanarTail`: it is the conclusion of Steps 3 and 4 of the handbook proof (the germ counting
with Lemmas 3.18.24 and 3.18.25) for the `p`-power monomials of the tail.

## The model

`IsFrobTail v F Φ Φi p Θ γ` says that the tail `Δ_m = Φ_∞ - Φ_m` has a value at least `γ m`, that
`γ m → Θ`, and that for each `n`, for the coefficients `α_{i, e}` (`e < n`) in `F`, not all zero,
and `c` in `F`,
`v(c + Σ_{i, e} α_{i, e} Δ_{m, i}^{p^e}) < min_{i, e} (v(α_{i, e}) + p^e Θ)`.
For `n = 1` this is the conclusion of Lemma 3.18.10 (`IsPlanarTail`).

## Theorem 3.18.26

In characteristic `p`, `statementD_frob` proves `StatementDHolds` (parts 1 and 2 of Theorem
3.18.26 and the inequality of Step 1) for each nonzero `f`, with no condition on the degree. The
proof is the induction of the handbook on the degree.

* Step 1 (Lucas). For `k ≠ 0`, take `i` with `k_i ≠ 0` and `p^e` the exact power of `p` in `k_i`.
  Then `C(k_i, p^e)` is prime to `p` (`not_dvd_choose_pow_mul`), and
  `(f^{[p^e e_i]})^{[k - p^e e_i]} = C(k_i, p^e) f^{[k]}` (`hasse_sub_hasse_single`). Part 2 for
  `h = f^{[p^e e_i]}` gives `v(f^{[p^e e_i]}(Φ_∞)) + p^e Θ < v(f^{[k]}(Φ_∞)) + |k| Θ` for
  `k ≠ p^e e_i`.
* Steps 2 and 3. The derivatives have stable values, and Taylor's formula splits `f(Φ_∞)` into
  `f(Φ_m)`, the `p`-power terms and a rest with a value more than `Λ`.
* Step 4. `IsFrobTail` gives `v(f(Φ_∞)) < Λ`.
* Step 5. Part 2 follows as in `statementD`.

## References

* Volume 7, Section 3.18 of the handbook: Lemmas 3.18.23 to 3.18.25 and Theorem 3.18.26.
-/

open MvPolynomial Filter Topology

namespace Singularity

namespace PlanarRuns

/-! ### Lucas -/

/-- By Lucas's theorem, `C(p^e u, p^e) ≡ C(u, 1) = u` modulo `p`. -/
theorem not_dvd_choose_pow_mul {p : ℕ} [hp : Fact p.Prime] (e : ℕ) {u : ℕ} (hu : ¬ p ∣ u) :
    ¬ p ∣ (p ^ e * u).choose (p ^ e) := by
  induction e with
  | zero => simpa using hu
  | succ e ih =>
    intro h
    apply ih
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p * (p ^ e * u))
      (k := p * p ^ e) (p := p)
    rw [Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hp.out.pos,
      Nat.mul_div_cancel_left _ hp.out.pos, Nat.choose_self, one_mul] at hl
    rw [show p ^ (e + 1) * u = p * (p ^ e * u) by ring, pow_succ'] at h
    exact Nat.modEq_zero_iff_dvd.mp (hl.symm.trans (Nat.modEq_zero_iff_dvd.mpr h))

/-- For `n ≠ 0`, the exact power `p^e` of `p` in `n` has `p^e ≤ n` and `C(n, p^e)` prime to
`p`. -/
theorem exists_pow_not_dvd_choose {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    ∃ e, p ^ e ≤ n ∧ ¬ p ∣ n.choose (p ^ e) := by
  have := Fact.mk hp
  refine ⟨n.factorization p, Nat.ordProj_le p hn, ?_⟩
  have h := not_dvd_choose_pow_mul (p := p) (n.factorization p) (Nat.not_dvd_ordCompl hp hn)
  rwa [Nat.ordProj_mul_ordCompl_eq_self] at h

/-! ### Hasse derivatives along `p^e e_i` -/

section Hasse

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

/-- The case `j = a e_i` of (18.5): `(f^{[a e_i]})^{[k - a e_i]} = C(k_i, a) f^{[k]}`. -/
theorem hasse_sub_hasse_single (k : σ →₀ ℕ) {i : σ} {a : ℕ} (ha : a ≤ k i)
    (f : MvPolynomial σ R) :
    hasse (k - Finsupp.single i a) (hasse (Finsupp.single i a) f) = (k i).choose a • hasse k f := by
  have hle : Finsupp.single i a ≤ k := Finsupp.single_le_iff.mpr ha
  rw [hasse_hasse, add_tsub_cancel_of_le hle]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp only [Finsupp.single_eq_same, Finsupp.tsub_apply]
    rw [Nat.add_sub_cancel' ha]
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

theorem ord_single (i : σ) (a : ℕ) : ord (Finsupp.single i a) = a := by
  simp [ord, Finsupp.single_apply]

theorem ord_sub_single' (k : σ →₀ ℕ) {i : σ} {a : ℕ} (ha : a ≤ k i) :
    ord (k - Finsupp.single i a) + a = ord k := by
  have hle : Finsupp.single i a ≤ k := Finsupp.single_le_iff.mpr ha
  have : ord (k - Finsupp.single i a) + ord (Finsupp.single i a) = ord k := by
    rw [ord, ord, ord, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finsupp.tsub_apply]
    have := Finsupp.le_def.mp hle l
    omega
  rwa [ord_single] at this

omit [DecidableEq σ] in
theorem prod_pow_single {M : Type*} [CommMonoid M] (Δ : σ → M) (i : σ) (a : ℕ) :
    ∏ l, Δ l ^ (Finsupp.single i a) l = Δ i ^ a := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

end Hasse

/-! ### Theorem 3.18.26 -/

section StatementD

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

/-- The abstract tail for the `p`-power monomials. The tail `Φ_∞ - Φ_m` has a value at least
`γ m`, `γ m → Θ`, and the conclusion of Steps 3 and 4 of the proof of Theorem 3.18.26 holds for
the coefficients in `F`. -/
structure IsFrobTail (v : AddValuation K (WithTop ℝ)) (F : Subring K) (Φ : ℕ → σ → F)
    (Φi : σ → K) (p : ℕ) (Θ : ℝ) (γ : ℕ → ℝ) : Prop where
  tendsto : Tendsto γ atTop (𝓝 Θ)
  le_map : ∀ m i, ((γ m : ℝ) : WithTop ℝ) ≤ v (Φi i - Φ m i)
  map_lt : ∀ m n (α : σ × ℕ → F) (c : F),
    (∃ x ∈ (Finset.univ : Finset σ) ×ˢ Finset.range n, α x ≠ 0) →
    v ((c : K) + ∑ x ∈ (Finset.univ : Finset σ) ×ˢ Finset.range n,
        (α x : K) * (Φi x.1 - Φ m x.1) ^ (p ^ x.2)) <
      ((Finset.univ : Finset σ) ×ˢ Finset.range n).inf
        (fun x => v (α x : K) + ((((p ^ x.2 : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ))

variable {v : AddValuation K (WithTop ℝ)} {F : Subring K} {Φ : ℕ → σ → F} {Φi : σ → K}
  {Θ : ℝ} {γ : ℕ → ℝ}

/-- Theorem 3.18.26 of the handbook (parts 1 and 2 and the inequality of Step 1) for the
abstract tail `IsFrobTail`, in characteristic `p`, for each nonzero polynomial. -/
theorem statementD_frob {p : ℕ} [CharP K p] (hp : p.Prime) (hT : IsFrobTail v F Φ Φi p Θ γ)
    (f : MvPolynomial σ F) (hf : f ≠ 0) : StatementDHolds v F Φ Φi Θ f := by
  set E : MvPolynomial σ F → K := fun g => eval₂ F.subtype Φi g with hE
  set s : σ × ℕ → σ →₀ ℕ := fun x => Finsupp.single x.1 (p ^ x.2) with hs
  suffices H : ∀ n (f : MvPolynomial σ F), ∑ i, degreeOf i f = n → f ≠ 0 →
      E f ≠ 0 ∧ (∀ k, k ≠ 0 → hasse k f ≠ 0 →
        v (E f) < v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ)) ∧
      ∀ᶠ m in atTop, v (E f) < v (E f - (eval (Φ m) f : K)) from H _ f rfl hf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn hf
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
  have hE_nsmul : ∀ (c : ℕ) g, E (c • g) = (c : K) * E g := by
    intro c g
    simp [hE, nsmul_eq_mul]
  have hne_top : ∀ x : K, x ≠ 0 → v x ≠ ⊤ := fun x hx => by rwa [Ne, AddValuation.top_iff]
  have hs0 : ∀ x, s x ≠ 0 := fun x => by
    simp only [hs, ne_eq, Finsupp.single_eq_zero]
    exact pow_ne_zero _ hp.ne_zero
  -- the set of indices
  set N := ∑ i, degreeOf i f with hN
  have hNi : ∀ i, degreeOf i f ≤ N := fun i =>
    Finset.single_le_sum (f := fun i => degreeOf i f) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  set P : Finset (σ × ℕ) := (Finset.univ : Finset σ) ×ˢ Finset.range (N + 1) with hP
  -- Step 1
  have hstep : ∀ k, k ≠ 0 → hasse k f ≠ 0 → ∃ x ∈ P, hasse (s x) f ≠ 0 ∧
      v (E (hasse (s x) f)) + ((((p ^ x.2 : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) ≤
        v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) ∧
      (k ≠ s x → v (E (hasse (s x) f)) + ((((p ^ x.2 : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) <
        v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ)) := by
    intro k hk hk0
    obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hk
    obtain ⟨a, ha, hnd⟩ := exists_pow_not_dvd_choose hp hi
    have hmem : (i, a) ∈ P := by
      rw [hP, Finset.mem_product, Finset.mem_range]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 : a < p ^ a := Nat.lt_pow_self hp.one_lt
      have h2 := le_degreeOf_of_hasse_ne_zero hk0 i
      have h3 := hNi i
      omega
    have hEk := (IH k hk hk0).1
    have hc : v ((k i).choose (p ^ a) : K) = 0 := v.map_natCast_eq_zero hp hnd
    have hc0 : ((k i).choose (p ^ a) : K) ≠ 0 := by
      intro h0
      rw [h0, AddValuation.map_zero] at hc
      exact WithTop.top_ne_zero hc
    have heval : E (hasse (k - s (i, a)) (hasse (s (i, a)) f)) =
        ((k i).choose (p ^ a) : K) * E (hasse k f) := by
      rw [hs]
      dsimp only
      rw [hasse_sub_hasse_single k ha, hE_nsmul]
    have hpoly : hasse (k - s (i, a)) (hasse (s (i, a)) f) ≠ 0 := by
      intro h0
      rw [h0] at heval
      simp only [hE, eval₂_zero] at heval
      exact mul_ne_zero hc0 hEk heval.symm
    have hsx : hasse (s (i, a)) f ≠ 0 := fun h0 => hpoly (by rw [h0, hasse_zero_right])
    have hval : v (E (hasse (k - s (i, a)) (hasse (s (i, a)) f))) = v (E (hasse k f)) := by
      rw [heval, AddValuation.map_mul, hc, zero_add]
    have hle : s (i, a) ≤ k := Finsupp.single_le_iff.mpr ha
    have hord := ord_sub_single' k ha
    have hstrict : k ≠ s (i, a) →
        v (E (hasse (s (i, a)) f)) + ((((p ^ a : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) <
          v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) := by
      intro hke
      have hj : k - s (i, a) ≠ 0 := by
        intro h0
        apply hke
        rw [← tsub_add_cancel_of_le hle, h0, zero_add]
      have h3 := (IH (s (i, a)) (hs0 _) hsx).2.1 (k - s (i, a)) hj hpoly
      rw [hval] at h3
      have hreal : ((ord k : ℝ) * Θ : ℝ) =
          ((ord (k - Finsupp.single i (p ^ a)) : ℝ) * Θ : ℝ) + (((p ^ a : ℕ) : ℝ) * Θ : ℝ) := by
        rw [← hord]
        push_cast
        ring
      calc v (E (hasse (s (i, a)) f)) + ((((p ^ a : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ)
          < v (E (hasse k f)) + (((ord (k - s (i, a)) : ℝ) * Θ : ℝ) : WithTop ℝ) +
              ((((p ^ a : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) :=
            WithTop.add_lt_add_right WithTop.coe_ne_top h3
        _ = v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) := by
            rw [hreal, WithTop.coe_add, add_assoc]
    refine ⟨(i, a), hmem, hsx, ?_, hstrict⟩
    by_cases hke : k = s (i, a)
    · have hok : ord k = p ^ a := by rw [hke, hs]; exact ord_single _ _
      rw [hok, hke]
    · exact (hstrict hke).le
  by_cases hcase : ∀ x ∈ P, hasse (s x) f = 0
  · -- `f` is a constant
    have hall : ∀ k, k ≠ 0 → hasse k f = 0 := by
      intro k hk
      by_contra hk0
      obtain ⟨x, hx, hx0, -⟩ := hstep k hk hk0
      exact hx0 (hcase x hx)
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
  obtain ⟨x0, hx0P, hx0⟩ := hcase
  -- the value `Λ`
  set lam : WithTop ℝ :=
    P.inf fun x => v (E (hasse (s x) f)) + ((((p ^ x.2 : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) with hlam
  have hlam_le : ∀ x ∈ P,
      lam ≤ v (E (hasse (s x) f)) + ((((p ^ x.2 : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) :=
    fun x hx => Finset.inf_le hx
  have hlam_top : lam ≠ ⊤ := by
    intro h
    have := hlam_le x0 hx0P
    rw [h, top_le_iff, WithTop.add_eq_top] at this
    rcases this with h1 | h1
    · exact hne_top _ (IH (s x0) (hs0 x0) hx0).1 h1
    · exact WithTop.coe_ne_top h1
  -- the chain
  have hchain : ∀ k, k ≠ 0 → hasse k f ≠ 0 →
      lam ≤ v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ) ∧
      ((∀ x ∈ P, k ≠ s x) → lam < v (E (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ)) := by
    intro k hk hk0
    obtain ⟨x, hx, -, h1, h2⟩ := hstep k hk hk0
    exact ⟨(hlam_le x hx).trans h1, fun hall => (hlam_le x hx).trans_lt (h2 (hall x hx))⟩
  have hNB : N ≤ p ^ N := (Nat.lt_pow_self hp.one_lt).le
  set S := box σ (p ^ N) with hS
  have hTaylor : ∀ m, E f = ∑ k ∈ S, ((eval (Φ m) (hasse k f) : F) : K) *
      ∏ i, (Φi i - Φ m i) ^ k i := by
    intro m
    have : Φi = (fun i => (Φ m i : K)) + fun i => Φi i - Φ m i := by
      funext i
      simp
    rw [hE]
    dsimp only
    conv_lhs => rw [this]
    rw [eval₂_add_eq_sum _ _ _ _ fun i => (hNi i).trans hNB]
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
  have hTv : ∀ᶠ m in atTop, ∀ k ∈ S, k ≠ 0 → hasse k f ≠ 0 → (∀ x ∈ P, k ≠ s x) →
      lam < v (E (hasse k f)) + (((ord k : ℝ) * γ m : ℝ) : WithTop ℝ) := by
    rw [Filter.eventually_all_finset]
    intro k _
    by_cases h : k ≠ 0 ∧ hasse k f ≠ 0 ∧ ∀ x ∈ P, k ≠ s x
    · filter_upwards [eventually_lt_add hT.tendsto (ord k) ((hchain k h.1 h.2.1).2 h.2.2)]
        with m hm _ _ _
      exact hm
    · exact Eventually.of_forall fun m h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h
  have hSs : ∀ x ∈ P, s x ∈ S := fun x hx => mem_box.mpr fun l => by
    have hx2 : x.2 ≤ N := by
      have := (Finset.mem_product.mp hx).2
      rw [Finset.mem_range] at this
      omega
    simp only [hs, Finsupp.single_apply]
    split_ifs
    · exact Nat.pow_le_pow_right hp.pos hx2
    · exact Nat.zero_le _
  have hS0 : (0 : σ →₀ ℕ) ∈ S := mem_box.mpr fun _ => Nat.zero_le _
  -- parts 1 and 2
  obtain ⟨m, hm1, hm2⟩ := (hEv.and hTv).exists
  set S1 : Finset (σ →₀ ℕ) := insert 0 (P.image s) with hS1def
  have hS1S : S1 ⊆ S := by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_image] at hk
    rcases hk with rfl | ⟨x, hx, rfl⟩
    · exact hS0
    · exact hSs x hx
  have h0img : (0 : σ →₀ ℕ) ∉ P.image s := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro x _ h
    exact hs0 x h
  have hs_inj : Function.Injective s := by
    intro x y h
    simp only [hs, Finsupp.single_eq_single_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Prod.ext h1 (Nat.pow_right_injective hp.two_le h2)
    · exact absurd h1 (pow_ne_zero _ hp.ne_zero)
  set α : σ × ℕ → F := fun x => eval (Φ m) (hasse (s x) f) with hα
  have hS1sum : ∑ k ∈ S1, ((eval (Φ m) (hasse k f) : F) : K) * ∏ i, (Φi i - Φ m i) ^ k i =
      ((eval (Φ m) f : F) : K) + ∑ x ∈ P, (α x : K) * (Φi x.1 - Φ m x.1) ^ (p ^ x.2) := by
    rw [hS1def, Finset.sum_insert h0img, Finset.sum_image (fun x _ y _ h => hs_inj h)]
    congr 1
    · simp [hasse_zero]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [hα, hs]
      dsimp only
      rw [prod_pow_single]
  have hαv : ∀ x ∈ P, v (α x : K) = v (E (hasse (s x) f)) := fun x hx =>
    hm1 (s x) (hSs x hx) (hs0 x)
  have hex : ∃ x ∈ P, α x ≠ 0 := by
    refine ⟨x0, hx0P, fun h0 => ?_⟩
    have := hαv x0 hx0P
    rw [h0, ZeroMemClass.coe_zero, AddValuation.map_zero] at this
    exact hne_top _ (IH (s x0) (hs0 x0) hx0).1 this.symm
  have hB : v (((eval (Φ m) f : F) : K) + ∑ x ∈ P, (α x : K) * (Φi x.1 - Φ m x.1) ^ (p ^ x.2)) <
      P.inf (fun x => v (α x : K) + ((((p ^ x.2 : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ)) :=
    hT.map_lt m (N + 1) α (eval (Φ m) f) hex
  have hinf : P.inf (fun x => v (α x : K) + ((((p ^ x.2 : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ)) =
      lam :=
    Finset.inf_congr rfl fun x hx => by rw [hαv x hx]
  rw [hinf] at hB
  have hR : lam <
      v (∑ k ∈ S \ S1, ((eval (Φ m) (hasse k f) : F) : K) * ∏ i, (Φi i - Φ m i) ^ k i) := by
    refine AddValuation.map_lt_sum v hlam_top fun k hk => ?_
    rw [Finset.mem_sdiff] at hk
    have hk0 : k ≠ 0 := fun h => hk.2 (by rw [h]; exact Finset.mem_insert_self _ _)
    have hks : ∀ x ∈ P, k ≠ s x := fun x hx h => hk.2 (by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))
    by_cases hkf : hasse k f = 0
    · simp only [hkf, map_zero, ZeroMemClass.coe_zero, zero_mul, AddValuation.map_zero]
      exact lt_top_iff_ne_top.mpr hlam_top
    · calc lam
            < v (E (hasse k f)) + (((ord k : ℝ) * γ m : ℝ) : WithTop ℝ) :=
            hm2 k hk.1 hk0 hkf hks
        _ = v ((eval (Φ m) (hasse k f) : F) : K) + (((ord k : ℝ) * γ m : ℝ) : WithTop ℝ) := by
            rw [hm1 k hk.1 hk0]
        _ ≤ _ := le_map_mul_prod_pow v (hT.le_map m) _ k
  have hEf : E f = (((eval (Φ m) f : F) : K) +
        ∑ x ∈ P, (α x : K) * (Φi x.1 - Φ m x.1) ^ (p ^ x.2)) +
      ∑ k ∈ S \ S1, ((eval (Φ m) (hasse k f) : F) : K) * ∏ i, (Φi i - Φ m i) ^ k i := by
    rw [hTaylor m, ← Finset.sum_sdiff hS1S, hS1sum, add_comm]
  have hlt1 : v (E f) < lam := by
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

end StatementD

end PlanarRuns

end Singularity
