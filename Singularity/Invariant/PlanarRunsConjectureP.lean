/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.PlanarRuns

/-!
# Conjecture P from the restart inequalities

This file proves Steps 2 to 5 of the proof of Theorem 3.19.6 of Volume 7 of the handbook
(Conjecture P, Theorem 3.1 of research note 74). The inputs of these steps, which are statements
on the run from each point `P_m`, are hypotheses.

## The model

We use the model of `Singularity.Invariant.PlanarRuns`: a valuation `v` on a field `K` of
characteristic `p`, a subring `F`, points `Φ m : σ → F` and a limit `Φi : σ → K`. The polynomial
`g` has coefficients in `F`. Write `E f = f(Φ_∞)`. Besides these there are:

* `vM m : ℝ`, the value `v(M_m)`, with `vM m → Θ`, where `Θ = 1 + θ`. So `δ_m = Θ - vM m`.
* `Mm m : K`, the monomial `M_m`, with `v(M_m) = vM m` and `M_m ≠ 0`.
* `H1 m i : K`, the value `g^{(m)}_{X_i}(Φ^{(m)}_∞)` of a first derivative of the function of
  `P_m` at the limit of the run from `P_m`.
* `μ m : WithTop ℝ`, the least value of the pair `H^{(m)}_{e, 1}, H^{(m)}_{e, 2}` of order `p^e`,
  for the order `e = e(m)` where `Λ^{(m)}_+` is attained.

## The hypotheses

* `hH1`, Lemma 3.19.2, part 1: `H1 m i = M_m^{1 - p} g_{X_i}(Φ_∞)`. In the polynomial model this
  is `eval_hasse_single_restart` of `Singularity.Invariant.PlanarRunsRestart`.
* `hD`, Theorem 3.18.26 (Statement D in each degree) for each nonzero Hasse derivative of `g`, in
  the form of the conclusion of `statementD` (`StatementDHolds`). In Lean, `statementD` proves it
  for the degrees less than `p`, given the conclusions of Lemmas 3.18.8 and 3.18.10
  (`IsPlanarTail`, see `statementDHolds_of_degreeOf_lt`). Theorem 3.18.26 for degrees at least
  `p` is not proved in Lean.
* `hrun`, for each large `m`, with `e = e(m) ≥ 1` and an index `k = k(m)`:
  1. Theorem 3.18.32, part 1, for the run from `P_m` (by Lemma 3.19.1):
     `Λ^{(m)}_0 ≥ Λ^{(m)}_e`, that is, `μ_m + p^e δ_m ≤ v(H1 m i) + δ_m` for each `i`.
  2. Corollary 3.18.33 for the run from `P_m`, with part 4 of Lemma 3.19.2: `k ∈ S^e_1 ∪ S^e_2`,
     that is, `g^{[k]} ≠ 0`, the `k_i` are not all divisible by `p`, and `C(k_{i'}, p^e)` is
     prime to `p` for some `i'`; and
     `μ_m ≥ (p^e - p) v(M_m) + v(g^{[k]}(Φ_m)) + (|k| - p^e) v(M_{m+1})`.

## Main result

`conjectureP_of_restart`: under these hypotheses we get `False`. So a planar corner run, for
which the hypotheses hold, does not exist. The proof is the pigeonhole on the finite set of the
pairs `(e, k)` (Step 4), the limit `m → ∞`, and Statement D for `g_{X_i}` at the index
`k - e_i` with `p ∤ k_i` (Step 5).

## What is not proved

The hypotheses `hD` (for degrees at least `p`) and `hrun` are not proved in Lean. They need
Theorem 3.18.26 in each degree, Theorem 3.18.32, Corollary 3.18.33, Lemma 3.19.1 and the value
bound of Lemma 3.19.2, part 4, and so the corner runs, the Hahn field and Lemmas 3.18.8 and
3.18.10.

## References

* Volume 7, Section 3.19 of the handbook: Theorem 3.19.6.
* Research note 74, Theorem 3.1.
-/

open MvPolynomial Filter Topology Finsupp

namespace Singularity

namespace PlanarRuns

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

/-- The conclusion of Statement D (Theorem 3.18.26 of the handbook) for `f`, in the form of the
conclusion of `statementD`. -/
def StatementDHolds (v : AddValuation K (WithTop ℝ)) (F : Subring K) (Φ : ℕ → σ → F)
    (Φi : σ → K) (Θ : ℝ) (f : MvPolynomial σ F) : Prop :=
  eval₂ F.subtype Φi f ≠ 0 ∧
    (∀ k, k ≠ 0 → hasse k f ≠ 0 →
      v (eval₂ F.subtype Φi f) <
        v (eval₂ F.subtype Φi (hasse k f)) + (((ord k : ℝ) * Θ : ℝ) : WithTop ℝ)) ∧
    ∀ᶠ m in atTop,
      v (eval₂ F.subtype Φi f) < v (eval₂ F.subtype Φi f - (eval (Φ m) f : K))

variable {v : AddValuation K (WithTop ℝ)} {F : Subring K} {Φ : ℕ → σ → F} {Φi : σ → K}
  {Θ : ℝ}

/-- `statementD` gives `StatementDHolds` for the degrees less than `p`. -/
theorem statementDHolds_of_degreeOf_lt {p : ℕ} [CharP K p] (hp : p.Prime) {γ : ℕ → ℝ}
    (hT : IsPlanarTail v F Φ Φi Θ γ) (f : MvPolynomial σ F) (hf : f ≠ 0)
    (hdeg : ∀ i, degreeOf i f < p) : StatementDHolds v F Φ Φi Θ f :=
  statementD_of_charP hp hT f hf hdeg

theorem add_coe_sub_le {a b : WithTop ℝ} {r s : ℝ}
    (h : a + (r : WithTop ℝ) ≤ b + (s : WithTop ℝ)) : a + ((r - s : ℝ) : WithTop ℝ) ≤ b := by
  have h2 := add_le_add h (le_refl ((-s : ℝ) : WithTop ℝ))
  rwa [add_assoc, add_assoc, ← WithTop.coe_add, ← WithTop.coe_add, add_neg_cancel,
    WithTop.coe_zero, add_zero, ← sub_eq_add_neg] at h2

theorem map_zpow_one_sub (v : AddValuation K (WithTop ℝ)) {M : K} (hM : M ≠ 0) {r : ℝ}
    (hr : v M = r) (p : ℕ) : v (M ^ (1 - p : ℤ)) = (((1 - p : ℝ) * r : ℝ) : WithTop ℝ) := by
  rw [zpow_sub₀ hM, zpow_one, zpow_natCast, AddValuation.map_div, AddValuation.map_pow, hr,
    ← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_sub, nsmul_eq_mul]
  congr 1
  ring

/-- Steps 2 to 5 of the proof of Theorem 3.19.6 (Conjecture P). The hypotheses are named in the
docstring of the file: `hH1` is Lemma 3.19.2, part 1, `hD` is Theorem 3.18.26 for the nonzero
derivatives of `g`, and `hrun` is Theorem 3.18.32, part 1, and Corollary 3.18.33 for the run
from `P_m`, with Lemma 3.19.2, part 4. -/
theorem conjectureP_of_restart {p : ℕ} [CharP K p] (hp : p.Prime) (g : MvPolynomial σ F)
    (vM : ℕ → ℝ) (hvM : Tendsto vM atTop (𝓝 Θ)) (Mm : ℕ → K) (hMv : ∀ m, v (Mm m) = vM m)
    (hM0 : ∀ m, Mm m ≠ 0) (H1 : ℕ → σ → K)
    (hH1 : ∀ m i, H1 m i = Mm m ^ (1 - p : ℤ) * eval₂ F.subtype Φi (hasse (single i 1) g))
    (hD : ∀ k, hasse k g ≠ 0 → StatementDHolds v F Φ Φi Θ (hasse k g))
    (μ : ℕ → WithTop ℝ)
    (hrun : ∀ᶠ m in atTop, ∃ e, 1 ≤ e ∧ ∃ k, hasse k g ≠ 0 ∧ ¬ (∀ i, p ∣ k i) ∧
      (∃ i, ¬ p ∣ (k i).choose (p ^ e)) ∧
      (∀ i, μ m + ((((p ^ e : ℕ) : ℝ) * (Θ - vM m) : ℝ) : WithTop ℝ) ≤
        v (H1 m i) + ((Θ - vM m : ℝ) : WithTop ℝ)) ∧
      v ((eval (Φ m) (hasse k g) : F) : K) +
          (((((p ^ e : ℕ) : ℝ) - p) * vM m + ((ord k : ℝ) - (p ^ e : ℕ)) * vM (m + 1) : ℝ) :
            WithTop ℝ) ≤ μ m) :
    False := by
  set N := ∑ i, degreeOf i g with hNdef
  have hNi : ∀ i, degreeOf i g ≤ N := fun i =>
    Finset.single_le_sum (f := fun i => degreeOf i g) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  -- the property of a pair `(e, k)` at the point `m`
  set P : ℕ → ℕ × (σ →₀ ℕ) → Prop := fun m t =>
    1 ≤ t.1 ∧ hasse t.2 g ≠ 0 ∧ ¬ (∀ i, p ∣ t.2 i) ∧ (∃ i, ¬ p ∣ (t.2 i).choose (p ^ t.1)) ∧
      (∀ i, μ m + ((((p ^ t.1 : ℕ) : ℝ) * (Θ - vM m) : ℝ) : WithTop ℝ) ≤
        v (H1 m i) + ((Θ - vM m : ℝ) : WithTop ℝ)) ∧
      v ((eval (Φ m) (hasse t.2 g) : F) : K) +
          (((((p ^ t.1 : ℕ) : ℝ) - p) * vM m + ((ord t.2 : ℝ) - (p ^ t.1 : ℕ)) * vM (m + 1) : ℝ) :
            WithTop ℝ) ≤ μ m with hP
  have hpe_le : ∀ (e : ℕ) (k : σ →₀ ℕ) (i : σ), ¬ p ∣ (k i).choose (p ^ e) → p ^ e ≤ k i := by
    intro e k i hi
    by_contra h
    exact hi (by rw [Nat.choose_eq_zero_of_lt (not_le.mp h)]; exact dvd_zero p)
  -- Step 4: the pairs lie in a finite set
  set T : Finset (ℕ × (σ →₀ ℕ)) := Finset.range (N + 1) ×ˢ box σ N with hT
  have hev : ∀ᶠ m in atTop, ∃ t ∈ T, P m t := by
    filter_upwards [hrun] with m ⟨e, he, k, hk0, hk1, ⟨i, hi⟩, h1, h2⟩
    refine ⟨(e, k), ?_, he, hk0, hk1, ⟨i, hi⟩, h1, h2⟩
    have hki : k i ≤ N := (le_degreeOf_of_hasse_ne_zero hk0 i).trans (hNi i)
    have hlt : e < p ^ e := Nat.lt_pow_self hp.one_lt
    have := hpe_le e k i hi
    rw [hT, Finset.mem_product, Finset.mem_range, mem_box]
    exact ⟨by omega, fun l => (le_degreeOf_of_hasse_ne_zero hk0 l).trans (hNi l)⟩
  obtain ⟨⟨e, k⟩, -, hfreq⟩ : ∃ t ∈ T, ∃ᶠ m in atTop, P m t := by
    by_contra hc
    have hc' : ∀ t ∈ T, ∀ᶠ m in atTop, ¬ P m t := fun t ht =>
      Filter.not_frequently.mp fun hf => hc ⟨t, ht, hf⟩
    obtain ⟨m, ⟨t, ht, hPt⟩, hm⟩ := (hev.and ((Filter.eventually_all_finset T).mpr hc')).exists
    exact hm t ht hPt
  -- the data that do not depend on `m`
  obtain ⟨m0, he, hk0, hk1, ⟨i', hi'⟩, -, -⟩ := hfreq.exists
  simp only at he hk0 hk1 hi'
  push Not at hk1
  obtain ⟨i0, hi0⟩ := hk1
  have hpe := hpe_le e k i' hi'
  have hp2 : 2 ≤ p ^ e := by
    have := hp.two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
  have hordk : p ^ e ≤ ord k := hpe.trans
    (Finset.single_le_sum (f := fun l => k l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i'))
  have hk0i : k i0 ≠ 0 := fun h => hi0 (by rw [h]; exact dvd_zero p)
  have hke : k - single i0 1 ≠ 0 := by
    intro h0
    have hle : single i0 1 ≤ k := Finsupp.single_le_iff.mpr (by omega)
    have hk : k = single i0 1 := by rw [← tsub_add_cancel_of_le hle, h0, zero_add]
    have : k i' ≤ 1 := by
      rw [hk, single_apply]
      split_ifs <;> omega
    omega
  -- Step 5: Statement D for `f = g_{X_{i0}}` at the index `k - e_{i0}`
  have hD0 := hD k hk0
  have hchain : hasse (k - single i0 1) (hasse (single i0 1) g) = k i0 • hasse k g :=
    hasse_sub_single_hasse_single k hk0i g
  have hEchain : eval₂ F.subtype Φi (hasse (k - single i0 1) (hasse (single i0 1) g)) =
      (k i0 : K) * eval₂ F.subtype Φi (hasse k g) := by
    rw [hchain]
    simp [nsmul_eq_mul]
  have hkK : (k i0 : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]
    exact hi0
  have hf1 : hasse (k - single i0 1) (hasse (single i0 1) g) ≠ 0 := by
    intro h0
    have := hEchain
    rw [h0] at this
    simp only [eval₂_zero] at this
    exact mul_ne_zero hkK hD0.1 this.symm
  have hf0 : hasse (single i0 1) g ≠ 0 := fun h0 => hf1 (by rw [h0, hasse_zero_right])
  have hDf := (hD (single i0 1) hf0).2.1 (k - single i0 1) hke hf1
  have hvk : v (k i0 : K) = 0 := v.map_natCast_eq_zero hp hi0
  rw [hEchain, AddValuation.map_mul, hvk, zero_add] at hDf
  have hord := ord_sub_single k hk0i
  -- the values
  set x := v (eval₂ F.subtype Φi (hasse (single i0 1) g)) with hx
  set β := v (eval₂ F.subtype Φi (hasse k g)) with hβ
  set n := ord k - p ^ e with hn
  have hreal : (((ord (k - single i0 1) : ℕ) : ℝ) * Θ : ℝ) =
      (((p ^ e : ℕ) : ℝ) - 1) * Θ + (n : ℝ) * Θ := by
    have h1 : ((ord (k - single i0 1) : ℕ) : ℝ) = (ord k : ℝ) - 1 := by
      rw [← hord]
      push_cast
      ring
    have h2 : (n : ℝ) = (ord k : ℝ) - ((p ^ e : ℕ) : ℝ) := by
      rw [hn, Nat.cast_sub hordk]
    rw [h1, h2]
    ring
  have hDf' : x < (β + (((((p ^ e : ℕ) : ℝ) - 1) * Θ : ℝ) : WithTop ℝ)) +
      (((n : ℝ) * Θ : ℝ) : WithTop ℝ) := by
    rw [add_assoc, ← WithTop.coe_add, ← hreal]
    exact hDf
  have hvM1 : Tendsto (fun m => vM (m + 1)) atTop (𝓝 Θ) :=
    hvM.comp (tendsto_add_atTop_nat 1)
  have hlim := eventually_lt_add hvM1 n hDf'
  -- `v(g^{[k]}(Φ_m)) = β` for `m` large
  have hval : ∀ᶠ m in atTop, v ((eval (Φ m) (hasse k g) : F) : K) = β := by
    filter_upwards [hD0.2.2] with m hm
    exact map_eq_of_lt_map_sub v hm
  -- the contradiction at one point `m`
  obtain ⟨m, ⟨-, -, -, -, h1, h2⟩, hm1, hm2⟩ := (hfreq.and_eventually (hlim.and hval)).exists
  simp only at h1 h2
  have h1' := h1 i0
  rw [hH1, AddValuation.map_mul, map_zpow_one_sub v (hM0 m) (hMv m)] at h1'
  rw [hm2] at h2
  -- `μ_m + p^e δ_m ≤ x + (1 - p) v(M_m) + δ_m` and
  -- `β + (p^e - p) v(M_m) + (|k| - p^e) v(M_{m+1}) ≤ μ_m`
  have h3 : β + (((((p ^ e : ℕ) : ℝ) - p) * vM m + ((ord k : ℝ) - (p ^ e : ℕ)) * vM (m + 1) +
      ((p ^ e : ℕ) : ℝ) * (Θ - vM m) : ℝ) : WithTop ℝ) ≤
      x + (((1 - p : ℝ) * vM m + (Θ - vM m) : ℝ) : WithTop ℝ) := by
    calc β + (((((p ^ e : ℕ) : ℝ) - p) * vM m + ((ord k : ℝ) - (p ^ e : ℕ)) * vM (m + 1) +
          ((p ^ e : ℕ) : ℝ) * (Θ - vM m) : ℝ) : WithTop ℝ)
        = β + (((((p ^ e : ℕ) : ℝ) - p) * vM m + ((ord k : ℝ) - (p ^ e : ℕ)) * vM (m + 1) :
            ℝ) : WithTop ℝ) + ((((p ^ e : ℕ) : ℝ) * (Θ - vM m) : ℝ) : WithTop ℝ) := by
          rw [WithTop.coe_add, add_assoc]
      _ ≤ μ m + ((((p ^ e : ℕ) : ℝ) * (Θ - vM m) : ℝ) : WithTop ℝ) := add_le_add h2 le_rfl
      _ ≤ (((1 - p : ℝ) * vM m : ℝ) : WithTop ℝ) + x + ((Θ - vM m : ℝ) : WithTop ℝ) := h1'
      _ = x + (((1 - p : ℝ) * vM m + (Θ - vM m) : ℝ) : WithTop ℝ) := by
          rw [WithTop.coe_add]
          ac_rfl
  have h4 := add_coe_sub_le h3
  have hn' : (n : ℝ) = (ord k : ℝ) - ((p ^ e : ℕ) : ℝ) := by
    rw [hn, Nat.cast_sub hordk]
  have h5 : β + (((((p ^ e : ℕ) : ℝ) - 1) * Θ : ℝ) : WithTop ℝ) +
      (((n : ℝ) * vM (m + 1) : ℝ) : WithTop ℝ) ≤ x := by
    have hr : (((p ^ e : ℕ) : ℝ) - 1) * Θ + (n : ℝ) * vM (m + 1) =
        (((p ^ e : ℕ) : ℝ) - p) * vM m + ((ord k : ℝ) - (p ^ e : ℕ)) * vM (m + 1) +
          ((p ^ e : ℕ) : ℝ) * (Θ - vM m) - ((1 - p : ℝ) * vM m + (Θ - vM m)) := by
      rw [hn']
      ring
    rw [add_assoc, ← WithTop.coe_add, hr]
    exact h4
  exact absurd (hm1.trans_le h5) (lt_irrefl _)

end PlanarRuns

end Singularity
