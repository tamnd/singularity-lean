/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.PlanarRunsLambda
import Singularity.Invariant.PlanarRunsLeastTerm

/-!
# The dominant derivative along a planar corner run

This file proves Lemma 3.18.30 of Volume 7 of the handbook in the Hahn model of
`PlanarRunsHahn`. If `Λ_0 < Λ_+`, the derivative `∂_{x_m} g̃_m` is `μ_m ε_m` with a unit
`ε_m`, and `μ_m` divides each coefficient `A_d` with `d ≠ 0` of the transform `g̃_m`.

## The model

* The free variable `x` of the handbook is the variable `i₀ : σ`, chosen with the least value
  of `g^{[e_i]}(Φ_∞)`. The hypothesis `Λ_0 < Λ_+` is the strict inequality
  `β_{e_{i₀}} + (1 + θ) < β_{p^a e_i} + p^a (1 + θ)` for each `i` and each `a ≥ 1`.
* `μ_m = c_X M_m ν_X` is the monomial of exponent `ν_X + expM w m`, with `ν_X` the order of
  `g^{[e_{i₀}]}(Φ_∞)`.

## Main results

* `IsCornerWord.dominantDerivative`: Lemma 3.18.30.
-/

open MvPolynomial Filter Topology

namespace Singularity

namespace PlanarRuns

open CornerExp

theorem withTop_lt_add_pred {V Θ : ℝ} {B : WithTop ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h : ((V : ℝ) : WithTop ℝ) + ((Θ : ℝ) : WithTop ℝ) < B + (((n : ℝ) * Θ : ℝ) : WithTop ℝ)) :
    ((V : ℝ) : WithTop ℝ) < B + ((((n - 1 : ℕ) : ℝ) * Θ : ℝ) : WithTop ℝ) := by
  induction B with
  | top => simp
  | coe b =>
    have h' : V + Θ < b + n * Θ := by exact_mod_cast h
    have : V < b + ((n - 1 : ℕ) : ℝ) * Θ := by
      rw [Nat.cast_sub hn]
      push_cast
      linarith
    exact_mod_cast this

section Derivative

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {θ : ℝ} {k : Type*} [Field k] {w : ℕ → Bool}

/-- The value `f(Φ_∞)` at the limit point of the run. -/
noncomputable def cornerEval (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k)
    (f : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring) : HahnSeries (CornerExp θ) k :=
  eval₂ (finiteTypeSubfield k hθ).toSubring.subtype (fun l => cornerLimit hw (fun j => t j l)) f

/-- Lemma 3.18.30 for the Hahn model of a planar corner run. Let `x = g^{[e_{i₀}]}(Φ_∞)` have
the least value among the `g^{[e_i]}(Φ_∞)`, and assume `Λ_0 < Λ_+`. Put
`μ_m = ν_X + expM w m` with `ν_X` the order of `x`. For `m` large, `μ_m` is a monomial at `P_m`,
the derivative `∂_{x_m} g̃_m` is `c_X` times the monomial `μ_m` times a unit, and `μ_m` divides
each coefficient `A_d` with `d ≠ 0` of `g̃_m`. -/
theorem IsCornerWord.dominantDerivative {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k) (hpl : IsPlanarRun t)
    (f : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring)
    (hf0 : ∀ e, Above (cone w 0) 0 (f.coeff e : HahnSeries (CornerExp θ) k)) (i₀ : σ)
    (hd0 : hasse (Finsupp.single i₀ 1) f ≠ 0)
    (hle : ∀ i, hahnVal θ k (cornerEval hθ hw t (hasse (Finsupp.single i₀ 1) f)) ≤
      hahnVal θ k (cornerEval hθ hw t (hasse (Finsupp.single i 1) f)))
    (hplus : ∀ i a, 1 ≤ a → hasse (Finsupp.single i (p ^ a)) f ≠ 0 →
      hahnVal θ k (cornerEval hθ hw t (hasse (Finsupp.single i₀ 1) f)) +
          (((1 + θ : ℝ)) : WithTop ℝ) <
        hahnVal θ k (cornerEval hθ hw t (hasse (Finsupp.single i (p ^ a)) f)) +
          ((((p ^ a : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ))
    {x : HahnSeries (CornerExp θ) k} (hx : cornerEval hθ hw t (hasse (Finsupp.single i₀ 1) f) = x) :
    ∃ m₂, ∀ m ≥ m₂, x.order + expM w m ∈ cone w m ∧
      ((hasse (Finsupp.single i₀ 1)
          (chartAt w t m (map (finiteTypeSubfield k hθ).toSubring.subtype f))).coeff 0).coeff
          (x.order + expM w m) = x.coeff x.order ∧
      (∀ d, Above (cone w m) (x.order + expM w m)
        ((hasse (Finsupp.single i₀ 1)
          (chartAt w t m (map (finiteTypeSubfield k hθ).toSubring.subtype f))).coeff d)) ∧
      ∀ d, d ≠ 0 → Above (cone w m) (x.order + expM w m)
        ((chartAt w t m (map (finiteTypeSubfield k hθ).toSubring.subtype f)).coeff d) := by
  classical
  unfold cornerEval at hle hplus hx
  set e₀ : σ →₀ ℕ := Finsupp.single i₀ 1 with he₀
  have hf : f ≠ 0 := by
    rintro rfl
    exact hd0 (hasse_zero_right _)
  set Φi : σ → HahnSeries (CornerExp θ) k := fun l => cornerLimit hw (fun j => t j l) with hΦi
  set g := map (finiteTypeSubfield k hθ).toSubring.subtype f with hg
  have hE : ∀ e, eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi (hasse e f) =
      MvPolynomial.eval Φi (hasse e g) := by
    intro e
    rw [hg, hasse_map, MvPolynomial.eval_map]
  have hEm : ∀ m e, ((eval (cornerPointFT (w := w) hθ t m) (hasse e f) :
      (finiteTypeSubfield k hθ).toSubring) : HahnSeries (CornerExp θ) k) =
        MvPolynomial.eval (cornerPoint (w := w) t m) (hasse e g) := by
    intro m e
    rw [coe_eval_cornerPointFT, hg, hasse_map]
  obtain ⟨hx0, -, -⟩ := statementDHolds_corner_frob hθ hw t hpl _ hd0
  rw [← hΦi, hx] at hx0
  rw [hx] at hle hplus
  set ν := x.order with hν
  set V := val θ ν with hV
  have hxV : hahnVal θ k x = ((V : ℝ) : WithTop ℝ) := hahnVal_of_ne hx0
  -- Part 1: Proposition 3.18.29 for `g^{[e₀]}`.
  have hf0' : ∀ e, Above (cone w 0) 0
      ((hasse e₀ f).coeff e : HahnSeries (CornerExp θ) k) := by
    intro e
    rw [coeff_hasse, AddSubmonoidClass.coe_nsmul]
    exact (hf0 _).nsmul _
  obtain ⟨m₃, h29⟩ := hw.leastTerm hθ t hpl (hasse e₀ f) hd0 hf0' hx
  -- The key inequality: `Λ_0 ≤ β_e + |e| (1 + θ)`, strict for `|e| ≥ 2`.
  have hkey : ∀ e, e ≠ 0 → hasse e f ≠ 0 →
      hahnVal θ k x + (((1 + θ : ℝ)) : WithTop ℝ) ≤
          hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
            (((ord e : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) ∧
        (2 ≤ ord e → hahnVal θ k x + (((1 + θ : ℝ)) : WithTop ℝ) <
          hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
            (((ord e : ℝ) * (1 + θ) : ℝ) : WithTop ℝ)) := by
    intro e he hef
    obtain ⟨i, a, -, hs0, hle', hlt'⟩ := lambda_le_corner hθ hw t hpl f e he hef
    rw [← hΦi, hE, hE] at hle' hlt'
    simp only [hE] at hle
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have h1 : hahnVal θ k x + (((1 + θ : ℝ)) : WithTop ℝ) ≤
          hahnVal θ k (MvPolynomial.eval Φi (hasse (Finsupp.single i (p ^ 0)) g)) +
            ((((p ^ 0 : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) := by
        simp only [pow_zero, Nat.cast_one, one_mul]
        exact add_le_add_left (hle i) _
      refine ⟨h1.trans hle', fun h2 => h1.trans_lt (hlt' ?_)⟩
      rintro rfl
      rw [ord_single, pow_zero] at h2
      omega
    · have h1 := hplus i a ha hs0
      rw [hE] at h1
      exact ⟨(h1.trans_le hle').le, fun _ => h1.trans_le hle'⟩
  set N := ∑ i, degreeOf i g with hNdef
  have hN : ∀ i, degreeOf i g ≤ N := fun i =>
    Finset.single_le_sum (f := fun i => degreeOf i g) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hbox : ∀ e, hasse e g ≠ 0 → e ∈ box σ N := by
    intro e he
    rw [mem_box]
    intro i
    by_contra hlt
    exact he (hasse_eq_zero_of_lt hN (not_le.mp hlt))
  have hgf : ∀ e, hasse e g ≠ 0 → hasse e f ≠ 0 := by
    intro e he h0
    apply he
    rw [hg, hasse_map, h0, map_zero]
  set γ : ℕ → ℝ := fun m => val θ (expM w (m + 1) : CornerExp θ) with hγ
  have hγt : Tendsto γ atTop (𝓝 (1 + θ)) := hw.tendsto_val_expM.comp (tendsto_add_atTop_nat 1)
  have hev : ∀ᶠ m in atTop, ∀ e ∈ box σ N, hasse e g ≠ 0 →
      hahnVal θ k (MvPolynomial.eval (cornerPoint (w := w) t m) (hasse e g)) =
          hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) ∧
        (2 ≤ ord e → hahnVal θ k x < hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
          ((((ord e - 1 : ℕ) : ℝ) * γ m : ℝ) : WithTop ℝ)) := by
    refine (Filter.eventually_all_finset _).mpr fun e _ => ?_
    by_cases he : hasse e g = 0
    · exact Filter.Eventually.of_forall fun _ h => absurd he h
    have hef := hgf e he
    obtain ⟨-, -, h2e⟩ := statementDHolds_corner_frob hθ hw t hpl (hasse e f) hef
    rw [← hΦi] at h2e
    have hA : ∀ᶠ m in atTop,
        hahnVal θ k (MvPolynomial.eval (cornerPoint (w := w) t m) (hasse e g)) =
          hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) := by
      filter_upwards [h2e] with m hm
      rw [hE, hEm] at hm
      exact map_eq_of_lt_map_sub _ hm
    have hB : ∀ᶠ m in atTop, 2 ≤ ord e →
        hahnVal θ k x < hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
          ((((ord e - 1 : ℕ) : ℝ) * γ m : ℝ) : WithTop ℝ) := by
      by_cases h2 : 2 ≤ ord e
      · have he0 : e ≠ 0 := by
          rintro rfl
          simp [ord] at h2
        have h3 := (hkey e he0 hef).2 h2
        rw [hxV] at h3
        have h4 := withTop_lt_add_pred (by omega) h3
        rw [← hxV] at h4
        filter_upwards [eventually_lt_add hγt (ord e - 1) h4] with m hm
        exact fun _ => hm
      · exact Filter.Eventually.of_forall fun _ h => absurd h h2
    filter_upwards [hA, hB] with m hm1 hm2
    exact fun _ => ⟨hm1, hm2⟩
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.mp hev
  set a : CornerExp θ := expM w (m₁ + 1) with ha
  set T := chart (cornerPoint (w := w) t m₁) 1 g with hT
  have hTc : ∀ e, T.coeff e = MvPolynomial.eval (cornerPoint (w := w) t m₁) (hasse e g) := by
    intro e
    rw [hT, coeff_chart, one_pow, one_mul]
  have hT0 : ∀ e, Above (cone w (m₁ + 1)) 0 (T.coeff e) := by
    intro e
    rw [hTc]
    refine Above.eval (a := 0) (fun i => above_cornerPoint t (Nat.le_succ m₁) i) fun e' => ?_
    rw [smul_zero, sub_zero, coeff_hasse, hg, coeff_map]
    exact ((hf0 _).mono_cone (cone_mono w (Nat.zero_le _))).nsmul _
  set S : Set (CornerExp θ) := {q | ∃ e, e ≠ 0 ∧ q - ord e • a ∈ (T.coeff e).support} with hS
  have hSc : ∀ q ∈ S, 0 ≤ coordY w (m₁ + 1) q ∧ 0 ≤ coordZ w (m₁ + 1) q := by
    rintro q ⟨e, -, he⟩
    have h1 := hT0 e _ he
    rw [sub_zero] at h1
    have h2 := add_mem h1 (nsmul_mem (expM_mem_cone (θ := θ) w le_rfl) (ord e))
    rwa [sub_add_cancel] at h2
  have hmin : ∀ q ∈ S, q ≠ ν + a → val θ (ν + a) < val θ q := by
    rintro q ⟨e, he0, he⟩ hqν
    have hTe : T.coeff e ≠ 0 := by
      rintro h0
      rw [h0] at he
      simp at he
    have hge : hasse e g ≠ 0 := by
      intro h0
      apply hTe
      rw [hTc, h0, map_zero]
    obtain ⟨hA, hB⟩ := hm₁ m₁ le_rfl e (hbox e hge) hge
    have h1 := hahnVal_le_of_mem he
    rw [hTc, hA] at h1
    have h5 : val θ q = val θ (q - ord e • a) + (ord e : ℝ) * γ m₁ := by
      rw [hγ, ← val_nsmul', ← val_add, sub_add_cancel]
    have h6 : val θ (ν + a) = V + γ m₁ := by rw [val_add]
    have hle' : val θ (ν + a) ≤ val θ q := by
      obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero he0
      have hord := ord_sub_single' e (i := i) (a := 1) (Nat.one_le_iff_ne_zero.mpr hi)
      rcases Nat.lt_or_ge (ord e) 2 with h2 | h2
      · have he1 : ord e = 1 := by omega
        have h3 := (hkey e he0 (hgf e hge)).1
        rw [he1, Nat.cast_one, one_mul, WithTop.add_le_add_iff_right WithTop.coe_ne_top,
          hxV] at h3
        have h4 : V ≤ val θ (q - ord e • a) := by exact_mod_cast h3.trans h1
        have h8 : (ord e : ℝ) = 1 := by exact_mod_cast he1
        rw [h5, h6, h8, one_mul]
        linarith
      · have h3 := hB h2
        rw [hxV] at h3
        have h4 : ((V : ℝ) : WithTop ℝ) <
            ((val θ (q - ord e • a) + ((ord e - 1 : ℕ) : ℝ) * γ m₁ : ℝ) : WithTop ℝ) := by
          rw [WithTop.coe_add]
          exact h3.trans_le (by gcongr)
        have h7 : V < val θ (q - ord e • a) + ((ord e - 1 : ℕ) : ℝ) * γ m₁ := by
          exact_mod_cast h4
        rw [Nat.cast_sub (by omega), Nat.cast_one] at h7
        rw [h5, h6]
        linarith
    exact lt_of_le_of_ne hle' fun h' => hqν ((val_injective hθ) h').symm
  obtain ⟨m₀, hm₀, hdom⟩ := hw.dominance (m₁ + 1) hSc hmin
  refine ⟨max m₀ m₃, fun m hm => ?_⟩
  have hm0 : m₀ ≤ m := le_of_max_le_left hm
  have hm3 : m₃ ≤ m := le_of_max_le_right hm
  have hm1m : m₁ + 1 ≤ m := hm₀.trans hm0
  obtain ⟨h29a, h29b, h29c⟩ := h29 m hm3
  rw [← hasse_map, ← hg] at h29b h29c
  have hhasse : ∀ d, (hasse e₀ (chartAt w t m g)).coeff d =
      cornerM θ k w m * (chartAt w t m (hasse e₀ g)).coeff d := by
    intro d
    rw [chartAt, chartAt, hasse_chart, coeff_C_mul, he₀, ord_single, pow_one]
  refine ⟨add_mem h29a (expM_mem_cone w le_rfl), ?_, fun d => ?_, fun d hd => ?_⟩
  · rw [hhasse, cornerM, HahnSeries.coeff_single_mul_add, one_mul]
    exact h29b
  · rw [hhasse, cornerM, add_comm]
    exact (Above.single _ _).mul (h29c d)
  -- Part 2.
  have hcone : ∀ q ∈ S, q - (ν + a) ∈ cone w m := by
    intro q hq
    by_cases hqν : q = ν + a
    · rw [hqν, sub_self]
      exact zero_mem _
    · obtain ⟨h1, h2⟩ := hdom m hm0 q hq hqν
      exact ⟨h1.le, h2.le⟩
  have hTm : ∀ e, e ≠ 0 → Above (cone w m) (ν + a - ord e • a) (T.coeff e) := by
    intro e he r hr
    have hq : r + ord e • a ∈ S := ⟨e, he, by rwa [add_sub_cancel_right]⟩
    have := hcone _ hq
    convert this using 1
    abel
  have hchart : chartAt w t m g =
      chart (fun i => cornerPoint (w := w) t m i - cornerPoint (w := w) t m₁ i)
        (cornerM θ k w m) T := by
    rw [hT, chart_chart, chartAt]
    congr 1
    · funext i
      ring
    · ring
  obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hd
  set n := ord (d - Finsupp.single i 1) with hn
  have hdn : ord d = n + 1 := (ord_sub_single' d (Nat.one_le_iff_ne_zero.mpr hi)).symm
  rw [hchart, coeff_chart, cornerM, HahnSeries.single_pow, one_pow]
  have h1 : Above (cone w m) (ν + expM w m - ord d • (expM w m : CornerExp θ))
      (MvPolynomial.eval (fun i => cornerPoint (w := w) t m i - cornerPoint (w := w) t m₁ i)
        (hasse d T)) := by
    refine Above.eval (a := a) (fun i => above_cornerPoint_sub t (by omega) i) fun e => ?_
    rw [coeff_hasse]
    have hed : e + d ≠ 0 := fun h => hd (add_eq_zero.mp h).2
    refine ((hTm (e + d) hed).mono ?_).nsmul _
    have hord : ord (e + d) = ord e + ord d := by
      simp [ord, Finset.sum_add_distrib]
    have : ν + a - ord (e + d) • a - (ν + expM w m - ord d • (expM w m : CornerExp θ) - ord e • a) =
        n • ((expM w m : CornerExp θ) - a) := by
      rw [hord, hdn]
      simp only [add_nsmul, one_nsmul, nsmul_sub]
      abel
    rw [this]
    exact nsmul_mem (expM_sub_mem_cone w (by omega) le_rfl) _
  have := (Above.single (C := cone w m) (ord d • (expM w m : CornerExp θ)) (1 : k)).mul h1
  rwa [add_sub_cancel] at this

end Derivative

end PlanarRuns

end Singularity
