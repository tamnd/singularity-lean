/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.PlanarRunsRho

/-!
# The dominance lemma along a corner run

This file proves Lemma 3.15.4 of Volume 7 of the handbook (the dominance lemma) in the exponent
language of the Hahn model of `PlanarRunsHahn`.

## The model

* An exponent `r : CornerExp θ` is the exponent of a monomial in `y_N, z_N`. Its exponents at
  `P_m` are `coordY w m r` and `coordZ w m r` (`PlanarRunsRho`).
* The weight `λ(q) = q_1 + θ_m q_2` of the handbook is `val θ q / v(y_m)`, so a unique minimiser
  of `λ` on `S` is a unique minimiser of `val θ` on `S`. The irrationality of `θ_m` only gives
  this uniqueness, so the statement takes the strict inequality as a hypothesis.
* The condition `S ⊆ ℕ²` at `P_m` is `0 ≤ coordY w m q` and `0 ≤ coordZ w m q` for each `q ∈ S`.

## Main results

* `dominance_core`: the estimate of the proof for real weights.
* `IsCornerWord.coord_col`: the columns from `P_m` to `P_{m'}`, with the values of `y_{m'}` and
  `z_{m'}`.
* `IsCornerWord.dominance`: Lemma 3.15.4.
-/

open Filter Topology

namespace Singularity

namespace PlanarRuns

open CornerExp

/-- The estimate of the proof of Lemma 3.15.4: for weights `u, v > 0` and a lower bound `-A` on
the first exponent, there is `η > 0` such that `b ε < α (a u + b v)` for each `(a, b)` of
positive weight, each `α ≥ 1` and each `0 < ε < η`. -/
theorem dominance_core {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (A : ℤ) :
    ∃ η > 0, ∀ a b : ℤ, -A ≤ a → 0 < (a : ℝ) * u + b * v → ∀ α : ℝ, 1 ≤ α →
      ∀ ε : ℝ, 0 < ε → ε < η → (b : ℝ) * ε < α * ((a : ℝ) * u + b * v) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * |(A : ℝ)| * u / v)
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / u)
  set F : Finset (ℤ × ℤ) := (Finset.Icc (-A) (M : ℤ) ×ˢ Finset.Icc 1 (N : ℤ)).filter
    (fun x => 0 < (x.1 : ℝ) * u + x.2 * v) with hF
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ > 0, ∀ x ∈ F, δ ≤ (x.1 : ℝ) * u + x.2 * v := by
    by_cases hne : F.Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := F.exists_min_image (fun x => (x.1 : ℝ) * u + x.2 * v) hne
      exact ⟨_, (Finset.mem_filter.mp hx0).2, hmin⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  have hN' : 2 * |(A : ℝ)| * u < N * v := by
    rwa [div_lt_iff₀ hv] at hN
  have hM' : 1 < M * u := by
    rwa [div_lt_iff₀ hu] at hM
  set δ' := min 1 δ with hδ'
  have hδ'pos : 0 < δ' := lt_min one_pos hδ
  refine ⟨min (v / 2) (δ' / (N + 1)), lt_min (by linarith) (by positivity), ?_⟩
  intro a b ha hL α hα ε hε hεη
  have hε1 : ε < v / 2 := lt_of_lt_of_le hεη (min_le_left _ _)
  have hε2 : ε < δ' / (N + 1) := lt_of_lt_of_le hεη (min_le_right _ _)
  set L := (a : ℝ) * u + b * v with hLdef
  have hαL : L ≤ α * L := le_mul_of_one_le_left hL.le hα
  suffices h : (b : ℝ) * ε < L from lt_of_lt_of_le h hαL
  rcases le_or_gt b 0 with hb | hb
  · have : (b : ℝ) ≤ 0 := by exact_mod_cast hb
    nlinarith
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have haR : -(|(A : ℝ)|) ≤ a := by
    have : (-A : ℝ) ≤ a := by exact_mod_cast ha
    linarith [le_abs_self (A : ℝ)]
  rcases lt_or_ge (N : ℤ) b with hbN | hbN
  · have hbN' : (N : ℝ) < b := by exact_mod_cast hbN
    have h1 : -(|(A : ℝ)|) * u ≤ a * u := mul_le_mul_of_nonneg_right haR hu.le
    have h2 : (N : ℝ) * v < b * v := mul_lt_mul_of_pos_right hbN' hv
    have h3 : (b : ℝ) * ε < b * (v / 2) := mul_lt_mul_of_pos_left hε1 hbR
    nlinarith
  · have hbN' : (b : ℝ) ≤ N := by exact_mod_cast hbN
    have hN1 : (0 : ℝ) < N + 1 := by positivity
    have h1 : (b : ℝ) * ε < δ' := by
      have : ε * (N + 1) < δ' := by rwa [lt_div_iff₀ hN1] at hε2
      nlinarith
    rcases le_or_gt 1 L with hL1 | hL1
    · exact lt_of_lt_of_le h1 (le_trans (min_le_left _ _) hL1)
    · have hau : (a : ℝ) * u < 1 := by nlinarith
      have haM : a ≤ (M : ℤ) := by
        have : (a : ℝ) < M := by
          by_contra hc
          push Not at hc
          nlinarith
        exact_mod_cast this.le
      have hmem : (a, b) ∈ F := by
        rw [hF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        exact ⟨⟨⟨ha, haM⟩, ⟨hb, hbN⟩⟩, hL⟩
      exact lt_of_lt_of_le h1 (le_trans (min_le_right _ _) (hδF _ hmem))

variable {θ : ℝ} {w : ℕ → Bool}

/-- The value of an exponent in the exponents at `P_m`. -/
theorem val_eq_coord (w : ℕ → Bool) (m : ℕ) (r : CornerExp θ) :
    val θ r = coordY w m r * val θ (expY w m : CornerExp θ) +
      coordZ w m r * val θ (expZ w m : CornerExp θ) := by
  conv_lhs => rw [← expAt_coord w m r]
  simp only [val, expAt, fst_mk, snd_mk, Int.cast_add, Int.cast_mul]
  ring

/-- The columns from `P_m` to `P_{m+n}`: the exponents at `P_{m+n}` are
`(α a + β b, γ a + δ b)` for the exponents `(a, b)` at `P_m`, with `α, δ ≥ 1` and `β, γ ≥ 0`, and
`v(z_{m+n}) = α v(z_m) - β v(y_m)`, `v(y_{m+n}) = δ v(y_m) - γ v(z_m)`. -/
theorem coord_col (w : ℕ → Bool) (m n : ℕ) :
    ∃ α β γ δ : ℤ, 1 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 1 ≤ δ ∧
      (∀ r : CornerExp θ, coordY w (m + n) r = α * coordY w m r + β * coordZ w m r) ∧
      (∀ r : CornerExp θ, coordZ w (m + n) r = γ * coordY w m r + δ * coordZ w m r) ∧
      val θ (expZ w (m + n) : CornerExp θ) =
        α * val θ (expZ w m : CornerExp θ) - β * val θ (expY w m : CornerExp θ) ∧
      val θ (expY w (m + n) : CornerExp θ) =
        δ * val θ (expY w m : CornerExp θ) - γ * val θ (expZ w m : CornerExp θ) := by
  induction n with
  | zero => exact ⟨1, 0, 0, 1, le_rfl, le_rfl, le_rfl, le_rfl, fun r => by simp,
      fun r => by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hY, hZ, hvz, hvy⟩ := ih
    rw [← add_assoc]
    cases hwm : w (m + n)
    · refine ⟨α, β, α + γ, β + δ, hα, hβ, by omega, by omega, fun r => ?_, fun r => ?_, ?_, ?_⟩
      · rw [coordY_succ, hwm]; simp [hY]
      · rw [coordZ_succ, hwm]; simp only [Bool.false_eq_true, ite_false, hY, hZ]; ring
      · rw [expZ_succ, hwm]; simpa using hvz
      · rw [expY_succ, hwm]; simp only [Bool.false_eq_true, ite_false, val_sub, hvy, hvz]
        push_cast; ring
    · refine ⟨α + γ, β + δ, γ, δ, by omega, by omega, hγ, hδ, fun r => ?_, fun r => ?_, ?_, ?_⟩
      · rw [coordY_succ, hwm]; simp only [ite_true, hY, hZ]; ring
      · rw [coordZ_succ, hwm]; simp [hZ]
      · rw [expZ_succ, hwm]; simp only [ite_true, val_sub, hvy, hvz]
        push_cast; ring
      · rw [expY_succ, hwm]; simpa using hvy

/-- `v(y_m) → 0` and `v(z_m) → 0` along a corner run. -/
theorem IsCornerWord.tendsto_val_expY_expZ (hw : IsCornerWord θ w) :
    Tendsto (fun m => val θ (expY w m : CornerExp θ)) atTop (𝓝 0) ∧
      Tendsto (fun m => val θ (expZ w m : CornerExp θ)) atTop (𝓝 0) := by
  have hs : Tendsto (fun m => val θ (expY w m : CornerExp θ) + val θ (expZ w m : CornerExp θ))
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 1 + θ)).sub hw.tendsto_val_expM
    rw [sub_self] at h
    refine h.congr fun m => ?_
    rw [expM_eq, val_sub, val_add]
    simp [val]
  refine ⟨?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
      (fun m => (hw.pos_y m).le) (fun m => ?_)
    linarith [hw.pos_z m]
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
      (fun m => (hw.pos_z m).le) (fun m => ?_)
    linarith [hw.pos_y m]

/-- Lemma 3.15.4 (dominance): let `S` be a set of exponents with nonnegative exponents at `P_m`
and a unique minimiser `q_*` of the value. Then there is `m_0 ≥ m` such that at each point
`P_{m'}` with `m' ≥ m_0`, each `q ∈ S` other than `q_*` has both exponents of `q - q_*`
positive: `y_{m'} z_{m'}` divides `q / q_*`. -/
theorem IsCornerWord.dominance (hw : IsCornerWord θ w) (m : ℕ) {S : Set (CornerExp θ)}
    {qs : CornerExp θ} (hS : ∀ q ∈ S, 0 ≤ coordY w m q ∧ 0 ≤ coordZ w m q)
    (hmin : ∀ q ∈ S, q ≠ qs → val θ qs < val θ q) :
    ∃ m₀, m ≤ m₀ ∧ ∀ m' ≥ m₀, ∀ q ∈ S, q ≠ qs →
      0 < coordY w m' (q - qs) ∧ 0 < coordZ w m' (q - qs) := by
  set u := val θ (expY w m : CornerExp θ) with hu
  set v := val θ (expZ w m : CornerExp θ) with hv
  have hu0 : 0 < u := hw.pos_y m
  have hv0 : 0 < v := hw.pos_z m
  obtain ⟨η₁, hη₁, h₁⟩ := dominance_core hu0 hv0 (coordY w m qs)
  obtain ⟨η₂, hη₂, h₂⟩ := dominance_core hv0 hu0 (coordZ w m qs)
  obtain ⟨hty, htz⟩ := hw.tendsto_val_expY_expZ
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((tendsto_order.1 htz).2 η₁ hη₁)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ((tendsto_order.1 hty).2 η₂ hη₂)
  refine ⟨max m (max N₁ N₂), le_max_left _ _, fun m' hm' q hq hne => ?_⟩
  have hmm' : m ≤ m' := le_trans (le_max_left _ _) hm'
  have hN₁' : N₁ ≤ m' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm'
  have hN₂' : N₂ ≤ m' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm'
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hmm'
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hY, hZ, hvz, hvy⟩ := coord_col (θ := θ) w m n
  set r := q - qs with hr
  set a := coordY w m r with ha
  set b := coordZ w m r with hb
  have hqr : q = r + qs := by rw [hr]; abel
  have haA : -coordY w m qs ≤ a := by
    have := (hS q hq).1
    rw [hqr, coordY_add] at this
    omega
  have hbB : -coordZ w m qs ≤ b := by
    have := (hS q hq).2
    rw [hqr, coordZ_add] at this
    omega
  have hL : 0 < (a : ℝ) * u + b * v := by
    rw [ha, hb, hu, hv, ← val_eq_coord, hr, val_sub]
    linarith [hmin q hq hne]
  have hαR : (1 : ℝ) ≤ α := by exact_mod_cast hα
  have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hεz := hw.pos_z (m + n)
  have hεy := hw.pos_y (m + n)
  have k₁ := h₁ a b haA hL α hαR _ hεz (hN₁ _ hN₁')
  have k₂ := h₂ b a hbB (by linarith) δ hδR _ hεy (hN₂ _ hN₂')
  rw [hvz] at k₁
  rw [hvy] at k₂
  constructor
  · rw [hY]
    have : (0 : ℝ) < (α * a + β * b : ℤ) := by
      push_cast
      have : u * (α * a + β * b) = α * (a * u + b * v) - b * (α * v - β * u) := by ring
      nlinarith
    exact_mod_cast this
  · rw [hZ]
    have : (0 : ℝ) < (γ * a + δ * b : ℤ) := by
      push_cast
      have : v * (γ * a + δ * b) = δ * (b * v + a * u) - a * (δ * u - γ * v) := by ring
      nlinarith
    exact_mod_cast this

end PlanarRuns

end Singularity
