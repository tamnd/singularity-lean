/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.PlanarRunsStar

/-!
# Theorem 3.18.32, part 2: the value of the cleaned limit

This file proves part 2 of Theorem 3.18.32 of Volume 7 of the handbook in the Hahn model of
`PlanarRunsHahn`: for a planar corner run that keeps `ρ ≥ 1`, the value of
`cl g(Φ_∞)` is at least `Λ = min_{k ≠ 0} (β_k + |k|(1 + θ))`, with `v(0) = ∞`.

## The statement

The minimum `Λ` is not a definition here. The statement says that `cl g(Φ_∞) ≠ 0` and
`v(cl g(Φ_∞)) < β_k + |k|(1 + θ)` for each `k ≠ 0` with `g^{[k]} ≠ 0` cannot both hold.

## Proof

This is the proof of the handbook. If the claim fails, then for `m` large the value of
`cl g(Φ_m)` is `v(cl g(Φ_∞))`, by Taylor's formula at `Φ_m` and part 2 of Theorem 3.18.26 for the
derivatives. The coefficients of the function of `P_m` are `M_m^{-p}` times
`cl g(Φ_m)` and `M_m^{|k|} g^{[k]}(Φ_m)` or their cleanings, and the values of the second ones
tend to `β_k + |k|(1 + θ)`. So (★★) holds at `P_m`, and this contradicts Proposition 3.17.3
(`KeepsRho.not_starStar`).

## Main results

* `IsCornerWord.not_hahnVal_hahnCl_lt`: Theorem 3.18.32, part 2.
-/

open MvPolynomial Filter Topology

namespace Singularity

namespace PlanarRuns

open CornerExp

section CleanValue

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {θ : ℝ} {k : Type*} [Field k] {w : ℕ → Bool}

theorem support_hahnCl_subset (p : ℕ) (x : HahnSeries (CornerExp θ) k) :
    (hahnCl p x).support ⊆ x.support := by
  intro r hr
  rw [HahnSeries.mem_support, coeff_hahnCl] at hr
  split_ifs at hr
  · exact absurd rfl hr
  · exact hr

/-- The cleaning does not lower the value. -/
theorem hahnVal_le_hahnCl (p : ℕ) (x : HahnSeries (CornerExp θ) k) :
    hahnVal θ k x ≤ hahnVal θ k (hahnCl p x) :=
  hahnVal_le_of_support_subset (support_hahnCl_subset p x)

omit [DecidableEq σ] in
theorem hahnVal_le_clCoeff (p : ℕ) (e : σ →₀ ℕ) (x : HahnSeries (CornerExp θ) k) :
    hahnVal θ k x ≤ hahnVal θ k (clCoeff p (hahnCl p) e x) := by
  unfold clCoeff
  split_ifs
  · exact hahnVal_le_hahnCl p x
  · exact le_rfl

/-- Theorem 3.18.32, part 2, for the Hahn model of a planar corner run over a perfect field,
with `θ` irrational and the coefficients in `𝔽`: if the run keeps `ρ ≥ 1`, then
`v(cl g(Φ_∞)) ≥ Λ`. In this form: `cl g(Φ_∞) ≠ 0` and `v(cl g(Φ_∞)) < β_n + |n|(1 + θ)` for each
`n ≠ 0` with `g^{[n]} ≠ 0` do not both hold. -/
theorem IsCornerWord.not_hahnVal_hahnCl_lt {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k) (hpl : IsPlanarRun t)
    (f : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring) {ρ₀ : ℕ∞}
    (hk : KeepsRho p w t (map (finiteTypeSubfield k hθ).toSubring.subtype f) ρ₀) :
    ¬ (hahnCl p (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
          (fun l => cornerLimit hw (fun j => t j l)) f) ≠ 0 ∧
        ∀ n, n ≠ 0 → hasse n f ≠ 0 →
          hahnVal θ k (hahnCl p (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
            (fun l => cornerLimit hw (fun j => t j l)) f)) <
          hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
            (fun l => cornerLimit hw (fun j => t j l)) (hasse n f)) +
            (((ord n : ℝ) * (1 + θ) : ℝ) : WithTop ℝ)) := by
  classical
  rintro ⟨hX, hlt⟩
  set Φi : σ → HahnSeries (CornerExp θ) k := fun l => cornerLimit hw (fun j => t j l) with hΦi
  set g := map (finiteTypeSubfield k hθ).toSubring.subtype f with hg
  have hE : ∀ e, eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi (hasse e f) =
      MvPolynomial.eval Φi (hasse e g) := by
    intro e
    rw [hg, hasse_map, MvPolynomial.eval_map]
  have hEm : ∀ m e, ((eval (cornerPointFT (w := w) hθ t m) (hasse e f) :
      (finiteTypeSubfield k hθ).toSubring) :
      HahnSeries (CornerExp θ) k) = MvPolynomial.eval (cornerPoint (w := w) t m) (hasse e g) := by
    intro m e
    rw [coe_eval_cornerPointFT, hg, hasse_map]
  have hE0 := hE 0
  rw [hasse_zero, hasse_zero] at hE0
  rw [hE0] at hX hlt
  simp only [hE] at hlt
  set X := MvPolynomial.eval Φi g with hXdef
  set V := hahnVal θ k (hahnCl p X) with hV
  have hVtop : V ≠ ⊤ := by
    rw [hV, Ne, AddValuation.top_iff]
    exact hX
  have hgf : ∀ e, hasse e g ≠ 0 → hasse e f ≠ 0 := by
    intro e he h0
    apply he
    rw [hg, hasse_map, h0, map_zero]
  set N := ∑ i, degreeOf i g with hNdef
  have hN : ∀ i, degreeOf i g ≤ N := fun i =>
    Finset.single_le_sum (f := fun i => degreeOf i g) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hbox : ∀ e, hasse e g ≠ 0 → e ∈ box σ N := by
    intro e he
    rw [mem_box]
    intro i
    by_contra hlt'
    exact he (hasse_eq_zero_of_lt hN (not_le.mp hlt'))
  set γ : ℕ → ℝ := fun m => val θ (expM w (m + 1) : CornerExp θ) with hγ
  have hγt : Tendsto γ atTop (𝓝 (1 + θ)) := hw.tendsto_val_expM.comp (tendsto_add_atTop_nat 1)
  have hδt : Tendsto (fun m => val θ (expM w m : CornerExp θ)) atTop (𝓝 (1 + θ)) :=
    hw.tendsto_val_expM
  -- The facts for `m` large.
  have hev : ∀ᶠ m in atTop, ∀ e ∈ box σ N, hasse e g ≠ 0 →
      hahnVal θ k (MvPolynomial.eval (cornerPoint (w := w) t m) (hasse e g)) =
          hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) ∧
        (e ≠ 0 → V < hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
            (((ord e : ℝ) * γ m : ℝ) : WithTop ℝ) ∧
          V < hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
            (((ord e : ℝ) * val θ (expM w m : CornerExp θ) : ℝ) : WithTop ℝ)) := by
    refine (Filter.eventually_all_finset _).mpr fun e _ => ?_
    by_cases he : hasse e g = 0
    · exact Filter.Eventually.of_forall fun _ h => absurd he h
    obtain ⟨-, -, h2e⟩ := statementDHolds_corner_frob hθ hw t hpl (hasse e f) (hgf e he)
    rw [← hΦi] at h2e
    have hA : ∀ᶠ m in atTop,
        hahnVal θ k (MvPolynomial.eval (cornerPoint (w := w) t m) (hasse e g)) =
          hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) := by
      filter_upwards [h2e] with m hm
      rw [hE, hEm] at hm
      exact map_eq_of_lt_map_sub _ hm
    have hB : ∀ᶠ m in atTop, e ≠ 0 →
        V < hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
            (((ord e : ℝ) * γ m : ℝ) : WithTop ℝ) ∧
          V < hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
            (((ord e : ℝ) * val θ (expM w m : CornerExp θ) : ℝ) : WithTop ℝ) := by
      by_cases he0 : e = 0
      · exact Filter.Eventually.of_forall fun _ h => absurd he0 h
      have := hlt e he0 (hgf e he)
      filter_upwards [eventually_lt_add hγt (ord e) this, eventually_lt_add hδt (ord e) this]
        with m hm1 hm2
      exact fun _ => ⟨hm1, hm2⟩
    filter_upwards [hA, hB] with m hm1 hm2
    exact fun _ => ⟨hm1, hm2⟩
  obtain ⟨m, hm⟩ := (eventually_atTop.mp hev)
  have hm := hm m le_rfl
  set φ : σ → HahnSeries (CornerExp θ) k := cornerPoint (w := w) t m with hφ
  -- Taylor's formula at `Φ_m`.
  have hT : X - MvPolynomial.eval φ g =
      ∑ e ∈ (box σ N).erase 0, MvPolynomial.eval φ (hasse e g) * ∏ i, (Φi i - φ i) ^ e i := by
    have h1 := eval₂_add_eq_sum (RingHom.id _) φ (fun i => Φi i - φ i) g hN
    have h2 : φ + (fun i => Φi i - φ i) = Φi := by
      funext i
      simp
    rw [h2] at h1
    have h0 : (0 : σ →₀ ℕ) ∈ box σ N := by
      rw [mem_box]
      intro i
      exact Nat.zero_le _
    rw [← Finset.add_sum_erase _ _ h0, hasse_zero] at h1
    simp only [Finsupp.coe_zero, Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one] at h1
    show eval₂ (RingHom.id _) Φi g - eval₂ (RingHom.id _) φ g =
      ∑ e ∈ (box σ N).erase 0, eval₂ (RingHom.id _) φ (hasse e g) * ∏ i, (Φi i - φ i) ^ e i
    rw [h1, add_sub_cancel_left]
  have hDelta : ∀ i, ((γ m : ℝ) : WithTop ℝ) ≤ hahnVal θ k (Φi i - φ i) := fun i =>
    le_hahnVal_cornerTail hw (fun j => t j i) m
  have hTv : V < hahnVal θ k (X - MvPolynomial.eval φ g) := by
    rw [hT]
    refine AddValuation.map_lt_sum _ hVtop fun e he => ?_
    obtain ⟨he0, heb⟩ := Finset.mem_erase.mp he
    by_cases hge : hasse e g = 0
    · rw [hge, map_zero, zero_mul, AddValuation.map_zero]
      exact lt_top_iff_ne_top.mpr hVtop
    obtain ⟨hA, hB⟩ := hm e heb hge
    have h1 := le_map_mul_prod_pow (hahnVal θ k) hDelta (MvPolynomial.eval φ (hasse e g)) e
    rw [hφ, hA] at h1
    exact (hB he0).1.trans_le h1
  -- The value of `cl g(Φ_m)`.
  have hcl : V < hahnVal θ k (hahnCl p X - hahnCl p (MvPolynomial.eval φ g)) := by
    rw [← map_sub]
    exact hTv.trans_le (hahnVal_le_hahnCl p _)
  have hVm : hahnVal θ k (hahnCl p (MvPolynomial.eval φ g)) = V :=
    map_eq_of_lt_map_sub _ hcl
  have hclm : hahnCl p (MvPolynomial.eval φ g) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hVm
    exact hVtop hVm.symm
  -- The criterion (★★) at `P_m`.
  have hstar : StarStar (cornerRunFn p w t g m) := by
    set a : WithTop ℝ := hahnVal θ k ((cornerM θ k w m ^ p)⁻¹) with ha
    have hatop : a ≠ ⊤ := by
      rw [ha, Ne, AddValuation.top_iff]
      exact inv_ne_zero (pow_ne_zero _ (HahnSeries.single_ne_zero one_ne_zero))
    have hc : ∀ e, (cornerRunFn p w t g m).coeff e = (cornerM θ k w m ^ p)⁻¹ *
        clCoeff p (hahnCl p) e (cornerM θ k w m ^ ord e * MvPolynomial.eval φ (hasse e g)) := by
      intro e
      rw [cornerRunFn_eq, coeff_restart]
    have hord0 : ord (0 : σ →₀ ℕ) = 0 := by simp [ord]
    have hc0 : (cornerRunFn p w t g m).coeff 0 = (cornerM θ k w m ^ p)⁻¹ *
        hahnCl p (MvPolynomial.eval φ g) := by
      rw [hc, hord0, pow_zero, one_mul, hasse_zero, clCoeff, ite_eq_left (fun i => by simp)]
    have hv0 : hahnVal θ k ((cornerRunFn p w t g m).coeff 0) = a + V := by
      rw [hc0, AddValuation.map_mul, hVm]
    refine ⟨?_, fun e he => ?_⟩
    · rw [hc0]
      exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (HahnSeries.single_ne_zero one_ne_zero)))
        hclm
    rw [hv0]
    by_cases hge : hasse e g = 0
    · rw [hc, hge, map_zero, mul_zero]
      unfold clCoeff
      simp only [map_zero, ite_self, mul_zero, AddValuation.map_zero]
      exact lt_top_iff_ne_top.mpr (WithTop.add_ne_top.mpr ⟨hatop, hVtop⟩)
    obtain ⟨hA, hB⟩ := hm e (hbox e hge) hge
    rw [hc, AddValuation.map_mul]
    refine (WithTop.add_lt_add_left hatop ?_).trans_le
      (add_le_add le_rfl (hahnVal_le_clCoeff p e _))
    rw [AddValuation.map_mul, AddValuation.map_pow, hahnVal_cornerM, hφ, hA, add_comm,
      ← WithTop.coe_nsmul, nsmul_eq_mul]
    exact (hB he).2
  exact hk.not_starStar hθ hw m hstar

end CleanValue

end PlanarRuns

end Singularity
