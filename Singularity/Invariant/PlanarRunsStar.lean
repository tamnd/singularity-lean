/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.PlanarRunsLeastTerm

/-!
# The criterion (★★) along a corner run

This file proves Proposition 3.17.3 of Volume 7 of the handbook in the Hahn model of
`PlanarRunsHahn`: if the criterion (★★) holds at a point `P_m` of a corner run, then the
residual factor `G` is a unit at each later point, for each choice of the later translations.
So `ρ = 0` at these points, and a run that keeps `ρ ≥ 1` has (★★) at no point.

## The model

* The function of `P_m` is `h = cornerRunFn p w t g m = M_m^{-p} g_m`. Its coefficient of
  `x^d` is `M_m^{-p}` times the coefficient of `g_m`, whose value is `w_d` of the handbook. The
  factor `M_m^{-p}` adds the same value to each `w_d`, so (★★) at `P_m` is `StarStar h`:
  `h_0 ≠ 0` and `v(h_0) < v(h_d)` for each `d ≠ 0`.
* The regularity of the function at the later point is a hypothesis, as in `KeepsRho`.

## Main results

* `IsCornerWord.rhoAt_eq_zero_of_starStar`: Proposition 3.17.3, first claim.
* `KeepsRho.not_starStar`: Proposition 3.17.3, second claim.
-/

open MvPolynomial

namespace Singularity

namespace PlanarRuns

open CornerExp

/-! ### The classes of the terms -/

section Classes

variable {θ : ℝ} {k : Type*} [Field k]

theorem classHom_nsmul_self (p : ℕ) (r : CornerExp θ) : classHom p (p • r) = 0 := by
  rw [map_nsmul]
  ext <;> simp

theorem coeff_hahnCl (p : ℕ) (x : HahnSeries (CornerExp θ) k) (r : CornerExp θ) :
    (hahnCl p x).coeff r = if classHom p r = 0 then 0 else x.coeff r := by
  rw [hahnCl_apply, HahnSeries.coeff_sub]
  change x.coeff r - (classPart p 0 x).coeff r = _
  rw [coeff_classPart]
  split_ifs <;> simp

/-- The class of an exponent is fixed by `y_m^a z_m^b` with `p ∣ a` and `p ∣ b`. -/
theorem classHom_expAt_eq_zero (p : ℕ) (w : ℕ → Bool) (m : ℕ) {a b : ℤ} (ha : (p : ℤ) ∣ a)
    (hb : (p : ℤ) ∣ b) : classHom p (expAt (θ := θ) w m a b) = 0 := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  change (((fst (expAt (θ := θ) w m _ _) : ℤ) : ZMod p), ((snd (expAt (θ := θ) w m _ _) : ℤ) :
    ZMod p)) = 0
  simp only [expAt, fst_mk, snd_mk]
  ext <;> simp

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The terms of the coefficient of `x^0` of a restart have a class other than `0`. -/
theorem classHom_ne_zero_of_mem_restart (p : ℕ) (φ : σ → HahnSeries (CornerExp θ) k)
    (a : CornerExp θ) (g : MvPolynomial σ (HahnSeries (CornerExp θ) k)) {r : CornerExp θ}
    (hr : r ∈ ((restart p (hahnCl p) φ (HahnSeries.single a 1) g).coeff 0).support) :
    classHom p r ≠ 0 := by
  intro h0
  rw [HahnSeries.mem_support, coeff_restart, HahnSeries.single_pow, one_pow,
    HahnSeries.inv_single, inv_one, HahnSeries.coeff_single_mul, one_mul, clCoeff,
    ite_eq_left (fun i => by simp), coeff_hahnCl, ite_eq_left] at hr
  · exact hr rfl
  · rw [sub_neg_eq_add, map_add, h0, classHom_nsmul_self, add_zero]

end Classes

/-! ### Divisibility and the cleaning -/

section Above

variable {θ : ℝ} {k : Type*} [Field k] {σ : Type*} [Fintype σ] {C : AddSubmonoid (CornerExp θ)}
  {a : CornerExp θ} {x : HahnSeries (CornerExp θ) k}

/-- The cleaning keeps a divisibility. -/
theorem Above.clCoeff {p : ℕ} (hx : Above C a x) (e : σ →₀ ℕ) :
    Above C a (clCoeff p (hahnCl p) e x) := by
  unfold PlanarRuns.clCoeff
  split_ifs
  · intro r hr
    apply hx r
    rw [HahnSeries.mem_support, coeff_hahnCl] at hr
    rw [HahnSeries.mem_support]
    split_ifs at hr
    · exact absurd rfl hr
    · exact hr
  · exact hx

/-- A series whose exponents all have a value larger than `val r` has no term at `r`. -/
theorem coeff_eq_zero_of_val_lt {r : CornerExp θ} (hx : ∀ s ∈ x.support, val θ r < val θ s) :
    x.coeff r = 0 := by
  by_contra h
  exact lt_irrefl _ (hx r h)

end Above

/-! ### Proposition 3.17.3 -/

section Star

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {θ : ℝ} {k : Type*} [Field k] {w : ℕ → Bool}

/-- The criterion (★★) for the function `h` of a point: `h_0 ≠ 0` and `v(h_0) < v(h_d)` for
each `d ≠ 0`. -/
def StarStar (h : MvPolynomial σ (HahnSeries (CornerExp θ) k)) : Prop :=
  h.coeff 0 ≠ 0 ∧ ∀ d, d ≠ 0 → hahnVal θ k (h.coeff 0) < hahnVal θ k (h.coeff d)

omit [Fintype σ] [DecidableEq σ] in
theorem val_nonneg_of_mem_cone (hw : IsCornerWord θ w) (m : ℕ) {r : CornerExp θ}
    (hr : r ∈ cone w m) : 0 ≤ val θ r := by
  rw [val_eq_coord w m]
  have hy := (hw.pos_y m).le
  have hz := (hw.pos_z m).le
  obtain ⟨h1, h2⟩ := hr
  have h1' : (0 : ℝ) ≤ coordY w m r := by exact_mod_cast h1
  have h2' : (0 : ℝ) ≤ coordZ w m r := by exact_mod_cast h2
  exact add_nonneg (mul_nonneg h1' hy) (mul_nonneg h2' hz)

omit [DecidableEq σ] in
/-- Proposition 3.17.3: if (★★) holds at `P_m`, then there is an `m₀` such that for each
`m' ≥ m₀` and each choice of the later translations, the residual factor at `P_{m'}` is a unit,
and so `ρ = 0` at `P_{m'}`. The function at `P_{m'}` is assumed regular. -/
theorem IsCornerWord.rhoAt_eq_zero_of_starStar {p : ℕ} [Fact p.Prime] [CharP k p]
    (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k)
    (g : MvPolynomial σ (HahnSeries (CornerExp θ) k)) (m : ℕ)
    (hreg : IsRegularAt w m (cornerRunFn p w t g m)) (hstar : StarStar (cornerRunFn p w t g m)) :
    ∃ m₀, m ≤ m₀ ∧ ∀ m' ≥ m₀, ∀ t' : ℕ → σ → k, (∀ j < m, t' j = t j) →
      IsRegularAt w m' (cornerRunFn p w t' g m') → rhoAt w m' (cornerRunFn p w t' g m') = 0 := by
  classical
  set h := cornerRunFn p w t g m with hh
  obtain ⟨h0, hlt⟩ := hstar
  set r₀ := (h.coeff 0).order with hr₀
  have hc0 : (h.coeff 0).coeff r₀ ≠ 0 := coeff_order_ne h0
  have hr₀s : r₀ ∈ (h.coeff 0).support := hc0
  -- The exponents of `h`.
  set S : Set (CornerExp θ) := {r | ∃ d, r ∈ (h.coeff d).support} with hS
  have hSc : ∀ q ∈ S, 0 ≤ coordY w m q ∧ 0 ≤ coordZ w m q := by
    rintro q ⟨d, hd⟩
    exact hreg d q hd
  have hval : ∀ d, d ≠ 0 → ∀ r ∈ (h.coeff d).support, val θ r₀ < val θ r := by
    intro d hd r hr
    have h1 := (hlt d hd).trans_le (hahnVal_le_of_mem hr)
    rw [hahnVal_of_ne h0] at h1
    exact_mod_cast h1
  have hmin : ∀ q ∈ S, q ≠ r₀ → val θ r₀ < val θ q := by
    rintro q ⟨d, hd⟩ hq
    by_cases hd0 : d = 0
    · subst hd0
      exact lt_of_le_of_ne (val_mono (HahnSeries.order_le_of_coeff_ne_zero hd))
        fun h' => hq ((val_injective hθ) h').symm
    · exact hval d hd0 q hd
  have hclass : classHom p r₀ ≠ 0 := by
    have hr := hr₀s
    rw [hh, cornerRunFn_eq] at hr
    exact classHom_ne_zero_of_mem_restart p _ (expM w m) g hr
  obtain ⟨m₀, hm₀, hdom⟩ := hw.dominance m hSc hmin
  refine ⟨m₀, hm₀, fun m' hm' t' ht' hreg' => ?_⟩
  have hmm' : m ≤ m' := hm₀.trans hm'
  -- The point `P_m` does not depend on the later translations.
  have hpt : ∀ i, cornerPoint (θ := θ) (w := w) t' m i = cornerPoint (w := w) t m i := by
    intro i
    rw [cornerPoint, cornerPoint, cornerSum_eq, cornerSum_eq]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ht' j (Finset.mem_range.mp hj)]
  have hh' : cornerRunFn p w t' g m = h := by
    rw [hh, cornerRunFn_eq, cornerRunFn_eq]
    simp only [hpt]
  -- The step from `P_m` to `P_{m'}`.
  set μ : CornerExp θ := expM w m' - expM w m with hμ
  have hμc : μ ∈ cone w m' := expM_sub_mem_cone w hmm' le_rfl
  have hM : cornerM θ k w m ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have hstep : cornerRunFn p w t' g m' = restart p (hahnCl p)
      (fun i => (cornerPoint (w := w) t' m' i - cornerPoint (w := w) t' m i) *
        HahnSeries.single (-expM w m) 1) (HahnSeries.single μ 1) h := by
    rw [cornerRunFn_eq p w t' g m', ← hh', cornerRunFn_eq p w t' g m,
      restart_restart (Fact.out : p.Prime) isClassPart_hahn]
    have hinv : HahnSeries.single (-expM w m) (1 : k) = (cornerM θ k w m)⁻¹ := by
      rw [cornerM, HahnSeries.inv_single, inv_one]
    congr 1
    · funext i
      rw [hinv, mul_comm _ (cornerM θ k w m)⁻¹, ← mul_assoc, mul_inv_cancel₀ hM, one_mul,
        add_sub_cancel]
    · rw [cornerM, cornerM, HahnSeries.single_mul_single, one_mul, hμ, add_sub_cancel]
  set φ' : σ → HahnSeries (CornerExp θ) k :=
    fun i => (cornerPoint (w := w) t' m' i - cornerPoint (w := w) t' m i) *
      HahnSeries.single (-expM w m) 1 with hφ'
  -- The divisibility at `P_{m'}`.
  have hA : ∀ d, Above (cone w m') r₀ (h.coeff d) := by
    intro d r hr
    by_cases hrr : r = r₀
    · rw [hrr, sub_self]
      exact zero_mem _
    · obtain ⟨h1, h2⟩ := hdom m' hm' r ⟨d, hr⟩ hrr
      exact ⟨h1.le, h2.le⟩
  have hφA : ∀ i, Above (cone w m') 0 (φ' i) := by
    intro i
    have h1 : Above (cone (θ := θ) w m') (expM w m)
        (cornerPoint (w := w) t' m' i - cornerPoint (w := w) t' m i) := by
      rw [cornerPoint, cornerPoint, cornerSum_eq, cornerSum_eq, ← Finset.sum_Ico_eq_sub _ hmm']
      refine Above.sum _ fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      exact (Above.single _ _).mono (expM_sub_mem_cone w (by omega) (by omega))
    have h2 := h1.mul (Above.single (C := cone w m') (-expM w m) (1 : k))
    rwa [add_neg_cancel] at h2
  set h' := cornerRunFn p w t' g m' with hh'def
  have hcoeff : ∀ d, h'.coeff d = HahnSeries.single (-(p • μ)) 1 *
      clCoeff p (hahnCl p) d (HahnSeries.single (ord d • μ) 1 *
        MvPolynomial.eval φ' (hasse d h)) := by
    intro d
    rw [hstep, coeff_restart]
    simp only [HahnSeries.single_pow, one_pow, HahnSeries.inv_single, inv_one]
  set r' : CornerExp θ := r₀ + -(p • μ) with hr'
  have hA' : ∀ d, Above (cone w m') r' (h'.coeff d) := by
    intro d
    rw [hcoeff, hr', add_comm r₀]
    refine (Above.single _ _).mul (Above.clCoeff ?_ d)
    have h1 : Above (cone w m') r₀ (MvPolynomial.eval φ' (hasse d h)) := by
      refine Above.eval (a := 0) hφA fun e => ?_
      rw [smul_zero, sub_zero, coeff_hasse]
      exact (hA _).nsmul _
    have h2 := (Above.single (C := cone w m') (ord d • μ) (1 : k)).mul h1
    refine h2.mono ?_
    rw [add_sub_cancel_right]
    exact nsmul_mem hμc _
  -- The term of least value is kept.
  have hE0 : (MvPolynomial.eval φ' h).coeff r₀ = (h.coeff 0).coeff r₀ := by
    rw [MvPolynomial.eval_eq', HahnSeries.coeff_sum, Finset.sum_eq_single 0]
    · simp
    · intro d _ hd
      refine coeff_eq_zero_of_val_lt fun s hs => ?_
      obtain ⟨u, hu, v, hv, rfl⟩ := HahnSeries.support_mul_subset hs
      have hv' := Above.prod (C := cone w m') Finset.univ (c := fun _ => (0 : CornerExp θ))
        (fun i _ => (hφA i).pow (d i)) v hv
      simp only [Finset.sum_const_zero, sub_zero] at hv'
      rw [val_add]
      linarith [hval d hd u hu, val_nonneg_of_mem_cone hw m' hv']
    · intro h0'
      rw [MvPolynomial.notMem_support_iff.mp h0', zero_mul, HahnSeries.coeff_zero]
  have hord0 : ord (0 : σ →₀ ℕ) = 0 := by simp [ord]
  have hcr' : (h'.coeff 0).coeff r' = (h.coeff 0).coeff r₀ := by
    rw [hcoeff, hr', HahnSeries.coeff_single_mul_add, one_mul, hord0, zero_smul,
      HahnSeries.single_zero_one, one_mul, hasse_zero, clCoeff, ite_eq_left (fun i => by simp),
      coeff_hahnCl, ite_eq_right hclass, hE0]
  have hr's : r' ∈ (h'.coeff 0).support := by
    rw [HahnSeries.mem_support, hcr']
    exact hc0
  have h0' : (0 : σ →₀ ℕ) ∈ h'.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0''
    rw [h0''] at hr's
    simp at hr's
  have hclass' : classHom p r' ≠ 0 := by
    rw [hr', map_add, map_neg, classHom_nsmul_self, neg_zero, add_zero]
    exact hclass
  obtain ⟨hY, hZ⟩ := hreg' 0 r' hr's
  -- The monomial factor at `P_{m'}` is the term `r'`.
  have hdivY : (divY w m' h' : ℤ) = coordY w m' r' := by
    have key : (⨅ q ∈ h'.support, ⨅ r ∈ (h'.coeff q).support,
        (((coordY w m' r).toNat : ℕ) : ℕ∞)) = (((coordY w m' r').toNat : ℕ) : ℕ∞) := by
      refine le_antisymm ((iInf₂_le 0 h0').trans (iInf₂_le r' hr's)) ?_
      refine le_iInf₂ fun q _ => le_iInf₂ fun r hr => ?_
      have h1 := (hA' q r hr).1
      have h2 := coordY_add w m' (r - r') r'
      rw [sub_add_cancel] at h2
      exact_mod_cast Int.toNat_le_toNat (by linarith)
    rw [divY, key, ENat.toNat_natCast, Int.toNat_of_nonneg hY]
  have hdivZ : (divZ w m' h' : ℤ) = coordZ w m' r' := by
    have key : (⨅ q ∈ h'.support, ⨅ r ∈ (h'.coeff q).support,
        (((coordZ w m' r).toNat : ℕ) : ℕ∞)) = (((coordZ w m' r').toNat : ℕ) : ℕ∞) := by
      refine le_antisymm ((iInf₂_le 0 h0').trans (iInf₂_le r' hr's)) ?_
      refine le_iInf₂ fun q _ => le_iInf₂ fun r hr => ?_
      have h1 := (hA' q r hr).2
      have h2 := coordZ_add w m' (r - r') r'
      rw [sub_add_cancel] at h2
      exact_mod_cast Int.toNat_le_toNat (by linarith)
    rw [divZ, key, ENat.toNat_natCast, Int.toNat_of_nonneg hZ]
  -- The residual factor is a unit.
  have hG : ((resid w m' h').coeff 0).coeff 0 ≠ 0 := by
    have he : expAt w m' (-(divY w m' h' : ℤ)) (-(divZ w m' h' : ℤ)) = -r' := by
      have hy := coordY_add w m' r' (-r')
      have hz := coordZ_add w m' r' (-r')
      rw [add_neg_cancel, coordY_zero] at hy
      rw [add_neg_cancel, coordZ_zero] at hz
      rw [hdivY, hdivZ]
      conv_rhs => rw [← expAt_coord w m' (-r')]
      congr 1 <;> linarith
    rw [resid, coeff_C_mul, he, HahnSeries.coeff_single_mul, one_mul, zero_sub, neg_neg, hcr']
    exact hc0
  have hnd : ¬ (p ∣ divY w m' h' ∧ p ∣ divZ w m' h') := by
    rintro ⟨hy, hz⟩
    apply hclass'
    rw [← expAt_coord w m' r', ← hdivY, ← hdivZ]
    exact classHom_expAt_eq_zero p w m' (Int.natCast_dvd_natCast.mpr hy)
      (Int.natCast_dvd_natCast.mpr hz)
  by_cases hy : p ∣ divY w m' h'
  · exact rhoAt_eq_zero_of_unit_z hG fun hz => hnd ⟨hy, hz⟩
  · exact rhoAt_eq_zero_of_unit_y hG hy

omit [DecidableEq σ] in
/-- Proposition 3.17.3, second claim: (★★) fails at each point of a corner run that keeps
`ρ ≥ 1`. -/
theorem KeepsRho.not_starStar {p : ℕ} [Fact p.Prime] [CharP k p] (hθ : Irrational θ)
    (hw : IsCornerWord θ w) {t : ℕ → σ → k} {g : MvPolynomial σ (HahnSeries (CornerExp θ) k)}
    {ρ₀ : ℕ∞} (hk : KeepsRho p w t g ρ₀) (m : ℕ) : ¬ StarStar (cornerRunFn p w t g m) := by
  intro hs
  obtain ⟨m₀, -, h⟩ := hw.rhoAt_eq_zero_of_starStar hθ t g m (hk.regular m) hs
  have h1 := h m₀ le_rfl t (fun _ _ => rfl) (hk.regular m₀)
  rw [hk.rho_eq m₀] at h1
  have h2 := hk.one_le
  rw [h1] at h2
  exact absurd h2 (by simp)

end Star

end PlanarRuns

end Singularity
