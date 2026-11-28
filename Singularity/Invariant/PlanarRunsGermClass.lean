/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.PlanarRunsCleanValue

/-!
# Corollary 3.18.33: the class of the germ monomial

This file proves Corollary 3.18.33 of Volume 7 of the handbook in the Hahn model of
`PlanarRunsHahn`: for a planar corner run that keeps `ρ ≥ 1`, if `e ≥ 1` and the derivative
`g^{[p^e e_i]}` attains `Λ`, then the monomial `ν_e` of least value of `g^{[p^e e_i]}(Φ_∞)` has
the class `0`.

## Proof

This is the proof of the handbook. Take `m` large, so that the derivatives have the same values at
`Φ_m` and at `Φ_∞` (Step 2 of the proof of Theorem 3.18.26). Taylor's formula at `Φ_m` splits
`g(Φ_∞)` into `g(Φ_m)`, the terms of `p`-power order and a rest. Step 1 of that proof (Lucas)
gives the rest a value more than `Λ`. In Step 4 with `e_0 = e`, a term
`ν_e t_j M_{j+1}^{p^e}` of the germ of order `p^e` is a term of `g(Φ_∞)` of value less than `Λ`
(`exists_coeff_germ_ne_zero`). The exponent `p^e M_{j+1}` has the class `0`, so this term has the
class of `ν_e`. If this class is not `0`, then `cl g(Φ_∞)` has a term of value less than `Λ`, and
this contradicts Theorem 3.18.32, part 2 (`IsCornerWord.not_hahnVal_hahnCl_lt`).

## Main results

* `exists_coeff_germ_ne_zero`: Step 4 of the proof of Theorem 3.18.26 with a given index of least
  value.
* `IsCornerWord.classHom_germ_eq_zero`: Corollary 3.18.33.
-/

open MvPolynomial Filter Topology

namespace Singularity

namespace PlanarRuns

open CornerExp

section GermClass

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {θ : ℝ} {k : Type*} [Field k] {w : ℕ → Bool}

omit [DecidableEq σ] in
/-- Step 4 of the proof of Theorem 3.18.26 for a planar corner run over a perfect field, with a
given index `(i_0, e_0)` of least value: for `α_{i, e}` and `c` of finite type, the term at
`ν_0 + p^{e_0} M_{j+1}` of `c + Σ_{i, e} α_{i, e} Δ_{m, i}^{p^e}` is not zero for some `j`, with
`ν_0` the order of `α_{i_0, e_0}`. Its value is less than `v(α_{i_0, e_0}) + p^{e_0}(1 + θ)`. -/
theorem exists_coeff_germ_ne_zero {p : ℕ} [hp : Fact p.Prime] [CharP k p]
    [PerfectRing k p] (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k)
    (hpl : IsPlanarRun t) (m n : ℕ) (α : σ × ℕ → HahnSeries (CornerExp θ) k)
    (hα : ∀ x, IsFiniteType (α x)) (c : HahnSeries (CornerExp θ) k) (hc : IsFiniteType c)
    (i0 : σ) (e0 : ℕ) (hx0P : (i0, e0) ∈ (Finset.univ : Finset σ) ×ˢ Finset.range n)
    (hx00 : α (i0, e0) ≠ 0)
    (hmin0 : ∀ x ∈ (Finset.univ : Finset σ) ×ˢ Finset.range n, α x ≠ 0 →
      val θ (α (i0, e0)).order + ((p ^ e0 : ℕ) : ℝ) * (1 + θ) ≤
        val θ (α x).order + ((p ^ x.2 : ℕ) : ℝ) * (1 + θ)) :
    ∃ j, (c + ∑ x ∈ (Finset.univ : Finset σ) ×ˢ Finset.range n,
        α x * (cornerLimit hw (fun j => t j x.1) - cornerPoint (w := w) t m x.1) ^ (p ^ x.2)).coeff
          ((α (i0, e0)).order + p ^ e0 • expM w (j + 1)) ≠ 0 ∧
      val θ ((α (i0, e0)).order + p ^ e0 • expM w (j + 1)) <
        val θ (α (i0, e0)).order + ((p ^ e0 : ℕ) : ℝ) * (1 + θ) := by
  classical
  set P := (Finset.univ : Finset σ) ×ˢ Finset.range n with hP
  set X := c + ∑ x ∈ P,
    α x * (cornerLimit hw (fun j => t j x.1) - cornerPoint (w := w) t m x.1) ^ (p ^ x.2) with hX
  have hpos : ∀ e, 0 < p ^ e := fun e => pow_pos hp.out.pos e
  -- the index of least value
  set ν0 := (α (i0, e0)).order with hν0
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = val θ ν0 + ((p ^ e0 : ℕ) : ℝ) * (1 + θ) := ⟨_, rfl⟩
  have hmin' : ∀ x ∈ P, α x ≠ 0 →
      L ≤ val θ (α x).order + ((p ^ x.2 : ℕ) : ℝ) * (1 + θ) := fun x hx h => by
    rw [hL]
    exact hmin0 x hx h
  -- the exponents `r_j = ν_0 + p^{e_0} M_{j+1}`
  set r : ℕ → CornerExp θ := fun j => ν0 + p ^ e0 • expM w (j + 1) with hr
  have hq0 : (0 : ℝ) < ((p ^ e0 : ℕ) : ℝ) := by exact_mod_cast hpos e0
  have hval_r : ∀ j, val θ (r j) < L := by
    intro j
    simp only [hr, val_add, val_nsmul]
    rw [hL]
    have := mul_lt_mul_of_pos_left (val_expM_lt hw (j + 1)) hq0
    linarith
  have hr_inj : Function.Injective r := fun a b h =>
    smul_expM_injective hw (hpos e0) (add_left_cancel h)
  -- the bad indices
  set Bad : Set ℕ := ⋃ x ∈ (P : Set (σ × ℕ)),
    ⋃ s ∈ {s | s ∈ belowSet L (α x) ∧ (e0 ≠ x.2 ∨ s - ν0 ≠ 0)},
      {j | ∃ j', p ^ e0 • (expM w (j + 1) : CornerExp θ) = (s - ν0) + p ^ x.2 • expM w (j' + 1)}
    with hBad
  have hBadfin : Bad.Finite :=
    Set.Finite.biUnion P.finite_toSet fun x _ =>
      Set.Finite.biUnion ((hα x L).subset fun s hs => hs.1) fun s hs =>
        finite_smul_expM_eq hθ hw hp.out (s - ν0) hs.2
  have hCfin : (r ⁻¹' belowSet L c).Finite := (hc L).preimage hr_inj.injOn
  obtain ⟨B, hB⟩ := (hBadfin.union hCfin).bddAbove
  -- the `p^{e_0}`-th roots of the coefficients of least value
  set a : σ → k := fun i => (α (i, e0)).coeff ν0 with ha
  set b : σ → k := fun i => (iterateFrobeniusEquiv k p e0).symm (a i) with hb
  have hab : ∀ i, b i ^ p ^ e0 = a i := fun i => by
    rw [hb]
    dsimp only
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  have hb0 : b ≠ 0 := by
    intro h
    have h1 := hab i0
    rw [h, Pi.zero_apply, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at h1
    exact coeff_order_ne hx00 h1.symm
  -- a good index `j`
  obtain ⟨j, hjt, hjm, hjB⟩ := ((hpl.frequently hb0).and_eventually
    ((eventually_ge_atTop m).and (eventually_gt_atTop B))).exists
  have hjBad : j ∉ Bad := fun h => absurd (hB (Set.mem_union_left _ h)) (not_le.mpr hjB)
  have hjC : j ∉ r ⁻¹' belowSet L c := fun h =>
    absurd (hB (Set.mem_union_right _ h)) (not_le.mpr hjB)
  refine ⟨j, ?_, by rw [← hL]; exact hval_r j⟩
  show X.coeff (r j) ≠ 0
  -- a truncation index `J`
  have hJev : ∀ᶠ J in atTop, ∀ x ∈ P, α x ≠ 0 →
      val θ (r j) < val θ (α x).order + ((p ^ x.2 : ℕ) : ℝ) * val θ (expM w (J + 1)) := by
    rw [Filter.eventually_all_finset]
    intro x hx
    by_cases hx0' : α x = 0
    · exact Eventually.of_forall fun _ h => absurd hx0' h
    have hlim : Tendsto
        (fun J => val θ (α x).order + ((p ^ x.2 : ℕ) : ℝ) * val θ (expM w (J + 1) : CornerExp θ))
        atTop (𝓝 (val θ (α x).order + ((p ^ x.2 : ℕ) : ℝ) * (1 + θ))) :=
      ((hw.tendsto_val_expM.comp (tendsto_add_atTop_nat 1)).const_mul _).const_add _
    filter_upwards [hlim.eventually_const_lt ((hval_r j).trans_le (hmin' x hx hx0'))]
      with J hJ _
    exact hJ
  obtain ⟨J, hJ, hJj⟩ := (hJev.and (eventually_gt_atTop j)).exists
  have hmJ : m ≤ J := by omega
  -- the coefficient of `r_j`
  have hpow : ∀ x : σ × ℕ,
      (cornerLimit hw (fun j => t j x.1) - cornerPoint (w := w) t m x.1) ^ (p ^ x.2) =
        ∑ j' ∈ Finset.Ico m J,
          HahnSeries.single (p ^ x.2 • (expM w (j' + 1) : CornerExp θ)) (t j' x.1 ^ p ^ x.2) +
        (cornerLimit hw (fun j => t j x.1) - cornerPoint (w := w) t J x.1) ^ (p ^ x.2) :=
    fun x => cornerTail_pow hw (fun j => t j x.1) x.2 hmJ
  have hcoeffX : X.coeff (r j) = c.coeff (r j) + ∑ x ∈ P,
      (∑ j' ∈ Finset.Ico m J,
          (α x).coeff (r j - p ^ x.2 • expM w (j' + 1)) * t j' x.1 ^ p ^ x.2 +
        (α x * (cornerLimit hw (fun j => t j x.1) - cornerPoint (w := w) t J x.1) ^ (p ^ x.2)).coeff
          (r j)) := by
    rw [hX, HahnSeries.coeff_add, HahnSeries.coeff_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hpow x, mul_add, HahnSeries.coeff_add, coeff_mul_sum_single]
  have hc0 : c.coeff (r j) = 0 := by
    by_contra h
    exact hjC (show r j ∈ belowSet L c from ⟨h, hval_r j⟩)
  have htail0 : ∀ x ∈ P,
      (α x * (cornerLimit hw (fun j => t j x.1) - cornerPoint (w := w) t J x.1) ^ (p ^ x.2)).coeff
        (r j) = 0 := by
    intro x hx
    by_cases hx0' : α x = 0
    · simp [hx0']
    by_contra h
    have h1 := val_le_of_mem_support_mul_pow (le_hahnVal_cornerTail hw (fun j => t j x.1) J)
      hx0' (p ^ x.2) h
    have h2 := hJ x hx hx0'
    push_cast at h1 h2
    linarith
  have hterm : ∀ x ∈ P, ∀ j' ∈ Finset.Ico m J, ¬ (x.2 = e0 ∧ j' = j) →
      (α x).coeff (r j - p ^ x.2 • expM w (j' + 1)) = 0 := by
    intro x hx j' _ hne
    by_contra h
    have hsv : val θ (r j - p ^ x.2 • expM w (j' + 1)) < L := by
      have h1 := val_expM_nonneg hw (j' + 1)
      have h2 := hval_r j
      have h3 : (0 : ℝ) ≤ ((p ^ x.2 : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [val_sub, val_nsmul]
      nlinarith
    have heq : p ^ e0 • (expM w (j + 1) : CornerExp θ) =
        (r j - p ^ x.2 • expM w (j' + 1) - ν0) + p ^ x.2 • expM w (j' + 1) := by
      simp only [hr]
      abel
    by_cases hd : e0 ≠ x.2 ∨ r j - p ^ x.2 • expM w (j' + 1) - ν0 ≠ 0
    · apply hjBad
      rw [hBad]
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      exact ⟨x, hx, _, ⟨⟨h, hsv⟩, hd⟩, j', heq⟩
    · push Not at hd
      obtain ⟨he, hs0⟩ := hd
      rw [hs0, zero_add, ← he] at heq
      exact hne ⟨he.symm, (smul_expM_injective hw (hpos e0) heq).symm⟩
  have hsum : (∑ x ∈ P, ∑ j' ∈ Finset.Ico m J,
      (α x).coeff (r j - p ^ x.2 • expM w (j' + 1)) * t j' x.1 ^ p ^ x.2) =
        ∑ i, a i * t j i ^ p ^ e0 := by
    have he0n : e0 ∈ Finset.range n := (Finset.mem_product.mp hx0P).2
    rw [hP, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single e0]
    · rw [Finset.sum_eq_single j]
      · simp only [hr, ha, add_sub_cancel_right]
      · intro j' hj' hne
        rw [hterm (i, e0) (Finset.mem_product.mpr ⟨Finset.mem_univ _, he0n⟩) j' hj'
          (fun h => hne h.2), zero_mul]
      · intro h
        exact absurd (Finset.mem_Ico.mpr ⟨hjm, hJj⟩) h
    · intro e he hne
      refine Finset.sum_eq_zero fun j' hj' => ?_
      rw [hterm (i, e) (Finset.mem_product.mpr ⟨Finset.mem_univ _, he⟩) j' hj'
        (fun h => hne h.1), zero_mul]
    · intro h
      exact absurd he0n h
  have hfrob : ∑ i, a i * t j i ^ p ^ e0 = (∑ i, b i * t j i) ^ p ^ e0 := by
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, hab]
  rw [hcoeffX, hc0, zero_add, Finset.sum_add_distrib,
    Finset.sum_eq_zero htail0, add_zero, hsum, hfrob]
  exact pow_ne_zero _ hjt

omit [DecidableEq σ] in
/-- Corollary 3.18.33 for the Hahn model of a planar corner run over a perfect field, with `θ`
irrational and the coefficients in `𝔽`: if the run keeps `ρ ≥ 1`, `e ≥ 1`, and the derivative
`g^{[p^e e_i]}` attains `Λ`, that is `β_{p^e e_i} + p^e (1 + θ) ≤ β_n + |n|(1 + θ)` for each
`n ≠ 0` with `g^{[n]} ≠ 0`, then the order `ν_e` of `g^{[p^e e_i]}(Φ_∞)` has the class `0`. -/
theorem IsCornerWord.classHom_germ_eq_zero {p : ℕ} [hp : Fact p.Prime] [CharP k p]
    [PerfectRing k p] (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k)
    (hpl : IsPlanarRun t) (f : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring) {ρ₀ : ℕ∞}
    (hk : KeepsRho p w t (map (finiteTypeSubfield k hθ).toSubring.subtype f) ρ₀)
    (i0 : σ) {e0 : ℕ} (he0 : 1 ≤ e0) (hs0 : hasse (Finsupp.single i0 (p ^ e0)) f ≠ 0)
    (hmin : ∀ n, n ≠ 0 → hasse n f ≠ 0 →
      hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
          (fun l => cornerLimit hw (fun j => t j l)) (hasse (Finsupp.single i0 (p ^ e0)) f)) +
          ((((p ^ e0 : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) ≤
        hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
          (fun l => cornerLimit hw (fun j => t j l)) (hasse n f)) +
          (((ord n : ℝ) * (1 + θ) : ℝ) : WithTop ℝ)) :
    classHom p (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
      (fun l => cornerLimit hw (fun j => t j l))
        (hasse (Finsupp.single i0 (p ^ e0)) f)).order = 0 := by
  classical
  by_contra hcl
  apply IsCornerWord.not_hahnVal_hahnCl_lt hθ hw t hpl f hk
  set Φi : σ → HahnSeries (CornerExp θ) k := fun l => cornerLimit hw (fun j => t j l) with hΦi
  set g := map (finiteTypeSubfield k hθ).toSubring.subtype f with hg
  set s0 := Finsupp.single i0 (p ^ e0) with hs0def
  set A := eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi (hasse s0 f) with hAdef
  set ν0 := A.order with hν0
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
  rw [hE0]
  simp only [hE]
  set X := MvPolynomial.eval Φi g with hXdef
  have hgf : ∀ e, hasse e g ≠ 0 → hasse e f ≠ 0 := by
    intro e he h0
    apply he
    rw [hg, hasse_map, h0, map_zero]
  have hfg : ∀ e, hasse e f ≠ 0 → hasse e g ≠ 0 := by
    intro e he h0
    apply he
    apply map_injective (finiteTypeSubfield k hθ).toSubring.subtype Subtype.val_injective
    rw [map_zero, ← hasse_map, ← hg]
    exact h0
  -- the value `Λ`
  have hA0 : A ≠ 0 := (statementDHolds_corner_frob hθ hw t hpl _ hs0).1
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = val θ ν0 + ((p ^ e0 : ℕ) : ℝ) * (1 + θ) := ⟨_, rfl⟩
  have hLW : ((L : ℝ) : WithTop ℝ) =
      hahnVal θ k A + ((((p ^ e0 : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) := by
    rw [hL, hahnVal_of_ne hA0, WithTop.coe_add]
  have hLle : ∀ n, n ≠ 0 → hasse n f ≠ 0 → ((L : ℝ) : WithTop ℝ) ≤
      hahnVal θ k (MvPolynomial.eval Φi (hasse n g)) +
        (((ord n : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) := by
    intro n hn hnf
    rw [hLW, ← hE]
    exact hmin n hn hnf
  suffices H : ∃ r, X.coeff r ≠ 0 ∧ val θ r < L ∧ classHom p r ≠ 0 by
    obtain ⟨r, hr, hrL, hrc⟩ := H
    have hcr : (hahnCl p X).coeff r ≠ 0 := by
      rw [coeff_hahnCl]
      simpa [hrc] using hr
    have hv : hahnVal θ k (hahnCl p X) < ((L : ℝ) : WithTop ℝ) :=
      (hahnVal_le_of_mem ((HahnSeries.mem_support _ _).mpr hcr)).trans_lt (WithTop.coe_lt_coe.mpr hrL)
    refine ⟨fun h0 => hcr (by rw [h0, HahnSeries.coeff_zero]), fun n hn hnf => ?_⟩
    exact hv.trans_le (hLle n hn hnf)
  -- the box of exponents
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
  set P : Finset (σ × ℕ) := (Finset.univ : Finset σ) ×ˢ Finset.range (N + 1) with hP
  set s : σ × ℕ → σ →₀ ℕ := fun x => Finsupp.single x.1 (p ^ x.2) with hs
  have hs0' : ∀ x, s x ≠ 0 := fun x => by
    simp only [hs, ne_eq, Finsupp.single_eq_zero]
    exact pow_ne_zero _ hp.out.ne_zero
  have hos : ∀ x, ord (s x) = p ^ x.2 := fun x => ord_single _ _
  -- Step 1 (Lucas): the other derivatives have a value more than `Λ`
  have hstep1 : ∀ e, e ≠ 0 → hasse e f ≠ 0 → (∀ x ∈ P, e ≠ s x) →
      ((L : ℝ) : WithTop ℝ) <
        hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi (hasse e f)) +
          (((ord e : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) := by
    intro e he hef hns
    obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero he
    obtain ⟨a, ha, hnd⟩ := exists_pow_not_dvd_choose hp.out hi
    have hmem : (i, a) ∈ P := by
      rw [hP, Finset.mem_product, Finset.mem_range]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 : a < p ^ a := Nat.lt_pow_self hp.out.one_lt
      have h2 := le_degreeOf_of_hasse_ne_zero (hfg e hef) i
      have h3 := hN i
      omega
    have hEk : eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi (hasse e f) ≠ 0 :=
      (statementDHolds_corner_frob hθ hw t hpl _ hef).1
    have hc : hahnVal θ k ((e i).choose (p ^ a) : HahnSeries (CornerExp θ) k) = 0 :=
      (hahnVal θ k).map_natCast_eq_zero hp.out hnd
    have hc0 : ((e i).choose (p ^ a) : HahnSeries (CornerExp θ) k) ≠ 0 := by
      intro h0
      rw [h0, AddValuation.map_zero] at hc
      exact WithTop.top_ne_zero hc
    have heval : eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi
        (hasse (e - s (i, a)) (hasse (s (i, a)) f)) =
        ((e i).choose (p ^ a) : HahnSeries (CornerExp θ) k) *
          eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi (hasse e f) := by
      rw [hs]
      dsimp only
      rw [hasse_sub_hasse_single e ha]
      simp [nsmul_eq_mul]
    have hpoly : hasse (e - s (i, a)) (hasse (s (i, a)) f) ≠ 0 := by
      intro h0
      rw [h0, eval₂_zero] at heval
      exact mul_ne_zero hc0 hEk heval.symm
    have hsx : hasse (s (i, a)) f ≠ 0 := fun h0 => hpoly (by rw [h0, hasse_zero_right])
    have hval : hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi
        (hasse (e - s (i, a)) (hasse (s (i, a)) f))) =
        hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi (hasse e f)) := by
      rw [heval, AddValuation.map_mul, hc, zero_add]
    have hle : s (i, a) ≤ e := Finsupp.single_le_iff.mpr ha
    have hord := ord_sub_single' e ha
    have hj : e - s (i, a) ≠ 0 := by
      intro h0
      apply hns (i, a) hmem
      rw [← tsub_add_cancel_of_le hle, h0, zero_add]
    have h3 := (statementDHolds_corner_frob hθ hw t hpl _ hsx).2.1 (e - s (i, a)) hj hpoly
    rw [← hΦi, hval] at h3
    have h4 := hmin (s (i, a)) (hs0' (i, a)) hsx
    rw [hos (i, a)] at h4
    have hreal : ((ord e : ℝ) * (1 + θ) : ℝ) =
        ((ord (e - Finsupp.single i (p ^ a)) : ℝ) * (1 + θ) : ℝ) +
          (((p ^ a : ℕ) : ℝ) * (1 + θ) : ℝ) := by
      rw [← hord]
      push_cast
      ring
    calc ((L : ℝ) : WithTop ℝ)
        = hahnVal θ k A + ((((p ^ e0 : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) := hLW
      _ ≤ hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi
            (hasse (s (i, a)) f)) + ((((p ^ a : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) := h4
      _ < hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi (hasse e f)) +
            (((ord (e - s (i, a)) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) +
            ((((p ^ a : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) :=
          WithTop.add_lt_add_right WithTop.coe_ne_top h3
      _ = hahnVal θ k (eval₂ (finiteTypeSubfield k hθ).toSubring.subtype Φi (hasse e f)) +
            (((ord e : ℝ) * (1 + θ) : ℝ) : WithTop ℝ) := by
          rw [hreal, WithTop.coe_add, add_assoc]
  -- Step 2: the facts for `m` large
  set γ : ℕ → ℝ := fun m => val θ (expM w (m + 1) : CornerExp θ) with hγ
  have hγt : Tendsto γ atTop (𝓝 (1 + θ)) := hw.tendsto_val_expM.comp (tendsto_add_atTop_nat 1)
  have hev : ∀ᶠ m in atTop, ∀ e ∈ box σ N, hasse e g ≠ 0 →
      hahnVal θ k (MvPolynomial.eval (cornerPoint (w := w) t m) (hasse e g)) =
          hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) ∧
        (e ≠ 0 → (∀ x ∈ P, e ≠ s x) → ((L : ℝ) : WithTop ℝ) <
          hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
            (((ord e : ℝ) * γ m : ℝ) : WithTop ℝ)) := by
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
    have hB : ∀ᶠ m in atTop, e ≠ 0 → (∀ x ∈ P, e ≠ s x) → ((L : ℝ) : WithTop ℝ) <
        hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
          (((ord e : ℝ) * γ m : ℝ) : WithTop ℝ) := by
      by_cases hc : e ≠ 0 ∧ ∀ x ∈ P, e ≠ s x
      · have := hstep1 e hc.1 (hgf e he) hc.2
        rw [hE] at this
        filter_upwards [eventually_lt_add hγt (ord e) this] with m hm
        exact fun _ _ => hm
      · exact Filter.Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hc
    filter_upwards [hA, hB] with m hm1 hm2
    exact fun _ => ⟨hm1, hm2⟩
  obtain ⟨m, hm⟩ := (eventually_atTop.mp hev)
  have hm := hm m le_rfl
  set φ : σ → HahnSeries (CornerExp θ) k := cornerPoint (w := w) t m with hφ
  -- Taylor's formula at `Φ_m`
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
  -- the data of Step 4
  set α : σ × ℕ → HahnSeries (CornerExp θ) k := fun x =>
    ((eval (cornerPointFT (w := w) hθ t m) (hasse (s x) f) : (finiteTypeSubfield k hθ).toSubring) :
      HahnSeries (CornerExp θ) k) with hαdef
  have hαe : ∀ x, α x = MvPolynomial.eval φ (hasse (s x) g) := fun x => hEm m (s x)
  set c : HahnSeries (CornerExp θ) k :=
    ((eval (cornerPointFT (w := w) hθ t m) f : (finiteTypeSubfield k hθ).toSubring) :
      HahnSeries (CornerExp θ) k) with hcdef
  have hce : c = MvPolynomial.eval φ g := by
    have h := hEm m 0
    rw [hasse_zero, hasse_zero] at h
    exact h
  have hs0g := hfg s0 hs0
  have hx0P : (i0, e0) ∈ P := by
    rw [hP, Finset.mem_product, Finset.mem_range]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : e0 < p ^ e0 := Nat.lt_pow_self hp.out.one_lt
    have h2 := le_degreeOf_of_hasse_ne_zero hs0g i0
    rw [hs0def, Finsupp.single_eq_same] at h2
    have h3 := hN i0
    omega
  have hαx0 : α (i0, e0) = MvPolynomial.eval φ (hasse s0 g) := hαe (i0, e0)
  obtain ⟨hv0, -⟩ := hm s0 (hbox s0 hs0g) hs0g
  have hAg : A = MvPolynomial.eval Φi (hasse s0 g) := hE s0
  have hAtop : hahnVal θ k A ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact hA0
  have hx00 : α (i0, e0) ≠ 0 := by
    intro h0
    rw [hαx0] at h0
    rw [h0, AddValuation.map_zero, ← hAg] at hv0
    exact hAtop hv0.symm
  have hord0 : (α (i0, e0)).order = ν0 := by
    have h1 : hahnVal θ k (α (i0, e0)) = hahnVal θ k A := by rw [hαx0, hv0, hAg]
    rw [hahnVal_of_ne hx00, hahnVal_of_ne hA0] at h1
    exact val_injective hθ (WithTop.coe_injective h1)
  have hmin0 : ∀ x ∈ P, α x ≠ 0 →
      val θ (α (i0, e0)).order + ((p ^ e0 : ℕ) : ℝ) * (1 + θ) ≤
        val θ (α x).order + ((p ^ x.2 : ℕ) : ℝ) * (1 + θ) := by
    intro x _ hax
    have hxg : hasse (s x) g ≠ 0 := fun h0 => hax (by rw [hαe x, h0, map_zero])
    obtain ⟨hv1, -⟩ := hm (s x) (hbox _ hxg) hxg
    have h5 := hLle (s x) (hs0' x) (hgf _ hxg)
    rw [hos x, ← hv1, ← hαe x, hahnVal_of_ne hax, ← WithTop.coe_add] at h5
    rw [hord0, ← hL]
    exact_mod_cast h5
  -- Step 4: a term of the germ of order `p^{e_0}`
  obtain ⟨j, hj, hjv⟩ := exists_coeff_germ_ne_zero hθ hw t hpl m (N + 1) α
    (fun x => (eval (cornerPointFT (w := w) hθ t m) (hasse (s x) f)).2) c
    (eval (cornerPointFT (w := w) hθ t m) f).2 i0 e0 hx0P hx00 hmin0
  rw [hord0] at hj hjv
  rw [← hL] at hjv
  set X' := c + ∑ x ∈ P, α x * (Φi x.1 - φ x.1) ^ (p ^ x.2) with hX'
  change X'.coeff (ν0 + p ^ e0 • expM w (j + 1)) ≠ 0 at hj
  -- the rest of Taylor's formula
  set T : (σ →₀ ℕ) → HahnSeries (CornerExp θ) k := fun e =>
    MvPolynomial.eval φ (hasse e g) * ∏ i, (Φi i - φ i) ^ e i with hT'
  have hinj : Set.InjOn s P := by
    intro x _ y _ hxy
    have hne : p ^ x.2 ≠ 0 := pow_ne_zero _ hp.out.ne_zero
    obtain ⟨h1, h2⟩ := ((Finsupp.single_eq_single_iff _ _ _ _).mp hxy).resolve_right
      (fun h => hne h.1)
    exact Prod.ext h1 (Nat.pow_right_injective hp.out.two_le h2)
  have hsumP : ∑ x ∈ P, α x * (Φi x.1 - φ x.1) ^ (p ^ x.2) = ∑ e ∈ P.image s, T e := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x _ => ?_
    show α x * (Φi x.1 - φ x.1) ^ (p ^ x.2) =
      MvPolynomial.eval φ (hasse (s x) g) * ∏ i, (Φi i - φ i) ^ (Finsupp.single x.1 (p ^ x.2)) i
    rw [hαe x, prod_pow_single]
  have hsub : ∀ e ∈ P.image s, e ∉ (box σ N).erase 0 → T e = 0 := by
    intro e he heU
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
    have hge : hasse (s x) g = 0 := by
      by_contra h0
      exact heU (Finset.mem_erase.mpr ⟨hs0' x, hbox _ h0⟩)
    simp only [hT', hge, map_zero, zero_mul]
  have hdecomp : X = X' + ∑ e ∈ (box σ N).erase 0 \ P.image s, T e := by
    have h1 : ∑ e ∈ (box σ N).erase 0, T e = ∑ e ∈ (box σ N).erase 0 ∪ P.image s, T e :=
      Finset.sum_subset Finset.subset_union_left fun e he heU => by
        rcases Finset.mem_union.mp he with h | h
        · exact absurd h heU
        · exact hsub e h heU
    have h2 := Finset.sum_sdiff (f := T)
      (show P.image s ⊆ (box σ N).erase 0 ∪ P.image s from Finset.subset_union_right)
    rw [Finset.union_sdiff_right] at h2
    have hX : X = c + ∑ e ∈ (box σ N).erase 0, T e := by
      rw [hce, ← hT]
      abel
    rw [hX, h1, ← h2, hX', hsumP]
    abel
  have hY : (∑ e ∈ (box σ N).erase 0 \ P.image s, T e).coeff
      (ν0 + p ^ e0 • expM w (j + 1)) = 0 := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨heU, heI⟩ := Finset.mem_sdiff.mp he
    obtain ⟨he0', heb⟩ := Finset.mem_erase.mp heU
    by_cases hge : hasse e g = 0
    · simp only [hT', hge, map_zero, zero_mul, HahnSeries.coeff_zero]
    have hns : ∀ x ∈ P, e ≠ s x := fun x hx h => heI (Finset.mem_image.mpr ⟨x, hx, h.symm⟩)
    obtain ⟨hA1, hB1⟩ := hm e heb hge
    have h1 := le_map_mul_prod_pow (hahnVal θ k) hDelta (MvPolynomial.eval φ (hasse e g)) e
    rw [hA1] at h1
    have h2 := (hB1 he0' hns).trans_le h1
    by_contra hne
    have h3 := hahnVal_le_of_mem ((HahnSeries.mem_support _ _).mpr hne)
    exact lt_asymm hjv (WithTop.coe_lt_coe.mp (h2.trans_le h3))
  have hpe : p ^ e0 • (expM w (j + 1) : CornerExp θ) =
      p • (p ^ (e0 - 1) • (expM w (j + 1) : CornerExp θ)) := by
    rw [smul_smul, ← pow_succ', Nat.sub_add_cancel he0]
  refine ⟨ν0 + p ^ e0 • expM w (j + 1), ?_, hjv, ?_⟩
  · rw [hdecomp, HahnSeries.coeff_add, hY, add_zero]
    exact hj
  · rw [map_add, hpe, classHom_nsmul_self, add_zero]
    exact hcl

end GermClass

end PlanarRuns

end Singularity
