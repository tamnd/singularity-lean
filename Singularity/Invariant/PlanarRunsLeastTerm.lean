/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.PlanarRunsDominance

/-!
# The least term along a planar corner run

This file proves Proposition 3.18.29 of Volume 7 of the handbook in the Hahn model of
`PlanarRunsHahn`: the transform `f(φ_m + M_m x_m, ψ_m + M_m w_m)` of a nonzero `f` is
`c ν (1 + h_m)` with `h_m` in the maximal ideal, for `m` large.

## The model

* The exponents of the monomials in `y_m, z_m` with nonnegative exponents form the submonoid
  `cone w m`. It grows with `m`.
* `Above C a x` says that each exponent of `x` is `a` plus an element of `C`, that is, the
  monomial of exponent `a` divides `x`.
* The transform at `P_m` is `chartAt w t m g = chart Φ_m M_m g`. Its coefficient of `x^d` is
  `A_d` of the handbook.
* The hypothesis `f ∈ K[[y_N, z_N]][X, W]` is `Above (cone w 0) 0` for each coefficient of `f`.

## Main results

* `Above.eval`: the divisibility of a value at a point.
* `IsCornerWord.leastTerm`: Proposition 3.18.29.
-/

open MvPolynomial Filter Topology

namespace Singularity

namespace PlanarRuns

open CornerExp

/-! ### The cone of the monomials at `P_m` -/

section Cone

variable {θ : ℝ}

/-- The exponents of the monomials in `y_m, z_m` with nonnegative exponents. -/
def cone (w : ℕ → Bool) (m : ℕ) : AddSubmonoid (CornerExp θ) where
  carrier := {r | 0 ≤ coordY w m r ∧ 0 ≤ coordZ w m r}
  add_mem' {r s} hr hs := by
    simp only [Set.mem_ofPred_eq, coordY_add, coordZ_add] at *
    exact ⟨by linarith [hr.1, hs.1], by linarith [hr.2, hs.2]⟩
  zero_mem' := by simp

theorem mem_cone {w : ℕ → Bool} {m : ℕ} {r : CornerExp θ} :
    r ∈ cone w m ↔ 0 ≤ coordY w m r ∧ 0 ≤ coordZ w m r := Iff.rfl

theorem cone_le_succ (w : ℕ → Bool) (m : ℕ) : cone (θ := θ) w m ≤ cone w (m + 1) := by
  intro r hr
  rw [mem_cone] at hr ⊢
  rw [coordY_succ, coordZ_succ]
  split_ifs <;> constructor <;> linarith [hr.1, hr.2]

theorem cone_mono (w : ℕ → Bool) {m n : ℕ} (h : m ≤ n) : cone (θ := θ) w m ≤ cone w n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (cone_le_succ w n)

theorem expL_mem_cone (w : ℕ → Bool) {l n : ℕ} (h : l < n) :
    (expL w l : CornerExp θ) ∈ cone w n := by
  apply cone_mono w h
  obtain ⟨h1, h2⟩ := coord_expL (θ := θ) w l
  rw [mem_cone, h1, h2]
  constructor <;> split_ifs <;> norm_num

/-- `M_b / M_a` is a monomial at `P_n` for `a ≤ b ≤ n`. -/
theorem expM_sub_mem_cone (w : ℕ → Bool) {a b n : ℕ} (hab : a ≤ b) (hb : b ≤ n) :
    (expM w b - expM w a : CornerExp θ) ∈ cone w n := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have : (expM w (b + 1) - expM w a : CornerExp θ) = (expM w b - expM w a) + expL w b := by
      rw [expM]
      abel
    rw [this]
    exact add_mem (ih (by omega)) (expL_mem_cone w (by omega))

theorem expM_mem_cone (w : ℕ → Bool) {b n : ℕ} (hb : b ≤ n) :
    (expM w b : CornerExp θ) ∈ cone w n := by
  simpa [expM] using expM_sub_mem_cone (θ := θ) w (Nat.zero_le b) hb

end Cone

/-! ### Divisibility by a monomial -/

section Above

variable {θ : ℝ} {k : Type*} [Field k]

/-- Each exponent of `x` is `a` plus an element of `C`. -/
def Above (C : AddSubmonoid (CornerExp θ)) (a : CornerExp θ) (x : HahnSeries (CornerExp θ) k) :
    Prop :=
  ∀ r ∈ x.support, r - a ∈ C

variable {C D : AddSubmonoid (CornerExp θ)} {a b : CornerExp θ}
  {x y : HahnSeries (CornerExp θ) k}

theorem Above.zero (a : CornerExp θ) : Above C a (0 : HahnSeries (CornerExp θ) k) := by
  intro r hr
  simp at hr

theorem Above.single (a : CornerExp θ) (c : k) : Above C a (HahnSeries.single a c) := by
  intro r hr
  rw [Set.mem_singleton_iff.mp (HahnSeries.support_single_subset hr), sub_self]
  exact zero_mem C

theorem Above.one : Above C 0 (1 : HahnSeries (CornerExp θ) k) := by
  rw [← HahnSeries.single_zero_one]
  exact Above.single 0 1

theorem Above.add (hx : Above C a x) (hy : Above C a y) : Above C a (x + y) := fun r hr =>
  ((Set.mem_union _ _ _).mp (HahnSeries.support_add_subset x y hr)).elim (hx r) (hy r)

theorem Above.mono (hx : Above C a x) (hab : a - b ∈ C) : Above C b x := fun r hr => by
  have := add_mem (hx r hr) hab
  rwa [sub_add_sub_cancel] at this

theorem Above.mono_cone (hx : Above C a x) (hCD : C ≤ D) : Above D a x := fun r hr =>
  hCD (hx r hr)

theorem Above.mul (hx : Above C a x) (hy : Above C b y) : Above C (a + b) (x * y) := by
  intro r hr
  obtain ⟨r1, hr1, r2, hr2, rfl⟩ := Set.mem_add.mp (HahnSeries.support_mul_subset hr)
  have := add_mem (hx r1 hr1) (hy r2 hr2)
  convert this using 1
  abel

theorem Above.pow (hx : Above C a x) (n : ℕ) : Above C (n • a) (x ^ n) := by
  induction n with
  | zero => simpa using (Above.one : Above C 0 (1 : HahnSeries (CornerExp θ) k))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul hx

theorem Above.nsmul (hx : Above C a x) (n : ℕ) : Above C a (n • x) := by
  induction n with
  | zero => simpa using Above.zero (C := C) (k := k) a
  | succ n ih =>
    rw [succ_nsmul]
    exact ih.add hx

theorem Above.sum {ι : Type*} (s : Finset ι) {z : ι → HahnSeries (CornerExp θ) k}
    (h : ∀ i ∈ s, Above C a (z i)) : Above C a (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Above.zero (C := C) (k := k) a
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem Above.prod {ι : Type*} (s : Finset ι) {c : ι → CornerExp θ}
    {z : ι → HahnSeries (CornerExp θ) k} (h : ∀ i ∈ s, Above C (c i) (z i)) :
    Above C (∑ i ∈ s, c i) (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Above.one : Above C 0 (1 : HahnSeries (CornerExp θ) k))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable {σ : Type*} [Fintype σ]

/-- If the monomial of exponent `a` divides each `φ_i`, and the monomial of exponent
`b - |e| a` divides the coefficient of `X^e` of `h` for each `e`, then the monomial of exponent
`b` divides `h(φ)`. -/
theorem Above.eval {φ : σ → HahnSeries (CornerExp θ) k} (hφ : ∀ i, Above C a (φ i))
    {h : MvPolynomial σ (HahnSeries (CornerExp θ) k)}
    (hh : ∀ e, Above C (b - ord e • a) (h.coeff e)) :
    Above C b (MvPolynomial.eval φ h) := by
  rw [MvPolynomial.eval_eq']
  refine Above.sum _ fun e _ => ?_
  have h1 := (hh e).mul (Above.prod Finset.univ (fun i _ => (hφ i).pow (e i)))
  have h2 : b - ord e • a + ∑ i, e i • a = b := by
    rw [← Finset.sum_smul, ord, sub_add_cancel]
  rwa [h2] at h1

end Above

/-! ### The least term of a nearby element -/

section Near

variable {θ : ℝ} {k : Type*} [Field k]

/-- If `v(x - y) > v(x)`, each other exponent of `y` has a value larger than `v(x)`. -/
theorem val_lt_of_mem_support (hθ : Irrational θ) {x y : HahnSeries (CornerExp θ) k} (hx : x ≠ 0)
    (hxy : hahnVal θ k x < hahnVal θ k (x - y)) {r : CornerExp θ} (hr : r ∈ y.support)
    (hne : r ≠ x.order) : val θ x.order < val θ r := by
  by_cases hrx : r ∈ x.support
  · have h1 := val_mono (θ := θ) (HahnSeries.order_le_of_coeff_ne_zero hrx)
    exact lt_of_le_of_ne h1 fun h' => hne ((val_injective hθ) h').symm
  · have hr' : r ∈ (x - y).support := by
      rw [HahnSeries.mem_support] at hr hrx ⊢
      rw [HahnSeries.coeff_sub, not_not.mp hrx, zero_sub, neg_ne_zero]
      exact hr
    have h1 := hahnVal_le_of_mem hr'
    rw [hahnVal_of_ne hx] at hxy
    exact_mod_cast hxy.trans_le h1

/-- If `v(x - y) > v(x)`, then `y` has the coefficient of `x` at the order of `x`. -/
theorem coeff_order_eq_of_lt {x y : HahnSeries (CornerExp θ) k} (hx : x ≠ 0)
    (hxy : hahnVal θ k x < hahnVal θ k (x - y)) : y.coeff x.order = x.coeff x.order := by
  by_contra hne
  have hr : x.order ∈ (x - y).support := by
    rw [HahnSeries.mem_support, HahnSeries.coeff_sub, sub_ne_zero]
    exact Ne.symm hne
  have h1 := hahnVal_le_of_mem hr
  rw [hahnVal_of_ne hx] at hxy
  exact absurd (hxy.trans_le h1) (lt_irrefl _)

end Near

/-! ### Proposition 3.18.29 -/

section LeastTerm

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {θ : ℝ} {k : Type*} [Field k] {w : ℕ → Bool}

/-- The transform `g(φ_m + M_m x_m, ψ_m + M_m w_m)` at `P_m`. -/
noncomputable def chartAt (w : ℕ → Bool) (t : ℕ → σ → k) (m : ℕ)
    (g : MvPolynomial σ (HahnSeries (CornerExp θ) k)) :
    MvPolynomial σ (HahnSeries (CornerExp θ) k) :=
  chart (cornerPoint (w := w) t m) (cornerM θ k w m) g

omit [Fintype σ] [DecidableEq σ] in
theorem coe_eval_cornerPointFT (hθ : Irrational θ) (t : ℕ → σ → k) (m : ℕ)
    (f : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring) :
    ((eval (cornerPointFT (w := w) hθ t m) f : (finiteTypeSubfield k hθ).toSubring) :
        HahnSeries (CornerExp θ) k) =
      MvPolynomial.eval (cornerPoint (w := w) t m)
        (map (finiteTypeSubfield k hθ).toSubring.subtype f) := by
  rw [coe_eval, MvPolynomial.eval_map]
  rfl

omit [Fintype σ] [DecidableEq σ] in
/-- The monomials of `φ_m` lie at `P_n` for `m ≤ n`. -/
theorem above_cornerPoint (t : ℕ → σ → k) {m n : ℕ} (h : m ≤ n) (i : σ) :
    Above (cone w n) 0 (cornerPoint (θ := θ) (w := w) t m i) := by
  rw [cornerPoint, cornerSum_eq]
  refine Above.sum _ fun j hj => ?_
  refine (Above.single _ _).mono ?_
  rw [sub_zero]
  exact expM_mem_cone w (by simp at hj; omega)

omit [Fintype σ] [DecidableEq σ] in
/-- The monomials of `φ_m - φ_{m₁}` are divisible by `M_{m₁+1}` at `P_m`. -/
theorem above_cornerPoint_sub (t : ℕ → σ → k) {m₁ m : ℕ} (h : m₁ ≤ m) (i : σ) :
    Above (cone w m) (expM w (m₁ + 1))
      (cornerPoint (θ := θ) (w := w) t m i - cornerPoint (θ := θ) (w := w) t m₁ i) := by
  rw [cornerPoint, cornerPoint, cornerSum_eq, cornerSum_eq, ← Finset.sum_Ico_eq_sub _ h]
  refine Above.sum _ fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  exact (Above.single _ _).mono (expM_sub_mem_cone w (by omega) (by omega))

theorem val_nsmul' (n : ℕ) (r : CornerExp θ) : val θ (n • r) = n * val θ r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, val_add, ih]
    push_cast
    ring

/-- Proposition 3.18.29 for the Hahn model of a planar corner run. Let `x = f(Φ_∞)` with the
term of least value `c ν`. For `m` large, `ν` is a monomial at `P_m`, the coefficient of `ν` in
`A_0 = f(Φ_m)` is `c`, and `ν` divides each `A_d` at `P_m`. So the transform is `c ν (1 + h_m)`
with `h_m` in the maximal ideal. -/
theorem IsCornerWord.leastTerm {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k) (hpl : IsPlanarRun t)
    (f : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring) (hf : f ≠ 0)
    (hf0 : ∀ e, Above (cone w 0) 0 (f.coeff e : HahnSeries (CornerExp θ) k))
    {x : HahnSeries (CornerExp θ) k}
    (hx : eval₂ (finiteTypeSubfield k hθ).toSubring.subtype
      (fun l => cornerLimit hw (fun j => t j l)) f = x) :
    ∃ m₂, ∀ m ≥ m₂, x.order ∈ cone w m ∧
      ((chartAt w t m (map (finiteTypeSubfield k hθ).toSubring.subtype f)).coeff 0).coeff x.order =
        x.coeff x.order ∧
      ∀ d, Above (cone w m) x.order
        ((chartAt w t m (map (finiteTypeSubfield k hθ).toSubring.subtype f)).coeff d) := by
  classical
  obtain ⟨hx0, h1, h2⟩ := statementDHolds_corner_frob hθ hw t hpl f hf
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
  rw [hx] at hx0 h1 h2
  set ν := x.order with hν
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
  set γ : ℕ → ℝ := fun m => val θ (expM w (m + 1) : CornerExp θ) with hγ
  have hγt : Tendsto γ atTop (𝓝 (1 + θ)) := hw.tendsto_val_expM.comp (tendsto_add_atTop_nat 1)
  -- The facts for `m` large.
  have hev : ∀ᶠ m in atTop,
      hahnVal θ k x < hahnVal θ k (x - MvPolynomial.eval (cornerPoint (w := w) t m) g) ∧
      ∀ e ∈ box σ N, hasse e g ≠ 0 →
        hahnVal θ k (MvPolynomial.eval (cornerPoint (w := w) t m) (hasse e g)) =
          hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) ∧
        (e ≠ 0 → hahnVal θ k x < hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
          (((ord e : ℝ) * γ m : ℝ) : WithTop ℝ)) := by
    refine Filter.Eventually.and ?_ ?_
    · filter_upwards [h2] with m hm
      have := hEm m 0
      rw [hasse_zero, hasse_zero] at this
      rwa [← this]
    · refine (Filter.eventually_all_finset _).mpr fun e _ => ?_
      by_cases he : hasse e g = 0
      · exact Filter.Eventually.of_forall fun _ h => absurd he h
      have hef : hasse e f ≠ 0 := by
        intro h0
        apply he
        rw [hg, hasse_map, h0, map_zero]
      obtain ⟨-, -, h2e⟩ := statementDHolds_corner_frob hθ hw t hpl (hasse e f) hef
      rw [← hΦi] at h2e
      have hA : ∀ᶠ m in atTop,
          hahnVal θ k (MvPolynomial.eval (cornerPoint (w := w) t m) (hasse e g)) =
            hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) := by
        filter_upwards [h2e] with m hm
        rw [hE, hEm] at hm
        exact map_eq_of_lt_map_sub _ hm
      have hB : ∀ᶠ m in atTop, e ≠ 0 →
          hahnVal θ k x < hahnVal θ k (MvPolynomial.eval Φi (hasse e g)) +
            (((ord e : ℝ) * γ m : ℝ) : WithTop ℝ) := by
        by_cases he0 : e = 0
        · exact Filter.Eventually.of_forall fun _ h => absurd he0 h
        have := h1 e he0 hef
        rw [hE] at this
        filter_upwards [eventually_lt_add hγt (ord e) this] with m hm
        exact fun _ => hm
      filter_upwards [hA, hB] with m hm1 hm2
      exact fun _ => ⟨hm1, hm2⟩
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.mp hev
  set a : CornerExp θ := expM w (m₁ + 1) with ha
  set T := chart (cornerPoint (w := w) t m₁) 1 g with hT
  have hTc : ∀ e, T.coeff e = MvPolynomial.eval (cornerPoint (w := w) t m₁) (hasse e g) := by
    intro e
    rw [hT, coeff_chart, one_pow, one_mul]
  -- The coefficients of `T` are monomials at `P_{m₁+1}`.
  have hT0 : ∀ e, Above (cone w (m₁ + 1)) 0 (T.coeff e) := by
    intro e
    rw [hTc]
    refine Above.eval (a := 0) (fun i => above_cornerPoint t (Nat.le_succ m₁) i) fun e' => ?_
    rw [smul_zero, sub_zero, coeff_hasse, hg, coeff_map]
    exact ((hf0 _).mono_cone (cone_mono w (Nat.zero_le _))).nsmul _
  set S : Set (CornerExp θ) := {q | ∃ e, q - ord e • a ∈ (T.coeff e).support} with hS
  have hSc : ∀ q ∈ S, 0 ≤ coordY w (m₁ + 1) q ∧ 0 ≤ coordZ w (m₁ + 1) q := by
    rintro q ⟨e, he⟩
    have h1 := hT0 e _ he
    rw [sub_zero] at h1
    have h2 := add_mem h1 (nsmul_mem (expM_mem_cone (θ := θ) w le_rfl) (ord e))
    rwa [sub_add_cancel] at h2
  have hmin : ∀ q ∈ S, q ≠ ν → val θ ν < val θ q := by
    rintro q ⟨e, he⟩ hqν
    have hTe : T.coeff e ≠ 0 := by
      rintro h0
      rw [h0] at he
      simp at he
    have hge : hasse e g ≠ 0 := by
      intro h0
      apply hTe
      rw [hTc, h0, map_zero]
    obtain ⟨hm0, hme⟩ := hm₁ m₁ le_rfl
    by_cases he0 : e = 0
    · subst he0
      have hq : q - ord (0 : σ →₀ ℕ) • a = q := by simp [ord]
      rw [hq, hTc, hasse_zero] at he
      exact val_lt_of_mem_support hθ hx0 hm0 he hqν
    · obtain ⟨hA, hB⟩ := hme e (hbox e hge) hge
      have hB := hB he0
      have h1 := hahnVal_le_of_mem he
      rw [hTc, hA] at h1
      have h3 : hahnVal θ k x < ((val θ (q - ord e • a) : ℝ) : WithTop ℝ) +
          (((ord e : ℝ) * γ m₁ : ℝ) : WithTop ℝ) :=
        hB.trans_le (by gcongr)
      rw [hahnVal_of_ne hx0, ← WithTop.coe_add] at h3
      have h4 := WithTop.coe_lt_coe.mp h3
      have h5 : val θ q = val θ (q - ord e • a) + (ord e : ℝ) * γ m₁ := by
        rw [hγ, ← val_nsmul', ← val_add, sub_add_cancel]
      rw [h5]
      exact h4
  obtain ⟨m₀, hm₀, hdom⟩ := hw.dominance (m₁ + 1) hSc hmin
  refine ⟨m₀, fun m hm => ?_⟩
  have hm1m : m₁ + 1 ≤ m := hm₀.trans hm
  -- Each point of `S` is above `ν` at `P_m`.
  have hcone : ∀ q ∈ S, q - ν ∈ cone w m := by
    intro q hq
    by_cases hqν : q = ν
    · rw [hqν, sub_self]
      exact zero_mem _
    · obtain ⟨h1, h2⟩ := hdom m hm q hq hqν
      exact ⟨h1.le, h2.le⟩
  have hTm : ∀ e, Above (cone w m) (ν - ord e • a) (T.coeff e) := by
    intro e r hr
    have hq : r + ord e • a ∈ S := ⟨e, by rwa [add_sub_cancel_right]⟩
    have := hcone _ hq
    convert this using 1
    abel
  -- `ν` is a point of `S`.
  have hνS : ν ∈ S := by
    refine ⟨0, ?_⟩
    have hq : ν - ord (0 : σ →₀ ℕ) • a = ν := by simp [ord]
    rw [hq, hTc, hasse_zero, HahnSeries.mem_support,
      coeff_order_eq_of_lt hx0 (hm₁ m₁ le_rfl).1]
    exact coeff_order_ne hx0
  have hchart : chartAt w t m g =
      chart (fun i => cornerPoint (w := w) t m i - cornerPoint (w := w) t m₁ i)
        (cornerM θ k w m) T := by
    rw [hT, chart_chart, chartAt]
    congr 1
    · funext i
      ring
    · ring
  refine ⟨?_, ?_, fun d => ?_⟩
  · have := hSc ν hνS
    exact cone_mono w hm1m this
  · have h0 : ord (0 : σ →₀ ℕ) = 0 := by simp [ord]
    rw [chartAt, coeff_chart, h0, pow_zero, one_mul, hasse_zero]
    exact coeff_order_eq_of_lt hx0 (hm₁ m (by omega)).1
  · rw [hchart, coeff_chart, cornerM, HahnSeries.single_pow, one_pow]
    have h1 : Above (cone w m) (ν - ord d • (expM w m : CornerExp θ))
        (MvPolynomial.eval (fun i => cornerPoint (w := w) t m i - cornerPoint (w := w) t m₁ i)
          (hasse d T)) := by
      refine Above.eval (a := a) (fun i => above_cornerPoint_sub t (by omega) i) fun e => ?_
      rw [coeff_hasse]
      refine ((hTm (e + d)).mono ?_).nsmul _
      have hord : ord (e + d) = ord e + ord d := by
        simp [ord, Finset.sum_add_distrib]
      have : ν - ord (e + d) • a - (ν - ord d • (expM w m : CornerExp θ) - ord e • a) =
          ord d • ((expM w m : CornerExp θ) - a) := by
        rw [hord, add_nsmul, nsmul_sub]
        abel
      rw [this]
      exact nsmul_mem (expM_sub_mem_cone w (by omega) le_rfl) _
    have := (Above.single (C := cone w m) (ord d • (expM w m : CornerExp θ)) (1 : k)).mul h1
    rwa [add_sub_cancel] at this

end LeastTerm

end PlanarRuns

end Singularity
