/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.OriginRuns
import Singularity.Invariant.LogJacobianCornerCurves

/-!
# Origin runs that use some of the charts

This file proves results of Volume 7, Section 3.14 of the handbook on the origin runs whose
letters are in a set `L` of `k` letters, with `U` the set of the other coordinates.

## The exponent formula (Lemma 3.14.3)

For an exponent vector `e` put `σ(e) = Σ_{u ∈ U} e_u` (`uSum`) and
`q_t(e) = (k - 1) e_t + σ(e) - p` for `t ∈ L` (`qVec`). The exponent columns `c_s`, `s ∈ L`, start
as the unit vectors (`unitCols`), and a step with the letter `j` replaces `c_j` by `Σ_{t ∈ L} c_t`
(`colStep`, `cols`). At each point of the run, the image of `x^e` has the exponent `E_s` of `x_s`,
`s ∈ L`, with `(k - 1) E_s = q(e) · c_s - σ(e) + p` (`qDot`), and the exponent `e_u` of `x_u`,
`u ∈ U` (`expSteps_formula`).

## Theorem 3.14.7, parts 1, 2 and 3

The inequalities of Lemma 3.14.6 are a hypothesis here (`CornerIneq`). Let `T` be a monomial of
`g_N`, and assume that for each monomial `μ` of `g_N` and each `s ∈ L` the number
`Δq(μ) · c_s = q(μ) · c_s - q(T) · c_s` is at least `0` and at least `σ(μ) - σ(T)`. The
monomials of `F` with `σ ≤ σ(T)` and the monomials that satisfy Lemma 3.14.6 have this property
(`cornerIneq_of`). Then at the point `P_m`, with `L ⊆ Δ`:

1. `r_s = E_s(T)` for each `s ∈ L` (`originRun_divisorExponent_eq`).
2. `d_m = ord G_m = σ(T) - r_U` (`originRun_ord_residualFactor`).
3. Each corner curve `C_t = V(x_i : i ≠ t)`, `t ∈ L`, has `ν^G = d_m`
   (`originRun_orderGAlong_corner`), and `ν^G ≥ ρ` (`originRun_logJacobianOrder_le_orderGAlong`).

The form for an infinite run is `originRun_cornerCurves`. The limit argument of Lemma 3.14.6, which
gives the point `m_0` after which the inequalities hold, is in the file
`Singularity/Invariant/OriginRunsLimit.lean` (`originRun_cornerCurves_eventually`). The statement
that the initial form of `G_m` is `h`, part 4 and part 5 are not proved.

## Example 3.14.9

The field is `ZMod p`, `n = 4`, the variables `x_1, x_2, x_3, x_4` are the indices `0, 1, 2, 3`
of `Fin 4`, `Δ = {0, 1, 2}` and `g = x_1 x_4^p + x_1^2 x_2 x_3 x_4^(p-2)` (`exPoly_start`). The
point after a word in the letters `1, 2, 3` is `x^r (x_4^p + x_1 x_2 x_3 x_4^(p-2))` with
`r_4 = 0` (`exPoly`, `polySteps_exPoly`). At each such point, `ρ = d = p`, the three corner curves
have `ν^G = p`, the surfaces `V(x_4, x_s)` have `ν^G = p - 1 < ρ`, and `V(x_4)` has
`ν^G = p - 2` (`example_3_14_9`). Each origin step with a letter in `{1, 2, 3}` is a step with
`ρ = p` at both points (`rhoStep_exPoly`). Part 3 of the example, on all the regular formal
subvarieties, is not proved.

## References

* Volume 7, Section 3.14 of the handbook: Lemma 3.14.3, Lemma 3.14.6, Theorem 3.14.7 and
  Example 3.14.9.
-/

open MvPolynomial Finsupp

namespace Singularity

namespace OriginRuns

/-! ### The exponent formula -/

section Columns

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (p : ℕ) (L : Finset σ)

/-- The number `σ(e) = Σ_{u ∈ U} e_u`, where `U` is the complement of the set `L` of letters. -/
def uSum (e : σ →₀ ℕ) : ℕ := ∑ u ∈ Lᶜ, e u

/-- The vector `q(e)` with the entries `q_t(e) = (k - 1) e_t + σ(e) - p`, where `k = |L|`. -/
def qVec (e : σ →₀ ℕ) (t : σ) : ℤ := ((L.card : ℤ) - 1) * e t + uSum L e - p

/-- The product `q(e) · c = Σ_{t ∈ L} q_t(e) c_t`. -/
def qDot (e : σ →₀ ℕ) (c : σ → ℤ) : ℤ := ∑ t ∈ L, qVec p L e t * c t

/-- The step with the letter `j` on the exponent columns: `c_j ← Σ_{t ∈ L} c_t`. -/
def colStep (j : σ) (c : σ → σ → ℤ) : σ → σ → ℤ := Function.update c j (∑ t ∈ L, c t)

/-- The steps with the letters of the list `l` on the exponent columns. -/
def colSteps (l : List σ) (c : σ → σ → ℤ) : σ → σ → ℤ := l.foldl (fun c j => colStep L j c) c

/-- The exponent columns at the start: `c_s` is the unit vector of `s`. -/
def unitCols : σ → σ → ℤ := fun s => Pi.single s 1

/-- The exponent columns of the run with the letters of `l` (Volume 7, Section 3.14 of the
handbook). The column `s` is `cols L l s`. -/
def cols (l : List σ) : σ → σ → ℤ := colSteps L l unitCols

/-- The formula of Lemma 3.14.3 for the exponent vector `e` of the image of `x^{e₀}` and the
columns `c`. -/
def ExpFormula (e₀ e : σ →₀ ℕ) (c : σ → σ → ℤ) : Prop :=
  (∀ u ∉ L, e u = e₀ u) ∧
    ∀ s ∈ L, ((L.card : ℤ) - 1) * e s = qDot p L e₀ (c s) - uSum L e₀ + p

/-- The formula of Lemma 3.14.3 holds at the start of the run, with the unit columns. -/
theorem expFormula_unitCols (e : σ →₀ ℕ) : ExpFormula p L e e unitCols := by
  refine ⟨fun _ _ => rfl, fun s hs => ?_⟩
  have h : qDot p L e (unitCols s) = qVec p L e s := by
    simp only [qDot, unitCols, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' L s, ite_eq_left hs]
  rw [h, qVec]
  ring

/-- One step keeps the formula of Lemma 3.14.3. -/
theorem expFormula_step {e₀ e : σ →₀ ℕ} {c : σ → σ → ℤ} (h : ExpFormula p L e₀ e c) {j : σ}
    (hj : j ∈ L) (hp : p ≤ e.degree) : ExpFormula p L e₀ (expStep p j e) (colStep L j c) := by
  obtain ⟨hU, hL⟩ := h
  refine ⟨fun u hu => ?_, fun s hs => ?_⟩
  · rw [expStep_apply_of_ne p (fun h : u = j => hu (h ▸ hj)), hU u hu]
  by_cases hsj : s = j
  · subst hsj
    rw [expStep_apply_self, colStep, Function.update_self]
    have hdeg : (e.degree : ℤ) = ∑ t ∈ L, (e t : ℤ) + uSum L e₀ := by
      rw [degree_eq_sum', Nat.cast_sum, ← Finset.sum_add_sum_compl L, uSum, Nat.cast_sum]
      congr 1
      exact Finset.sum_congr rfl fun u hu => by rw [hU u (Finset.mem_compl.mp hu)]
    have hdot : qDot p L e₀ (∑ t ∈ L, c t) = ∑ t ∈ L, qDot p L e₀ (c t) := by
      simp only [qDot, Finset.sum_apply, Finset.mul_sum]
      exact Finset.sum_comm
    have hsum : ∑ t ∈ L, qDot p L e₀ (c t) =
        ∑ t ∈ L, (((L.card : ℤ) - 1) * e t + uSum L e₀ - p) :=
      Finset.sum_congr rfl fun t ht => by linarith [hL t ht]
    rw [hdot, hsum, Nat.cast_sub hp, hdeg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  · rw [expStep_apply_of_ne p hsj, colStep, Function.update_of_ne hsj]
    exact hL s hs

/-- The steps with the letters of `l` keep the formula of Lemma 3.14.3. -/
theorem expFormula_expSteps {l : List σ} (hl : ∀ j ∈ l, j ∈ L) {e₀ e : σ →₀ ℕ}
    {c : σ → σ → ℤ} (h : ExpFormula p L e₀ e c) (he : ExpAdmissible p l e) :
    ExpFormula p L e₀ (expSteps p l e) (colSteps L l c) := by
  induction l generalizing e c with
  | nil => exact h
  | cons j l ih =>
    exact ih (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj'))
      (expFormula_step p L h (hl j List.mem_cons_self) he.1) he.2

/-- **The exponent formula** (Volume 7, Lemma 3.14.3 of the handbook). Let each letter of `l` be
in `L`, and let each step be defined. At the end of the run, the image of the monomial `x^e` has
the exponent `e_u` of `x_u` for `u ∉ L`, and the exponent `E_s` of `x_s` for `s ∈ L`, where
`(k - 1) E_s = q(e) · c_s - σ(e) + p` and `c_s` is the column `s` at the end of the run. -/
theorem expSteps_formula {l : List σ} (hl : ∀ j ∈ l, j ∈ L) {e : σ →₀ ℕ}
    (he : ExpAdmissible p l e) :
    (∀ u ∉ L, expSteps p l e u = e u) ∧
      ∀ s ∈ L, ((L.card : ℤ) - 1) * expSteps p l e s = qDot p L e (cols L l s) - uSum L e + p :=
  expFormula_expSteps p L hl (expFormula_unitCols p L e) he

/-- The steps do not change `σ(e)` (Volume 7, Section 3.14 of the handbook). -/
theorem uSum_expSteps {l : List σ} (hl : ∀ j ∈ l, j ∈ L) {e : σ →₀ ℕ}
    (he : ExpAdmissible p l e) : uSum L (expSteps p l e) = uSum L e :=
  Finset.sum_congr rfl fun u hu =>
    (expSteps_formula p L hl he).1 u (Finset.mem_compl.mp hu)

omit [Fintype σ] in
/-- A step with a letter other than `u` keeps the exponent of `x_u`. -/
theorem expSteps_apply_of_forall_ne {l : List σ} {u : σ} (hu : ∀ j ∈ l, j ≠ u)
    (e : σ →₀ ℕ) : expSteps p l e u = e u := by
  induction l generalizing e with
  | nil => rfl
  | cons j l ih =>
    rw [show expSteps p (j :: l) e = expSteps p l (expStep p j e) from rfl,
      ih (fun j' hj' => hu j' (List.mem_cons_of_mem _ hj')),
      expStep_apply_of_ne p (Ne.symm (hu j List.mem_cons_self))]

end Columns

/-! ### Theorem 3.14.7 -/

section TheoremB

variable {σ k : Type*} [Fintype σ] [DecidableEq σ] [Field k]

/-- **The inequalities of Lemma 3.14.6, in the form that the proof of Theorem 3.14.7 uses.** For
each `s ∈ L`, the number `Δq(μ) · c_s = q(μ) · c_s - q(T) · c_s` is at least `0` and at least
`σ(μ) - σ(T)`. -/
def CornerIneq (p : ℕ) (L : Finset σ) (c : σ → σ → ℤ) (T μ : σ →₀ ℕ) : Prop :=
  ∀ s ∈ L, 0 ≤ qDot p L μ (c s) - qDot p L T (c s) ∧
    (uSum L μ : ℤ) - uSum L T ≤ qDot p L μ (c s) - qDot p L T (c s)

/-- The two cases of the handbook give `CornerIneq` (Volume 7, Section 3.14 of the handbook). If
`μ` is in `F`, that is `q(μ) = q(T)`, and `σ(μ) ≤ σ(T)`, or if `μ` satisfies the inequality
`Δq(μ) · c_s ≥ max(1, Δσ(μ))` of Lemma 3.14.6, then `CornerIneq` holds for `μ`. -/
theorem cornerIneq_of {p : ℕ} {L : Finset σ} {c : σ → σ → ℤ} {T μ : σ →₀ ℕ}
    (h : ((∀ t ∈ L, qVec p L μ t = qVec p L T t) ∧ uSum L μ ≤ uSum L T) ∨
      ∀ s ∈ L, max 1 ((uSum L μ : ℤ) - uSum L T) ≤ qDot p L μ (c s) - qDot p L T (c s)) :
    CornerIneq p L c T μ := by
  rcases h with ⟨hq, hσ⟩ | h
  · intro s _
    have : qDot p L μ (c s) = qDot p L T (c s) :=
      Finset.sum_congr rfl fun t ht => by rw [hq t ht]
    rw [this, sub_self]
    exact ⟨le_rfl, by omega⟩
  · intro s hs
    have h1 := h s hs
    exact ⟨by linarith [le_max_left (1 : ℤ) ((uSum L μ : ℤ) - uSum L T)],
      by linarith [le_max_right (1 : ℤ) ((uSum L μ : ℤ) - uSum L T)]⟩

omit [Fintype σ] in
/-- If `a ≥ 1` and `a b ≥ 0`, then `b ≥ 0`. -/
theorem nonneg_of_mul_nonneg_of_one_le {a b : ℤ} (ha : 1 ≤ a) (h : 0 ≤ a * b) : 0 ≤ b := by
  by_contra hb
  push Not at hb
  nlinarith

/-- The degree of `e` is `Σ_{s ∈ L} e_s + σ(e)`. -/
theorem degree_eq_sum_add_uSum (L : Finset σ) (e : σ →₀ ℕ) :
    e.degree = ∑ s ∈ L, e s + uSum L e := by
  rw [degree_eq_sum', uSum, Finset.sum_add_sum_compl]

/-- For `t ∈ L`, the sum over the variables other than `t` is the sum over `L \ {t}` and `U`. -/
theorem sum_univ_erase_eq {L : Finset σ} {t : σ} (ht : t ∈ L) (f : σ → ℕ) :
    ∑ i ∈ Finset.univ.erase t, f i = ∑ s ∈ L.erase t, f s + ∑ u ∈ Lᶜ, f u := by
  have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ t)
  have h2 := Finset.add_sum_erase L f ht
  have h3 := Finset.sum_add_sum_compl L f
  omega

variable {p : ℕ} {L Δ : Finset σ} {l : List σ} {g : MvPolynomial σ k} {T : σ →₀ ℕ}

/-- The main step of part 1 of Theorem 3.14.7. Under `CornerIneq`, the image of `T` has the
least exponent of `x_s` for each `s ∈ L`: `(k - 1) (E_s(μ) - E_s(T)) = Δq(μ) · c_s - Δσ(μ) ≥ 0`.
-/
theorem originRun_exp_le (hk : 2 ≤ L.card) (hl : ∀ j ∈ l, j ∈ L) (hadm : IsAdmissible p l g)
    (hT : T ∈ g.support) {μ : σ →₀ ℕ} (hμ : μ ∈ g.support) (hineq : CornerIneq p L (cols L l) T μ)
    {s : σ} (hs : s ∈ L) : expSteps p l T s ≤ expSteps p l μ s := by
  have hE := (support_polySteps hadm).2
  have h1 := (expSteps_formula p L hl (hE μ hμ)).2 s hs
  have h2 := (expSteps_formula p L hl (hE T hT)).2 s hs
  have h3 := (hineq s hs).2
  have hk' : (1 : ℤ) ≤ L.card - 1 := by
    have : (2 : ℤ) ≤ L.card := by exact_mod_cast hk
    linarith
  have h4 : 0 ≤ ((L.card : ℤ) - 1) * ((expSteps p l μ s : ℤ) - expSteps p l T s) := by
    rw [mul_sub, h1, h2]
    linarith
  have := nonneg_of_mul_nonneg_of_one_le hk' h4
  omega

/-- The main step of part 2 of Theorem 3.14.7. Under `CornerIneq`, the image of `T` has the least
degree: `(k - 1) (|E(μ)| - |E(T)|) = Σ_{s ∈ L} Δq(μ) · c_s - Δσ(μ) ≥ 0`. -/
theorem originRun_degree_le (hk : 2 ≤ L.card) (hl : ∀ j ∈ l, j ∈ L) (hadm : IsAdmissible p l g)
    (hT : T ∈ g.support) {μ : σ →₀ ℕ} (hμ : μ ∈ g.support)
    (hineq : CornerIneq p L (cols L l) T μ) :
    (expSteps p l T).degree ≤ (expSteps p l μ).degree := by
  have hE := (support_polySteps hadm).2
  have hfμ := expSteps_formula p L hl (hE μ hμ)
  have hfT := expSteps_formula p L hl (hE T hT)
  have hk' : (1 : ℤ) ≤ L.card - 1 := by
    have : (2 : ℤ) ≤ L.card := by exact_mod_cast hk
    linarith
  obtain ⟨s₀, hs₀⟩ : L.Nonempty := Finset.card_pos.mp (by omega)
  set D : σ → ℤ := fun s => qDot p L μ (cols L l s) - qDot p L T (cols L l s) with hD
  set δσ : ℤ := (uSum L μ : ℤ) - uSum L T with hδσ
  have hX : ((L.card : ℤ) - 1) *
      (∑ s ∈ L, ((expSteps p l μ s : ℤ) - expSteps p l T s) + δσ) = ∑ s ∈ L, D s - δσ := by
    rw [mul_add, Finset.mul_sum]
    have : ∀ s ∈ L, ((L.card : ℤ) - 1) * ((expSteps p l μ s : ℤ) - expSteps p l T s) =
        D s - δσ := fun s hs => by
      rw [mul_sub, hfμ.2 s hs, hfT.2 s hs, hD, hδσ]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hpos : δσ ≤ ∑ s ∈ L, D s :=
    (hineq s₀ hs₀).2.trans (Finset.single_le_sum (f := D) (fun s hs => (hineq s hs).1) hs₀)
  have h0 := nonneg_of_mul_nonneg_of_one_le hk' (by rw [hX]; linarith)
  rw [degree_eq_sum_add_uSum L, degree_eq_sum_add_uSum L, uSum_expSteps p L hl (hE μ hμ),
    uSum_expSteps p L hl (hE T hT)]
  rw [Finset.sum_sub_distrib] at h0
  have : ((∑ s ∈ L, expSteps p l T s : ℕ) : ℤ) + uSum L T ≤
      ((∑ s ∈ L, expSteps p l μ s : ℕ) : ℤ) + uSum L μ := by
    push_cast
    linarith
  exact_mod_cast this

/-- The main step of part 3 of Theorem 3.14.7. Under `CornerIneq`, the image of `T` has the least
order along the corner curve `C_t = V(x_i : i ≠ t)`. The reason is that
`(k - 1)` times the difference is `Σ_{s ∈ L, s ≠ t} Δq(μ) · c_s ≥ 0`. -/
theorem originRun_corner_le (hk : 2 ≤ L.card) (hl : ∀ j ∈ l, j ∈ L) (hadm : IsAdmissible p l g)
    (hT : T ∈ g.support) {μ : σ →₀ ℕ} (hμ : μ ∈ g.support)
    (hineq : CornerIneq p L (cols L l) T μ) {t : σ} (ht : t ∈ L) :
    ∑ i ∈ Finset.univ.erase t, expSteps p l T i ≤ ∑ i ∈ Finset.univ.erase t, expSteps p l μ i := by
  have hE := (support_polySteps hadm).2
  have hfμ := expSteps_formula p L hl (hE μ hμ)
  have hfT := expSteps_formula p L hl (hE T hT)
  have hk' : (1 : ℤ) ≤ L.card - 1 := by
    have : (2 : ℤ) ≤ L.card := by exact_mod_cast hk
    linarith
  set D : σ → ℤ := fun s => qDot p L μ (cols L l s) - qDot p L T (cols L l s) with hD
  set δσ : ℤ := (uSum L μ : ℤ) - uSum L T with hδσ
  have hX : ((L.card : ℤ) - 1) *
      (∑ s ∈ L.erase t, ((expSteps p l μ s : ℤ) - expSteps p l T s) + δσ) =
        ∑ s ∈ L.erase t, D s := by
    rw [mul_add, Finset.mul_sum]
    have : ∀ s ∈ L.erase t, ((L.card : ℤ) - 1) * ((expSteps p l μ s : ℤ) - expSteps p l T s) =
        D s - δσ := fun s hs => by
      rw [mul_sub, hfμ.2 s (Finset.mem_of_mem_erase hs), hfT.2 s (Finset.mem_of_mem_erase hs),
        hD, hδσ]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem ht, Nat.cast_sub (by omega : 1 ≤ L.card)]
    push_cast
    ring
  have hpos : 0 ≤ ∑ s ∈ L.erase t, D s :=
    Finset.sum_nonneg fun s hs => (hineq s (Finset.mem_of_mem_erase hs)).1
  have h0 := nonneg_of_mul_nonneg_of_one_le hk' (by rw [hX]; exact hpos)
  rw [sum_univ_erase_eq ht, sum_univ_erase_eq ht]
  have hUμ : ∑ u ∈ Lᶜ, expSteps p l μ u = uSum L μ := uSum_expSteps p L hl (hE μ hμ)
  have hUT : ∑ u ∈ Lᶜ, expSteps p l T u = uSum L T := uSum_expSteps p L hl (hE T hT)
  rw [hUμ, hUT]
  rw [Finset.sum_sub_distrib] at h0
  have : ((∑ s ∈ L.erase t, expSteps p l T s : ℕ) : ℤ) + uSum L T ≤
      ((∑ s ∈ L.erase t, expSteps p l μ s : ℕ) : ℤ) + uSum L μ := by
    push_cast
    linarith
  exact_mod_cast this

omit [Fintype σ] in
/-- If `b` is a monomial of `F` with the least exponent of `x_i`, `i ∈ Δ`, then `r_i = b_i`. -/
theorem divisorExponent_apply_eq_of {F : MvPolynomial σ k} {i : σ} (hi : i ∈ Δ) {b : σ →₀ ℕ}
    (hb : b ∈ F.support) (hle : ∀ d ∈ F.support, b i ≤ d i) : divisorExponent Δ F i = b i := by
  rw [divisorExponent_apply, ite_eq_left hi]
  have hmem : b i ∈ (fun d : σ →₀ ℕ => d i) '' (F.support : Set (σ →₀ ℕ)) :=
    ⟨b, Finset.mem_coe.mpr hb, rfl⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
  rintro _ ⟨d, hd, rfl⟩
  exact hle d (Finset.mem_coe.mp hd)

/-- The exponent `r_u` of `u ∉ L` does not change along the run (Volume 7, Section 3.14 of the
handbook). -/
theorem divisorExponent_polySteps_of_notMem (hl : ∀ j ∈ l, j ∈ L) (hadm : IsAdmissible p l g)
    {u : σ} (hu : u ∉ L) : divisorExponent Δ (polySteps p l g) u = divisorExponent Δ g u := by
  rw [divisorExponent_apply, divisorExponent_apply]
  split_ifs
  · rw [(support_polySteps hadm).1, Finset.coe_image, Set.image_image]
    congr 1
    exact Set.image_congr fun μ _ =>
      expSteps_apply_of_forall_ne p (fun j hj (h : j = u) => hu (h ▸ hl j hj)) μ
  · rfl

omit [Fintype σ] [DecidableEq σ] in
/-- If `b` is a monomial of `g` of the least degree, then `ord g = |b|`. -/
theorem ord_eq_of_min {F : MvPolynomial σ k} {b : σ →₀ ℕ} (hb : b ∈ F.support)
    (hmin : ∀ d ∈ F.support, b.degree ≤ d.degree) : ord F = (b.degree : ℕ∞) := by
  refine le_antisymm (ord_le (MvPolynomial.mem_support_iff.mp hb)) (le_ord_iff.mpr fun d hd => ?_)
  by_contra hc
  have := hmin d (MvPolynomial.mem_support_iff.mpr hc)
  have hd' : d.degree < b.degree := by exact_mod_cast hd
  omega

omit [Fintype σ] in
/-- **The clean order along a coordinate subvariety** (Volume 7, Lemma 3.13.1 of the handbook,
for polynomials). If `g` is clean and `b` is a monomial of `g` with the least order along
`Z = V(x_i : i ∈ S)`, then `ν̄_Z(g) = Σ_{i ∈ S} b_i`. The reason is that `b` is not in `p ℕ^n`, so
no `p`-th power `h^p` has the monomial `b`. -/
theorem cleanOrdAlong_eq_of_min [CharP k p] (hp : p.Prime) {S : Finset σ} {F : MvPolynomial σ k}
    (hc : IsClean p F) {b : σ →₀ ℕ} (hb : b ∈ F.support)
    (hmin : ∀ d ∈ F.support, ∑ i ∈ S, b i ≤ ∑ i ∈ S, d i) :
    cleanOrdAlong p S F = ((∑ i ∈ S, b i : ℕ) : ℕ∞) := by
  have : ExpChar k p := ExpChar.prime hp
  refine le_antisymm (iSup_le fun h => ?_) ((le_ordAlong fun d hd => by
    exact_mod_cast hmin d hd).trans (ordAlong_le_cleanOrdAlong hp.ne_zero S F))
  have hpow := coeff_pow_eq_zero_of_not_dvd p 1 h (d := b) (by simpa using hc b hb)
  rw [pow_one] at hpow
  have hne : (F + h ^ p).coeff b ≠ 0 := by
    rw [coeff_add_apply, hpow, add_zero]
    exact MvPolynomial.mem_support_iff.mp hb
  exact ordAlong_le hne

/-- **Theorem 3.14.7, part 1** (Volume 7, Section 3.14 of the handbook). Let `L ⊆ Δ` have at least
two letters, let each letter of `l` be in `L`, let each step be defined, and let `T` be a monomial
of `g` such that each monomial of `g` satisfies `CornerIneq`. Then at the end of the run
`r_s = E_s(T)` for each `s ∈ L`. -/
theorem originRun_divisorExponent_eq (hk : 2 ≤ L.card) (hLΔ : L ⊆ Δ) (hl : ∀ j ∈ l, j ∈ L)
    (hadm : IsAdmissible p l g) (hT : T ∈ g.support)
    (hineq : ∀ μ ∈ g.support, CornerIneq p L (cols L l) T μ) :
    ∀ s ∈ L, divisorExponent Δ (polySteps p l g) s = expSteps p l T s := by
  intro s hs
  have hsupp := (support_polySteps hadm).1
  refine divisorExponent_apply_eq_of (hLΔ hs) (hsupp ▸ Finset.mem_image_of_mem _ hT) ?_
  intro d hd
  rw [hsupp, Finset.mem_image] at hd
  obtain ⟨μ, hμ, rfl⟩ := hd
  exact originRun_exp_le hk hl hadm hT hμ (hineq μ hμ) hs

/-- **Theorem 3.14.7, part 2, the degree** (Volume 7, Section 3.14 of the handbook). In the
setting of `originRun_divisorExponent_eq`, the order of `G` at the end of the run is
`d_m = σ(T) - r_U`, where `r_U = Σ_{u ∉ L} r_u` is computed at the start. -/
theorem originRun_ord_residualFactor (hk : 2 ≤ L.card) (hLΔ : L ⊆ Δ) (hl : ∀ j ∈ l, j ∈ L)
    (hadm : IsAdmissible p l g) (hT : T ∈ g.support)
    (hineq : ∀ μ ∈ g.support, CornerIneq p L (cols L l) T μ) :
    ord (residualFactor Δ (polySteps p l g)) =
      ((uSum L T - ∑ u ∈ Lᶜ, divisorExponent Δ g u : ℕ) : ℕ∞) := by
  set g' := polySteps p l g with hg'
  have hsupp := (support_polySteps hadm).1
  have hE := (support_polySteps hadm).2
  have hET : expSteps p l T ∈ g'.support := hsupp ▸ Finset.mem_image_of_mem _ hT
  have hord : ord g' = ((expSteps p l T).degree : ℕ∞) := by
    refine ord_eq_of_min hET fun d hd => ?_
    rw [hsupp, Finset.mem_image] at hd
    obtain ⟨μ, hμ, rfl⟩ := hd
    exact originRun_degree_le hk hl hadm hT hμ (hineq μ hμ)
  have hadd : ord (residualFactor Δ g') + ((divisorExponent Δ g').degree : ℕ∞) = ord g' :=
    ord_divMonomial_add fun β hβ => divisorExponent_le hβ
  have h1 := originRun_divisorExponent_eq hk hLΔ hl hadm hT hineq
  have hr : (divisorExponent Δ g').degree =
      ∑ s ∈ L, expSteps p l T s + ∑ u ∈ Lᶜ, divisorExponent Δ g u := by
    rw [degree_eq_sum_add_uSum L, uSum]
    congr 1
    · exact Finset.sum_congr rfl fun s hs => h1 s hs
    · exact Finset.sum_congr rfl fun u hu =>
        divisorExponent_polySteps_of_notMem hl hadm (Finset.mem_compl.mp hu)
  have hdT : (expSteps p l T).degree = ∑ s ∈ L, expSteps p l T s + uSum L T := by
    rw [degree_eq_sum_add_uSum L, uSum_expSteps p L hl (hE T hT)]
  rw [hord, hr, hdT] at hadd
  have hfin : ord (residualFactor Δ g') ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hadd
    exact ENat.top_ne_natCast _ hadd
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at hadd ⊢
  have : n + (∑ s ∈ L, expSteps p l T s + ∑ u ∈ Lᶜ, divisorExponent Δ g u) =
      ∑ s ∈ L, expSteps p l T s + uSum L T := by exact_mod_cast hadd
  congr 1
  omega

/-- **Theorem 3.14.7, part 3** (Volume 7, Section 3.14 of the handbook). In the setting of
`originRun_divisorExponent_eq`, let `g` be clean. For each `t ∈ L`, the corner curve
`C_t = V(x_i : i ≠ t)` has `ν^G_{C_t} = σ(T) - r_U` at the end of the run. This is `d_m` by
`originRun_ord_residualFactor`. -/
theorem originRun_orderGAlong_corner [CharP k p] (hp : p.Prime) (hc : IsClean p g)
    (hk : 2 ≤ L.card) (hLΔ : L ⊆ Δ) (hl : ∀ j ∈ l, j ∈ L) (hadm : IsAdmissible p l g)
    (hT : T ∈ g.support) (hineq : ∀ μ ∈ g.support, CornerIneq p L (cols L l) T μ) {t : σ}
    (ht : t ∈ L) :
    orderGAlong p Δ (Finset.univ.erase t) (polySteps p l g) =
      ((uSum L T - ∑ u ∈ Lᶜ, divisorExponent Δ g u : ℕ) : ℕ∞) := by
  set g' := polySteps p l g with hg'
  have hsupp := (support_polySteps hadm).1
  have hE := (support_polySteps hadm).2
  have hET : expSteps p l T ∈ g'.support := hsupp ▸ Finset.mem_image_of_mem _ hT
  have hmin : ∀ d ∈ g'.support,
      ∑ i ∈ Finset.univ.erase t, expSteps p l T i ≤ ∑ i ∈ Finset.univ.erase t, d i := by
    intro d hd
    rw [hsupp, Finset.mem_image] at hd
    obtain ⟨μ, hμ, rfl⟩ := hd
    exact originRun_corner_le hk hl hadm hT hμ (hineq μ hμ) ht
  have h1 := originRun_divisorExponent_eq hk hLΔ hl hadm hT hineq
  have hs : ∑ i ∈ Δ ∩ Finset.univ.erase t, divisorExponent Δ g' i =
      ∑ i ∈ Finset.univ.erase t, divisorExponent Δ g' i :=
    Finset.sum_subset Finset.inter_subset_right fun i hiS hi =>
      divisorExponent_eq_zero fun hiΔ => hi (Finset.mem_inter.mpr ⟨hiΔ, hiS⟩)
  rw [orderGAlong, cleanOrdAlong_eq_of_min hp (isClean_polySteps hadm hc) hET hmin, hs,
    ← ENat.natCast_sub]
  congr 1
  have e1 := sum_univ_erase_eq ht (expSteps p l T)
  have e2 := sum_univ_erase_eq ht (divisorExponent Δ g')
  have hL' : ∑ s ∈ L.erase t, divisorExponent Δ g' s = ∑ s ∈ L.erase t, expSteps p l T s :=
    Finset.sum_congr rfl fun s hs => h1 s (Finset.mem_of_mem_erase hs)
  have hU : ∑ u ∈ Lᶜ, divisorExponent Δ g' u = ∑ u ∈ Lᶜ, divisorExponent Δ g u :=
    Finset.sum_congr rfl fun u hu =>
      divisorExponent_polySteps_of_notMem hl hadm (Finset.mem_compl.mp hu)
  have hUT : ∑ u ∈ Lᶜ, expSteps p l T u = uSum L T := uSum_expSteps p L hl (hE T hT)
  omega

/-- **Theorem 3.14.7, part 3, `ν^G ≥ ρ`** (Volume 7, Section 3.14 of the handbook). In the setting
of `originRun_orderGAlong_corner`, each corner curve has `ν^G_{C_t} = d_m ≥ ρ` at the end of the
run. -/
theorem originRun_logJacobianOrder_le_orderGAlong [CharP k p] (hp : p.Prime) (hc : IsClean p g)
    (hk : 2 ≤ L.card) (hLΔ : L ⊆ Δ) (hl : ∀ j ∈ l, j ∈ L) (hadm : IsAdmissible p l g)
    (hT : T ∈ g.support) (hineq : ∀ μ ∈ g.support, CornerIneq p L (cols L l) T μ) {t : σ}
    (ht : t ∈ L) :
    orderGAlong p Δ (Finset.univ.erase t) (polySteps p l g) =
        ord (residualFactor Δ (polySteps p l g)) ∧
      logJacobianOrder Δ (polySteps p l g) ≤
        orderGAlong p Δ (Finset.univ.erase t) (polySteps p l g) := by
  have h1 : orderGAlong p Δ (Finset.univ.erase t) (polySteps p l g) =
      ord (residualFactor Δ (polySteps p l g)) := by
    rw [originRun_orderGAlong_corner hp hc hk hLΔ hl hadm hT hineq ht,
      originRun_ord_residualFactor hk hLΔ hl hadm hT hineq]
  exact ⟨h1, h1 ▸ logJacobianOrder_le p (isClean_polySteps hadm hc)⟩

omit [Fintype σ] in
/-- If each letter is in `Δ`, the divisor does not change along the run. -/
theorem runDivisor_eq_of_forall_mem {w : ℕ → σ} (hw : ∀ m, w m ∈ Δ) (m : ℕ) :
    runDivisor w Δ m = Δ := by
  induction m with
  | zero => rfl
  | succ m ih => rw [runDivisor, ih, Finset.insert_eq_of_mem (hw m)]

/-- **Theorem 3.14.7, parts 1, 2 and 3, for an infinite origin run** (Volume 7, Section 3.14 of
the handbook). Let `g` be clean, let `L ⊆ Δ` have at least two letters, and let `w` be the letters
of an origin run where each letter is in `L` and each step is defined. Let `T` be a monomial of
`g`, and assume that at the point `P_m` the inequalities `CornerIneq` hold for the columns of the
first `m` steps. Then at `P_m` the divisor is `Δ`, `r_s = E_s(T)` for `s ∈ L`, the order of `G` is
`d_m = σ(T) - r_U`, and each corner curve `C_t`, `t ∈ L`, has `ν^G_{C_t} = d_m ≥ ρ`. The handbook
gets the inequalities for `m` large from Proposition 3.14.4 and Lemma 3.14.6. Here they are a
hypothesis. -/
theorem originRun_cornerCurves [CharP k p] (hp : p.Prime) (hc : IsClean p g) (hk : 2 ≤ L.card)
    (hLΔ : L ⊆ Δ) {w : ℕ → σ} (hw : ∀ m, w m ∈ L) (hadm : ∀ m, DegreeGe p (runPoly p w g m))
    (hT : T ∈ g.support) (m : ℕ)
    (hineq : ∀ μ ∈ g.support, CornerIneq p L (cols L (runList w 0 m)) T μ) :
    runDivisor w Δ m = Δ ∧
      (∀ s ∈ L, divisorExponent Δ (runPoly p w g m) s = expSteps p (runList w 0 m) T s) ∧
      ord (residualFactor Δ (runPoly p w g m)) =
        ((uSum L T - ∑ u ∈ Lᶜ, divisorExponent Δ g u : ℕ) : ℕ∞) ∧
      ∀ t ∈ L, orderGAlong p Δ (Finset.univ.erase t) (runPoly p w g m) =
          ord (residualFactor Δ (runPoly p w g m)) ∧
        logJacobianOrder Δ (runPoly p w g m) ≤
          orderGAlong p Δ (Finset.univ.erase t) (runPoly p w g m) := by
  have hrun : runPoly p w g m = polySteps p (runList w 0 m) g := by
    have := runPoly_add p w g 0 m
    rwa [zero_add] at this
  have hl : ∀ j ∈ runList w 0 m, j ∈ L := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hj
    exact hw _
  have hadm' : IsAdmissible p (runList w 0 m) g := isAdmissible_runList hadm 0 m
  rw [hrun]
  exact ⟨runDivisor_eq_of_forall_mem (fun m => hLΔ (hw m)) m,
    originRun_divisorExponent_eq hk hLΔ hl hadm' hT hineq,
    originRun_ord_residualFactor hk hLΔ hl hadm' hT hineq,
    fun t ht => originRun_logJacobianOrder_le_orderGAlong hp hc hk hLΔ hl hadm' hT hineq ht⟩

end TheoremB

/-! ### Example 3.14.9 -/

section Example

/-- A sum of two monomials of degree at least `n` has the order at least `n`. -/
theorem le_ord_monomial_add_monomial {σ R : Type*} [CommSemiring R] {n : ℕ} {A B : σ →₀ ℕ}
    (hA : n ≤ A.degree) (hB : n ≤ B.degree) (a b : R) :
    (n : ℕ∞) ≤ ord (monomial A a + monomial B b) := by
  classical
  refine le_ord_iff.mpr fun d hd => ?_
  rw [coeff_add_apply, coeff_monomial, coeff_monomial, ite_eq_right (by rintro rfl; omega),
    ite_eq_right (by rintro rfl; omega), add_zero]

variable (p : ℕ) [Fact p.Prime]

/-- The exponent `(1, 1, 1, 0)` of `x_1 x_2 x_3`. -/
noncomputable def exOnes : Fin 4 →₀ ℕ := single 0 1 + single 1 1 + single 2 1

/-- The residual factor `G = x_4^p + x_1 x_2 x_3 x_4^(p-2)` of Example 3.14.9. -/
noncomputable def exG : MvPolynomial (Fin 4) (ZMod p) :=
  monomial (single 3 p) 1 + monomial (exOnes + single 3 (p - 2)) 1

/-- The polynomial `x^v (x_4^p + x_1 x_2 x_3 x_4^(p-2))` of Example 3.14.9. -/
noncomputable def exPoly (v : Fin 4 →₀ ℕ) : MvPolynomial (Fin 4) (ZMod p) :=
  monomial (v + single 3 p) 1 + monomial (v + exOnes + single 3 (p - 2)) 1

/-- The divisor `Δ = {x_1, x_2, x_3}` of Example 3.14.9. -/
def exDivisor : Finset (Fin 4) := {0, 1, 2}

/-- The step with the letter `j` on the exponent `v` of the monomial factor: `v_j ← |v|`. -/
noncomputable def exStep (j : Fin 4) (v : Fin 4 →₀ ℕ) : Fin 4 →₀ ℕ := Finsupp.update v j v.degree

/-- The steps with the letters of `l` on the exponent of the monomial factor. -/
noncomputable def exSteps (l : List (Fin 4)) (v : Fin 4 →₀ ℕ) : Fin 4 →₀ ℕ :=
  l.foldl (fun v j => exStep j v) v

variable {p}

/-- The prime `p` is at least `2`. -/
theorem two_le_p : 2 ≤ p := (Fact.out : p.Prime).two_le

omit [Fact p.Prime] in
/-- The two monomials of `x^v G` are different. -/
theorem exPoly_ne (v : Fin 4 →₀ ℕ) : v + single 3 p ≠ v + exOnes + single 3 (p - 2) := by
  intro h
  have := DFunLike.congr_fun h 0
  simp [exOnes] at this

/-- The residual factor `G` is `x^v G` for `v = 0`. -/
theorem exG_eq_exPoly : exG p = exPoly p 0 := by
  simp [exG, exPoly]

/-- The residual factor of Example 3.14.9 is `x_4^p + x_1 x_2 x_3 x_4^(p-2)`. -/
theorem exG_eq : exG p = X 3 ^ p + X 0 * X 1 * X 2 * X 3 ^ (p - 2) := by
  rw [exG, X_pow_eq_monomial, X_pow_eq_monomial]
  simp only [X, monomial_mul_monomial, mul_one, exOnes]

/-- The polynomial `exPoly p v` is the product of `x^v` and `G`. -/
theorem exPoly_eq_mul (v : Fin 4 →₀ ℕ) : exPoly p v = monomial v 1 * exG p := by
  rw [exPoly, exG, mul_add, monomial_mul_monomial, monomial_mul_monomial, one_mul, add_assoc]

/-- **The start of Example 3.14.9**: `g = x_1 x_4^p + x_1^2 x_2 x_3 x_4^(p-2)`. -/
theorem exPoly_start :
    exPoly p (single 0 1) = X 0 * X 3 ^ p + X 0 ^ 2 * X 1 * X 2 * X 3 ^ (p - 2) := by
  rw [exPoly_eq_mul, exG_eq, show (monomial (single 0 1) 1 : MvPolynomial (Fin 4) (ZMod p)) = X 0
    from rfl]
  ring

/-- Each monomial of `x^v G` is one of its two monomials. -/
theorem mem_support_exPoly {v d : Fin 4 →₀ ℕ} (hd : d ∈ (exPoly p v).support) :
    d = v + single 3 p ∨ d = v + exOnes + single 3 (p - 2) := by
  by_contra hne
  push Not at hne
  apply MvPolynomial.mem_support_iff.mp hd
  rw [exPoly, coeff_add_apply, coeff_monomial, coeff_monomial, ite_eq_right (Ne.symm hne.1),
    ite_eq_right (Ne.symm hne.2), add_zero]

/-- The coefficient of `x^v x_4^p` in `x^v G` is `1`. -/
theorem coeff_exPoly_left (v : Fin 4 →₀ ℕ) : (exPoly p v).coeff (v + single 3 p) = 1 := by
  rw [exPoly, coeff_add_apply, coeff_monomial, coeff_monomial, ite_eq_left rfl,
    ite_eq_right (exPoly_ne v).symm, add_zero]

/-- The coefficient of `x^v x_1 x_2 x_3 x_4^(p-2)` in `x^v G` is `1`. -/
theorem coeff_exPoly_right (v : Fin 4 →₀ ℕ) :
    (exPoly p v).coeff (v + exOnes + single 3 (p - 2)) = 1 := by
  rw [exPoly, coeff_add_apply, coeff_monomial, coeff_monomial,
    ite_eq_right (exPoly_ne v), ite_eq_left rfl, zero_add]

/-- The polynomial `x^v G` is not `0`. -/
theorem exPoly_ne_zero (v : Fin 4 →₀ ℕ) : exPoly p v ≠ 0 := by
  intro h
  have := coeff_exPoly_left (p := p) v
  rw [h] at this
  simp at this

omit [Fact p.Prime] in
/-- The degree of `x^v x_4^p` is `|v| + p`. -/
theorem degree_exLeft (v : Fin 4 →₀ ℕ) : (v + single 3 p).degree = v.degree + p := by
  rw [map_add, Finsupp.degree_single]

omit [Fact p.Prime] in
/-- The degree of `x^v x_1 x_2 x_3 x_4^(p-2)` is `|v| + 3 + (p - 2)`. -/
theorem degree_exRight (v : Fin 4 →₀ ℕ) :
    (v + exOnes + single 3 (p - 2)).degree = v.degree + 3 + (p - 2) := by
  simp only [exOnes, map_add, Finsupp.degree_single]

/-- Each monomial of `x^v G` has the degree at least `p`, so each origin step is defined. -/
theorem degreeGe_exPoly (v : Fin 4 →₀ ℕ) : DegreeGe p (exPoly p v) := by
  intro d hd
  rcases mem_support_exPoly hd with rfl | rfl
  · rw [degree_exLeft]
    omega
  · rw [degree_exRight]
    omega

omit [Fact p.Prime] in
/-- The origin step with a letter `j ≠ 4` on the exponent of `x^v x_4^p`. -/
theorem expStep_exLeft {j : Fin 4} (hj : j ≠ 3) (v : Fin 4 →₀ ℕ) :
    expStep p j (v + single 3 p) = exStep j v + single 3 p := by
  ext i
  by_cases hi : i = j
  · subst hi
    rw [expStep_apply_self, degree_exLeft, exStep, Finsupp.coe_add, Pi.add_apply,
      Finsupp.update_apply, ite_eq_left rfl, Finsupp.single_eq_of_ne hj, add_zero,
      Nat.add_sub_cancel]
  · rw [expStep_apply_of_ne p hi, exStep, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_add,
      Pi.add_apply, Finsupp.update_apply, ite_eq_right hi]

/-- The entries of `(1, 1, 1, 0)` at the first three indices are `1`. -/
theorem exOnes_apply {j : Fin 4} (hj : j ≠ 3) : exOnes j = 1 := by
  fin_cases j <;> simp_all [exOnes]

/-- The origin step with a letter `j ≠ 4` on the exponent of `x^v x_1 x_2 x_3 x_4^(p-2)`. -/
theorem expStep_exRight {j : Fin 4} (hj : j ≠ 3) (v : Fin 4 →₀ ℕ) :
    expStep p j (v + exOnes + single 3 (p - 2)) = exStep j v + exOnes + single 3 (p - 2) := by
  have hp := two_le_p (p := p)
  ext i
  by_cases hi : i = j
  · subst hi
    rw [expStep_apply_self, degree_exRight, exStep, Finsupp.coe_add, Pi.add_apply,
      Finsupp.coe_add, Pi.add_apply, Finsupp.update_apply, ite_eq_left rfl,
      Finsupp.single_eq_of_ne hj, add_zero, exOnes_apply hj]
    omega
  · rw [expStep_apply_of_ne p hi, exStep, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_add,
      Pi.add_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.update_apply, ite_eq_right hi]

/-- **An origin step of Example 3.14.9**: the step with a letter `j ∈ {1, 2, 3}` sends
`x^v (x_4^p + x_1 x_2 x_3 x_4^(p-2))` to the same form with `v_j ← |v|`. -/
theorem originTransform_exPoly {j : Fin 4} (hj : j ≠ 3) (v : Fin 4 →₀ ℕ) :
    originTransform p j (exPoly p v) = exPoly p (exStep j v) := by
  have hX : (X j ^ p : MvPolynomial (Fin 4) (ZMod p)) ≠ 0 := pow_ne_zero _ (X_ne_zero j)
  refine mul_left_cancel₀ hX ?_
  have hp := two_le_p (p := p)
  rw [← pointChart_eq_X_pow_mul_originTransform j (degreeGe_exPoly v), exPoly, map_add,
    pointChart_monomial p j (by rw [degree_exLeft]; omega),
    pointChart_monomial p j (by rw [degree_exRight]; omega), expStep_exLeft hj,
    expStep_exRight hj, exPoly, mul_add]

/-- A step with a letter `j ≠ 4` keeps `v_4`. -/
theorem exStep_apply_three {j : Fin 4} (hj : j ≠ 3) (v : Fin 4 →₀ ℕ) :
    exStep j v 3 = v 3 := by
  rw [exStep, Finsupp.update_apply, ite_eq_right (Ne.symm hj)]

/-- Steps with letters other than `4` keep `v_4`. -/
theorem exSteps_apply_three {l : List (Fin 4)} (hl : ∀ j ∈ l, j ≠ 3) (v : Fin 4 →₀ ℕ) :
    exSteps l v 3 = v 3 := by
  induction l generalizing v with
  | nil => rfl
  | cons j l ih =>
    rw [show exSteps (j :: l) v = exSteps l (exStep j v) from rfl,
      ih (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')),
      exStep_apply_three (hl j List.mem_cons_self)]

/-- **The points of Example 3.14.9**: after the steps with letters in `{1, 2, 3}`, the point is
`x^v (x_4^p + x_1 x_2 x_3 x_4^(p-2))`, and each step is defined. -/
theorem polySteps_exPoly {l : List (Fin 4)} (hl : ∀ j ∈ l, j ≠ 3) (v : Fin 4 →₀ ℕ) :
    polySteps p l (exPoly p v) = exPoly p (exSteps l v) ∧ IsAdmissible p l (exPoly p v) := by
  induction l generalizing v with
  | nil => exact ⟨rfl, trivial⟩
  | cons j l ih =>
    have hj := hl j List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')) (exStep j v)
    refine ⟨?_, degreeGe_exPoly v, ?_⟩
    · rw [polySteps_cons, originTransform_exPoly hj, h1]
      rfl
    · rw [originTransform_exPoly hj]
      exact h2

/-- The start of Example 3.14.9 is clean. -/
theorem isClean_exPoly_start : IsClean p (exPoly p (single 0 1)) := by
  have hp := (Fact.out : p.Prime)
  intro d hd hall
  rcases mem_support_exPoly hd with rfl | rfl
  · have := hall 0
    simp [Nat.dvd_one, hp.ne_one] at this
  · have := hall 1
    simp [exOnes, Nat.dvd_one, hp.ne_one] at this

/-- If `v_4 = 0`, then `x^v` has its support in the divisor. -/
theorem exDivisor_hr {v : Fin 4 →₀ ℕ} (hv : v 3 = 0) : ∀ i, i ∉ exDivisor → v i = 0 := by
  intro i hi
  fin_cases i <;> simp_all [exDivisor]

/-- For each `i ∈ Δ`, the monomial `x_4^p` of `G` does not contain `x_i`. -/
theorem exDivisor_hG : ∀ i ∈ exDivisor, ∃ d ∈ (exG p).support, d i = 0 := by
  intro i hi
  refine ⟨single 3 p, ?_, ?_⟩
  · rw [MvPolynomial.mem_support_iff, exG_eq_exPoly]
    have := coeff_exPoly_left (p := p) 0
    rw [zero_add] at this
    rw [this]
    exact one_ne_zero
  · fin_cases i <;> simp_all [exDivisor]

/-- If `v_4 = 0`, the exponent of the divisor part of `x^v G` is `v`. -/
theorem divisorExponent_exPoly {v : Fin 4 →₀ ℕ} (hv : v 3 = 0) :
    divisorExponent exDivisor (exPoly p v) = v := by
  rw [exPoly_eq_mul]
  exact KangarooCounterexample.divisorExponent_monomial_mul' (exDivisor_hr hv) exDivisor_hG

/-- If `v_4 = 0`, the residual factor of `x^v G` is `G`. -/
theorem residualFactor_exPoly {v : Fin 4 →₀ ℕ} (hv : v 3 = 0) :
    residualFactor exDivisor (exPoly p v) = exG p := by
  rw [exPoly_eq_mul]
  exact residualFactor_monomial_mul (exDivisor_hr hv) exDivisor_hG

/-- **`d = p`** (Example 3.14.9). -/
theorem ord_exG : ord (exG p) = p := by
  have hp := two_le_p (p := p)
  refine le_antisymm ?_ ?_
  · have h := coeff_exPoly_left (p := p) 0
    rw [zero_add, ← exG_eq_exPoly] at h
    have := ord_le (f := exG p) (d := single 3 p) (by rw [h]; exact one_ne_zero)
    rwa [Finsupp.degree_single] at this
  · rw [exG]
    refine le_ord_monomial_add_monomial (by rw [Finsupp.degree_single]) ?_ _ _
    simp only [exOnes, map_add, Finsupp.degree_single]
    omega

/-- The generator `c G + x_i ∂_i G` for `i ≠ 4` is `c x_4^p + (c + 1) x_1 x_2 x_3 x_4^(p-2)`. -/
theorem exGen_eq {i : Fin 4} (hi : i ≠ 3) (c : ZMod p) :
    c • exG p + X i * pderiv i (exG p) =
      monomial (single 3 p) c + monomial (exOnes + single 3 (p - 2)) (c + 1) := by
  have hBi : (exOnes + single 3 (p - 2) : Fin 4 →₀ ℕ) i = 1 := by
    rw [Finsupp.coe_add, Pi.add_apply, exOnes_apply hi, Finsupp.single_eq_of_ne hi, add_zero]
  rw [exG, map_add, mul_add, X_mul_pderiv_monomial, X_mul_pderiv_monomial, smul_add, smul_monomial,
    smul_monomial, Finsupp.single_eq_of_ne hi, hBi, zero_smul, one_smul, smul_eq_mul, mul_one,
    map_add]
  abel

/-- The derivative `∂_4 G` is `(p - 2) x_1 x_2 x_3 x_4^(p-3)`. -/
theorem pderiv_three_exG :
    pderiv 3 (exG p) =
      monomial (exOnes + single 3 (p - 2) - single 3 1) ((p - 2 : ℕ) : ZMod p) := by
  rw [exG, map_add, pderiv_monomial, pderiv_monomial, Finsupp.single_eq_same,
    ZMod.natCast_self, mul_zero, monomial_zero, zero_add, one_mul]
  congr 2
  rw [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
  simp [exOnes]

/-- **`ρ = p`** (Example 3.14.9). At each point `x^v G` with `v_4 = 0` that is clean, the order of
the residual log-Jacobian ideal is `p`. The generators `r_s G + x_s ∂_s G` and `∂_4 G` have the
order at least `p`. Since the monomial `x^v x_4^p` is not a `p`-th power, some `r_s` is not `0`
mod `p`, and the generator of `s` has the term `r_s x_4^p`. -/
theorem logJacobianOrder_exPoly {v : Fin 4 →₀ ℕ} (hv : v 3 = 0) (hc : IsClean p (exPoly p v)) :
    logJacobianOrder exDivisor (exPoly p v) = p := by
  have hp := two_le_p (p := p)
  rw [logJacobianOrder, divisorExponent_exPoly hv, residualFactor_exPoly hv]
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, ¬ p ∣ (v + single 3 p : Fin 4 →₀ ℕ) i := by
    have := hc _ (MvPolynomial.mem_support_iff.mpr (by rw [coeff_exPoly_left]; exact one_ne_zero))
    push Not at this
    exact this
  have hi3 : i ≠ 3 := by
    rintro rfl
    simp [hv] at hi
  have hvi : ¬ p ∣ v i := by
    rwa [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hi3, add_zero] at hi
  have hvi' : ((v i : ℕ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hlow : ∀ c c' : ZMod p, (p : ℕ∞) ≤
      ord (monomial (single 3 p) c + monomial (exOnes + single 3 (p - 2)) c') := by
    intro c c'
    refine le_ord_monomial_add_monomial (by rw [Finsupp.degree_single]) ?_ _ _
    simp only [exOnes, map_add, Finsupp.degree_single]
    omega
  refine SurfaceRuns.idealOrd_span_eq' ?_ (f := (v i : ZMod p) • exG p + X i * pderiv i (exG p))
    (Or.inl ⟨i, by fin_cases i <;> simp_all [exDivisor], rfl⟩) ?_
  · rintro s (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · have hj3 : j ≠ 3 := by
        rintro rfl
        simp [exDivisor] at hj
      beta_reduce
      rw [exGen_eq hj3]
      exact hlow _ _
    · have hj3 : j = 3 := by
        fin_cases j <;> simp_all [exDivisor]
      subst hj3
      beta_reduce
      rw [pderiv_three_exG]
      by_cases h0 : ((p - 2 : ℕ) : ZMod p) = 0
      · rw [h0, monomial_zero, ord_zero]
        exact le_top
      · have hp3 : 3 ≤ p := by
          by_contra h
          have : p - 2 = 0 := by omega
          rw [this, Nat.cast_zero] at h0
          exact h0 rfl
        rw [ord_monomial h0]
        have : (exOnes + single 3 (p - 2) - single 3 1 : Fin 4 →₀ ℕ) =
            exOnes + single 3 (p - 3) := by
          ext l
          fin_cases l <;> simp [exOnes]
          omega
        rw [this]
        simp only [exOnes, map_add, Finsupp.degree_single]
        exact_mod_cast (by omega : p ≤ 1 + 1 + 1 + (p - 3))
  · rw [exGen_eq hi3]
    refine le_antisymm ?_ (hlow _ _)
    have hcoeff : (monomial (single 3 p) ((v i : ℕ) : ZMod p) +
        monomial (exOnes + single 3 (p - 2)) (((v i : ℕ) : ZMod p) + 1)).coeff (single 3 p) ≠
          0 := by
      have hne : exOnes + single 3 (p - 2) ≠ single 3 p := by
        have := exPoly_ne (p := p) 0
        rw [zero_add, zero_add] at this
        exact this.symm
      rw [coeff_add_apply, coeff_monomial, coeff_monomial, ite_eq_left rfl, ite_eq_right hne,
        add_zero]
      exact hvi'
    have := ord_le hcoeff
    rwa [Finsupp.degree_single] at this

/-- The clean order of `x^v G` along `Z = V(x_i : i ∈ S)` is the least order of its two
monomials. -/
theorem cleanOrdAlong_exPoly (S : Finset (Fin 4)) {v : Fin 4 →₀ ℕ}
    (hc : IsClean p (exPoly p v)) :
    cleanOrdAlong p S (exPoly p v) =
      ((min (∑ i ∈ S, (v + single 3 p : Fin 4 →₀ ℕ) i)
        (∑ i ∈ S, (v + exOnes + single 3 (p - 2) : Fin 4 →₀ ℕ) i) : ℕ) : ℕ∞) := by
  have hA : v + single 3 p ∈ (exPoly p v).support :=
    MvPolynomial.mem_support_iff.mpr (by rw [coeff_exPoly_left]; exact one_ne_zero)
  have hB : v + exOnes + single 3 (p - 2) ∈ (exPoly p v).support :=
    MvPolynomial.mem_support_iff.mpr (by rw [coeff_exPoly_right]; exact one_ne_zero)
  rcases le_total (∑ i ∈ S, (v + single 3 p : Fin 4 →₀ ℕ) i)
      (∑ i ∈ S, (v + exOnes + single 3 (p - 2) : Fin 4 →₀ ℕ) i) with h | h
  · rw [min_eq_left h]
    refine cleanOrdAlong_eq_of_min (Fact.out : p.Prime) hc hA fun d hd => ?_
    rcases mem_support_exPoly hd with rfl | rfl
    · exact le_rfl
    · exact h
  · rw [min_eq_right h]
    refine cleanOrdAlong_eq_of_min (Fact.out : p.Prime) hc hB fun d hd => ?_
    rcases mem_support_exPoly hd with rfl | rfl
    · exact h
    · exact le_rfl

/-- **The corner curves of Example 3.14.9.** For `t ∈ {1, 2, 3}`, the curve
`C_t = V(x_i : i ≠ t)` has `ν^G = p`. -/
theorem orderGAlong_exPoly_curve {v : Fin 4 →₀ ℕ} (hv : v 3 = 0) (hc : IsClean p (exPoly p v))
    {t : Fin 4} (ht : t ≠ 3) :
    orderGAlong p exDivisor (Finset.univ.erase t) (exPoly p v) = p := by
  have hp := two_le_p (p := p)
  rw [orderGAlong, cleanOrdAlong_exPoly _ hc, divisorExponent_exPoly hv, ← ENat.natCast_sub]
  congr 1
  rcases (by fin_cases t <;> simp_all : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  · rw [show (Finset.univ.erase (0 : Fin 4)) = {1, 2, 3} by decide,
      show exDivisor ∩ ({1, 2, 3} : Finset (Fin 4)) = {1, 2} by decide]
    simp [exOnes, Finset.sum_insert, Finsupp.single_apply, hv]
    omega
  · rw [show (Finset.univ.erase (1 : Fin 4)) = {0, 2, 3} by decide,
      show exDivisor ∩ ({0, 2, 3} : Finset (Fin 4)) = {0, 2} by decide]
    simp [exOnes, Finset.sum_insert, Finsupp.single_apply, hv]
    omega
  · rw [show (Finset.univ.erase (2 : Fin 4)) = {0, 1, 3} by decide,
      show exDivisor ∩ ({0, 1, 3} : Finset (Fin 4)) = {0, 1} by decide]
    simp [exOnes, Finset.sum_insert, Finsupp.single_apply, hv]
    omega

/-- **The surfaces of Example 3.14.9.** For `s ∈ {1, 2, 3}`, the surface `V(x_4, x_s)` has
`ν^G = p - 1`. -/
theorem orderGAlong_exPoly_surface {v : Fin 4 →₀ ℕ} (hv : v 3 = 0) (hc : IsClean p (exPoly p v))
    {s : Fin 4} (hs : s ≠ 3) :
    orderGAlong p exDivisor {3, s} (exPoly p v) = (p - 1 : ℕ) := by
  have hp := two_le_p (p := p)
  rw [orderGAlong, cleanOrdAlong_exPoly _ hc, divisorExponent_exPoly hv, ← ENat.natCast_sub]
  congr 1
  rcases (by fin_cases s <;> simp_all : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
  · rw [show exDivisor ∩ ({3, 0} : Finset (Fin 4)) = {0} by decide]
    simp [exOnes, Finset.sum_insert, Finsupp.single_apply, hv]
    omega
  · rw [show exDivisor ∩ ({3, 1} : Finset (Fin 4)) = {1} by decide]
    simp [exOnes, Finset.sum_insert, Finsupp.single_apply, hv]
    omega
  · rw [show exDivisor ∩ ({3, 2} : Finset (Fin 4)) = {2} by decide]
    simp [exOnes, Finset.sum_insert, Finsupp.single_apply, hv]
    omega

/-- **The surface `V(x_4)` of Example 3.14.9** has `ν^G = p - 2`. -/
theorem orderGAlong_exPoly_x4 {v : Fin 4 →₀ ℕ} (hv : v 3 = 0) (hc : IsClean p (exPoly p v)) :
    orderGAlong p exDivisor {3} (exPoly p v) = (p - 2 : ℕ) := by
  have hp := two_le_p (p := p)
  rw [orderGAlong, cleanOrdAlong_exPoly _ hc, divisorExponent_exPoly hv, ← ENat.natCast_sub,
    show exDivisor ∩ ({3} : Finset (Fin 4)) = ∅ by decide]
  congr 1
  simp [exOnes, Finsupp.single_apply, hv]

/-- **Each origin step of Example 3.14.9 keeps `ρ = p`.** At a clean point `x^v G` with
`v_4 = 0`, the origin of the `x_j`-chart for `j ∈ {1, 2, 3}` is a blowup step where `ρ = p` at
both points, and the divisor stays `{x_1, x_2, x_3}`. -/
theorem rhoStep_exPoly {j : Fin 4} (hj : j ≠ 3) {v : Fin 4 →₀ ℕ} (hv : v 3 = 0)
    (hc : IsClean p (exPoly p v)) :
    RhoStep p p (exDivisor, exPoly p v) (exDivisor, exPoly p (exStep j v)) := by
  have hjΔ : j ∈ exDivisor := by fin_cases j <;> simp_all [exDivisor]
  have hc' : IsClean p (exPoly p (exStep j v)) := by
    rw [← originTransform_exPoly hj]
    exact isClean_originTransform j (degreeGe_exPoly v) hc
  have h := rhoStep_originStep (m := p) (Δ := exDivisor) (j := j) (exPoly_ne_zero v) hc
    (le_ord_of_degreeGe (degreeGe_exPoly v)) (logJacobianOrder_exPoly hv hc)
    (by rw [Finset.insert_eq_of_mem hjΔ, originTransform_exPoly hj]
        exact logJacobianOrder_exPoly ((exStep_apply_three hj v).trans hv) hc')
  rwa [Finset.insert_eq_of_mem hjΔ, originTransform_exPoly hj] at h

/-- **Example 3.14.9** (Volume 7, Section 3.14 of the handbook). Let `n = 4`, `Δ = {x_1, x_2, x_3}`
and `g = x_1 x_4^p + x_1^2 x_2 x_3 x_4^(p-2)` over `ZMod p`. Let `l` be a word in the letters
`1, 2, 3` (the indices `0, 1, 2`). Then each step of the origin run with the letters `l` is
defined, and at its end the point is `x^v (x_4^p + x_1 x_2 x_3 x_4^(p-2))` with `v_4 = 0`. It is
clean, `ρ = d = p`, the three corner curves have `ν^G = p`, the surfaces `V(x_4, x_s)` have
`ν^G = p - 1 < ρ`, the surface `V(x_4)` has `ν^G = p - 2`, and the next step with a letter in
`{1, 2, 3}` keeps `ρ = p`. -/
theorem example_3_14_9 {l : List (Fin 4)} (hl : ∀ j ∈ l, j ≠ 3) :
    let v := exSteps l (single 0 1)
    polySteps p l (exPoly p (single 0 1)) = exPoly p v ∧
      IsAdmissible p l (exPoly p (single 0 1)) ∧ IsClean p (exPoly p v) ∧
      logJacobianOrder exDivisor (exPoly p v) = p ∧
      ord (residualFactor exDivisor (exPoly p v)) = p ∧
      (∀ t, t ≠ 3 → orderGAlong p exDivisor (Finset.univ.erase t) (exPoly p v) = p) ∧
      (∀ s, s ≠ 3 → orderGAlong p exDivisor {3, s} (exPoly p v) = (p - 1 : ℕ) ∧
        ((p - 1 : ℕ) : ℕ∞) < logJacobianOrder exDivisor (exPoly p v)) ∧
      orderGAlong p exDivisor {3} (exPoly p v) = (p - 2 : ℕ) ∧
      ∀ j, j ≠ 3 → RhoStep p p (exDivisor, exPoly p v) (exDivisor, exPoly p (exStep j v)) := by
  intro v
  have hp := two_le_p (p := p)
  obtain ⟨h1, h2⟩ := polySteps_exPoly (p := p) hl (single 0 1)
  have hv : v 3 = 0 := by
    rw [exSteps_apply_three hl]
    simp
  have hc : IsClean p (exPoly p v) := h1 ▸ isClean_polySteps h2 isClean_exPoly_start
  have hρ := logJacobianOrder_exPoly hv hc
  refine ⟨h1, h2, hc, hρ, by rw [residualFactor_exPoly hv, ord_exG], fun t ht =>
    orderGAlong_exPoly_curve hv hc ht, fun s hs => ⟨orderGAlong_exPoly_surface hv hc hs, ?_⟩,
    orderGAlong_exPoly_x4 hv hc, fun j hj => rhoStep_exPoly hj hv hc⟩
  rw [hρ]
  exact_mod_cast (by omega : p - 1 < p)

end Example

end OriginRuns

end Singularity
