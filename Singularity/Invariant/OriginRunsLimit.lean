/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.OriginRunsCorner

/-!
# The limit argument for origin runs that use some of the charts

This file proves Lemma 3.14.6 of Volume 7 of the handbook for polynomials, in a combinatorial
form, and so it removes the hypothesis `CornerIneq` from parts 1, 2 and 3 of Theorem 3.14.7.

## The sign of a difference along the columns

Let `L` be a set of `k ≥ 2` letters, and let `c_s`, `s ∈ L`, be the exponent columns of the run
(`cols`). For an integer vector `δ` on `L`, the vector `(δ · c_s)_{s ∈ L}` changes at a step with
the letter `j` by the rule `δ_j ← Σ_s δ_s` of Lemma 3.14.2 (`colDot_colStep`, `colDot_colSteps`).
For two exponent vectors `μ` and `ν`, the vector `(q(μ) - q(ν)) · c_s` is this vector for
`δ = q(μ) - q(ν)` (`qDot_sub_cols`).

The handbook uses the limit ray `ω` of Proposition 3.14.4. This file does not use it. It uses
these facts on the step of Lemma 3.14.2 instead:

1. The step keeps `δ ≠ 0` (`diffSteps_ne_zero`).
2. If `δ ≥ 0`, the step does not make an entry smaller (`le_diffSteps_of_nonneg`).
3. If `δ ≥ 0` and `δ ≠ 0`, a window with all the letters makes each entry at least `1`. If each
   entry is at least `a ≥ 1`, a window makes each entry at least `a + 1`, since `k ≥ 2`
   (`add_length_le_diffSteps`).
4. By part 4 of Lemma 3.14.2, after `Φ(δ)` windows `δ` is not strictly mixed. So after `Φ(δ) + B`
   windows, each entry is at least `B`, or each entry is at most `-B`
   (`diffSteps_windows_sign`).

So in a run where each letter of `L` occurs an infinite number of times, for each `δ ≠ 0` and
each bound `B`, from some point on each entry of the vector is at least `B`, or from some point
on each entry is at most `-B` (`eventually_sign`).

## Lemma 3.14.6 and Theorem 3.14.7

Let `S` be a finite set of exponent vectors, for example the support of `g`. Choose `m₀` after
the point where the signs of all the differences `q(μ) - q(ν)`, `μ, ν ∈ S`, are fixed, with the
bound `B = 1 + max σ`. Let `T` be a vector of `S` with the least value of `q(T) · c_{s₀}` at `m₀`
for a fixed letter `s₀`, and with the largest `σ(T)` among these vectors. Then for each `m ≥ m₀`
and each `μ ∈ S`, either `q(μ) = q(T)` and `σ(μ) ≤ σ(T)`, or
`Δq(μ) · c_s ≥ max(1, Δσ(μ))` for each `s ∈ L` (`exists_corner_le_eventually`). This gives
`CornerIneq` for each monomial (`exists_cornerIneq_eventually`). So parts 1, 2 and 3 of
Theorem 3.14.7 hold at each point after `m₀`, with no hypothesis on the inequalities
(`originRun_cornerCurves_eventually`).

The vector `T` of this file is in the set `F_top` of the handbook, but the file does not prove
this, since it does not define `ω`. The statement that the initial form of `G_m` is `h`, part 4
and part 5 of Theorem 3.14.7 are not proved.

## References

* Volume 7, Section 3.14 of the handbook: Lemma 3.14.2, Proposition 3.14.4, Lemma 3.14.6 and
  Theorem 3.14.7.
-/

open MvPolynomial Finsupp

namespace Singularity

namespace OriginRuns

/-! ### Growth of the step of Lemma 3.14.2 -/

section Growth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `δ ≥ 0`, a step does not make an entry smaller. -/
theorem le_diffStep_of_nonneg {δ : ι → ℤ} (h : ∀ i, 0 ≤ δ i) (j i : ι) :
    δ i ≤ diffStep j δ i := by
  by_cases hi : i = j
  · subst hi
    rw [diffStep, Function.update_self]
    exact Finset.single_le_sum (f := δ) (fun i _ => h i) (Finset.mem_univ i)
  · rw [diffStep, Function.update_of_ne hi]

/-- If `δ ≥ 0`, the steps of `l` do not make an entry smaller. -/
theorem le_diffSteps_of_nonneg {δ : ι → ℤ} (h : ∀ i, 0 ≤ δ i) (l : List ι) (i : ι) :
    δ i ≤ diffSteps l δ i := by
  induction l generalizing δ with
  | nil => exact le_rfl
  | cons j l ih => exact (le_diffStep_of_nonneg h j i).trans (ih (nonneg_diffStep h j))

/-- If `δ ≥ 0`, a step does not make the sum of the entries smaller. -/
theorem sum_le_sum_diffStep {δ : ι → ℤ} (h : ∀ i, 0 ≤ δ i) (j : ι) :
    ∑ i, δ i ≤ ∑ i, diffStep j δ i :=
  Finset.sum_le_sum fun i _ => le_diffStep_of_nonneg h j i

/-- If `δ ≥ 0` and `b ≤ Σ δ`, then after the steps of `l` the entry of each letter of `l` is at
least `b`. -/
theorem le_diffSteps_of_mem {δ : ι → ℤ} (h : ∀ i, 0 ≤ δ i) {b : ℤ} (hb : b ≤ ∑ i, δ i)
    {l : List ι} {i : ι} (hi : i ∈ l) : b ≤ diffSteps l δ i := by
  induction l generalizing δ with
  | nil => simp at hi
  | cons j l ih =>
    rw [diffSteps_cons]
    have h' := nonneg_diffStep h j
    by_cases hil : i ∈ l
    · exact ih h' (hb.trans (sum_le_sum_diffStep h j)) hil
    · have hij : i = j := by
        rcases List.mem_cons.mp hi with h1 | h1
        · exact h1
        · exact absurd h1 hil
      subst hij
      refine le_trans ?_ (le_diffSteps_of_nonneg h' l i)
      rw [diffStep, Function.update_self]
      exact hb

/-- The growth along the windows. Let `k ≥ 2`, let each entry of `δ` be at least `a ≥ 0`, and let
`Σ δ ≥ 1`. After `w` windows, each with all the letters, each entry is at least `a + w`. -/
theorem add_length_le_diffSteps (hk : 2 ≤ Fintype.card ι) {ws : List (List ι)}
    (hws : ∀ v ∈ ws, ∀ i, i ∈ v) {δ : ι → ℤ} {a : ℤ} (ha : 0 ≤ a) (h : ∀ i, a ≤ δ i)
    (hS : 1 ≤ ∑ i, δ i) : ∀ i, a + ws.length ≤ diffSteps ws.flatten δ i := by
  induction ws generalizing δ a with
  | nil => simpa using h
  | cons v ws ih =>
    intro i
    rw [List.flatten_cons, diffSteps_append]
    have h0 : ∀ i, 0 ≤ δ i := fun i => ha.trans (h i)
    have hcard : (Fintype.card ι : ℤ) * a ≤ ∑ i, δ i := by
      have := Finset.card_nsmul_le_sum Finset.univ δ a fun i _ => h i
      simpa [Finset.card_univ, nsmul_eq_mul] using this
    have hk' : (2 : ℤ) ≤ Fintype.card ι := by exact_mod_cast hk
    have h2a : 2 * a ≤ ∑ i, δ i := by nlinarith
    have hb : a + 1 ≤ ∑ i, δ i := by
      generalize ∑ i, δ i = S at h2a hS ⊢
      omega
    have h1 : ∀ i, a + 1 ≤ diffSteps v δ i := fun i =>
      le_diffSteps_of_mem h0 hb (hws v List.mem_cons_self i)
    have h2 : 1 ≤ ∑ i, diffSteps v δ i :=
      hS.trans (Finset.sum_le_sum fun i _ => le_diffSteps_of_nonneg h0 v i)
    have := ih (fun v' hv' => hws v' (List.mem_cons_of_mem _ hv')) (by linarith) h1 h2 i
    rw [List.length_cons]
    push_cast
    linarith

/-- The steps keep `δ ≠ 0`. -/
theorem diffSteps_ne_zero {δ : ι → ℤ} (h : δ ≠ 0) (l : List ι) : diffSteps l δ ≠ 0 := by
  induction l generalizing δ with
  | nil => exact h
  | cons j l ih => exact ih fun h' => h (eq_zero_of_diffStep_eq_zero h')

omit [DecidableEq ι] in
/-- If `δ ≥ 0` and `δ ≠ 0`, then `Σ δ ≥ 1`. -/
theorem one_le_sum_of_nonneg {δ : ι → ℤ} (h : ∀ i, 0 ≤ δ i) (hδ : δ ≠ 0) : 1 ≤ ∑ i, δ i := by
  obtain ⟨i, hi⟩ : ∃ i, δ i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hδ (funext hc)
  have h1 := Finset.single_le_sum (f := δ) (fun i _ => h i) (Finset.mem_univ i)
  have h2 := h i
  omega

/-- **The sign after the windows** (Volume 7, Section 3.14 of the handbook). Let `k ≥ 2` and
`δ ≠ 0`. Let `ws₁` be at least `Φ(δ)` windows and let `ws₂` be `B` windows, each with all the
letters. After the steps of `ws₁` and then `ws₂`, each entry is at least `B`, or each entry is at
most `-B`. -/
theorem diffSteps_windows_sign (hk : 2 ≤ Fintype.card ι) {δ : ι → ℤ} (hδ : δ ≠ 0)
    {ws₁ ws₂ : List (List ι)} (hws₁ : ∀ v ∈ ws₁, ∀ i, i ∈ v) (hws₂ : ∀ v ∈ ws₂, ∀ i, i ∈ v)
    (hlen : phi δ ≤ ws₁.length) :
    (∀ i, (ws₂.length : ℤ) ≤ diffSteps (ws₁.flatten ++ ws₂.flatten) δ i) ∨
      ∀ i, diffSteps (ws₁.flatten ++ ws₂.flatten) δ i ≤ -ws₂.length := by
  rw [diffSteps_append]
  have hne : diffSteps ws₁.flatten δ ≠ 0 := diffSteps_ne_zero hδ _
  rcases not_isMixed_iff.mp (not_isMixed_of_phi_le hws₁ hlen) with h | h
  · left
    have := add_length_le_diffSteps hk hws₂ le_rfl h (one_le_sum_of_nonneg h hne)
    simpa using this
  · right
    have h' : ∀ i, 0 ≤ (-diffSteps ws₁.flatten δ) i := fun i => by
      simp only [Pi.neg_apply]
      linarith [h i]
    have hne' : -diffSteps ws₁.flatten δ ≠ 0 := neg_ne_zero.mpr hne
    have key := add_length_le_diffSteps hk hws₂ le_rfl h' (one_le_sum_of_nonneg h' hne')
    rw [diffSteps_neg] at key
    intro i
    have := key i
    simp only [Pi.neg_apply, zero_add] at this
    linarith

/-- **The eventual sign along a run** (Volume 7, Section 3.14 of the handbook). Let `k ≥ 2`, and
let each letter occur an infinite number of times in `w`. For each `δ ≠ 0` and each `B`, there is
an `M` such that each entry of the vector after the first `m` steps is at least `B` for each
`m ≥ M`, or each entry is at most `-B` for each `m ≥ M`. -/
theorem eventually_sign (hk : 2 ≤ Fintype.card ι) {w : ℕ → ι}
    (hinf : ∀ i N, ∃ m, N ≤ m ∧ w m = i) {δ : ι → ℤ} (hδ : δ ≠ 0) (B : ℕ) :
    ∃ M, (∀ m, M ≤ m → ∀ i, (B : ℤ) ≤ diffSteps (runList w 0 m) δ i) ∨
      ∀ m, M ≤ m → ∀ i, diffSteps (runList w 0 m) δ i ≤ -B := by
  obtain ⟨ws₁, n₁, hlen₁, hws₁, hflat₁⟩ := exists_windows hinf (phi δ).toNat 0
  obtain ⟨ws₂, n₂, hlen₂, hws₂, hflat₂⟩ := exists_windows hinf B (0 + n₁)
  have hl : phi δ ≤ ws₁.length := by
    rw [hlen₁]
    exact Int.self_le_toNat _
  have key := diffSteps_windows_sign hk hδ hws₁ hws₂ hl
  rw [hflat₁, hflat₂, ← runList_add, hlen₂] at key
  refine ⟨n₁ + n₂, ?_⟩
  have hsplit : ∀ m, n₁ + n₂ ≤ m → runList w 0 m =
      runList w 0 (n₁ + n₂) ++ runList w (0 + (n₁ + n₂)) (m - (n₁ + n₂)) := fun m hm => by
    rw [← runList_add, Nat.add_sub_cancel' hm]
  have hB : (0 : ℤ) ≤ B := Nat.cast_nonneg B
  rcases key with h | h
  · left
    intro m hm i
    rw [hsplit m hm, diffSteps_append]
    exact (h i).trans (le_diffSteps_of_nonneg (fun i => hB.trans (h i)) _ i)
  · right
    intro m hm i
    rw [hsplit m hm, diffSteps_append]
    have h' : ∀ i, 0 ≤ (-diffSteps (runList w 0 (n₁ + n₂)) δ) i := fun i => by
      simp only [Pi.neg_apply]
      linarith [h i]
    have := le_diffSteps_of_nonneg h' (runList w (0 + (n₁ + n₂)) (m - (n₁ + n₂))) i
    rw [diffSteps_neg] at this
    simp only [Pi.neg_apply] at this
    linarith [h i]

end Growth

/-! ### The columns and the step of Lemma 3.14.2 -/

section Columns

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {L : Finset σ}

variable (L) in
/-- The vector `(δ · c_s)_{s ∈ L}` for the columns `c`, where `δ · c_s = Σ_{t ∈ L} δ_t c_{s,t}`. -/
def colDot (δ : σ → ℤ) (c : σ → σ → ℤ) : L → ℤ := fun s => ∑ t ∈ L, δ t * c s t

omit [Fintype σ] in
/-- A step with the letter `j` on the columns is the step `δ_j ← Σ δ` of Lemma 3.14.2 on the
vector `(δ · c_s)_{s ∈ L}` (Volume 7, proof of Proposition 3.14.4 of the handbook). -/
theorem colDot_colStep (δ : σ → ℤ) (c : σ → σ → ℤ) (j : L) :
    colDot L δ (colStep L j c) = diffStep j (colDot L δ c) := by
  funext s
  by_cases hs : s = j
  · subst hs
    simp only [colDot, colStep, diffStep, Function.update_self, Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact (Finset.sum_coe_sort L (fun t' => ∑ t ∈ L, δ t * c t' t)).symm
  · simp only [colDot, colStep, diffStep, Function.update_of_ne hs,
      Function.update_of_ne (fun h => hs (Subtype.ext h))]

omit [Fintype σ] in
/-- The steps with the letters of `l` on the columns are the steps of Lemma 3.14.2 on the vector
`(δ · c_s)_{s ∈ L}`. -/
theorem colDot_colSteps (δ : σ → ℤ) (l : List L) (c : σ → σ → ℤ) :
    colDot L δ (colSteps L (l.map Subtype.val) c) = diffSteps l (colDot L δ c) := by
  induction l generalizing c with
  | nil => rfl
  | cons j l ih =>
    rw [List.map_cons, diffSteps_cons, ← colDot_colStep, ← ih]
    rfl

omit [Fintype σ] in
/-- For the unit columns, `δ · c_s = δ_s`. -/
theorem colDot_unitCols (δ : σ → ℤ) : colDot L δ unitCols = fun s : L => δ s := by
  funext s
  simp only [colDot, unitCols, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' L s, ite_eq_left s.2]

/-- The difference `q(μ) - q(ν)` as a vector on `L`. -/
def qDiff (p : ℕ) (L : Finset σ) (μ ν : σ →₀ ℕ) : L → ℤ := fun t => qVec p L μ t - qVec p L ν t

/-- The difference `q(μ) · c - q(ν) · c` is `(q(μ) - q(ν)) · c`. -/
theorem qDot_sub_qDot (p : ℕ) (μ ν : σ →₀ ℕ) (c : σ → σ → ℤ) (s : L) :
    qDot p L μ (c s) - qDot p L ν (c s) =
      colDot L (fun t => qVec p L μ t - qVec p L ν t) c s := by
  simp only [qDot, colDot, ← Finset.sum_sub_distrib, sub_mul]

/-- **The differences along the columns** (Volume 7, Section 3.14 of the handbook). After the
steps with the letters of `l`, the vector `(Δq · c_s)_{s ∈ L}` with `Δq = q(μ) - q(ν)` is the
vector `q(μ) - q(ν)` after the steps of Lemma 3.14.2 with the letters of `l`. -/
theorem qDot_sub_cols (p : ℕ) (μ ν : σ →₀ ℕ) (l : List L) (s : L) :
    qDot p L μ (cols L (l.map Subtype.val) s) - qDot p L ν (cols L (l.map Subtype.val) s) =
      diffSteps l (qDiff p L μ ν) s := by
  rw [qDot_sub_qDot, cols, colDot_colSteps, colDot_unitCols]
  rfl

end Columns

/-! ### Lemma 3.14.6 -/

section Limit

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **Lemma 3.14.6 of the handbook**, in a combinatorial form. Let `L` have at least two letters,
let each letter of the run `w` be in `L`, and let each letter of `L` occur an infinite number of
times. Let `S` be a finite set of exponent vectors that is not empty. Then there are a vector
`T ∈ S` and an `m₀` such that for each `m ≥ m₀` and each `μ ∈ S`, either `q(μ) = q(T)` and
`σ(μ) ≤ σ(T)`, or `Δq(μ) · c_s ≥ max(1, Δσ(μ))` for each `s ∈ L`, where `c_s` are the columns
after the first `m` steps. -/
theorem exists_corner_le_eventually {p : ℕ} {L : Finset σ} (hk : 2 ≤ L.card) {w : ℕ → σ}
    (hw : ∀ m, w m ∈ L) (hinf : ∀ s ∈ L, ∀ N, ∃ m, N ≤ m ∧ w m = s)
    {S : Finset (σ →₀ ℕ)} (hS : S.Nonempty) :
    ∃ T ∈ S, ∃ m₀, ∀ m, m₀ ≤ m → ∀ μ ∈ S,
      ((∀ t ∈ L, qVec p L μ t = qVec p L T t) ∧ uSum L μ ≤ uSum L T) ∨
        ∀ s ∈ L, max 1 ((uSum L μ : ℤ) - uSum L T) ≤
          qDot p L μ (cols L (runList w 0 m) s) - qDot p L T (cols L (runList w 0 m) s) := by
  obtain ⟨wL, hwL⟩ : ∃ wL : ℕ → L, ∀ m, (wL m : σ) = w m :=
    ⟨fun m => ⟨w m, hw m⟩, fun _ => rfl⟩
  have hinfL : ∀ i : L, ∀ N, ∃ m, N ≤ m ∧ wL m = i := fun i N => by
    obtain ⟨m, hm, he⟩ := hinf i i.2 N
    exact ⟨m, hm, Subtype.ext ((hwL m).trans he)⟩
  have hkL : 2 ≤ Fintype.card L := by
    rw [Fintype.card_coe]
    exact hk
  have hrl : ∀ m, (runList wL 0 m).map Subtype.val = runList w 0 m := fun m => by
    simp only [runList, List.map_map]
    congr 1
    funext i
    exact hwL _
  have hdot : ∀ m μ ν s (hs : s ∈ L),
      qDot p L μ (cols L (runList w 0 m) s) - qDot p L ν (cols L (runList w 0 m) s) =
        diffSteps (runList wL 0 m) (qDiff p L μ ν) ⟨s, hs⟩ := by
    intro m μ ν s hs
    have := qDot_sub_cols p μ ν (runList wL 0 m) ⟨s, hs⟩
    rw [hrl] at this
    exact this
  obtain ⟨B, hB1, hBσ⟩ : ∃ B : ℕ, 1 ≤ B ∧ ∀ μ ∈ S, uSum L μ < B :=
    ⟨S.sup (uSum L) + 1, by omega, fun μ hμ => Nat.lt_succ_of_le (Finset.le_sup hμ)⟩
  have hsign : ∀ μ ν : σ →₀ ℕ, ∃ M, qDiff p L μ ν ≠ 0 →
      (∀ m, M ≤ m → ∀ i, (B : ℤ) ≤ diffSteps (runList wL 0 m) (qDiff p L μ ν) i) ∨
        ∀ m, M ≤ m → ∀ i, diffSteps (runList wL 0 m) (qDiff p L μ ν) i ≤ -B := by
    intro μ ν
    by_cases h : qDiff p L μ ν = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨M, hM⟩ := eventually_sign hkL hinfL h B
      exact ⟨M, fun _ => hM⟩
  choose M hM using hsign
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, ∀ μ ∈ S, ∀ ν ∈ S, M μ ν ≤ m₀ :=
    ⟨(S ×ˢ S).sup fun pr => M pr.1 pr.2, fun μ hμ ν hν =>
      Finset.le_sup (s := S ×ˢ S) (f := fun pr : (σ →₀ ℕ) × (σ →₀ ℕ) => M pr.1 pr.2)
        (b := (μ, ν)) (Finset.mem_product.mpr ⟨hμ, hν⟩)⟩
  obtain ⟨s₀, hs₀⟩ : L.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨T₁, hT₁, hmin⟩ :=
    S.exists_min_image (fun μ => qDot p L μ (cols L (runList w 0 m₀) s₀)) hS
  obtain ⟨T, hT, hmax⟩ := (S.filter fun μ => qDot p L μ (cols L (runList w 0 m₀) s₀) =
      qDot p L T₁ (cols L (runList w 0 m₀) s₀)).exists_max_image (uSum L)
    ⟨T₁, Finset.mem_filter.mpr ⟨hT₁, rfl⟩⟩
  obtain ⟨hTS, hfT⟩ := Finset.mem_filter.mp hT
  refine ⟨T, hTS, m₀, fun m hm μ hμ => ?_⟩
  by_cases hq : ∀ t ∈ L, qVec p L μ t = qVec p L T t
  · left
    refine ⟨hq, hmax μ (Finset.mem_filter.mpr ⟨hμ, ?_⟩)⟩
    have : qDot p L μ (cols L (runList w 0 m₀) s₀) = qDot p L T (cols L (runList w 0 m₀) s₀) :=
      Finset.sum_congr rfl fun t ht => by rw [hq t ht]
    exact this.trans hfT
  · right
    have hne : qDiff p L μ T ≠ 0 := by
      intro h0
      apply hq
      intro t ht
      have := congrFun h0 ⟨t, ht⟩
      simp only [qDiff, Pi.zero_apply] at this
      linarith
    have hMle := hm₀ μ hμ T hTS
    rcases hM μ T hne with h | h
    · intro s hs
      rw [hdot m μ T s hs]
      have h1 := h m (hMle.trans hm) ⟨s, hs⟩
      have h2 := hBσ μ hμ
      have h3 : (1 : ℤ) ≤ B := by exact_mod_cast hB1
      have h4 : (uSum L μ : ℤ) - uSum L T ≤ B := by omega
      exact max_le (h3.trans h1) (h4.trans h1)
    · exfalso
      have h1 := h m₀ hMle ⟨s₀, hs₀⟩
      rw [← hdot m₀ μ T s₀ hs₀] at h1
      have h2 : qDot p L T₁ (cols L (runList w 0 m₀) s₀) ≤
          qDot p L μ (cols L (runList w 0 m₀) s₀) := hmin μ hμ
      have h3 : (1 : ℤ) ≤ B := by exact_mod_cast hB1
      linarith

/-- **Lemma 3.14.6 of the handbook, in the form of `CornerIneq`.** In the setting of
`exists_corner_le_eventually`, there are a vector `T ∈ S` and an `m₀` such that `CornerIneq`
holds for each `μ ∈ S` and the columns after the first `m` steps, for each `m ≥ m₀`. -/
theorem exists_cornerIneq_eventually {p : ℕ} {L : Finset σ} (hk : 2 ≤ L.card) {w : ℕ → σ}
    (hw : ∀ m, w m ∈ L) (hinf : ∀ s ∈ L, ∀ N, ∃ m, N ≤ m ∧ w m = s)
    {S : Finset (σ →₀ ℕ)} (hS : S.Nonempty) :
    ∃ T ∈ S, ∃ m₀, ∀ m, m₀ ≤ m → ∀ μ ∈ S, CornerIneq p L (cols L (runList w 0 m)) T μ := by
  obtain ⟨T, hT, m₀, h⟩ := exists_corner_le_eventually (p := p) hk hw hinf hS
  exact ⟨T, hT, m₀, fun m hm μ hμ => cornerIneq_of (h m hm μ hμ)⟩

variable {k : Type*} [Field k] {p : ℕ} {L Δ : Finset σ} {g : MvPolynomial σ k}

/-- **Theorem 3.14.7, parts 1, 2 and 3** (Volume 7, Section 3.14 of the handbook). Let `g` be
clean and not `0`, let `L ⊆ Δ` have at least two letters, and let `w` be the letters of an origin
run where each letter is in `L`, each letter of `L` occurs an infinite number of times, and each
step is defined. Then there are a monomial `T` of `g` and an `m₀` such that for each `m ≥ m₀`, at
the point `P_m` the divisor is `Δ`, `r_s = E_s(T)` for `s ∈ L`, the order of `G` is
`d_m = σ(T) - r_U`, and each corner curve `C_t`, `t ∈ L`, has `ν^G_{C_t} = d_m ≥ ρ`. The
inequalities of Lemma 3.14.6 are not a hypothesis here: they come from
`exists_cornerIneq_eventually`. -/
theorem originRun_cornerCurves_eventually [CharP k p] (hp : p.Prime) (hc : IsClean p g)
    (hg : g ≠ 0) (hk : 2 ≤ L.card) (hLΔ : L ⊆ Δ) {w : ℕ → σ} (hw : ∀ m, w m ∈ L)
    (hinf : ∀ s ∈ L, ∀ N, ∃ m, N ≤ m ∧ w m = s) (hadm : ∀ m, DegreeGe p (runPoly p w g m)) :
    ∃ T ∈ g.support, ∃ m₀, ∀ m, m₀ ≤ m →
      runDivisor w Δ m = Δ ∧
        (∀ s ∈ L, divisorExponent Δ (runPoly p w g m) s = expSteps p (runList w 0 m) T s) ∧
        ord (residualFactor Δ (runPoly p w g m)) =
          ((uSum L T - ∑ u ∈ Lᶜ, divisorExponent Δ g u : ℕ) : ℕ∞) ∧
        ∀ t ∈ L, orderGAlong p Δ (Finset.univ.erase t) (runPoly p w g m) =
            ord (residualFactor Δ (runPoly p w g m)) ∧
          logJacobianOrder Δ (runPoly p w g m) ≤
            orderGAlong p Δ (Finset.univ.erase t) (runPoly p w g m) := by
  obtain ⟨T, hT, m₀, h⟩ :=
    exists_cornerIneq_eventually (p := p) hk hw hinf (MvPolynomial.support_nonempty.mpr hg)
  exact ⟨T, hT, m₀, fun m hm =>
    originRun_cornerCurves hp hc hk hLΔ hw hadm hT m (h m hm)⟩

end Limit

end OriginRuns

end Singularity
