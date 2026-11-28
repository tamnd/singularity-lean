/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.NumberTheory.Real.Irrational
import Singularity.Invariant.PlanarRunsHahn

/-!
# The field of finite type and the planar tails

This file proves Lemma 3.18.8 and Lemma 3.18.10 of Volume 7 of the handbook for the Hahn model of
`Singularity.Invariant.PlanarRunsHahn`. With them, the abstract planar tail `IsPlanarTail` of
`Singularity.Invariant.PlanarRuns` holds for each planar corner run (`isPlanarTail_corner`).

## Main definitions

* `IsFiniteType x`: the series `x` has only a finite number of terms below each value.
* `finiteTypeSubfield hθ`: for `θ` irrational, the subfield `𝔽` of the series of finite type
  (Lemma 3.18.8).
* `IsLinearRun t` and `IsPlanarRun t` (Definition 3.17.5): the run with the translations `t` is
  linear if there is a `λ ≠ 0` with `t^λ_j = Σ_l λ_l t_{j, l} = 0` for `j` large, and planar if
  not.

## Main results

* `finiteTypeSubfield` (Lemma 3.18.8): the series of finite type form a subfield that contains the
  points `Φ_m` (`isFiniteType_cornerPoint`).
* `hahnVal_add_sum_mul_tail_lt` (Lemma 3.18.10): on a planar run, for `α ≠ 0` and `c` of finite
  type, `v(c + Σ_l α_l Δ_{m, l}) < min_l v(α_l) + 1 + θ`.
* `isPlanarTail_corner`: the planar tail `IsPlanarTail` of the run, with `γ m = v(M_{m+1})` and
  `Θ = 1 + θ`.
* `statementDHolds_corner` (Theorem 3.18.11 for the run): Statement D for the polynomials over `𝔽`
  with all degrees less than `p`.
* `conjectureP_planarRun`: Theorem 3.19.6 (Conjecture P) for the planar corner runs, with
  Theorem 3.18.26 as a hypothesis only for the derivatives of `g` of degree at least `p` in some
  variable.

The handbook has two free coordinates. The file works with any finite set `σ` of free
coordinates.

## References

* Volume 7, Sections 3.17 and 3.18 of the handbook: Definition 3.17.5, Lemma 3.18.8,
  Lemma 3.18.10 and Theorem 3.18.11.
-/

open MvPolynomial Filter Topology Finsupp

namespace Singularity

namespace PlanarRuns

open CornerExp

variable {θ : ℝ} {k : Type*} [Field k]

/-! ### Values of exponents -/

theorem CornerExp.eq_zero_of_val_eq_zero (hθ : Irrational θ) {r : CornerExp θ}
    (h : val θ r = 0) : r = 0 := by
  have hb : snd r = 0 := by
    by_contra hb
    apply hθ
    refine ⟨(-(fst r : ℚ)) / (snd r : ℚ), ?_⟩
    have hb' : ((snd r : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hb
    unfold val at h
    push_cast
    field_simp
    linarith
  have ha : fst r = 0 := by
    unfold val at h
    rw [hb] at h
    simpa using h
  exact ext ha hb

theorem CornerExp.val_injective (hθ : Irrational θ) : Function.Injective (val θ) := by
  intro r s h
  have := eq_zero_of_val_eq_zero hθ (r := r - s) (by rw [val_sub, h, sub_self])
  exact sub_eq_zero.mp this

theorem CornerExp.val_pos (hθ : Irrational θ) {r : CornerExp θ} (h : 0 < r) : 0 < val θ r := by
  rcases (val_mono h.le).lt_or_eq with h' | h'
  · simpa using h'
  · exact absurd (eq_zero_of_val_eq_zero hθ (by simpa using h'.symm)) h.ne'

theorem val_order_le {x : HahnSeries (CornerExp θ) k} {r : CornerExp θ} (hr : r ∈ x.support) :
    val θ x.order ≤ val θ r :=
  val_mono (HahnSeries.order_le_of_coeff_ne_zero hr)

/-! ### Series of finite type -/

/-- The terms of `x` of value less than `V`. -/
def belowSet (V : ℝ) (x : HahnSeries (CornerExp θ) k) : Set (CornerExp θ) :=
  {r | r ∈ x.support ∧ val θ r < V}

/-- A series of finite type: it has only a finite number of terms below each value. -/
def IsFiniteType (x : HahnSeries (CornerExp θ) k) : Prop :=
  ∀ V : ℝ, (belowSet V x).Finite

theorem belowSet_mono {V : ℝ} {x y : HahnSeries (CornerExp θ) k} (h : y.support ⊆ x.support) :
    belowSet V y ⊆ belowSet V x :=
  fun _ hr => ⟨h hr.1, hr.2⟩

theorem belowSet_add_subset (V : ℝ) (x y : HahnSeries (CornerExp θ) k) :
    belowSet V (x + y) ⊆ belowSet V x ∪ belowSet V y := by
  rintro r ⟨hr, hv⟩
  rcases HahnSeries.support_add_subset x y hr with h | h
  · exact Or.inl ⟨h, hv⟩
  · exact Or.inr ⟨h, hv⟩

theorem finite_belowSet_sum {ι : Type*} (s : Finset ι) (V : ℝ)
    (x : ι → HahnSeries (CornerExp θ) k) (h : ∀ i ∈ s, (belowSet V (x i)).Finite) :
    (belowSet V (∑ i ∈ s, x i)).Finite := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [belowSet]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((h a (Finset.mem_insert_self a s)).union
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).subset (belowSet_add_subset V _ _)

theorem isFiniteType_of_support_subset {x y : HahnSeries (CornerExp θ) k}
    (hx : IsFiniteType x) (h : y.support ⊆ x.support) : IsFiniteType y :=
  fun V => (hx V).subset (belowSet_mono h)

theorem isFiniteType_single (r : CornerExp θ) (c : k) :
    IsFiniteType (HahnSeries.single r c) :=
  fun _ => (Set.finite_singleton r).subset fun _ h => HahnSeries.support_single_subset h.1

theorem IsFiniteType.add {x y : HahnSeries (CornerExp θ) k} (hx : IsFiniteType x)
    (hy : IsFiniteType y) : IsFiniteType (x + y) :=
  fun V => ((hx V).union (hy V)).subset (belowSet_add_subset V x y)

theorem IsFiniteType.neg {x : HahnSeries (CornerExp θ) k} (hx : IsFiniteType x) :
    IsFiniteType (-x) :=
  isFiniteType_of_support_subset hx (by rw [HahnSeries.support_neg])

/-- The terms of `x * y` below `V` come from a finite number of pairs of terms. -/
theorem belowSet_mul_subset (V : ℝ) (x y : HahnSeries (CornerExp θ) k) :
    belowSet V (x * y) ⊆ Set.image2 (· + ·) (belowSet (V - val θ y.order) x)
      (belowSet (V - val θ x.order) y) := by
  rintro r ⟨hr, hv⟩
  obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_add.mp (HahnSeries.support_mul_subset hr)
  have h1 := val_order_le hs
  have h2 := val_order_le ht
  rw [val_add] at hv
  exact ⟨s, ⟨hs, by linarith⟩, t, ⟨ht, by linarith⟩, rfl⟩

theorem IsFiniteType.mul {x y : HahnSeries (CornerExp θ) k} (hx : IsFiniteType x)
    (hy : IsFiniteType y) : IsFiniteType (x * y) :=
  fun V => ((hx _).image2 _ (hy _)).subset (belowSet_mul_subset V x y)

/-! ### The inverse -/

theorem val_nonneg_of_mem_closure {S : Set (CornerExp θ)} (hS : ∀ s ∈ S, 0 ≤ val θ s)
    {r : CornerExp θ} (hr : r ∈ AddSubmonoid.closure S) : 0 ≤ val θ r := by
  induction hr using AddSubmonoid.closure_induction with
  | mem s hs => exact hS s hs
  | zero => simp
  | add x y _ _ hx hy => rw [val_add]; linarith

theorem eq_zero_or_add_of_mem_closure {S : Set (CornerExp θ)} {r : CornerExp θ}
    (hr : r ∈ AddSubmonoid.closure S) :
    r = 0 ∨ ∃ s ∈ S, ∃ r' ∈ AddSubmonoid.closure S, r = s + r' := by
  induction hr using AddSubmonoid.closure_induction with
  | mem s hs => exact Or.inr ⟨s, hs, 0, AddSubmonoid.zero_mem _, (add_zero s).symm⟩
  | zero => exact Or.inl rfl
  | add x y hx hy ihx ihy =>
    rcases ihx with rfl | ⟨s, hs, r', hr', rfl⟩
    · rw [zero_add]
      exact ihy
    · exact Or.inr ⟨s, hs, r' + y, AddSubmonoid.add_mem _ hr' hy, by abel⟩

/-- The sums of elements of `S` have only a finite number of values below each `V`, if the
elements of `S` have values at least `s0 > 0` and `S` has only a finite number of elements
below each value. -/
theorem finite_closure_below {S : Set (CornerExp θ)} {s0 : ℝ} (hs0 : 0 < s0)
    (hS : ∀ s ∈ S, s0 ≤ val θ s) (hfin : ∀ V : ℝ, {s | s ∈ S ∧ val θ s < V}.Finite) (V : ℝ) :
    {r | r ∈ AddSubmonoid.closure S ∧ val θ r < V}.Finite := by
  have hS0 : ∀ s ∈ S, 0 ≤ val θ s := fun s hs => hs0.le.trans (hS s hs)
  suffices h : ∀ n : ℕ, ∀ V : ℝ, V ≤ n * s0 →
      {r | r ∈ AddSubmonoid.closure S ∧ val θ r < V}.Finite by
    obtain ⟨n, hn⟩ := exists_nat_ge (V / s0)
    exact h n V (by rwa [div_le_iff₀ hs0] at hn)
  intro n
  induction n with
  | zero =>
    intro V hV
    refine Set.finite_empty.subset ?_
    rintro r ⟨hr, hv⟩
    have := val_nonneg_of_mem_closure hS0 hr
    simp at hV
    linarith
  | succ n ih =>
    intro V hV
    refine ((Set.finite_singleton (0 : CornerExp θ)).union
      ((hfin V).image2 (· + ·) (ih (V - s0) (by push_cast at hV; linarith)))).subset ?_
    rintro r ⟨hr, hv⟩
    rcases eq_zero_or_add_of_mem_closure hr with rfl | ⟨s, hs, r', hr', rfl⟩
    · exact Or.inl rfl
    · right
      have h1 := hS s hs
      have h2 := val_nonneg_of_mem_closure hS0 hr'
      rw [val_add] at hv
      exact ⟨s, ⟨hs, by linarith⟩, r', ⟨hr', by linarith⟩, rfl⟩

theorem IsFiniteType.inv (hθ : Irrational θ) {x : HahnSeries (CornerExp θ) k}
    (hx : IsFiniteType x) : IsFiniteType x⁻¹ := by
  by_cases h0 : x = 0
  · rw [h0, inv_zero]
    exact isFiniteType_of_support_subset (isFiniteType_single 0 (0 : k)) (by simp)
  set ε := 1 - HahnSeries.single (-x.order) (x.leadingCoeff)⁻¹ * x with hε
  have hεpos : 0 < ε.orderTop := HahnSeries.unit_aux x
    (inv_mul_cancel₀ (HahnSeries.leadingCoeff_ne_zero.mpr h0)) _ (neg_add_cancel x.order)
  have hεft : IsFiniteType ε := by
    rw [hε, sub_eq_add_neg]
    exact (isFiniteType_single 0 (1 : k)).add ((isFiniteType_single _ _).mul hx).neg
  rw [HahnSeries.inv_def]
  refine (isFiniteType_single _ _).mul ?_
  -- the support of the sum of the powers lies in the sums of the terms of `ε`
  have hsub : (HahnSeries.SummableFamily.powers ε).hsum.support ⊆
      AddSubmonoid.closure ε.support := by
    refine HahnSeries.SummableFamily.support_hsum_subset.trans (Set.iUnion_subset fun n => ?_)
    rw [HahnSeries.SummableFamily.powers_of_orderTop_pos hεpos]
    exact HahnSeries.SummableFamily.support_pow_subset_closure ε n
  by_cases hε0 : ε = 0
  · refine isFiniteType_of_support_subset (isFiniteType_single 0 (1 : k)) ?_
    intro r hr
    have := hsub hr
    rw [hε0] at this
    simp only [HahnSeries.support_zero, AddSubmonoid.closure_empty] at this
    rw [this]
    simp
  have hord : 0 < ε.order := by
    rw [HahnSeries.zero_lt_orderTop_iff hε0] at hεpos
    exact hεpos
  have hs0 := CornerExp.val_pos hθ hord
  intro V
  refine (finite_closure_below hs0 (fun s hs => val_order_le hs) hεft V).subset ?_
  rintro r ⟨hr, hv⟩
  exact ⟨hsub hr, hv⟩

variable (k) in
/-- Lemma 3.18.8: the series of finite type form a subfield `𝔽` of the Hahn field. -/
def finiteTypeSubfield (hθ : Irrational θ) : Subfield (HahnSeries (CornerExp θ) k) where
  carrier := {x | IsFiniteType x}
  mul_mem' hx hy := IsFiniteType.mul hx hy
  one_mem' := isFiniteType_single 0 1
  add_mem' hx hy := IsFiniteType.add hx hy
  zero_mem' := isFiniteType_of_support_subset (isFiniteType_single 0 (0 : k)) (by simp)
  neg_mem' hx := IsFiniteType.neg hx
  inv_mem' _ hx := IsFiniteType.inv hθ hx

theorem mem_finiteTypeSubfield (hθ : Irrational θ) {x : HahnSeries (CornerExp θ) k} :
    x ∈ finiteTypeSubfield k hθ ↔ IsFiniteType x := Iff.rfl

/-! ### Planar runs -/

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {w : ℕ → Bool}

/-- Definition 3.17.5: a run is linear if there is a direction `λ ≠ 0` with
`t^λ_j = Σ_l λ_l t_{j, l} = 0` for `j` large. -/
def IsLinearRun (t : ℕ → σ → k) : Prop :=
  ∃ c : σ → k, c ≠ 0 ∧ ∀ᶠ j in atTop, ∑ l, c l * t j l = 0

/-- Definition 3.17.5: a run is planar if it is not linear. -/
def IsPlanarRun (t : ℕ → σ → k) : Prop := ¬ IsLinearRun t

omit [DecidableEq σ] in
theorem IsPlanarRun.frequently {t : ℕ → σ → k} (h : IsPlanarRun t) {c : σ → k} (hc : c ≠ 0) :
    ∃ᶠ j in atTop, ∑ l, c l * t j l ≠ 0 := by
  rw [Filter.Frequently]
  intro h'
  exact h ⟨c, hc, by simpa using h'⟩

omit [Fintype σ] [DecidableEq σ] in
/-- The points `Φ_m` are of finite type (Lemma 3.18.8, last claim). -/
theorem isFiniteType_cornerPoint (t : ℕ → σ → k) (m : ℕ) (l : σ) :
    IsFiniteType (cornerPoint (θ := θ) (w := w) t m l) := by
  intro V
  rw [cornerPoint, cornerSum_eq]
  exact finite_belowSet_sum _ V _ fun j _ => isFiniteType_single _ _ V

theorem coeff_cornerTail (hw : IsCornerWord θ w) (c : ℕ → k) (m j : ℕ) :
    (cornerLimit hw c - cornerSum (cornerL θ k w) (fun j => HahnSeries.C (c j)) m).coeff
      (expM w (j + 1)) = if m ≤ j then c j else 0 := by
  rw [cornerSum_eq, HahnSeries.coeff_sub, HahnSeries.coeff_sum, coeff_cornerLimit_expM]
  simp only [HahnSeries.coeff_single]
  split_ifs with hj
  · rw [Finset.sum_eq_zero, sub_zero]
    intro i hi
    rw [ite_eq_right]
    intro h'
    have := Nat.succ_injective (hw.strictMono_expM.injective h')
    rw [Finset.mem_range] at hi
    omega
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [ite_eq_right]
      intro h'
      exact hij (Nat.succ_injective (hw.strictMono_expM.injective h'.symm))
    · intro hj'
      exact absurd (Finset.mem_range.mpr (by omega)) hj'

theorem val_expM_lt (hw : IsCornerWord θ w) (n : ℕ) : val θ (expM w n : CornerExp θ) < 1 + θ :=
  (hw.val_expM_lt n).trans_le
    (hw.strictMono_val_expM.monotone.ge_of_tendsto hw.tendsto_val_expM (n + 1))

theorem val_expM_nonneg (hw : IsCornerWord θ w) (n : ℕ) : 0 ≤ val θ (expM w n : CornerExp θ) := by
  have := hw.strictMono_val_expM.monotone (Nat.zero_le n)
  simpa [expM] using this

/-- The products `u Δ_m` with `v(u) > 0` on its terms have only a finite number of terms
below `1 + θ`. -/
theorem finite_belowSet_mul_tail (hw : IsCornerWord θ w) (c : ℕ → k) (m : ℕ)
    {u : HahnSeries (CornerExp θ) k} (hu : IsFiniteType u) {s0 : ℝ} (hs0 : 0 < s0)
    (hus : ∀ r ∈ u.support, s0 ≤ val θ r) :
    (belowSet (1 + θ) (u * (cornerLimit hw c -
      cornerSum (cornerL θ k w) (fun j => HahnSeries.C (c j)) m))).Finite := by
  obtain ⟨J, hJ⟩ := (hw.tendsto_val_expM.eventually_const_lt
    (show 1 + θ - s0 < 1 + θ by linarith)).exists_forall_of_atTop
  refine ((hu (1 + θ)).image2 (· + ·)
    ((Finset.range J).finite_toSet.image fun j => (expM w (j + 1) : CornerExp θ))).subset ?_
  rintro r ⟨hr, hv⟩
  obtain ⟨s, hs, t', ht, rfl⟩ := Set.mem_add.mp (HahnSeries.support_mul_subset hr)
  obtain ⟨j, -, rfl⟩ := support_cornerTail hw c m t' ht
  have h1 := hus s hs
  have h2 := val_expM_nonneg hw (j + 1)
  rw [val_add] at hv
  refine ⟨s, ⟨hs, by linarith⟩, _, ⟨j, ?_, rfl⟩, rfl⟩
  by_contra hj
  have := hJ (j + 1) (by simp at hj; omega)
  linarith

omit [DecidableEq σ] in
/-- Lemma 3.18.10: on a planar run, for `α ≠ 0` and `c` of finite type,
`v(c + Σ_l α_l Δ_{m, l}) < min_l v(α_l) + 1 + θ`. -/
theorem hahnVal_add_sum_mul_tail_lt (hθ : Irrational θ) (hw : IsCornerWord θ w)
    (t : ℕ → σ → k) (hpl : IsPlanarRun t) (m : ℕ) (α : σ → HahnSeries (CornerExp θ) k)
    (hα : ∀ l, IsFiniteType (α l)) (hα0 : α ≠ 0) (c : HahnSeries (CornerExp θ) k)
    (hc : IsFiniteType c) :
    hahnVal θ k (c + ∑ l, α l * (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l)) <
      Finset.univ.inf (fun l => hahnVal θ k (α l)) + (((1 + θ : ℝ)) : WithTop ℝ) := by
  set Δ : σ → HahnSeries (CornerExp θ) k :=
    fun l => cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l with hΔ
  -- the index of least value
  have hne : (Finset.univ : Finset σ).Nonempty := by
    by_contra h
    apply hα0
    funext l
    exact absurd ⟨l, Finset.mem_univ l⟩ h
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fun l => hahnVal θ k (α l)) hne
  have hinf : Finset.univ.inf (fun l => hahnVal θ k (α l)) = hahnVal θ k (α i0) :=
    le_antisymm (Finset.inf_le (Finset.mem_univ _)) (Finset.le_inf fun l _ => hi0 l (Finset.mem_univ l))
  have hai0 : α i0 ≠ 0 := by
    obtain ⟨l, hl⟩ : ∃ l, α l ≠ 0 := by
      by_contra h
      push Not at h
      exact hα0 (funext h)
    intro h0
    have := hi0 l (Finset.mem_univ l)
    rw [h0, AddValuation.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact hl this
  -- the quotients `u_l = α_l / α_{i0}`, their constant terms and the rest
  set u : σ → HahnSeries (CornerExp θ) k := fun l => α l / α i0 with hu
  set lam : σ → k := fun l => (u l).coeff 0 with hlam
  set u' : σ → HahnSeries (CornerExp θ) k := fun l => u l - HahnSeries.C (lam l) with hu'
  have huft : ∀ l, IsFiniteType (u l) := fun l => (hα l).mul ((hα i0).inv hθ)
  have hu'ft : ∀ l, IsFiniteType (u' l) := by
    intro l
    rw [hu']
    simp only
    rw [sub_eq_add_neg, HahnSeries.C_apply]
    exact (huft l).add (isFiniteType_single 0 _).neg
  have hvu : ∀ l, 0 ≤ hahnVal θ k (u l) := by
    intro l
    by_cases hul : u l = 0
    · rw [hul, AddValuation.map_zero]
      exact le_top
    have h1 := hi0 l (Finset.mem_univ l)
    have h2 : hahnVal θ k (α l) = hahnVal θ k (u l) + hahnVal θ k (α i0) := by
      rw [← AddValuation.map_mul, hu]
      simp only
      rw [div_mul_cancel₀ _ hai0]
    rw [h2, hahnVal_of_ne hul, hahnVal_of_ne hai0, ← WithTop.coe_add, WithTop.coe_le_coe] at h1
    rw [hahnVal_of_ne hul]
    exact_mod_cast (show (0 : ℝ) ≤ val θ (u l).order by linarith)
  -- the terms of `u'_l` have positive values
  have hu'pos : ∀ l, ∃ s0 : ℝ, 0 < s0 ∧ ∀ r ∈ (u' l).support, s0 ≤ val θ r := by
    intro l
    by_cases h0 : u' l = 0
    · exact ⟨1, one_pos, by simp [h0]⟩
    refine ⟨val θ (u' l).order, ?_, fun r hr => val_order_le hr⟩
    have hmem := coeff_order_ne h0
    have hsub : (u' l).support ⊆ (u l).support := by
      intro r hr hr0
      apply hr
      rw [hu']
      simp only [HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single]
      split_ifs with h
      · rw [h, hlam]
        simp
      · rw [hr0, sub_zero]
    have hne0 : (u' l).order ≠ 0 := by
      intro h
      apply hmem
      rw [h, hu']
      simp [hlam]
    have hnn : 0 ≤ val θ (u' l).order := by
      have hul : u l ≠ 0 := by
        intro h
        apply h0
        rw [hu']
        simp only
        rw [h]
        simp [hlam, h]
      have := hvu l
      rw [hahnVal_of_ne hul] at this
      have h' : (0 : ℝ) ≤ val θ (u l).order := by exact_mod_cast this
      exact h'.trans (val_order_le (hsub hmem))
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (eq_zero_of_val_eq_zero hθ h.symm) hne0
  -- `S = c / α_{i0} + Σ u_l Δ_l` has an infinite number of terms below `1 + θ`
  set S := c / α i0 + ∑ l, u l * Δ l with hS
  have hSeq : c + ∑ l, α l * Δ l = α i0 * S := by
    rw [hS, mul_add, Finset.mul_sum, hu]
    congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun l _ => ?_
      field_simp
  set T2 := c / α i0 + ∑ l, u' l * Δ l with hT2
  have hT2fin : (belowSet (1 + θ) T2).Finite := by
    refine (((hc.mul ((hα i0).inv hθ)) (1 + θ)).union
      (finite_belowSet_sum Finset.univ _ _ fun l _ => ?_)).subset (belowSet_add_subset _ _ _)
    obtain ⟨s0, hs0, hs⟩ := hu'pos l
    exact finite_belowSet_mul_tail hw (fun j => t j l) m (hu'ft l) hs0 hs
  have hcoeffS : ∀ j, m ≤ j → S.coeff (expM w (j + 1)) =
      (∑ l, lam l * t j l) + T2.coeff (expM w (j + 1)) := by
    intro j hj
    have hsplit : S = (∑ l, HahnSeries.C (lam l) * Δ l) + T2 := by
      rw [hS, hT2]
      have : ∀ l, u l * Δ l = HahnSeries.C (lam l) * Δ l + u' l * Δ l := by
        intro l
        rw [hu', sub_mul]
        ring
      simp_rw [this, Finset.sum_add_distrib]
      ring
    rw [hsplit, HahnSeries.coeff_add, HahnSeries.coeff_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, hΔ]
    simp only
    rw [cornerPoint, coeff_cornerTail hw _ m j, ite_eq_left hj, smul_eq_mul]
  have hlam0 : lam ≠ 0 := by
    intro h
    have := congrFun h i0
    rw [hlam] at this
    simp only [hu, div_self hai0, Pi.zero_apply] at this
    simp [HahnSeries.coeff_one] at this
  have hinfS : (belowSet (1 + θ) S).Infinite := by
    have hJ : {j | m ≤ j ∧ ∑ l, lam l * t j l ≠ 0}.Infinite := by
      have := ((hpl.frequently hlam0).and_eventually (eventually_ge_atTop m))
      rw [Nat.frequently_atTop_iff_infinite] at this
      exact this.mono fun j hj => ⟨hj.2, hj.1⟩
    have himg := (hJ.image (fun i _ j _ h => Nat.succ_injective
      (hw.strictMono_expM.injective h))).sdiff hT2fin
    refine himg.mono ?_
    rintro r ⟨⟨j, ⟨hj, hjt⟩, rfl⟩, hr2⟩
    refine ⟨?_, val_expM_lt hw _⟩
    rw [HahnSeries.mem_support, hcoeffS j hj]
    have : T2.coeff (expM w (j + 1)) = 0 := by
      by_contra h
      exact hr2 ⟨h, val_expM_lt hw _⟩
    rw [this, add_zero]
    exact hjt
  have hS0 : S ≠ 0 := by
    intro h
    apply hinfS
    rw [h]
    exact Set.finite_empty.subset fun r hr => by simpa using hr.1
  have hvS : hahnVal θ k S < (((1 + θ : ℝ)) : WithTop ℝ) := by
    obtain ⟨r, hr, hv⟩ := hinfS.nonempty
    rw [hahnVal_of_ne hS0]
    exact WithTop.coe_lt_coe.mpr ((val_order_le hr).trans_lt hv)
  rw [hinf, hSeq, AddValuation.map_mul, hahnVal_of_ne hai0]
  exact WithTop.add_lt_add_left WithTop.coe_ne_top hvS

/-! ### The planar tail and Conjecture P -/

/-- The points `Φ_m` of a corner run, as points of the subfield `𝔽` of finite type. -/
noncomputable def cornerPointFT (hθ : Irrational θ) (t : ℕ → σ → k) (m : ℕ) (l : σ) :
    (finiteTypeSubfield k hθ).toSubring :=
  ⟨cornerPoint (w := w) t m l, isFiniteType_cornerPoint t m l⟩

omit [DecidableEq σ] in
/-- The planar tail `IsPlanarTail` of a planar corner run, with `γ m = v(M_{m+1})` and
`Θ = 1 + θ`. It is Lemma 3.18.10 with the bound `v(Δ_m) ≥ v(M_{m+1})`. -/
theorem isPlanarTail_corner (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k)
    (hpl : IsPlanarRun t) :
    IsPlanarTail (hahnVal θ k) (finiteTypeSubfield k hθ).toSubring (cornerPointFT (w := w) hθ t)
      (fun l => cornerLimit hw (fun j => t j l)) (1 + θ)
      (fun m => val θ (expM w (m + 1) : CornerExp θ)) where
  tendsto := hw.tendsto_val_expM.comp (tendsto_add_atTop_nat 1)
  le_map m l := le_hahnVal_cornerTail hw (fun j => t j l) m
  map_lt m α c hα := by
    refine hahnVal_add_sum_mul_tail_lt hθ hw t hpl m (fun l => (α l : _)) (fun l => (α l).2) ?_
      (c : _) c.2
    intro h
    apply hα
    funext l
    exact Subtype.ext (congrFun h l)

/-- Theorem 3.18.11 for a planar corner run: Statement D for the polynomials over `𝔽` with all
degrees less than `p`. -/
theorem statementDHolds_corner {p : ℕ} [Fact p.Prime] [CharP k p] (hθ : Irrational θ)
    (hw : IsCornerWord θ w) (t : ℕ → σ → k) (hpl : IsPlanarRun t)
    (f : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring) (hf : f ≠ 0)
    (hdeg : ∀ i, degreeOf i f < p) :
    StatementDHolds (hahnVal θ k) (finiteTypeSubfield k hθ).toSubring (cornerPointFT (w := w) hθ t)
      (fun l => cornerLimit hw (fun j => t j l)) (1 + θ) f :=
  statementDHolds_of_degreeOf_lt Fact.out (isPlanarTail_corner hθ hw t hpl) f hf hdeg

/-- Theorem 3.19.6 (Conjecture P) for the planar corner runs of the Hahn model, with `θ`
irrational. The polynomial `g` has its coefficients in the subfield `𝔽` of finite type, and the
function of `P_m` is `restart p (hahnCl p) Φ_m M_m g`. The facts on the classes, the bound
`v(Δ_m) ≥ v(M_{m+1})`, the planar tail (Lemmas 3.18.8 and 3.18.10) and Statement D for the
degrees less than `p` (Theorem 3.18.11) are proved. The hypotheses are:

* `hD`: Theorem 3.18.26 for the nonzero derivatives of `g` with a degree at least `p` in some
  variable.
* `hrun`: for each large `m`, Theorem 3.18.32, part 1, and Corollary 3.18.33 for the run from
  `P_m`, as in `conjectureP_cornerRun`. -/
theorem conjectureP_planarRun {p : ℕ} [hp : Fact p.Prime] [CharP k p] (hθ : Irrational θ)
    (hw : IsCornerWord θ w) (t : ℕ → σ → k) (hpl : IsPlanarRun t)
    (g : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring)
    (hD : ∀ kk, hasse kk g ≠ 0 → (∃ i, p ≤ degreeOf i (hasse kk g)) →
      StatementDHolds (hahnVal θ k) (finiteTypeSubfield k hθ).toSubring (cornerPointFT (w := w) hθ t)
        (fun l => cornerLimit hw (fun j => t j l)) (1 + θ) (hasse kk g))
    (μ : ℕ → WithTop ℝ)
    (hrun : ∀ᶠ m in atTop, ∃ e, 1 ≤ e ∧
      (∀ i, μ m + ((((p ^ e : ℕ) : ℝ) * (1 + θ - val θ (expM w m)) : ℝ) : WithTop ℝ) ≤
        hahnVal θ k (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (single i 1)
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map (finiteTypeSubfield k hθ).toSubring.subtype g)))) +
          ((1 + θ - val θ (expM w m) : ℝ) : WithTop ℝ)) ∧
      ∃ i, eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map (finiteTypeSubfield k hθ).toSubring.subtype g))) -
        hahnCl p (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map (finiteTypeSubfield k hθ).toSubring.subtype g)))) ≠ 0 ∧
      hahnVal θ k (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map (finiteTypeSubfield k hθ).toSubring.subtype g))) -
        hahnCl p (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map (finiteTypeSubfield k hθ).toSubring.subtype g))))) ≤ μ m) :
    False := by
  refine conjectureP_cornerRun hw t (finiteTypeSubfield k hθ).toSubring
    (fun m l => isFiniteType_cornerPoint t m l) g (fun kk hk => ?_) μ hrun
  by_cases hdeg : ∀ i, degreeOf i (hasse kk g) < p
  · exact statementDHolds_corner hθ hw t hpl _ hk hdeg
  · push Not at hdeg
    exact hD kk hk hdeg

end PlanarRuns

end Singularity
