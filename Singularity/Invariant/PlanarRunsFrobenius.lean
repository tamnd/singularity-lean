/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Perfect
import Singularity.Invariant.PlanarRunsAnyDegree
import Singularity.Invariant.PlanarRunsFiniteType

/-!
# Theorem 3.18.26 for the planar corner runs

This file proves Theorem 3.18.26 of Volume 7 of the handbook for the planar corner runs of the
Hahn model of `PlanarRunsHahn.lean`, with `θ` irrational and a perfect field `k` of
characteristic `p`. It removes the hypothesis `hD` of `conjectureP_planarRun`.

## Main results

* `det_expY_expZ`: Lemma 3.18.23. The exponents of `y_m` and `z_m` have determinant `1`, so the
  exponent `U_m` of `y_m z_m` is not divisible by `p` (`not_dvd_expU`).
* `finite_smul_expM_eq`: Lemma 3.18.24. For `(e, d) ≠ (e', 0)`, the equation
  `p^e M_{j+1} = d + p^{e'} M_{j'+1}` has solutions for only a finite number of `j`.
* `cornerTail_pow`: in characteristic `p`,
  `Δ_m^{p^e} = Σ_{m ≤ j < J} t_j^{p^e} M_{j+1}^{p^e} + Δ_J^{p^e}`.
* `hahnVal_add_sum_mul_tail_pow_lt`: Steps 3 and 4 of the proof of Theorem 3.18.26 (the germ
  counting with Lemmas 3.18.24 and 3.18.25). On a planar run, for `α_{i, e}` and `c` of finite
  type, not all `α_{i, e}` zero,
  `v(c + Σ_{i, e} α_{i, e} Δ_{m, i}^{p^e}) < min_{i, e} (v(α_{i, e}) + p^e (1 + θ))`.
  The `p^e`-th roots of the coefficients of least value exist since `k` is perfect, and the
  planar condition gives an infinite number of nonzero germs.
* `isFrobTail_corner`: the tail `IsFrobTail` of `PlanarRunsAnyDegree.lean`.
* `statementDHolds_corner_frob`: Theorem 3.18.26 for each nonzero polynomial over `𝔽`.
* `conjectureP_planarRun_perfect`: Theorem 3.19.6 (Conjecture P) for the planar corner runs
  over a perfect field, with only Theorem 3.18.32, part 1, and Corollary 3.18.33 for the run from
  each `P_m` as hypotheses.

## References

* Volume 7, Sections 3.18 and 3.19 of the handbook.
-/

open MvPolynomial Filter Topology

namespace Singularity

namespace PlanarRuns

open CornerExp

variable {θ : ℝ} {k : Type*} [Field k] {w : ℕ → Bool}

/-! ### Exponents -/

theorem CornerExp.fst_nsmul (n : ℕ) (r : CornerExp θ) : fst (n • r) = (n : ℤ) * fst r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, fst_add, ih]
    push_cast
    ring

theorem CornerExp.snd_nsmul (n : ℕ) (r : CornerExp θ) : snd (n • r) = (n : ℤ) * snd r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, snd_add, ih]
    push_cast
    ring

theorem CornerExp.val_nsmul (n : ℕ) (r : CornerExp θ) : val θ (n • r) = (n : ℝ) * val θ r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, val_add, ih]
    push_cast
    ring

/-- Lemma 3.18.23: `det(y_m, z_m) = 1`. -/
theorem det_expY_expZ (w : ℕ → Bool) (m : ℕ) :
    fst (expY w m : CornerExp θ) * snd (expZ w m : CornerExp θ) -
      snd (expY w m : CornerExp θ) * fst (expZ w m : CornerExp θ) = 1 := by
  induction m with
  | zero => simp [expY, expZ, expYZ]
  | succ m ih =>
    rw [expY_succ, expZ_succ]
    split_ifs
    · simp only [fst_sub, snd_sub]
      linear_combination ih
    · simp only [fst_sub, snd_sub]
      linear_combination ih

/-- Lemma 3.18.23: the exponent `U_m` of `y_m z_m` is not divisible by `p`. -/
theorem not_dvd_expU {p : ℕ} (hp : p.Prime) (w : ℕ → Bool) (m : ℕ) :
    ¬ ((p : ℤ) ∣ fst (expY w m + expZ w m : CornerExp θ) ∧
      (p : ℤ) ∣ snd (expY w m + expZ w m : CornerExp θ)) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have h := det_expY_expZ (θ := θ) w m
  simp only [fst_add, snd_add] at ha hb
  have h1 : (p : ℤ) ∣ 1 := ⟨fst (expY w m : CornerExp θ) * b - snd (expY w m : CornerExp θ) * a, by
    rw [← h]
    linear_combination (fst (expY w m : CornerExp θ)) * hb - (snd (expY w m : CornerExp θ)) * ha⟩
  have h2 := Int.eq_one_of_dvd_one (by positivity) h1
  exact hp.ne_one (by exact_mod_cast h2)

theorem dvd_of_pow_mul_eq {p : ℤ} (hp : p ≠ 0) {e e' : ℕ} (h : e < e') {a b : ℤ}
    (hab : p ^ e * a = p ^ e' * b) : p ∣ a := by
  have he : p ^ e' = p ^ e * p ^ (e' - e) := by
    rw [← pow_add]
    congr 1
    omega
  rw [he, mul_assoc] at hab
  rw [mul_left_cancel₀ (pow_ne_zero e hp) hab]
  exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) b

theorem smul_expM_injective (hw : IsCornerWord θ w) {q : ℕ} (hq : 0 < q) :
    Function.Injective (fun j => q • (expM w (j + 1) : CornerExp θ)) := by
  intro a b h
  have h1 := congrArg (val θ) h
  simp only [val_nsmul] at h1
  have hq' : (q : ℝ) ≠ 0 := by positivity
  exact Nat.succ_injective (hw.strictMono_val_expM.injective (mul_left_cancel₀ hq' h1))

/-- Lemma 3.18.24: for `(e, d) ≠ (e', 0)`, the equation `p^e M_{j+1} = d + p^{e'} M_{j'+1}` has
solutions for only a finite number of `j`. -/
theorem finite_smul_expM_eq (hθ : Irrational θ) (hw : IsCornerWord θ w) {p : ℕ} (hp : p.Prime)
    {e e' : ℕ} (d : CornerExp θ) (hd : e ≠ e' ∨ d ≠ 0) :
    {j | ∃ j', p ^ e • (expM w (j + 1) : CornerExp θ) = d + p ^ e' • expM w (j' + 1)}.Finite := by
  have hq : (0 : ℝ) < ((p ^ e : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos e
  have hq' : (0 : ℝ) < ((p ^ e' : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos e'
  by_cases hδ : val θ d = (((p ^ e : ℕ) : ℝ) - ((p ^ e' : ℕ) : ℝ)) * (1 + θ)
  · have hv : val θ (mk 1 1 : CornerExp θ) = 1 + θ := by simp [val]
    have hd' : d = p ^ e • (mk 1 1 : CornerExp θ) - p ^ e' • mk 1 1 := by
      apply val_injective hθ
      rw [val_sub, val_nsmul, val_nsmul, hδ, hv]
      ring
    have hne : e ≠ e' := by
      rcases hd with h | h
      · exact h
      · intro hee
        apply h
        rw [hd', hee, sub_self]
    refine Set.finite_empty.subset ?_
    rintro j ⟨j', hj⟩
    rw [hd'] at hj
    have h1 := congrArg fst hj
    have h2 := congrArg snd hj
    simp only [expM_eq, fst_add, fst_sub, fst_nsmul, fst_mk, snd_add, snd_sub, snd_nsmul,
      snd_mk] at h1 h2
    push_cast at h1 h2
    have hf : (p : ℤ) ^ e * fst (expY w (j + 1) + expZ w (j + 1) : CornerExp θ) =
        (p : ℤ) ^ e' * fst (expY w (j' + 1) + expZ w (j' + 1) : CornerExp θ) := by
      simp only [fst_add]
      linear_combination -h1
    have hs : (p : ℤ) ^ e * snd (expY w (j + 1) + expZ w (j + 1) : CornerExp θ) =
        (p : ℤ) ^ e' * snd (expY w (j' + 1) + expZ w (j' + 1) : CornerExp θ) := by
      simp only [snd_add]
      linear_combination -h2
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact not_dvd_expU hp w (j + 1) ⟨dvd_of_pow_mul_eq hpz hlt hf, dvd_of_pow_mul_eq hpz hlt hs⟩
    · exact not_dvd_expU hp w (j' + 1)
        ⟨dvd_of_pow_mul_eq hpz hlt hf.symm, dvd_of_pow_mul_eq hpz hlt hs.symm⟩
  · set δ := val θ d - (((p ^ e : ℕ) : ℝ) - ((p ^ e' : ℕ) : ℝ)) * (1 + θ) with hδdef
    have hδ0 : 0 < |δ| := abs_pos.mpr (sub_ne_zero.mpr hδ)
    have hu : Tendsto (fun n => 1 + θ - val θ (expM w (n + 1) : CornerExp θ)) atTop (𝓝 0) := by
      have := (hw.tendsto_val_expM.comp (tendsto_add_atTop_nat 1)).const_sub (1 + θ)
      rwa [sub_self] at this
    have h1 : ∀ᶠ n in atTop,
        ((p ^ e : ℕ) : ℝ) * (1 + θ - val θ (expM w (n + 1) : CornerExp θ)) < |δ| := by
      have := hu.const_mul ((p ^ e : ℕ) : ℝ)
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds hδ0)
    have h2 : ∀ᶠ n in atTop,
        ((p ^ e' : ℕ) : ℝ) * (1 + θ - val θ (expM w (n + 1) : CornerExp θ)) < |δ| := by
      have := hu.const_mul ((p ^ e' : ℕ) : ℝ)
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds hδ0)
    obtain ⟨J0, hJ0⟩ := (h1.and h2).exists_forall_of_atTop
    have hfin : ({j | j < J0} ∪ ⋃ j' ∈ {j' : ℕ | j' < J0},
        {j | p ^ e • (expM w (j + 1) : CornerExp θ) = d + p ^ e' • expM w (j' + 1)}).Finite :=
      (Set.finite_lt_nat J0).union (Set.Finite.biUnion (Set.finite_lt_nat J0) fun j' _ =>
        Set.Subsingleton.finite fun a (ha : p ^ e • _ = _) b (hb : p ^ e • _ = _) =>
          smul_expM_injective hw (pow_pos hp.pos e) (ha.trans hb.symm))
    refine hfin.subset ?_
    rintro j ⟨j', hj⟩
    by_cases hjJ : j < J0
    · exact Set.mem_union_left _ hjJ
    by_cases hj'J : j' < J0
    · exact Set.mem_union_right _ (Set.mem_biUnion (show j' ∈ {j' : ℕ | j' < J0} from hj'J) hj)
    exfalso
    push Not at hjJ hj'J
    have hv := congrArg (val θ) hj
    rw [val_nsmul, val_add, val_nsmul] at hv
    obtain ⟨ha1, -⟩ := hJ0 j hjJ
    obtain ⟨-, hb2⟩ := hJ0 j' hj'J
    have hpj := val_expM_lt hw (j + 1)
    have hpj' := val_expM_lt hw (j' + 1)
    have hA : 0 < ((p ^ e : ℕ) : ℝ) * (1 + θ - val θ (expM w (j + 1) : CornerExp θ)) :=
      mul_pos hq (by linarith)
    have hB : 0 < ((p ^ e' : ℕ) : ℝ) * (1 + θ - val θ (expM w (j' + 1) : CornerExp θ)) :=
      mul_pos hq' (by linarith)
    have hrel : ((p ^ e' : ℕ) : ℝ) * (1 + θ - val θ (expM w (j' + 1) : CornerExp θ)) -
        ((p ^ e : ℕ) : ℝ) * (1 + θ - val θ (expM w (j + 1) : CornerExp θ)) = δ := by
      rw [hδdef]
      linear_combination hv
    rcases le_or_gt 0 δ with h | h
    · rw [abs_of_nonneg h] at ha1 hb2
      linarith
    · rw [abs_of_neg h] at ha1 hb2
      linarith

/-! ### Powers of the tail -/

theorem hahnVal_le_of_mem {x : HahnSeries (CornerExp θ) k} {r : CornerExp θ}
    (hr : r ∈ x.support) : hahnVal θ k x ≤ ((val θ r : ℝ) : WithTop ℝ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hr
  rw [hahnVal_of_ne hx]
  exact WithTop.coe_le_coe.mpr (val_order_le hr)

theorem val_le_of_mem_support_mul_pow {α Δ : HahnSeries (CornerExp θ) k} {γ : ℝ}
    (hΔ : ((γ : ℝ) : WithTop ℝ) ≤ hahnVal θ k Δ) (hα : α ≠ 0) (n : ℕ) {r : CornerExp θ}
    (hr : r ∈ (α * Δ ^ n).support) : val θ α.order + (n : ℝ) * γ ≤ val θ r := by
  have h1 := hahnVal_le_of_mem hr
  rw [AddValuation.map_mul, AddValuation.map_pow, hahnVal_of_ne hα] at h1
  have h2 : (((n : ℝ) * γ : ℝ) : WithTop ℝ) ≤ n • hahnVal θ k Δ := by
    rw [← nsmul_eq_mul, WithTop.coe_nsmul]
    exact nsmul_le_nsmul_right hΔ n
  have h3 : ((val θ α.order + (n : ℝ) * γ : ℝ) : WithTop ℝ) ≤ ((val θ r : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_add]
    exact (add_le_add le_rfl h2).trans h1
  exact_mod_cast h3

theorem coeff_mul_sum_single {ι : Type*} (s : Finset ι) (α : HahnSeries (CornerExp θ) k)
    (a : ι → CornerExp θ) (b : ι → k) (r : CornerExp θ) :
    (α * ∑ i ∈ s, HahnSeries.single (a i) (b i)).coeff r = ∑ i ∈ s, α.coeff (r - a i) * b i := by
  rw [Finset.mul_sum, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := HahnSeries.coeff_mul_single_add (x := α) (r := b i) (a := r - a i) (b := a i)
  rwa [sub_add_cancel] at this

/-- In characteristic `p`, `Δ_m^{p^e} = Σ_{m ≤ j < J} c_j^{p^e} M_{j+1}^{p^e} + Δ_J^{p^e}`. -/
theorem cornerTail_pow (hw : IsCornerWord θ w) (c : ℕ → k) {p : ℕ} [Fact p.Prime] [CharP k p]
    (e : ℕ) {m J : ℕ} (hmJ : m ≤ J) :
    (cornerLimit hw c - cornerSum (cornerL θ k w) (fun j => HahnSeries.C (c j)) m) ^ p ^ e =
      ∑ j ∈ Finset.Ico m J,
        HahnSeries.single (p ^ e • (expM w (j + 1) : CornerExp θ)) (c j ^ p ^ e) +
      (cornerLimit hw c - cornerSum (cornerL θ k w) (fun j => HahnSeries.C (c j)) J) ^ p ^ e := by
  have h : cornerLimit hw c - cornerSum (cornerL θ k w) (fun j => HahnSeries.C (c j)) m =
      (∑ j ∈ Finset.Ico m J, HahnSeries.single (expM w (j + 1)) (c j)) +
      (cornerLimit hw c - cornerSum (cornerL θ k w) (fun j => HahnSeries.C (c j)) J) := by
    rw [cornerSum_eq, cornerSum_eq, Finset.sum_Ico_eq_sub _ hmJ]
    abel
  rw [h, add_pow_char_pow, sum_pow_char_pow]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [HahnSeries.single_pow]

/-! ### The germ counting -/

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
/-- Steps 3 and 4 of the proof of Theorem 3.18.26 for a planar corner run over a perfect field:
for `α_{i, e}` and `c` of finite type, not all `α_{i, e}` zero,
`v(c + Σ_{i, e} α_{i, e} Δ_{m, i}^{p^e}) < min_{i, e} (v(α_{i, e}) + p^e (1 + θ))`. -/
theorem hahnVal_add_sum_mul_tail_pow_lt {p : ℕ} [hp : Fact p.Prime] [CharP k p]
    [PerfectRing k p] (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k)
    (hpl : IsPlanarRun t) (m n : ℕ) (α : σ × ℕ → HahnSeries (CornerExp θ) k)
    (hα : ∀ x, IsFiniteType (α x))
    (hα0 : ∃ x ∈ (Finset.univ : Finset σ) ×ˢ Finset.range n, α x ≠ 0)
    (c : HahnSeries (CornerExp θ) k) (hc : IsFiniteType c) :
    hahnVal θ k (c + ∑ x ∈ (Finset.univ : Finset σ) ×ˢ Finset.range n,
        α x * (cornerLimit hw (fun j => t j x.1) - cornerPoint (w := w) t m x.1) ^ (p ^ x.2)) <
      ((Finset.univ : Finset σ) ×ˢ Finset.range n).inf
        (fun x => hahnVal θ k (α x) + ((((p ^ x.2 : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ)) := by
  classical
  set P := (Finset.univ : Finset σ) ×ˢ Finset.range n with hP
  set X := c + ∑ x ∈ P,
    α x * (cornerLimit hw (fun j => t j x.1) - cornerPoint (w := w) t m x.1) ^ (p ^ x.2) with hX
  have hpos : ∀ e, 0 < p ^ e := fun e => pow_pos hp.out.pos e
  -- the index of least value
  obtain ⟨xa, hxa, hxa0⟩ := hα0
  obtain ⟨⟨i0, e0⟩, hx0, hmin⟩ := (P.filter fun x => α x ≠ 0).exists_min_image
    (fun x => val θ (α x).order + ((p ^ x.2 : ℕ) : ℝ) * (1 + θ))
    ⟨xa, Finset.mem_filter.mpr ⟨hxa, hxa0⟩⟩
  obtain ⟨hx0P, hx00⟩ := Finset.mem_filter.mp hx0
  set ν0 := (α (i0, e0)).order with hν0
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = val θ ν0 + ((p ^ e0 : ℕ) : ℝ) * (1 + θ) := ⟨_, rfl⟩
  have hmin' : ∀ x ∈ P, α x ≠ 0 →
      L ≤ val θ (α x).order + ((p ^ x.2 : ℕ) : ℝ) * (1 + θ) := fun x hx h => by
    rw [hL]
    exact hmin x (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hLinf : (L : WithTop ℝ) ≤ P.inf
      (fun x => hahnVal θ k (α x) + ((((p ^ x.2 : ℕ) : ℝ) * (1 + θ) : ℝ) : WithTop ℝ)) := by
    refine Finset.le_inf fun x hx => ?_
    by_cases hx0' : α x = 0
    · rw [hx0', AddValuation.map_zero, WithTop.top_add]
      exact le_top
    · rw [hahnVal_of_ne hx0', ← WithTop.coe_add, WithTop.coe_le_coe]
      exact hmin' x hx hx0'
  suffices hS : ∃ r ∈ X.support, val θ r < L by
    obtain ⟨r, hr, hv⟩ := hS
    exact ((hahnVal_le_of_mem hr).trans_lt (WithTop.coe_lt_coe.mpr hv)).trans_le hLinf
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
  refine ⟨r j, ?_, hval_r j⟩
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
  rw [HahnSeries.mem_support, hcoeffX, hc0, zero_add, Finset.sum_add_distrib,
    Finset.sum_eq_zero htail0, add_zero, hsum, hfrob]
  exact pow_ne_zero _ hjt

/-! ### Theorem 3.18.26 and Conjecture P -/

omit [DecidableEq σ] in
/-- The tail `IsFrobTail` of a planar corner run over a perfect field, with `γ m = v(M_{m+1})`
and `Θ = 1 + θ`. -/
theorem isFrobTail_corner {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k) (hpl : IsPlanarRun t) :
    IsFrobTail (hahnVal θ k) (finiteTypeSubfield k hθ).toSubring (cornerPointFT (w := w) hθ t)
      (fun l => cornerLimit hw (fun j => t j l)) p (1 + θ)
      (fun m => val θ (expM w (m + 1) : CornerExp θ)) where
  tendsto := hw.tendsto_val_expM.comp (tendsto_add_atTop_nat 1)
  le_map m l := le_hahnVal_cornerTail hw (fun j => t j l) m
  map_lt m n α c hα := by
    obtain ⟨x, hx, hx0⟩ := hα
    exact hahnVal_add_sum_mul_tail_pow_lt hθ hw t hpl m n (fun x => (α x : _)) (fun x => (α x).2)
      ⟨x, hx, fun h => hx0 (Subtype.ext h)⟩ (c : _) c.2

/-- Theorem 3.18.26 for a planar corner run over a perfect field: Statement D for each nonzero
polynomial over `𝔽`, with no condition on the degree. -/
theorem statementDHolds_corner_frob {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k) (hpl : IsPlanarRun t)
    (f : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring) (hf : f ≠ 0) :
    StatementDHolds (hahnVal θ k) (finiteTypeSubfield k hθ).toSubring (cornerPointFT (w := w) hθ t)
      (fun l => cornerLimit hw (fun j => t j l)) (1 + θ) f :=
  statementD_frob Fact.out (isFrobTail_corner hθ hw t hpl) f hf

/-- Theorem 3.19.6 (Conjecture P) for the planar corner runs of the Hahn model over a perfect
field `k`, with `θ` irrational. Theorem 3.18.26 is proved (`statementDHolds_corner_frob`), so the
only hypothesis `hrun` is Theorem 3.18.32, part 1, and Corollary 3.18.33 for the run from each
`P_m`, as in `conjectureP_planarRun`. -/
theorem conjectureP_planarRun_perfect {p : ℕ} [hp : Fact p.Prime] [CharP k p] [PerfectRing k p]
    (hθ : Irrational θ) (hw : IsCornerWord θ w) (t : ℕ → σ → k) (hpl : IsPlanarRun t)
    (g : MvPolynomial σ (finiteTypeSubfield k hθ).toSubring)
    (μ : ℕ → WithTop ℝ)
    (hrun : ∀ᶠ m in atTop, ∃ e, 1 ≤ e ∧
      (∀ i, μ m + ((((p ^ e : ℕ) : ℝ) * (1 + θ - val θ (expM w m)) : ℝ) : WithTop ℝ) ≤
        hahnVal θ k (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (Finsupp.single i 1)
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map (finiteTypeSubfield k hθ).toSubring.subtype g)))) +
          ((1 + θ - val θ (expM w m) : ℝ) : WithTop ℝ)) ∧
      ∃ i, eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (Finsupp.single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map (finiteTypeSubfield k hθ).toSubring.subtype g))) -
        hahnCl p (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (Finsupp.single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map (finiteTypeSubfield k hθ).toSubring.subtype g)))) ≠ 0 ∧
      hahnVal θ k (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (Finsupp.single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map (finiteTypeSubfield k hθ).toSubring.subtype g))) -
        hahnCl p (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (Finsupp.single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map (finiteTypeSubfield k hθ).toSubring.subtype g))))) ≤ μ m) :
    False :=
  conjectureP_planarRun hθ hw t hpl g
    (fun _ hk _ => statementDHolds_corner_frob hθ hw t hpl _ hk) μ hrun

end PlanarRuns

end Singularity
