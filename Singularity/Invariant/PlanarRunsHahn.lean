/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Topology.Order.MonotoneConvergence
import Singularity.Invariant.PlanarRunsConjectureP

/-!
# The Hahn field of a corner run in four variables

This file builds the Hahn field `𝕂` of Lemma 3.15.6 of Volume 7 of the handbook, the classes of
Section 3.18, and the corner runs in four variables of Section 3.17 (Definition 3.17.5), on top
of the Hahn series of Mathlib. With them it proves, for the concrete model, the facts on the
classes and the bound `v(Δ_m) ≥ v(M_{m+1})` that `conjectureP_of_restart_model` takes as
hypotheses.

## The model

* `CornerExp θ` is the group `ℤ × ℤ` of the exponents `(a, b)` of the Laurent monomials
  `y_N^a z_N^b`, with the value `val θ (a, b) = a + θ b`. Its order is the order of the value,
  with a lexicographic tie break on `(a, b)`. For `θ` irrational there is no tie, and the order is
  the order of the value. The tie break makes the order linear for each `θ`, so the order does
  not need a hypothesis.
* `HahnSeries (CornerExp θ) k` is the Hahn field `𝕂`, for a field `k` (the field `K` of the
  handbook). `hahnVal θ k` is the valuation `v` with values in `WithTop ℝ`, the value of the
  term of least exponent.
* `classHom p` sends `(a, b)` to its class in `(ℤ/p)²`. `classPart0 p x` is the sum of the terms
  of `x` of class `0`, `hahnCl p x = x - classPart0 p x` is the sum of the terms of nonzero class,
  and `hahnK0 p` is the subring of the series with only terms of class `0`.
* A corner run is given by its word `w : ℕ → Bool` (`true` for a `y`-step) and its translations
  `t : ℕ → σ → k`. The exponents of `y_m` and `z_m` at `P_N` are `expY` and `expZ`, the chart
  variable `L_m` has the exponent `expL`, and `M_m` has the exponent `expM`. The point is
  `cornerPoint`, the sum `Φ_m = Σ_{j < m} t_j M_{j+1}` of `cornerSum` of `PlanarRunsRestart`,
  and the limit is `cornerLimit`, the series `Φ_∞ = Σ_j t_j M_{j+1}`.
* `IsCornerWord θ w` says that each chart occurs an infinite number of times and that
  `v(y_m) > 0` and `v(z_m) > 0` for each `m`. This is the choice of `θ` of Lemma 3.13.24.

## Main results

* `isClassPart_hahn` and `hahnVal_le_sub_hahnCl`: the facts 1 to 3 of the classes, that is,
  `IsClassPart p (hahnK0 p) (hahnCl p)` and `v(x) ≤ v(x - cl x)`.
* `tendsto_val_expM` (Lemma 3.13.24): `v(M_m) → 1 + θ`.
* `le_hahnVal_cornerTail`: each entry of `Δ_m = Φ_∞ - Φ_m` has a value at least `v(M_{m+1})`.
* `conjectureP_cornerRun`: Theorem 3.19.6 (Conjecture P) for the corner runs of this model,
  with the hypotheses of `conjectureP_of_restart_model` on the classes and on `Δ_m` removed.

## References

* Volume 7, Sections 3.15, 3.17 and 3.18 of the handbook: Lemma 3.15.6, Definition 3.17.5,
  Lemma 3.18.23.
-/

open MvPolynomial Filter Topology Finsupp

namespace Singularity

namespace PlanarRuns

/-! ### The group of exponents -/

/-- The exponents `(a, b)` of the Laurent monomials `y_N^a z_N^b`, ordered by the value
`a + θ b`. -/
def CornerExp (_θ : ℝ) : Type := ℤ × ℤ

namespace CornerExp

variable {θ : ℝ}

instance : AddCommGroup (CornerExp θ) := inferInstanceAs (AddCommGroup (ℤ × ℤ))

/-- The exponent `(a, b)`. -/
def mk (a b : ℤ) : CornerExp θ := ((a, b) : ℤ × ℤ)

/-- The first exponent. -/
def fst (r : CornerExp θ) : ℤ := (r : ℤ × ℤ).1

/-- The second exponent. -/
def snd (r : CornerExp θ) : ℤ := (r : ℤ × ℤ).2

@[simp] theorem fst_mk (a b : ℤ) : fst (mk a b : CornerExp θ) = a := rfl
@[simp] theorem snd_mk (a b : ℤ) : snd (mk a b : CornerExp θ) = b := rfl
@[simp] theorem fst_add (r s : CornerExp θ) : fst (r + s) = fst r + fst s := rfl
@[simp] theorem snd_add (r s : CornerExp θ) : snd (r + s) = snd r + snd s := rfl
@[simp] theorem fst_sub (r s : CornerExp θ) : fst (r - s) = fst r - fst s := rfl
@[simp] theorem snd_sub (r s : CornerExp θ) : snd (r - s) = snd r - snd s := rfl
@[simp] theorem fst_neg (r : CornerExp θ) : fst (-r) = -fst r := rfl
@[simp] theorem snd_neg (r : CornerExp θ) : snd (-r) = -snd r := rfl
@[simp] theorem fst_zero : fst (0 : CornerExp θ) = 0 := rfl
@[simp] theorem snd_zero : snd (0 : CornerExp θ) = 0 := rfl

theorem ext {r s : CornerExp θ} (h1 : fst r = fst s) (h2 : snd r = snd s) : r = s :=
  Prod.ext h1 h2

variable (θ) in
/-- The value `v(y_N^a z_N^b) = a + θ b`. -/
def val (r : CornerExp θ) : ℝ := (fst r : ℝ) + θ * (snd r : ℝ)

@[simp] theorem val_add (r s : CornerExp θ) : val θ (r + s) = val θ r + val θ s := by
  simp only [val, fst_add, snd_add, Int.cast_add]
  ring

@[simp] theorem val_sub (r s : CornerExp θ) : val θ (r - s) = val θ r - val θ s := by
  simp only [val, fst_sub, snd_sub, Int.cast_sub]
  ring

@[simp] theorem val_zero : val θ (0 : CornerExp θ) = 0 := by simp [val]

/-- The key of the order: the value, then `(a, b)`. -/
def key (r : CornerExp θ) : ℝ ×ₗ (ℤ ×ₗ ℤ) := toLex (val θ r, toLex (fst r, snd r))

theorem key_injective : Function.Injective (key : CornerExp θ → ℝ ×ₗ (ℤ ×ₗ ℤ)) := by
  intro r s h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  exact ext h.2.1 h.2.2

theorem key_add (r s : CornerExp θ) : key (r + s) = key r + key s := by
  simp only [key, val_add, fst_add, snd_add]
  rfl

noncomputable instance : LinearOrder (CornerExp θ) := LinearOrder.lift' key key_injective

theorem le_iff_key {r s : CornerExp θ} : r ≤ s ↔ key r ≤ key s := Iff.rfl

instance : IsOrderedCancelAddMonoid (CornerExp θ) :=
  Function.Injective.isOrderedCancelAddMonoid key key_add Iff.rfl

theorem val_mono : Monotone (val θ) := by
  intro r s h
  have := Prod.Lex.monotone_fst _ _ (le_iff_key.mp h)
  simpa [key] using this

theorem lt_of_val_lt {r s : CornerExp θ} (h : val θ r < val θ s) : r < s := by
  rcases lt_or_ge r s with h' | h'
  · exact h'
  · exact absurd (val_mono h') (not_le.mpr h)

end CornerExp

open CornerExp

/-! ### The Hahn field and its valuation -/

section HahnField

variable (θ : ℝ) (k : Type*) [Field k]

/-- The value map `WithTop (CornerExp θ) → WithTop ℝ`. -/
noncomputable def valHom : WithTop (CornerExp θ) →+o WithTop ℝ where
  toFun := WithTop.map (val θ)
  map_zero' := by simp [WithTop.map_zero]
  map_add' x y := by
    cases x <;> cases y <;> simp [← WithTop.coe_add]
  monotone' := WithTop.monotone_map_iff.mpr val_mono

/-- The valuation `v` of the Hahn field `𝕂`, with `v(y_N^a z_N^b) = a + θ b`. -/
noncomputable def hahnVal : AddValuation (HahnSeries (CornerExp θ) k) (WithTop ℝ) :=
  (HahnSeries.addVal (CornerExp θ) k).map (valHom θ) rfl

variable {θ k}

theorem coeff_order_ne {x : HahnSeries (CornerExp θ) k} (hx : x ≠ 0) : x.coeff x.order ≠ 0 :=
  mt HahnSeries.coeff_order_eq_zero.mp hx

theorem hahnVal_of_ne {x : HahnSeries (CornerExp θ) k} (hx : x ≠ 0) :
    hahnVal θ k x = ((val θ x.order : ℝ) : WithTop ℝ) := by
  simp [hahnVal, valHom, HahnSeries.addVal_apply_of_ne hx]

theorem hahnVal_single {r : CornerExp θ} {c : k} (hc : c ≠ 0) :
    hahnVal θ k (HahnSeries.single r c) = ((val θ r : ℝ) : WithTop ℝ) := by
  rw [hahnVal_of_ne (HahnSeries.single_ne_zero hc), HahnSeries.order_single hc]

/-- A lower bound for the value from a lower bound on the support. -/
theorem le_hahnVal_of_forall {x : HahnSeries (CornerExp θ) k} {γ : ℝ}
    (h : ∀ r ∈ x.support, γ ≤ val θ r) : ((γ : ℝ) : WithTop ℝ) ≤ hahnVal θ k x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [hahnVal_of_ne hx]
    exact WithTop.coe_le_coe.mpr (h _ (coeff_order_ne hx))

/-- The value goes down when the support grows. -/
theorem hahnVal_le_of_support_subset {x y : HahnSeries (CornerExp θ) k}
    (h : y.support ⊆ x.support) : hahnVal θ k x ≤ hahnVal θ k y := by
  by_cases hy : y = 0
  · simp [hy]
  have hx : x ≠ 0 := by
    intro hx
    apply hy
    rw [← HahnSeries.support_eq_empty_iff]
    exact Set.subset_empty_iff.mp (by simpa [hx] using h)
  rw [hahnVal_of_ne hx, hahnVal_of_ne hy]
  exact WithTop.coe_le_coe.mpr (val_mono (HahnSeries.order_le_of_coeff_ne_zero
    (h (coeff_order_ne hy))))

instance hahn_charP (p : ℕ) [CharP k p] : CharP (HahnSeries (CornerExp θ) k) p :=
  charP_of_injective_ringHom (HahnSeries.C_injective) p

end HahnField

/-! ### The classes -/

section Classes

variable {θ : ℝ} (p : ℕ)

/-- The class of an exponent, in `(ℤ/p)²`. -/
def classHom : CornerExp θ →+ ZMod p × ZMod p where
  toFun r := ((fst r : ZMod p), (snd r : ZMod p))
  map_zero' := by simp
  map_add' r s := by simp

variable {k : Type*} [Field k]

/-- The terms of a given class `c`. -/
noncomputable def classPart (c : ZMod p × ZMod p) (x : HahnSeries (CornerExp θ) k) :
    HahnSeries (CornerExp θ) k where
  coeff r := if classHom p r = c then x.coeff r else 0
  isPWO_support' := x.isPWO_support.mono fun r hr => by
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hr
    exact hr.2

@[simp] theorem coeff_classPart (c : ZMod p × ZMod p) (x : HahnSeries (CornerExp θ) k)
    (r : CornerExp θ) :
    (classPart p c x).coeff r = if classHom p r = c then x.coeff r else 0 := rfl

theorem classPart_add (c : ZMod p × ZMod p) (x y : HahnSeries (CornerExp θ) k) :
    classPart p c (x + y) = classPart p c x + classPart p c y := by
  ext r
  simp only [coeff_classPart, HahnSeries.coeff_add]
  split_ifs <;> simp

/-- The terms of class `0`. -/
noncomputable def classPart0 : HahnSeries (CornerExp θ) k →+ HahnSeries (CornerExp θ) k where
  toFun := classPart p 0
  map_zero' := by ext r; simp
  map_add' := classPart_add p 0

/-- The part `cl x` of nonzero class. -/
noncomputable def hahnCl : HahnSeries (CornerExp θ) k →+ HahnSeries (CornerExp θ) k :=
  AddMonoidHom.id _ - classPart0 p

theorem hahnCl_apply (x : HahnSeries (CornerExp θ) k) : hahnCl p x = x - classPart0 p x := rfl

theorem sub_hahnCl (x : HahnSeries (CornerExp θ) k) : x - hahnCl p x = classPart0 p x := by
  rw [hahnCl_apply, sub_sub_cancel]

/-- The series with only terms of a class `c`. -/
def InClass (c : ZMod p × ZMod p) (x : HahnSeries (CornerExp θ) k) : Prop :=
  ∀ r ∈ x.support, classHom p r = c

theorem InClass.mul {c d : ZMod p × ZMod p} {x y : HahnSeries (CornerExp θ) k}
    (hx : InClass p c x) (hy : InClass p d y) : InClass p (c + d) (x * y) := by
  intro r hr
  obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_add.mp (HahnSeries.support_mul_subset hr)
  rw [map_add, hx s hs, hy t ht]

theorem inClass_one : InClass p 0 (1 : HahnSeries (CornerExp θ) k) := by
  intro r hr
  rw [HahnSeries.eq_of_mem_support_single hr, map_zero]

theorem InClass.pow {c : ZMod p × ZMod p} {x : HahnSeries (CornerExp θ) k}
    (hx : InClass p c x) (n : ℕ) : InClass p (n • c) (x ^ n) := by
  induction n with
  | zero => simpa using inClass_one p
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul p hx

theorem inClass_classPart (c : ZMod p × ZMod p) (x : HahnSeries (CornerExp θ) k) :
    InClass p c (classPart p c x) := by
  intro r hr
  rw [HahnSeries.mem_support, coeff_classPart] at hr
  by_contra h
  exact hr (ite_eq_right h)

/-- The subring `K0` of the series with only terms of class `0`. -/
def hahnK0 : Subring (HahnSeries (CornerExp θ) k) where
  carrier := {x | InClass p 0 x}
  mul_mem' {x y} hx hy := by simpa using InClass.mul p hx hy
  one_mem' := inClass_one p
  add_mem' {x y} hx hy r hr := by
    rcases HahnSeries.support_add_subset x y hr with h | h
    · exact hx r h
    · exact hy r h
  zero_mem' r hr := by simp at hr
  neg_mem' {x} hx r hr := hx r (by rwa [HahnSeries.support_neg] at hr)

theorem mem_hahnK0 {x : HahnSeries (CornerExp θ) k} : x ∈ hahnK0 p ↔ InClass p 0 x := Iff.rfl

theorem classPart_of_inClass {c : ZMod p × ZMod p} {x : HahnSeries (CornerExp θ) k}
    (hx : InClass p c x) : classPart p c x = x := by
  ext r
  rw [coeff_classPart]
  split_ifs with h
  · rfl
  · by_contra h'
    exact h (hx r (Ne.symm h'))

theorem classPart0_eq_zero_of {x : HahnSeries (CornerExp θ) k}
    (hx : ∀ r ∈ x.support, classHom p r ≠ 0) : classPart0 p x = 0 := by
  ext r
  change (if classHom p r = 0 then x.coeff r else 0) = 0
  split_ifs with h
  · by_contra h'
    exact hx r h' h
  · rfl

theorem support_sub_classPart0 (x : HahnSeries (CornerExp θ) k) :
    ∀ r ∈ (x - classPart0 p x).support, classHom p r ≠ 0 := by
  intro r hr h
  apply hr
  change x.coeff r - (if classHom p r = 0 then x.coeff r else 0) = 0
  rw [ite_eq_left h, sub_self]

theorem sum_classPart [NeZero p] (x : HahnSeries (CornerExp θ) k) :
    ∑ c, classPart p c x = x := by
  ext r
  rw [HahnSeries.coeff_sum]
  simp only [coeff_classPart]
  rw [Finset.sum_ite_eq Finset.univ (classHom p r)]
  simp

/-- The facts 1 to 3 of the classes for the Hahn field. -/
theorem isClassPart_hahn {p : ℕ} [Fact p.Prime] [CharP k p] :
    IsClassPart p (hahnK0 p) (hahnCl p : HahnSeries (CornerExp θ) k →+ _) where
  pow_mem x := by
    rw [← sum_classPart p x, sum_pow_char]
    refine Subring.sum_mem _ fun c _ => ?_
    have h := (inClass_classPart p c x).pow p p
    have hc : p • c = 0 := by
      ext <;> simp
    rw [mem_hahnK0]
    rwa [hc] at h
  map_mul a ha x := by
    have hsplit : x = classPart0 p x + (x - classPart0 p x) := by abel
    have h0 : classPart0 p (a * (x - classPart0 p x)) = 0 := by
      apply classPart0_eq_zero_of
      intro r hr
      obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_add.mp (HahnSeries.support_mul_subset hr)
      rw [map_add, ha s hs, zero_add]
      exact support_sub_classPart0 p x t ht
    have h1 : classPart0 p (a * classPart0 p x) = a * classPart0 p x := by
      have := (InClass.mul p ha (inClass_classPart p 0 x))
      rw [zero_add] at this
      exact classPart_of_inClass p this
    rw [hahnCl_apply, hahnCl_apply]
    conv_lhs => rw [hsplit, mul_add, map_add, h0, h1]
    ring
  map_eq_zero a ha := by
    rw [hahnCl_apply]
    change a - classPart p 0 a = 0
    rw [classPart_of_inClass p ha, sub_self]
  sub_mem x := by
    rw [sub_hahnCl]
    exact inClass_classPart p 0 x

theorem support_classPart_subset (c : ZMod p × ZMod p) (x : HahnSeries (CornerExp θ) k) :
    (classPart p c x).support ⊆ x.support := by
  intro r hr h
  apply hr
  rw [coeff_classPart, h, ite_self]

/-- `v(x) ≤ v(x - cl x)`. -/
theorem hahnVal_le_sub_hahnCl (x : HahnSeries (CornerExp θ) k) :
    hahnVal θ k x ≤ hahnVal θ k (x - hahnCl p x) := by
  rw [sub_hahnCl]
  exact hahnVal_le_of_support_subset (support_classPart_subset p 0 x)

end Classes

/-! ### Corner runs in four variables -/

section CornerRun

variable {θ : ℝ}

/-- The exponents of `(y_m, z_m)` at `P_N`, for the word `w` (`true` for a `y`-step). -/
def expYZ (w : ℕ → Bool) : ℕ → CornerExp θ × CornerExp θ
  | 0 => (mk 1 0, mk 0 1)
  | m + 1 => if w m then ((expYZ w m).1, (expYZ w m).2 - (expYZ w m).1)
      else ((expYZ w m).1 - (expYZ w m).2, (expYZ w m).2)

/-- The exponent of `y_m`. -/
def expY (w : ℕ → Bool) (m : ℕ) : CornerExp θ := (expYZ w m).1

/-- The exponent of `z_m`. -/
def expZ (w : ℕ → Bool) (m : ℕ) : CornerExp θ := (expYZ w m).2

/-- The exponent of the chart variable `L_m`: `y_{m+1} = y_m` in a `y`-step and
`z_{m+1} = z_m` in a `z`-step. -/
def expL (w : ℕ → Bool) (m : ℕ) : CornerExp θ := if w m then expY w m else expZ w m

/-- The exponent of `M_m = L_N ⋯ L_{m-1}`. -/
def expM (w : ℕ → Bool) : ℕ → CornerExp θ
  | 0 => 0
  | m + 1 => expM w m + expL w m

theorem expY_succ (w : ℕ → Bool) (m : ℕ) :
    (expY w (m + 1) : CornerExp θ) = if w m then expY w m else expY w m - expZ w m := by
  simp only [expY, expZ, expYZ]
  split_ifs <;> rfl

theorem expZ_succ (w : ℕ → Bool) (m : ℕ) :
    (expZ w (m + 1) : CornerExp θ) = if w m then expZ w m - expY w m else expZ w m := by
  simp only [expY, expZ, expYZ]
  split_ifs <;> rfl

/-- `M_m = y_N z_N / (y_m z_m)`. -/
theorem expM_eq (w : ℕ → Bool) (m : ℕ) :
    (expM w m : CornerExp θ) = mk 1 1 - (expY w m + expZ w m) := by
  induction m with
  | zero => exact ext (by simp [expM, expY, expZ, expYZ]) (by simp [expM, expY, expZ, expYZ])
  | succ m ih =>
    rw [expM, ih, expY_succ, expZ_succ, expL]
    split_ifs <;> abel

/-- The word of a corner run: each chart occurs an infinite number of times, and `θ` is such
that `v(y_m) > 0` and `v(z_m) > 0` at each point (Lemma 3.13.24). -/
structure IsCornerWord (θ : ℝ) (w : ℕ → Bool) : Prop where
  frequently_y : ∃ᶠ m in atTop, w m = true
  frequently_z : ∃ᶠ m in atTop, w m = false
  pos_y : ∀ m, 0 < val θ (expY w m)
  pos_z : ∀ m, 0 < val θ (expZ w m)

variable {w : ℕ → Bool}

theorem IsCornerWord.pos_L (hw : IsCornerWord θ w) (m : ℕ) : 0 < val θ (expL w m) := by
  unfold expL
  split_ifs
  · exact hw.pos_y m
  · exact hw.pos_z m

/-- `v(M_m)` increases strictly. -/
theorem IsCornerWord.val_expM_lt (hw : IsCornerWord θ w) (m : ℕ) :
    val θ (expM w m) < val θ (expM w (m + 1)) := by
  rw [expM, val_add]
  linarith [hw.pos_L m]

theorem IsCornerWord.strictMono_expM (hw : IsCornerWord θ w) :
    StrictMono (expM w : ℕ → CornerExp θ) :=
  strictMono_nat_of_lt_succ fun m => lt_of_val_lt (hw.val_expM_lt m)

theorem IsCornerWord.strictMono_val_expM (hw : IsCornerWord θ w) :
    StrictMono (fun m => val θ (expM w m : CornerExp θ)) :=
  strictMono_nat_of_lt_succ hw.val_expM_lt

/-- Lemma 3.13.24: `v(y_m z_m) → 0`, so `v(M_m) → 1 + θ`. -/
theorem IsCornerWord.tendsto_val_expM (hw : IsCornerWord θ w) :
    Tendsto (fun m => val θ (expM w m : CornerExp θ)) atTop (𝓝 (1 + θ)) := by
  set s : ℕ → ℝ := fun m => val θ (expY w m : CornerExp θ) + val θ (expZ w m) with hs
  have hM : ∀ m, val θ (expM w m : CornerExp θ) = 1 + θ - s m := by
    intro m
    rw [expM_eq, val_sub, val_add]
    simp [val, hs]
  have hstep : ∀ m, s (m + 1) = s m - val θ (expL w m : CornerExp θ) := by
    intro m
    simp only [hs, expY_succ, expZ_succ, expL]
    split_ifs <;> simp only [val_sub] <;> ring
  have hanti : Antitone s := antitone_nat_of_succ_le fun m => by
    rw [hstep]
    linarith [hw.pos_L m]
  have hpos : ∀ m, 0 ≤ s m := fun m => by
    simp only [hs]
    linarith [hw.pos_y m, hw.pos_z m]
  -- `s` converges, so the steps `v(L_m)` tend to `0`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Tendsto s atTop (𝓝 ℓ) :=
    ⟨_, tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨m, rfl⟩; exact hpos m⟩⟩
  have hL : Tendsto (fun m => val θ (expL w m : CornerExp θ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun m => s m - s (m + 1)) atTop (𝓝 (ℓ - ℓ)) :=
      hℓ.sub (hℓ.comp (tendsto_add_atTop_nat 1))
    rw [sub_self] at h2
    refine h2.congr fun m => ?_
    rw [hstep]
    ring
  -- at a `y`-step followed by a `z`-step, `s` is less than twice the step
  have hswitch : ∀ m, w m = true → w (m + 1) = false →
      s (m + 1) < 2 * val θ (expL w m : CornerExp θ) := by
    intro m h1 h2
    have hz := hw.pos_y (m + 2)
    rw [expY_succ, h2] at hz
    simp only [Bool.false_eq_true, ite_false, val_sub] at hz
    have hy : (expY w (m + 1) : CornerExp θ) = expL w m := by
      rw [expY_succ, h1, expL, h1]
      rfl
    simp only [hs]
    rw [hy] at hz ⊢
    linarith
  have hfreq : ∃ᶠ m in atTop, w m = true ∧ w (m + 1) = false := by
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨b, hb, hwb⟩ := Filter.frequently_atTop.mp hw.frequently_y a
    obtain ⟨c, hc, hwc⟩ := Filter.frequently_atTop.mp hw.frequently_z b
    -- the last `y` before `c`
    have hex : ∃ n, b + n < c ∧ w (b + n) = true ∧ w (b + n + 1) = false := by
      by_contra hne
      push Not at hne
      have : ∀ n, b + n ≤ c → w (b + n) = true := by
        intro n
        induction n with
        | zero => intro _; simpa using hwb
        | succ n ih =>
          intro hn
          have h1 := ih (by omega)
          have h2 := hne n (by omega) h1
          rw [← add_assoc]
          simpa using h2
      have := this (c - b) (by omega)
      rw [show b + (c - b) = c by omega, hwc] at this
      exact Bool.false_ne_true this
    obtain ⟨n, -, h1, h2⟩ := hex
    exact ⟨b + n, by omega, h1, h2⟩
  have h0 : Tendsto s atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hL (ε / 2) (by linarith)
    obtain ⟨m, hm, h1, h2⟩ := Filter.frequently_atTop.mp hfreq N
    refine ⟨m + 1, fun n hn => ?_⟩
    have hLm := hN m hm
    rw [Real.dist_eq, sub_zero, abs_of_pos (hw.pos_L m)] at hLm
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpos n)]
    linarith [hanti hn, hswitch m h1 h2]
  have := (tendsto_const_nhds (x := 1 + θ)).sub h0
  rw [sub_zero] at this
  exact this.congr fun m => (hM m).symm

variable (θ) (k : Type*) [Field k]

/-- The monomial `M_m` in the Hahn field. -/
noncomputable def cornerM (w : ℕ → Bool) (m : ℕ) : HahnSeries (CornerExp θ) k :=
  HahnSeries.single (expM w m) 1

/-- The chart variable `L_m` in the Hahn field. -/
noncomputable def cornerL (w : ℕ → Bool) (m : ℕ) : HahnSeries (CornerExp θ) k :=
  HahnSeries.single (expL w m) 1

variable {θ k}

theorem cornerMono_cornerL (w : ℕ → Bool) (m : ℕ) :
    cornerMono (cornerL θ k w) m = cornerM θ k w m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [cornerMono, ih, cornerM, cornerM, cornerL, HahnSeries.single_mul_single, mul_one, expM]

theorem cornerM_ne_zero (w : ℕ → Bool) (m : ℕ) : cornerM θ k w m ≠ 0 :=
  HahnSeries.single_ne_zero one_ne_zero

theorem hahnVal_cornerM (w : ℕ → Bool) (m : ℕ) :
    hahnVal θ k (cornerM θ k w m) = ((val θ (expM w m) : ℝ) : WithTop ℝ) :=
  hahnVal_single one_ne_zero

/-- The point `Φ_m = Σ_{j < m} c_j M_{j+1}` of `cornerSum`, in coordinates. -/
theorem cornerSum_eq (w : ℕ → Bool) (c : ℕ → k) (m : ℕ) :
    cornerSum (cornerL θ k w) (fun j => HahnSeries.C (c j)) m =
      ∑ j ∈ Finset.range m, HahnSeries.single (expM w (j + 1)) (c j) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [cornerSum, ih, Finset.sum_range_succ, cornerMono_cornerL, cornerM,
      HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]

open Classical in
/-- The limit `Φ_∞ = Σ_j c_j M_{j+1}` in the Hahn field. The exponents of the `M_{j+1}` increase
strictly, so their set is well ordered. -/
noncomputable def cornerLimit (hw : IsCornerWord θ w) (c : ℕ → k) : HahnSeries (CornerExp θ) k where
  coeff r := if h : ∃ j, expM w (j + 1) = r then c (Classical.choose h) else 0
  isPWO_support' := by
    refine ((Set.isPWO_of_wellQuasiOrderedLE (Set.univ : Set ℕ)).image_of_monotone
      (f := fun j => (expM w (j + 1) : CornerExp θ))
      (fun i j hij => hw.strictMono_expM.monotone (Nat.succ_le_succ hij))).mono ?_
    intro r hr
    simp only [Function.mem_support, ne_eq, dite_eq_right_iff, not_forall] at hr
    obtain ⟨⟨j, hj⟩, -⟩ := hr
    exact ⟨j, Set.mem_univ _, hj⟩

open Classical in
theorem coeff_cornerLimit (hw : IsCornerWord θ w) (c : ℕ → k) (r : CornerExp θ) :
    (cornerLimit hw c).coeff r =
      if h : ∃ j, expM w (j + 1) = r then c (Classical.choose h) else 0 := by
  rfl

theorem coeff_cornerLimit_expM (hw : IsCornerWord θ w) (c : ℕ → k) (j : ℕ) :
    (cornerLimit hw c).coeff (expM w (j + 1)) = c j := by
  rw [coeff_cornerLimit, dite_eq_left ⟨j, rfl⟩]
  congr 1
  have h := Classical.choose_spec (⟨j, rfl⟩ : ∃ i, expM w (i + 1) = (expM w (j + 1) : CornerExp θ))
  exact Nat.succ_injective (hw.strictMono_expM.injective h)

theorem coeff_cornerLimit_of_notMem (hw : IsCornerWord θ w) (c : ℕ → k) {r : CornerExp θ}
    (hr : ∀ j, expM w (j + 1) ≠ r) : (cornerLimit hw c).coeff r = 0 := by
  rw [coeff_cornerLimit, dite_eq_right (by push Not; exact hr)]

/-- The tail `Δ_m = Φ_∞ - Φ_m` has only the terms `c_j M_{j+1}` with `j ≥ m`. -/
theorem support_cornerTail (hw : IsCornerWord θ w) (c : ℕ → k) (m : ℕ) :
    ∀ r ∈ (cornerLimit hw c - cornerSum (cornerL θ k w) (fun j => HahnSeries.C (c j)) m).support,
      ∃ j, m ≤ j ∧ expM w (j + 1) = r := by
  intro r hr
  rw [cornerSum_eq, HahnSeries.mem_support, HahnSeries.coeff_sub, HahnSeries.coeff_sum] at hr
  by_cases h : ∃ j, expM w (j + 1) = r
  · obtain ⟨j, rfl⟩ := h
    refine ⟨j, ?_, rfl⟩
    by_contra hj
    apply hr
    rw [coeff_cornerLimit_expM]
    simp only [HahnSeries.coeff_single]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [ite_eq_right]
      intro h'
      exact hij (Nat.succ_injective (hw.strictMono_expM.injective h'.symm))
    · intro hj'
      exact absurd (Finset.mem_range.mpr (by omega)) hj'
  · push Not at h
    exfalso
    apply hr
    rw [coeff_cornerLimit_of_notMem hw c h]
    simp only [HahnSeries.coeff_single]
    rw [Finset.sum_eq_zero]
    · simp
    · intro i _
      rw [ite_eq_right (h i).symm]

/-- The bound `v(Δ_m) ≥ v(M_{m+1})`. -/
theorem le_hahnVal_cornerTail (hw : IsCornerWord θ w) (c : ℕ → k) (m : ℕ) :
    ((val θ (expM w (m + 1)) : ℝ) : WithTop ℝ) ≤
      hahnVal θ k (cornerLimit hw c - cornerSum (cornerL θ k w) (fun j => HahnSeries.C (c j)) m) := by
  apply le_hahnVal_of_forall
  intro r hr
  obtain ⟨j, hj, rfl⟩ := support_cornerTail hw c m r hr
  exact hw.strictMono_val_expM.monotone (by omega)

end CornerRun

/-! ### Conjecture P for the corner runs -/

section ConjectureP

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {θ : ℝ} {k : Type*} [Field k]
  {w : ℕ → Bool}

/-- The point `Φ_m` of a corner run with the translations `t`. -/
noncomputable def cornerPoint (t : ℕ → σ → k) (m : ℕ) (l : σ) : HahnSeries (CornerExp θ) k :=
  cornerSum (cornerL θ k w) (fun j => HahnSeries.C (t j l)) m

/-- Theorem 3.19.6 (Conjecture P) for the corner runs of the Hahn model. The function of `P_m`
is `restart p cl Φ_m M_m g` with the classes `hahnCl p` of the Hahn field, its limit is
`Δ_m / M_m`, and `H^{(m)}_{e, i}` is its Hasse derivative of order `p^e e_i` at this limit. The
facts on the classes and the bound `v(Δ_m) ≥ v(M_{m+1})` are proved. The points `Φ_m` lie in a
subring `F` that contains the coefficients of `g`. The hypotheses are:

* `hD`: Theorem 3.18.26 for the nonzero derivatives of `g`.
* `hrun`: for each large `m`, Theorem 3.18.32, part 1, and Corollary 3.18.33 for the run from
  `P_m`, as in `conjectureP_of_restart_model`. -/
theorem conjectureP_cornerRun {p : ℕ} [hp : Fact p.Prime] [CharP k p] (hw : IsCornerWord θ w)
    (t : ℕ → σ → k) (F : Subring (HahnSeries (CornerExp θ) k))
    (hF : ∀ m l, cornerPoint (w := w) t m l ∈ F) (g : MvPolynomial σ F)
    (hD : ∀ kk, hasse kk g ≠ 0 → StatementDHolds (hahnVal θ k) F
      (fun m l => ⟨cornerPoint (w := w) t m l, hF m l⟩) (fun l => cornerLimit hw (fun j => t j l))
      (1 + θ) (hasse kk g))
    (μ : ℕ → WithTop ℝ)
    (hrun : ∀ᶠ m in atTop, ∃ e, 1 ≤ e ∧
      (∀ i, μ m + ((((p ^ e : ℕ) : ℝ) * (1 + θ - val θ (expM w m)) : ℝ) : WithTop ℝ) ≤
        hahnVal θ k (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (single i 1)
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map F.subtype g)))) +
          ((1 + θ - val θ (expM w m) : ℝ) : WithTop ℝ)) ∧
      ∃ i, eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map F.subtype g))) -
        hahnCl p (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map F.subtype g)))) ≠ 0 ∧
      hahnVal θ k (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map F.subtype g))) -
        hahnCl p (eval (fun l => (cornerLimit hw (fun j => t j l) - cornerPoint (w := w) t m l) /
            cornerM θ k w m) (hasse (single i (p ^ e))
          (restart p (hahnCl p) (fun l => cornerPoint (w := w) t m l) (cornerM θ k w m)
            (map F.subtype g))))) ≤ μ m) :
    False :=
  conjectureP_of_restart_model (K := HahnSeries (CornerExp θ) k) (v := hahnVal θ k) (F := F)
    (Φ := fun m l => ⟨cornerPoint (w := w) t m l, hF m l⟩)
    (Φi := fun l => cornerLimit hw (fun j => t j l)) hp.out g (fun m => val θ (expM w m))
    hw.tendsto_val_expM (cornerM θ k w) (hahnVal_cornerM w) (cornerM_ne_zero w) (hahnK0 p)
    (hahnCl p) isClassPart_hahn (hahnVal_le_sub_hahnCl p)
    (fun m l => le_hahnVal_cornerTail hw (fun j => t j l) m) hD μ hrun

end ConjectureP

end PlanarRuns

end Singularity
