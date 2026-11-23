/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Data.ENat.Lattice

/-!
# The Hilbert-Samuel function and the order of an element

Let `R` be a commutative ring, let `I` be an ideal of `R` and let `M` be an `R`-module. The Hilbert-Samuel function of `M` with respect to `I` is the function `n ↦ ℓ(M / I^n M)`, where `ℓ` is the length. This file defines it with values in `ℕ∞` and proves its basic laws.

The order of an element `f` of `R` with respect to `I` is the largest `n` with `f ∈ I^n`, or `⊤` if `f` is in each power of `I`. When `R` is a regular local ring and `I` is the maximal ideal, the order of `f` is the multiplicity of the hypersurface `f = 0` at the closed point. This is the invariant that the classical proofs of resolution make smaller. The Samuel multiplicity of a general local ring is the normalized leading coefficient of the Hilbert-Samuel polynomial. That polynomial needs the theorem of Hilbert and Serre, which is not in this file.

## Main results

* `hilbertSamuel_zero`, `hilbertSamuel_succ`, `hilbertSamuel_mono`: the value at 0, the recursion `χ(n + 1) = χ(n) + ℓ(I^n M / I^(n+1) M)` and the monotony.
* `hilbertSamuel_anti`: a larger ideal gives a smaller function.
* `hilbertSamuel_ne_top`: if `R` is Noetherian, `M` is finite and `I` contains a power of a maximal ideal `m` with `I ≤ m`, then each value is finite.
* `hilbertSamuel_self_one`: `ℓ(R / m) = 1` for a maximal ideal `m`.
* `le_order_iff`, `order_add`, `order_mul`, `order_eq_top_iff`, `order_eq_zero_iff`: the laws of the order.
-/

universe u v

namespace Singularity.Algebra

open Module

section Length

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Let `N ≤ P` be submodules of `M`. Then `ℓ(M / N) = ℓ(P / N) + ℓ(M / P)`. -/
theorem length_quotient_eq_add {N P : Submodule R M} (h : N ≤ P) :
    length R (M ⧸ N) = length R (P ⧸ N.comap P.subtype) + length R (M ⧸ P) := by
  let f : (P ⧸ N.comap P.subtype) →ₗ[R] M ⧸ N := Submodule.mapQ _ _ P.subtype le_rfl
  let g : (M ⧸ N) →ₗ[R] M ⧸ P := Submodule.mapQ _ _ LinearMap.id h
  refine length_eq_add_of_exact f g ?_ ?_ ?_
  · intro x y hxy
    induction x using Submodule.Quotient.induction_on with | _ x => ?_
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy ⊢
    simpa [Submodule.mem_comap] using hxy
  · intro y
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hy
      exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, rfl⟩
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | _ x => ?_
      simp only [f, Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
      have : (x : M) - y ∈ P := h hx
      simpa using P.sub_mem x.2 this

/-- Let `m` be a maximal ideal of a Noetherian ring `R`, and let `Q` be a finite `R`-module with `m Q = 0`. Then `Q` has finite length. -/
theorem length_ne_top_of_smul_eq_bot [IsNoetherianRing R] (m : Ideal R) [m.IsMaximal]
    (Q : Type v) [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (hQ : m • (⊤ : Submodule R Q) = ⊥) : length R Q ≠ ⊤ := by
  have hT : Module.IsTorsionBySet R Q m := by
    intro x a
    have : (a : R) • x ∈ m • (⊤ : Submodule R Q) := Submodule.smul_mem_smul a.2 trivial
    rw [hQ] at this
    exact this
  let _ : Field (R ⧸ m) := Ideal.Quotient.field m
  let _ : Module (R ⧸ m) Q := hT.module
  have : IsScalarTower R (R ⧸ m) Q := hT.isScalarTower
  have : Module.Finite (R ⧸ m) Q := Module.Finite.of_restrictScalars_finite R (R ⧸ m) Q
  rw [length_eq_of_surjective (S := R) (R := R ⧸ m) (M := Q) Ideal.Quotient.mk_surjective,
    length_eq_finrank (R ⧸ m) Q]
  exact ENat.natCast_ne_top _

end Length

section HilbertSamuel

variable {R : Type u} [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-- The Hilbert-Samuel function `n ↦ ℓ(M / I^n M)` of `M` with respect to `I`. -/
noncomputable def hilbertSamuel (n : ℕ) : ℕ∞ :=
  length R (M ⧸ (I ^ n • ⊤ : Submodule R M))

theorem hilbertSamuel_zero : hilbertSamuel I M 0 = 0 := by
  rw [hilbertSamuel, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  exact length_eq_zero

/-- The recursion `χ(n + 1) = χ(n) + ℓ(I^n M / I^(n+1) M)`. -/
theorem hilbertSamuel_succ (n : ℕ) :
    hilbertSamuel I M (n + 1) = hilbertSamuel I M n +
      length R ((I ^ n • ⊤ : Submodule R M) ⧸
        (I ^ (n + 1) • ⊤ : Submodule R M).comap (I ^ n • ⊤ : Submodule R M).subtype) := by
  rw [hilbertSamuel, hilbertSamuel, length_quotient_eq_add, add_comm]
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)

theorem hilbertSamuel_mono : Monotone (hilbertSamuel I M) :=
  monotone_nat_of_le_succ fun n => by rw [hilbertSamuel_succ]; exact le_self_add

variable {I} in
/-- A larger ideal gives a smaller Hilbert-Samuel function. -/
theorem hilbertSamuel_anti {J : Ideal R} (h : I ≤ J) (n : ℕ) :
    hilbertSamuel J M n ≤ hilbertSamuel I M n :=
  length_le_of_surjective (Submodule.mapQ _ _ LinearMap.id
    (Submodule.smul_mono_left (Ideal.pow_right_mono h n))) (by
      intro y
      induction y using Submodule.Quotient.induction_on with | _ y => ?_
      exact ⟨Submodule.Quotient.mk y, rfl⟩)

variable {I} in
/-- If `J^k ≤ I`, then `χ_I(n) ≤ χ_J(k n)`. -/
theorem hilbertSamuel_le_of_pow_le {J : Ideal R} {k : ℕ} (h : J ^ k ≤ I) (n : ℕ) :
    hilbertSamuel I M n ≤ hilbertSamuel J M (k * n) := by
  rw [hilbertSamuel, hilbertSamuel, pow_mul]
  exact length_le_of_surjective (Submodule.mapQ _ _ LinearMap.id
    (Submodule.smul_mono_left (Ideal.pow_right_mono h n))) (by
      intro y
      induction y using Submodule.Quotient.induction_on with | _ y => ?_
      exact ⟨Submodule.Quotient.mk y, rfl⟩)

/-- Let `m` be a maximal ideal of a Noetherian ring and let `M` be a finite module. Then each value of the Hilbert-Samuel function of `M` with respect to `m` is finite. -/
theorem hilbertSamuel_ne_top_of_isMaximal [IsNoetherianRing R] [Module.Finite R M]
    (m : Ideal R) [m.IsMaximal] (n : ℕ) : hilbertSamuel m M n ≠ ⊤ := by
  induction n with
  | zero => rw [hilbertSamuel_zero]; exact ENat.zero_ne_top
  | succ n ih =>
    rw [hilbertSamuel_succ]
    refine WithTop.add_ne_top.mpr ⟨ih, length_ne_top_of_smul_eq_bot m _ ?_⟩
    rw [eq_bot_iff]
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      induction y using Submodule.Quotient.induction_on with | _ z => ?_
      rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, pow_succ',
        Submodule.mul_smul]
      exact Submodule.smul_mem_smul hr z.2
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb

/-- Let `m` be a maximal ideal of a Noetherian ring, let `M` be a finite module and let `I ≤ m` be an ideal that contains a power of `m`. Then each value of the Hilbert-Samuel function of `M` with respect to `I` is finite. -/
theorem hilbertSamuel_ne_top [IsNoetherianRing R] [Module.Finite R M] (m : Ideal R)
    [m.IsMaximal] {k : ℕ} (hk : m ^ k ≤ I) (n : ℕ) : hilbertSamuel I M n ≠ ⊤ :=
  ne_top_of_le_ne_top (hilbertSamuel_ne_top_of_isMaximal M m (k * n))
    (hilbertSamuel_le_of_pow_le M hk n)

/-- For a maximal ideal `m` of `R`, `ℓ(R / m) = 1`. -/
theorem hilbertSamuel_self_one (m : Ideal R) [m.IsMaximal] : hilbertSamuel m R 1 = 1 := by
  rw [hilbertSamuel, pow_one, Ideal.smul_eq_mul, Ideal.mul_top]
  have : IsSimpleModule R (R ⧸ m) := isSimpleModule_iff_isCoatom.mpr Ideal.IsMaximal.out
  exact length_eq_one R (R ⧸ m)

end HilbertSamuel

section Order

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The order of `f` with respect to `I`: the largest `n` with `f ∈ I^n`, or `⊤` if `f` is in each power of `I`. -/
noncomputable def order (f : R) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : f ∈ I ^ n), (n : ℕ∞)

variable {I}

theorem le_order_of_mem {f : R} {n : ℕ} (h : f ∈ I ^ n) : (n : ℕ∞) ≤ order I f :=
  le_iSup₂_of_le n h le_rfl

/-- The basic law of the order: `n ≤ ord_I(f)` if and only if `f ∈ I^n`. -/
theorem le_order_iff {f : R} {n : ℕ} : (n : ℕ∞) ≤ order I f ↔ f ∈ I ^ n := by
  refine ⟨fun h => ?_, le_order_of_mem⟩
  cases n with
  | zero => simp
  | succ n =>
    have hlt : (n : ℕ∞) < order I f :=
      lt_of_lt_of_le (by exact_mod_cast n.lt_succ_self) h
    obtain ⟨m, hm⟩ := lt_iSup_iff.mp hlt
    obtain ⟨hf, hnm⟩ := lt_iSup_iff.mp hm
    exact Ideal.pow_le_pow_right (by exact_mod_cast hnm) hf

theorem order_zero : order I 0 = ⊤ := by
  refine eq_top_iff.mpr (ENat.forall_natCast_le_iff_le.mp fun n _ => ?_)
  exact le_order_of_mem (Ideal.zero_mem _)

theorem order_eq_top_iff_forall {f : R} : order I f = ⊤ ↔ ∀ n : ℕ, f ∈ I ^ n := by
  refine ⟨fun h n => le_order_iff.mp (h ▸ le_top), fun h => ?_⟩
  exact eq_top_iff.mpr (ENat.forall_natCast_le_iff_le.mp fun n _ => le_order_of_mem (h n))

/-- By the intersection theorem of Krull, in a Noetherian local ring only `0` has order `⊤` with respect to a proper ideal. -/
theorem order_eq_top_iff [IsNoetherianRing R] [IsLocalRing R] (hI : I ≠ ⊤) {f : R} :
    order I f = ⊤ ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ order_zero⟩
  have hf : f ∈ ⨅ n : ℕ, I ^ n := Submodule.mem_iInf _ |>.mpr (order_eq_top_iff_forall.mp h)
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing I hI] at hf

theorem order_neg (f : R) : order I (-f) = order I f := by
  apply le_antisymm <;> refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_ <;>
    refine le_order_of_mem ?_
  · simpa using (I ^ n).neg_mem (le_order_iff.mp hn)
  · exact (I ^ n).neg_mem (le_order_iff.mp hn)

/-- The order of a sum is at least the smaller order. -/
theorem order_add (f g : R) : min (order I f) (order I g) ≤ order I (f + g) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => le_order_of_mem ?_
  exact Ideal.add_mem _ (le_order_iff.mp (hn.trans (min_le_left _ _)))
    (le_order_iff.mp (hn.trans (min_le_right _ _)))

/-- The order of a product is at least the sum of the orders. -/
theorem order_mul (f g : R) : order I f + order I g ≤ order I (f * g) := by
  rcases eq_top_or_lt_top (order I f) with hf | hf
  · rw [order_eq_top_iff_forall] at hf
    have : order I (f * g) = ⊤ := order_eq_top_iff_forall.mpr fun n => Ideal.mul_mem_right _ _ (hf n)
    rw [this]; exact le_top
  rcases eq_top_or_lt_top (order I g) with hg | hg
  · rw [order_eq_top_iff_forall] at hg
    have : order I (f * g) = ⊤ := order_eq_top_iff_forall.mpr fun n => Ideal.mul_mem_left _ _ (hg n)
    rw [this]; exact le_top
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hf.ne
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hg.ne
  rw [← ha, ← hb, ← Nat.cast_add]
  refine le_order_of_mem ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul (le_order_iff.mp ha.le) (le_order_iff.mp hb.le)

theorem order_one (hI : I ≠ ⊤) : order I 1 = 0 := by
  refine le_antisymm ?_ bot_le
  by_contra h
  have h1 : ((1 : ℕ) : ℕ∞) ≤ order I 1 := by
    rw [not_le] at h
    exact Order.one_le_iff_pos.mpr h
  rw [le_order_iff, pow_one] at h1
  exact hI ((Ideal.eq_top_iff_one I).mpr h1)

variable (I) in
/-- A smaller ideal gives a smaller order. -/
theorem order_mono {J : Ideal R} (h : I ≤ J) (f : R) : order I f ≤ order J f :=
  ENat.forall_natCast_le_iff_le.mp fun n hn =>
    le_order_of_mem (Ideal.pow_right_mono h n (le_order_iff.mp hn))

/-- In a local ring, the order of `f` with respect to the maximal ideal is `0` if and only if `f` is a unit. -/
theorem order_eq_zero_iff [IsLocalRing R] {f : R} :
    order (IsLocalRing.maximalIdeal R) f = 0 ↔ IsUnit f := by
  constructor
  · intro h
    by_contra hf
    have : ((1 : ℕ) : ℕ∞) ≤ order (IsLocalRing.maximalIdeal R) f :=
      le_order_of_mem (by rw [pow_one]; exact hf)
    rw [h] at this
    exact absurd this (by norm_num)
  · intro hf
    refine le_antisymm ?_ bot_le
    by_contra h
    rw [not_le] at h
    have h1 := le_order_iff.mp (Order.one_le_iff_pos.mpr h)
    rw [pow_one] at h1
    exact h1 hf

end Order

end Singularity.Algebra
