/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.FrobeniusBasis
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.CharP.Algebra

/-!
# The Frobenius of a power series ring over a perfect field

This file proves Volume 1, Corollary 6.1.6 of the handbook in the following form. Let `K` be a perfect field of characteristic `p` and let `q = p ^ e`. The map `f ↦ f ^ q` is an isomorphism from `K[[x_1, ..., x_n]]` onto the subring `K[[x_1^q, ..., x_n^q]]` (`bijective_frobeniusToPowSubalgebra`). With Proposition 6.1.5 this shows that the `e`-th power of the Frobenius is finite and flat (`iterateFrobenius_finite_and_flat`).
-/

namespace Singularity.Algebra

open MvPowerSeries

variable {σ K : Type*} [Field K] (p : ℕ) [CharP K p]

/-- The ring `K[[x_1, ..., x_n]]` has characteristic `p` when `K` has characteristic `p`. -/
theorem charP_mvPowerSeries : CharP (MvPowerSeries σ K) p :=
  charP_of_injective_algebraMap (algebraMap K (MvPowerSeries σ K)).injective p

attribute [local instance] charP_mvPowerSeries

variable [Fact p.Prime]

/-- The power `f ↦ f ^ (p ^ e)` is injective on `K[[x_1, ..., x_n]]`. -/
theorem pow_injective (e : ℕ) :
    Function.Injective fun f : MvPowerSeries σ K => f ^ p ^ e := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  intro f g h
  simp only [← map_iterateFrobenius_expand p hp _ e] at h
  ext m
  have h' := congrArg (coeff (p ^ e • m)) h
  rw [coeff_map, coeff_map, coeff_expand_smul, coeff_expand_smul] at h'
  exact iterateFrobenius_inj K p e h'

/-- The power `f ^ (p ^ e)` of a power series is in `K[[x_1^q, ..., x_n^q]]`, where `q = p ^ e`. -/
theorem pow_mem_powSubalgebra (e : ℕ) (f : MvPowerSeries σ K) :
    f ^ p ^ e ∈ powSubalgebra σ K (p ^ e) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [mem_powSubalgebra]
  intro β hβ
  push Not at hβ
  obtain ⟨i, hi⟩ := hβ
  rw [← map_iterateFrobenius_expand p hp f e, coeff_map,
    coeff_expand_of_not_dvd (p ^ e) (pow_ne_zero e hp) f hi, map_zero]

/-- When `K` is perfect, each element of `K[[x_1^q, ..., x_n^q]]` is a power `f ^ q` with `q = p ^ e`. -/
theorem exists_pow_eq_of_mem_powSubalgebra [PerfectRing K p] (e : ℕ)
    {g : MvPowerSeries σ K} (hg : g ∈ powSubalgebra σ K (p ^ e)) :
    ∃ f : MvPowerSeries σ K, f ^ p ^ e = g := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let ψ := (iterateFrobeniusEquiv K p e).symm
  let f : MvPowerSeries σ K := fun m => ψ (coeff (p ^ e • m) g)
  refine ⟨f, ?_⟩
  rw [← map_iterateFrobenius_expand p hp f e]
  ext n
  rw [coeff_map]
  by_cases hn : ∀ i, p ^ e ∣ n i
  · let m : σ →₀ ℕ := n.mapRange (· / p ^ e) (by simp)
    have hm : p ^ e • m = n := by
      ext i
      simp [m, Nat.mul_div_cancel' (hn i)]
    rw [← hm, coeff_expand_smul]
    change iterateFrobenius K p e (ψ (coeff (p ^ e • m) g)) = _
    rw [← iterateFrobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  · rw [mem_powSubalgebra] at hg
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    rw [coeff_expand_of_not_dvd (p ^ e) (pow_ne_zero e hp) f hi, map_zero,
      hg n (fun h => hi (h i))]

variable (σ K)

/-- The `e`-th power of the Frobenius of `K[[x_1, ..., x_n]]`, with its values in `K[[x_1^q, ..., x_n^q]]`. -/
noncomputable def frobeniusToPowSubalgebra (e : ℕ) :
    MvPowerSeries σ K →+* powSubalgebra σ K (p ^ e) :=
  (iterateFrobenius (MvPowerSeries σ K) p e).codRestrict (powSubalgebra σ K (p ^ e))
    fun f => by rw [iterateFrobenius_def]; exact pow_mem_powSubalgebra p e f

theorem frobeniusToPowSubalgebra_apply (e : ℕ) (f : MvPowerSeries σ K) :
    (frobeniusToPowSubalgebra σ K p e f : MvPowerSeries σ K) = f ^ p ^ e := rfl

/-- When `K` is perfect, the `e`-th power of the Frobenius is an isomorphism from `K[[x_1, ..., x_n]]` onto `K[[x_1^q, ..., x_n^q]]`. -/
theorem bijective_frobeniusToPowSubalgebra [PerfectRing K p] (e : ℕ) :
    Function.Bijective (frobeniusToPowSubalgebra σ K p e) := by
  refine ⟨fun f g h => ?_, fun g => ?_⟩
  · have h' := congrArg Subtype.val h
    exact pow_injective p e h'
  · obtain ⟨f, hf⟩ := exists_pow_eq_of_mem_powSubalgebra p e g.2
    exact ⟨f, Subtype.ext hf⟩

theorem iterateFrobenius_eq_comp (e : ℕ) :
    iterateFrobenius (MvPowerSeries σ K) p e =
      (algebraMap (powSubalgebra σ K (p ^ e)) (MvPowerSeries σ K)).comp
        (frobeniusToPowSubalgebra σ K p e) := by
  ext f
  rfl

variable [Fintype σ] [DecidableEq σ]

/-- Volume 1, Corollary 6.1.6 of the handbook: when `K` is a perfect field of characteristic `p`, the `e`-th power of the Frobenius of `K[[x_1, ..., x_n]]` is finite and flat. -/
theorem iterateFrobenius_finite_and_flat [PerfectRing K p] (e : ℕ) :
    (iterateFrobenius (MvPowerSeries σ K) p e).Finite ∧
      (iterateFrobenius (MvPowerSeries σ K) p e).Flat := by
  have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hb := bijective_frobeniusToPowSubalgebra σ K p e
  have : Module.Free (powSubalgebra σ K (p ^ e)) (MvPowerSeries σ K) :=
    Module.Free.of_basis (boxBasis σ K hq)
  have : Module.Finite (powSubalgebra σ K (p ^ e)) (MvPowerSeries σ K) :=
    Module.Finite.of_basis (boxBasis σ K hq)
  rw [iterateFrobenius_eq_comp]
  refine ⟨RingHom.Finite.comp ?_ (RingHom.Finite.of_surjective _ hb.2), ?_⟩
  · exact RingHom.finite_algebraMap.mpr inferInstance
  · exact RingHom.Flat.comp (RingHom.Flat.of_bijective hb)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)

end Singularity.Algebra
