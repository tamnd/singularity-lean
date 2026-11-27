/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.FrobeniusFlat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Power series over a finite extension, and the Frobenius of an F-finite field

This file proves Volume 1, Corollary 6.4.4 and Proposition 6.4.5 of the handbook when the field extension is finite.

Let `L → K` be a map of commutative rings such that `K` is a free `L`-module with a finite basis `b`. A power series over `K` has coefficients `c_α = ∑_i c_{α,i} b_i`, so it is `∑_i f_i b_i` with unique `f_i ∈ L[[x]]`. Thus `b` is a basis of `K[[x]]` over `L[[x]]` (`basisSeries`). In particular, `K[[x]]` is flat over `L[[x]]` when `[K : L]` is finite (`flat_mvPowerSeries_of_finiteDimensional`).

The Frobenius of `K[[x_1, ..., x_n]]` is `f ↦ map F (expand p f)`. The map `expand p` is finite and flat by Proposition 6.1.5 (`expand_finite_and_flat`), and `map F` is finite and flat when `K` is finite over `K^p`. So the Frobenius of `K[[x_1, ..., x_n]]` is finite and flat when `[K : K^p]` is finite (`frobenius_mvPowerSeries_finite_and_flat`).

The handbook proves Corollary 6.4.4 for each extension `L ⊆ K` with Lemma 6.4.3, a criterion of flatness modulo the powers of an ideal. That lemma, and so the case of an infinite extension, is not in Lean. Thus Proposition 6.4.5 for a field `K` with `[K : K^p]` infinite is not in Lean.

* `Singularity.Algebra.basisSeries`: a finite basis of `K` over `L` is a basis of `K[[x]]` over `L[[x]]`.
* `Singularity.Algebra.free_finite_mvPowerSeries`: if `K` is free and finite over `L`, then `K[[x]]` is free and finite over `L[[x]]`.
* `Singularity.Algebra.flat_mvPowerSeries_of_finiteDimensional`: Corollary 6.4.4 when `[K : L]` is finite.
* `Singularity.Algebra.map_finite_and_flat_of_finite`: for a finite map `φ` of a field to a ring, `map φ` is finite and flat.
* `Singularity.Algebra.expand_finite_and_flat`: `expand q` of `K[[x_1, ..., x_n]]` is finite and flat.
* `Singularity.Algebra.frobenius_mvPowerSeries_finite_and_flat`: Proposition 6.4.5 when `[K : K^p]` is finite.
-/

namespace Singularity.Algebra

open MvPowerSeries

section BaseChange

variable {σ L K ι : Type*} [CommRing L] [CommRing K] [Algebra L K] [Fintype ι]

theorem smul_mvPowerSeries_def (a : MvPowerSeries σ L) (f : MvPowerSeries σ K) :
    a • f = map (algebraMap L K) a * f := by
  rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply'']

/-- The coordinate of a power series over `K` along the `i`-th element of a basis of `K` over `L`, taken coefficient by coefficient. -/
noncomputable def basisCoordSeries (b : Module.Basis ι L K) (i : ι) (f : MvPowerSeries σ K) :
    MvPowerSeries σ L :=
  fun m => b.repr (coeff m f) i

omit [Fintype ι] in
theorem coeff_basisCoordSeries (b : Module.Basis ι L K) (i : ι) (f : MvPowerSeries σ K)
    (m : σ →₀ ℕ) : coeff m (basisCoordSeries b i f) = b.repr (coeff m f) i := rfl

/-- The power series over `K` with the coordinates `g i` along a basis of `K` over `L`. -/
noncomputable def basisSumSeries (b : Module.Basis ι L K) (g : ι → MvPowerSeries σ L) :
    MvPowerSeries σ K :=
  fun m => ∑ i, coeff m (g i) • b i

theorem coeff_basisSumSeries (b : Module.Basis ι L K) (g : ι → MvPowerSeries σ L)
    (m : σ →₀ ℕ) : coeff m (basisSumSeries b g) = ∑ i, coeff m (g i) • b i := rfl

/-- A basis of `K` over `L` gives a linear isomorphism of `K[[x]]` with `L[[x]]^ι`. -/
noncomputable def basisSeriesEquiv (b : Module.Basis ι L K) :
    MvPowerSeries σ K ≃ₗ[MvPowerSeries σ L] (ι → MvPowerSeries σ L) where
  toFun f i := basisCoordSeries b i f
  map_add' f g := by
    funext i
    ext m
    simp [coeff_basisCoordSeries]
  map_smul' a f := by
    classical
    funext i
    ext m
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, coeff_basisCoordSeries,
      smul_mvPowerSeries_def, coeff_mul, coeff_map, map_sum, Finsupp.coe_finsetSum,
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  invFun g := basisSumSeries b g
  left_inv f := by
    ext m
    rw [coeff_basisSumSeries]
    simp only [coeff_basisCoordSeries]
    exact b.sum_repr (coeff m f)
  right_inv g := by
    funext i
    ext m
    rw [coeff_basisCoordSeries, coeff_basisSumSeries, b.repr_sum_self]

/-- A finite basis of `K` over `L` is a basis of `K[[x]]` over `L[[x]]`. -/
noncomputable def basisSeries (b : Module.Basis ι L K) :
    Module.Basis ι (MvPowerSeries σ L) (MvPowerSeries σ K) :=
  Module.Basis.ofEquivFun (basisSeriesEquiv b)

variable (σ L K) in
/-- If `K` is free and finite over `L`, then `K[[x]]` is free and finite over `L[[x]]`. -/
theorem free_finite_mvPowerSeries [Module.Free L K] [Module.Finite L K] :
    Module.Free (MvPowerSeries σ L) (MvPowerSeries σ K) ∧
      Module.Finite (MvPowerSeries σ L) (MvPowerSeries σ K) := by
  let b := Module.Free.chooseBasis L K
  exact ⟨Module.Free.of_basis (basisSeries (σ := σ) b),
    Module.Finite.of_basis (basisSeries (σ := σ) b)⟩

variable (σ L K) in
/-- Volume 1, Corollary 6.4.4 of the handbook when `[K : L]` is finite: `K[[x]]` is a flat `L[[x]]`-module. -/
theorem flat_mvPowerSeries_of_finiteDimensional {L K : Type*} [Field L] [Field K] [Algebra L K]
    [FiniteDimensional L K] : Module.Flat (MvPowerSeries σ L) (MvPowerSeries σ K) := by
  have := (free_finite_mvPowerSeries σ L K).1
  infer_instance

end BaseChange

section RingHom

variable {σ L K : Type*}

/-- If `φ : L → K` is a finite map of a field to a ring, then `L[[x]] → K[[x]]` is finite and flat. -/
theorem map_finite_and_flat_of_finite [Field L] [CommRing K] (φ : L →+* K) (hφ : φ.Finite) :
    (MvPowerSeries.map (σ := σ) φ).Finite ∧ (MvPowerSeries.map (σ := σ) φ).Flat := by
  let := φ.toAlgebra
  have : Module.Finite L K := hφ
  obtain ⟨h1, h2⟩ := free_finite_mvPowerSeries σ L K
  have e : MvPowerSeries.map (σ := σ) φ = algebraMap (MvPowerSeries σ L) (MvPowerSeries σ K) :=
    rfl
  rw [e]
  exact ⟨RingHom.finite_algebraMap.mpr h2, RingHom.flat_algebraMap_iff.mpr inferInstance⟩

variable [CommRing K]

/-- The map `expand q` of `K[[x]]`, with its values in `K[[x_1^q, ..., x_n^q]]`. -/
noncomputable def expandToPowSubalgebra (q : ℕ) (hq : q ≠ 0) :
    MvPowerSeries σ K →+* powSubalgebra σ K q :=
  (expand q hq : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K).toRingHom.codRestrict
    (powSubalgebra σ K q) fun f => by
      rw [mem_powSubalgebra]
      intro β hβ
      push Not at hβ
      obtain ⟨i, hi⟩ := hβ
      exact coeff_expand_of_not_dvd q hq f hi

theorem bijective_expandToPowSubalgebra (q : ℕ) (hq : q ≠ 0) :
    Function.Bijective (expandToPowSubalgebra (σ := σ) (K := K) q hq) := by
  refine ⟨fun f g h => ?_, fun g => ?_⟩
  · have h' := congrArg Subtype.val h
    ext m
    have := congrArg (coeff (q • m)) h'
    simpa [expandToPowSubalgebra] using this
  · let f : MvPowerSeries σ K := fun m => coeff (q • m) (g : MvPowerSeries σ K)
    refine ⟨f, Subtype.ext ?_⟩
    change expand q hq f = (g : MvPowerSeries σ K)
    ext n
    by_cases hn : ∀ i, q ∣ n i
    · let m : σ →₀ ℕ := n.mapRange (· / q) (by simp)
      have hm : q • m = n := by
        ext i
        simp [m, Nat.mul_div_cancel' (hn i)]
      rw [← hm, coeff_expand_smul]
      rfl
    · have hg := g.2
      rw [mem_powSubalgebra] at hg
      push Not at hn
      obtain ⟨i, hi⟩ := hn
      rw [coeff_expand_of_not_dvd q hq f hi, hg n (fun h => hi (h i))]

variable [Fintype σ] [DecidableEq σ]

/-- The map `expand q` of `K[[x_1, ..., x_n]]` is finite and flat, by Proposition 6.1.5. -/
theorem expand_finite_and_flat (q : ℕ) (hq : q ≠ 0) :
    (expand q hq : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K).toRingHom.Finite ∧
      (expand q hq : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K).toRingHom.Flat := by
  have hq' : 0 < q := Nat.pos_of_ne_zero hq
  have hb := bijective_expandToPowSubalgebra (σ := σ) (K := K) q hq
  have : Module.Free (powSubalgebra σ K q) (MvPowerSeries σ K) :=
    Module.Free.of_basis (boxBasis σ K hq')
  have : Module.Finite (powSubalgebra σ K q) (MvPowerSeries σ K) :=
    Module.Finite.of_basis (boxBasis σ K hq')
  have e : (expand q hq : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K).toRingHom =
      (algebraMap (powSubalgebra σ K q) (MvPowerSeries σ K)).comp
        (expandToPowSubalgebra q hq) := by
    ext f
    rfl
  rw [e]
  refine ⟨RingHom.Finite.comp ?_ (RingHom.Finite.of_surjective _ hb.2), ?_⟩
  · exact RingHom.finite_algebraMap.mpr inferInstance
  · exact RingHom.Flat.comp (RingHom.Flat.of_bijective hb)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)

end RingHom

section Frobenius

variable (σ : Type*) {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

attribute [local instance] charP_mvPowerSeries

theorem frobenius_mvPowerSeries_eq_comp :
    frobenius (MvPowerSeries σ K) p =
      (MvPowerSeries.map (frobenius K p)).comp
        (expand p (Fact.out : p.Prime).ne_zero :
          MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K).toRingHom := by
  ext1 f
  rw [frobenius_def, RingHom.comp_apply]
  exact (map_frobenius_expand p (Fact.out : p.Prime).ne_zero).symm

variable [Fintype σ] [DecidableEq σ]

/-- Volume 1, Proposition 6.4.5 of the handbook when `[K : K^p]` is finite: the Frobenius of `K[[x_1, ..., x_n]]` is finite and flat. -/
theorem frobenius_mvPowerSeries_finite_and_flat (hK : (frobenius K p).Finite) :
    (frobenius (MvPowerSeries σ K) p).Finite ∧ (frobenius (MvPowerSeries σ K) p).Flat := by
  obtain ⟨h1, h2⟩ := expand_finite_and_flat (σ := σ) (K := K) p (Fact.out : p.Prime).ne_zero
  obtain ⟨h3, h4⟩ := map_finite_and_flat_of_finite (σ := σ) (frobenius K p) hK
  rw [frobenius_mvPowerSeries_eq_comp]
  exact ⟨h3.comp h1, RingHom.Flat.comp h2 h4⟩

end Frobenius

end Singularity.Algebra
