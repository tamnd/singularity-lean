/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.DegreePTowers
import Singularity.Algebra.RegularIntegrallyClosed
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.Exponent

/-!
# Regular centres along purely inseparable towers

Let `k` be a perfect field of characteristic `p > 0`, let `K` be a function field over `k` with `trdeg_k K = n`, and let `V` be a valuation of `K/k`. This file reduces local uniformization of `V` to two explicit hypotheses. The first hypothesis is the theorem of Temkin [Tem13] (`localUniformization_inseparable`). It gives a finite purely inseparable extension `L` of `K` and an extension `W` of `V` to `L` with a regular centre on an affine model of `L/k`. The second hypothesis is `RegularCenterInseparableStep p n k`. It says that one regular centre passes up through one purely inseparable step of degree `p`.

Why a new step hypothesis. The hypothesis `LocalUniformizationInseparableStep` of `Singularity/Valuation/DegreePTowers.lean` says that local uniformization of `W ∩ E` gives local uniformization of `W`. The theorem of Temkin does not give local uniformization of a valuation of a smaller field. It gives one regular centre, on one model of `L`, that contains the image of a given finite set. So the two statements do not combine. The step of this file says that one regular centre below gives one regular centre above. This step combines with the theorem of Temkin, and the result is local uniformization over a perfect field. The text is in Volume 5 of the handbook.

## Main definitions

* `Singularity.RegularCenterInseparableStep`: the passage of one regular centre through one purely inseparable step of degree `p`. This is a hypothesis.

## Main results

* `Singularity.hasRegularCenter_iff_centerSubring`: a regular centre in terms of the subring `T_A` of `Singularity.centerSubring`.
* `Singularity.HasRegularCenter.mono`: a regular centre for a set is a regular centre for each subset.
* `Singularity.hasRegularCenter_union_of_mem_centerSubring` and `Singularity.HasRegularCenter.union_of_pow_mem`: a regular centre takes in a finite set of elements whose powers lie in the model.
* `Singularity.hasRegularCenter_of_isPurelyInseparable`: regular centres pass up a finite purely inseparable tower.
* `Singularity.exists_intermediateField_hasRegularCenter_of_isPurelyInseparable`: the Frobenius descent from `L` to a subfield `K₀` of `K`.
* `Singularity.hasLocalUniformization_of_regularCenterInseparableStep`: the theorem of Temkin and the step give local uniformization over a perfect field.

## The proof

Let `s ⊆ V` be finite. The theorem of Temkin gives `L` and `W` with a regular centre of `W` on an affine model of `L/k` that contains `s`. Let `p ^ N` be the exponent of `L/K`. The map `y ↦ y ^ p ^ N` sends `L` into `K`. Its image `K₀` is a subfield of `K`, and `L → K₀` is an isomorphism of rings. This isomorphism is not `k`-linear. But `k` is perfect, so each element of `k` is a `p ^ N`-th power, and the isomorphism maps the image of `k` onto the image of `k`. Thus it maps affine models of `L/k` to affine models of `K₀/k`, and it maps `W` to `V ∩ K₀`. This is the Frobenius descent. It gives a regular centre of `V ∩ K₀` that contains the elements `y ^ p ^ N` for `y ∈ s`.

The extension `K/K₀` is finite and purely inseparable, and `trdeg_k K₀ = n`. The step hypothesis, applied along a tower of steps of degree `p` from `K₀` to `K`, gives a regular centre of `V` on an affine model `A` of `K/k` that contains the elements `y ^ p ^ N`. The local ring `T_A` of `A` at the centre is regular, so it is integrally closed. It contains `y ^ p ^ N`, so it contains `y`. Then the model `k[A, s]` lies between `A` and `T_A`. It has the same local ring at the centre, and it contains `s`.

## What is not proved

The theorem of Temkin (`localUniformization_inseparable`) and the step (`RegularCenterInseparableStep`) are hypotheses. The library proves neither of them. For `n ≤ 3` the step follows from local uniformization in dimension at most 3 [CP19]. For `n = 4` the step is open. This file does not prove local uniformization in dimension 4.

## References

* [CP19] V. Cossart and O. Piltant, *Resolution of singularities of arithmetical threefolds*, J. Algebra 529 (2019).
* [Tem13] M. Temkin, *Inseparable local uniformization*, J. Algebra 373 (2013).
-/

open IntermediateField Module

universe u v

namespace Singularity

section Hypothesis

variable (p n : ℕ) (k : Type v) [Field k]

/-- The passage of one regular centre through one purely inseparable step of degree `p`, for extensions of transcendence degree `n` over `k`. Let `E'/E` be a purely inseparable extension of degree `p`, where `E` is an extension of `k` with `trdeg_k E = n`. Let `W` be a valuation subring of `E'`, and let `s` be a finite subset of `E`. If `W ∩ E` has a regular centre on an affine model of `E/k` that contains `s`, then `W` has a regular centre on an affine model of `E'/k` that contains the image of `s`.

This is an explicit hypothesis. The library does not prove it. For `n ≤ 3` it follows from local uniformization in dimension at most 3 [CP19]. For `n = 4` it is open. -/
def RegularCenterInseparableStep [CharP k p] : Prop :=
  ∀ (E E' : Type u) [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E']
    [IsScalarTower k E E'], Algebra.trdeg k E = n → finrank E E' = p → IsPurelyInseparable E E' →
      ∀ (W : ValuationSubring E') (s : Finset E),
        HasRegularCenter k (W.comap (algebraMap E E')) (s : Set E) →
          HasRegularCenter k W (algebraMap E E' '' (s : Set E))

end Hypothesis

section Center

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **A regular centre in terms of the ring `T_A`.** The valuation subring `V` has a regular centre on an affine model that contains `S` if and only if there is an affine model `A` with `S ⊆ A ⊆ V` such that the subring `T_A` of `Singularity.centerSubring` is a regular local ring. -/
theorem hasRegularCenter_iff_centerSubring (V : ValuationSubring K) (S : Set K) :
    HasRegularCenter k V S ↔ ∃ A : Subalgebra k K, (∀ a ∈ A, a ∈ V) ∧ IsAffineModel A ∧
      S ⊆ (A : Set K) ∧ IsRegularLocalRing (centerSubring V A.toSubring) := by
  constructor
  · rintro ⟨A, hA, hmod, hS, hreg⟩
    exact ⟨A, fun a ha => hA ⟨a, ha⟩, hmod, hS, (isRegularLocalRing_localization_iff A hA).1 hreg⟩
  · rintro ⟨A, hA, hmod, hS, hreg⟩
    exact ⟨A, fun a => hA a a.2, hmod, hS, (isRegularLocalRing_localization_iff A _).2 hreg⟩

/-- A regular centre on a model that contains `S` is also a regular centre on a model that contains each subset `S'` of `S`. -/
theorem HasRegularCenter.mono {V : ValuationSubring K} {S S' : Set K} (hS : S' ⊆ S)
    (h : HasRegularCenter k V S) : HasRegularCenter k V S' := by
  obtain ⟨A, hA, hmod, hSA, hreg⟩ := h
  exact ⟨A, hA, hmod, hS.trans hSA, hreg⟩

/-- If a subring `R` of `K` lies in `V`, then `T_R` lies in `V`. If `z c = a` with `a ∈ R` and `v(c) = 1`, then `v(z) = v(a) ≤ 1`. -/
private theorem mem_of_mem_centerSubring {V : ValuationSubring K} {R : Subring K}
    (hR : ∀ a ∈ R, a ∈ V) {z : K} (hz : z ∈ centerSubring V R) : z ∈ V := by
  obtain ⟨a, ha, c, hc, hc1, hzc⟩ := mem_centerSubring.mp hz
  rw [← V.valuation_le_one_iff]
  calc V.valuation z = V.valuation z * V.valuation c := by rw [hc1, mul_one]
    _ = V.valuation a := by rw [← map_mul, hzc]
    _ ≤ 1 := (V.valuation_le_one_iff a).2 (hR a ha)

/-- The subring `T_A` of `Singularity.centerSubring` for a `k`-subalgebra `A`, as a `k`-subalgebra of `K`. -/
private def centerSubalgebra (V : ValuationSubring K) (A : Subalgebra k K) : Subalgebra k K :=
  { centerSubring V A.toSubring with
    algebraMap_mem' := fun c => le_centerSubring A.toSubring (A.algebraMap_mem c) }

/-- **A regular centre takes in a finite subset of its local ring.** Let `A ⊆ V` be an affine model of `K/k` with `S ⊆ A` such that `T_A` is a regular local ring, and let `t` be a finite subset of `T_A`. Then `V` has a regular centre on an affine model that contains `S ∪ t`. The new model is `B = k[g, t]`, where `g` generates `A`. Then `A ⊆ B ⊆ T_A`, so `T_B = T_A`. -/
theorem hasRegularCenter_union_of_mem_centerSubring {V : ValuationSubring K} {S : Set K}
    {A : Subalgebra k K} (hAV : ∀ a ∈ A, a ∈ V) (hA : IsAffineModel A) (hSA : S ⊆ (A : Set K))
    (hreg : IsRegularLocalRing (centerSubring V A.toSubring)) (t : Finset K)
    (ht : ∀ x ∈ t, x ∈ centerSubring V A.toSubring) : HasRegularCenter k V (S ∪ t) := by
  classical
  obtain ⟨⟨g, hg⟩, hfrac⟩ := hA
  set B : Subalgebra k K := Algebra.adjoin k ((g ∪ t : Finset K) : Set K)
  have hAB : A ≤ B := by
    rw [← hg]
    exact Algebra.adjoin_mono (Finset.coe_subset.2 Finset.subset_union_left)
  have hBT : B ≤ centerSubalgebra V A := by
    refine Algebra.adjoin_le fun w hw => ?_
    rw [Finset.coe_union, Set.mem_union] at hw
    rcases hw with hw | hw
    · have hwA : w ∈ A := by
        rw [← hg]
        exact Algebra.subset_adjoin hw
      exact le_centerSubring A.toSubring hwA
    · exact ht w hw
  have hT : centerSubring V B.toSubring = centerSubring V A.toSubring :=
    le_antisymm (centerSubring_le fun z hz => hBT hz) (centerSubring_mono fun z hz => hAB hz)
  have hBV : ∀ b : B, (b : K) ∈ V := fun b => mem_of_mem_centerSubring hAV (hBT b.2)
  refine ⟨B, hBV, ⟨⟨g ∪ t, rfl⟩, ?_⟩, ?_, ?_⟩
  · refine IsFractionRing.of_field B K fun z => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    exact ⟨⟨a, hAB a.2⟩, ⟨b, hAB b.2⟩, rfl⟩
  · rintro z (hz | hz)
    · exact hAB (hSA hz)
    · refine Algebra.subset_adjoin ?_
      rw [Finset.coe_union]
      exact Set.mem_union_right _ hz
  · exact (isRegularLocalRing_localization_iff B hBV).2
      (IsRegularLocalRing.of_ringEquiv (RingEquiv.subringCongr hT.symm))

/-- If `A ⊆ V` is an affine model of `K/k`, then `K` is the fraction field of `T_A`, because `A ⊆ T_A ⊆ K`. -/
theorem isFractionRing_centerSubring {V : ValuationSubring K} {A : Subalgebra k K}
    (hA : IsFractionRing A K) : IsFractionRing (centerSubring V A.toSubring) K := by
  refine IsFractionRing.of_field _ K fun z => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
  exact ⟨⟨a, le_centerSubring A.toSubring a.2⟩, ⟨b, le_centerSubring A.toSubring b.2⟩, rfl⟩

/-- **A regular centre takes in the roots of its elements.** Let `V` have a regular centre on an affine model that contains `S`, and let `t` be a finite set such that each `x ∈ t` has a power `x ^ m ∈ S` with `m ≠ 0`. Then `V` has a regular centre on an affine model that contains `S ∪ t`. The local ring `T_A` at the centre is regular, so it is integrally closed. It contains `x ^ m`, so it contains `x`. -/
theorem HasRegularCenter.union_of_pow_mem {V : ValuationSubring K} {S : Set K}
    (h : HasRegularCenter k V S) (t : Finset K) (ht : ∀ x ∈ t, ∃ m : ℕ, m ≠ 0 ∧ x ^ m ∈ S) :
    HasRegularCenter k V (S ∪ t) := by
  obtain ⟨A, hAV, hA, hSA, hreg⟩ := (hasRegularCenter_iff_centerSubring V S).1 h
  refine hasRegularCenter_union_of_mem_centerSubring hAV hA hSA hreg t fun x hx => ?_
  obtain ⟨m, hm, hxm⟩ := ht x hx
  have : IsFractionRing (centerSubring V A.toSubring) K := isFractionRing_centerSubring hA.2
  have hmem : x ^ m ∈ (algebraMap (centerSubring V A.toSubring) K).range :=
    ⟨⟨x ^ m, le_centerSubring A.toSubring (hSA hxm)⟩, rfl⟩
  obtain ⟨y, hy⟩ := Algebra.mem_range_algebraMap_of_pow_mem hm hmem
  rw [← hy]
  exact y.2

end Center

section Towers

variable (p n : ℕ) [hp : Fact p.Prime] {k : Type v} [Field k] [CharP k p]

attribute [local instance] isScalarTower_intermediateField

/-- If `K → L` is bijective, a regular centre of `W ∩ K` that contains `S` gives a regular centre of `W` that contains the image of `S`. -/
private theorem hasRegularCenter_of_bot_eq_top {K L : Type*} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] (hbot : (⊥ : IntermediateField K L) = ⊤)
    (W : ValuationSubring L) {S : Set K} (h : HasRegularCenter k (W.comap (algebraMap K L)) S) :
    HasRegularCenter k W (algebraMap K L '' S) := by
  have hsurj : Function.Surjective (algebraMap K L) := fun x => by
    have hx : x ∈ (⊥ : IntermediateField K L) := hbot ▸ IntermediateField.mem_top
    exact IntermediateField.mem_bot.1 hx
  set e : K ≃ₐ[k] L := AlgEquiv.ofBijective (IsScalarTower.toAlgHom k K L)
    ⟨(algebraMap K L).injective, hsurj⟩
  have he : (e : K →+* L) = algebraMap K L := by
    ext x
    rfl
  rw [← he] at h
  exact h.map e

/-- **Regular centres along a purely inseparable tower.** Let `k` be a field of characteristic `p`, let `K` be an extension of `k` with `trdeg_k K = n`, and let `L/K` be a finite purely inseparable extension. Let `W` be a valuation subring of `L`, and let `s` be a finite subset of `K`. Assume `RegularCenterInseparableStep p n k` (an explicit hypothesis that the library does not prove). If `W ∩ K` has a regular centre on an affine model of `K/k` that contains `s`, then `W` has a regular centre on an affine model of `L/k` that contains the image of `s`. -/
theorem hasRegularCenter_of_isPurelyInseparable (hstep : RegularCenterInseparableStep.{u} p n k)
    {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hK : Algebra.trdeg k K = n) (W : ValuationSubring L) (s : Finset K)
    (h : HasRegularCenter k (W.comap (algebraMap K L)) (s : Set K)) :
    HasRegularCenter k W (algebraMap K L '' (s : Set K)) := by
  classical
  suffices H : ∀ d : ℕ, ∀ (K : Type u) [Field K] [Algebra k K] [Algebra K L]
      [IsScalarTower k K L] [FiniteDimensional K L] [IsPurelyInseparable K L], finrank K L = d →
        Algebra.trdeg k K = n → ∀ s : Finset K,
          HasRegularCenter k (W.comap (algebraMap K L)) (s : Set K) →
            HasRegularCenter k W (algebraMap K L '' (s : Set K)) from H _ K rfl hK s h
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K _ _ _ _ _ _ hd hK s h
  by_cases hbot : (⊥ : IntermediateField K L) = ⊤
  · exact hasRegularCenter_of_bot_eq_top hbot W h
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  obtain ⟨r, E, θ, hE0, hEr, hstepE⟩ := exists_purelyInseparable_tower_from (K := K) p W ⊥
  have hr : r ≠ 0 := by
    rintro rfl
    exact hbot (hE0.symm.trans hEr)
  set M := E 1
  have hM : finrank K M = p := by
    obtain ⟨-, -, -, hrel, -⟩ := hstepE 0 (by omega)
    rwa [hE0, relfinrank_bot_left] at hrel
  have hmul : finrank K M * finrank M L = finrank K L := Module.finrank_mul_finrank K M L
  have hpos : 0 < finrank M L := Module.finrank_pos
  have hlt : finrank M L < d := by
    rw [← hd, ← hmul, hM]
    exact lt_mul_of_one_lt_left hpos hp.out.one_lt
  have hMtr : Algebra.trdeg k M = n := by rw [trdeg_eq_of_finiteDimensional (K := K), hK]
  have hWM : HasRegularCenter k (W.comap (algebraMap M L)) (algebraMap K M '' (s : Set K)) := by
    refine hstep K M hK hM inferInstance _ s ?_
    rwa [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]
  rw [← Finset.coe_image] at hWM
  have h' := ih _ hlt M rfl hMtr _ hWM
  have hcomp : (fun x => algebraMap M L (algebraMap K M x)) = algebraMap K L :=
    funext fun x => (IsScalarTower.algebraMap_apply K M L x).symm
  rwa [Finset.coe_image, Set.image_image, hcomp] at h'

end Towers

section Frobenius

variable {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L]

/-- The image of a ring homomorphism `φ : L → K` as an intermediate field of `K/k`, when it contains the image of `k`. -/
private def imageField (φ : L →+* K) (hk : ∀ c : k, algebraMap k K c ∈ φ.fieldRange) :
    IntermediateField k K :=
  φ.fieldRange.toIntermediateField hk

omit [Algebra k L] [Algebra K L] [IsScalarTower k K L] in
/-- The elements of `imageField φ hk` are the values of `φ`. -/
private theorem mem_imageField {φ : L →+* K} {hk : ∀ c : k, algebraMap k K c ∈ φ.fieldRange}
    {x : K} : x ∈ imageField φ hk ↔ ∃ y, φ y = x :=
  RingHom.mem_fieldRange

/-- The ring isomorphism from `L` to the image of `φ`. It is not `k`-linear in general. -/
private noncomputable def imageEquiv (φ : L →+* K)
    (hk : ∀ c : k, algebraMap k K c ∈ φ.fieldRange) : L ≃+* imageField φ hk :=
  RingEquiv.ofBijective (φ.codRestrict (imageField φ hk) fun y => mem_imageField.2 ⟨y, rfl⟩)
    ⟨fun a b hab => φ.injective (congrArg Subtype.val hab), fun z => by
      obtain ⟨y, hy⟩ := mem_imageField.1 z.2
      exact ⟨y, Subtype.ext hy⟩⟩

/-- **Transport of a regular centre along a Frobenius map.** Let `φ : L → K` be a ring homomorphism with `φ(y) = y ^ q` in `L`, where `q ≠ 0` and each element of `k` is a `q`-th power in `k`. Let `K₀` be the image of `φ`, an intermediate field of `K/k`, and let `e : L → K₀` be the induced ring isomorphism. If `W` has a regular centre on an affine model of `L/k` that contains `S`, then `W ∩ K₀` has a regular centre on an affine model of `K₀/k` that contains `e(S)`. -/
private theorem hasRegularCenter_imageField (φ : L →+* K)
    (hk : ∀ c : k, algebraMap k K c ∈ φ.fieldRange) {q : ℕ} (hq : q ≠ 0)
    (hφ : ∀ y, algebraMap K L (φ y) = y ^ q) (hroot : ∀ c : k, ∃ d : k, d ^ q = c)
    {W : ValuationSubring L} {S : Set L} (h : HasRegularCenter k W S) :
    HasRegularCenter k ((W.comap (algebraMap K L)).comap (algebraMap (imageField φ hk) K))
      (imageEquiv φ hk '' S) := by
  classical
  set K₀ := imageField φ hk
  set e := imageEquiv φ hk
  set V₀ := (W.comap (algebraMap K L)).comap (algebraMap K₀ K)
  have hV₀ : V₀.comap e.toRingHom = W := by
    ext y
    change algebraMap K L (φ y) ∈ W ↔ y ∈ W
    rw [hφ, valuationSubring_pow_mem_iff W hq]
  have he : ∀ c : k, e (algebraMap k L c) = algebraMap k K₀ (c ^ q) := fun c => by
    apply Subtype.ext
    change φ (algebraMap k L c) = algebraMap k K (c ^ q)
    apply (algebraMap K L).injective
    rw [hφ, map_pow, map_pow, ← IsScalarTower.algebraMap_apply]
  obtain ⟨A, hAW, ⟨⟨g, hg⟩, hfrac⟩, hSA, hreg⟩ := h
  set A₀ : Subalgebra k K₀ := Algebra.adjoin k ((g.image e : Finset K₀) : Set K₀)
  have hR : ∀ c : k, algebraMap k K₀ c ∈ A.toSubring.map e.toRingHom := fun c => by
    obtain ⟨d, rfl⟩ := hroot c
    exact ⟨algebraMap k L d, A.algebraMap_mem d, he d⟩
  have h1 : A₀.toSubring ≤ A.toSubring.map e.toRingHom := by
    let RA : Subalgebra k K₀ := { A.toSubring.map e.toRingHom with algebraMap_mem' := hR }
    have hle : A₀ ≤ RA := by
      refine Algebra.adjoin_le fun z hz => ?_
      rw [Finset.coe_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxA : x ∈ A := by
        rw [← hg]
        exact Algebra.subset_adjoin hx
      exact ⟨x, hxA, rfl⟩
    exact fun z hz => hle hz
  have h2 : A.toSubring.map e.toRingHom ≤ A₀.toSubring := by
    let P : Subalgebra k L :=
      { A₀.toSubring.comap e.toRingHom with
        algebraMap_mem' := fun c => by
          change e (algebraMap k L c) ∈ A₀
          rw [he]
          exact A₀.algebraMap_mem _ }
    have hle : A ≤ P := by
      rw [← hg]
      refine Algebra.adjoin_le fun x hx => ?_
      change e x ∈ A₀
      exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_image_of_mem e hx))
    rintro _ ⟨y, hy, rfl⟩
    exact hle hy
  have hA₀ : A₀.toSubring = A.toSubring.map e.toRingHom := le_antisymm h1 h2
  have hA₀V : ∀ a : A₀, (a : K₀) ∈ V₀ := by
    rintro ⟨a, ha⟩
    obtain ⟨y, hy, rfl⟩ := h1 ha
    have hy' : y ∈ V₀.comap e.toRingHom := by
      rw [hV₀]
      exact hAW ⟨y, hy⟩
    exact hy'
  refine ⟨A₀, hA₀V, ⟨⟨g.image e, rfl⟩, ?_⟩, ?_, ?_⟩
  · refine IsFractionRing.of_field A₀ K₀ fun z => ?_
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := A) (e.symm z)
    refine ⟨⟨e a, h2 ⟨a, a.2, rfl⟩⟩, ⟨e b, h2 ⟨b, b.2, rfl⟩⟩, ?_⟩
    change z = e a / e b
    rw [← map_div₀]
    change z = e (algebraMap A L a / algebraMap A L b)
    rw [hab, RingEquiv.apply_symm_apply]
  · rintro _ ⟨y, hy, rfl⟩
    exact h2 ⟨y, hSA hy, rfl⟩
  · rw [isRegularLocalRing_localization_iff A hAW] at hreg
    rw [isRegularLocalRing_localization_iff A₀ hA₀V, hA₀, centerSubring_map, hV₀]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.subringMap e)

variable (p : ℕ) [hp : Fact p.Prime] [CharP k p] [PerfectField k] [FiniteDimensional K L]
  [IsPurelyInseparable K L]

open scoped Classical in
/-- **The Frobenius descent.** Let `k` be a perfect field of characteristic `p`, let `L/K` be a finite purely inseparable extension of extensions of `k`, and let `W` be a valuation subring of `L`. Let `s` be a finite subset of `K`, and assume that `W` has a regular centre on an affine model of `L/k` that contains the image of `s`. Then there are `N` and an intermediate field `K₀` of `K/k` with `x ^ p ^ N ∈ K₀` for each `x ∈ K`, such that `W ∩ K₀` has a regular centre on an affine model of `K₀/k` that contains the elements `y ^ p ^ N` for `y ∈ s`.

The field `K₀` is the image of the map `L → K`, `y ↦ y ^ p ^ N`, where `p ^ N` is the exponent of `L/K`. This map is an isomorphism of rings from `L` to `K₀`. It is not `k`-linear, but it maps the image of `k` onto the image of `k`, because `k` is perfect. So it maps affine models to affine models. -/
theorem exists_intermediateField_hasRegularCenter_of_isPurelyInseparable
    {W : ValuationSubring L} {s : Finset K}
    (h : HasRegularCenter k W (algebraMap K L '' (s : Set K))) :
    ∃ (N : ℕ) (K₀ : IntermediateField k K) (hK₀ : ∀ x : K, x ^ p ^ N ∈ K₀),
      HasRegularCenter k ((W.comap (algebraMap K L)).comap (algebraMap K₀ K))
        ((s.image fun y => (⟨y ^ p ^ N, hK₀ y⟩ : K₀)) : Set K₀) := by
  have : ExpChar k p := ExpChar.prime hp.out
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have : ExpChar K p := ExpChar.prime hp.out
  set N := IsPurelyInseparable.exponent K L
  set φ := IsPurelyInseparable.iterateFrobenius K L p (le_refl N)
  have hφ : ∀ y, algebraMap K L (φ y) = y ^ p ^ N :=
    IsPurelyInseparable.algebraMap_iterateFrobenius K p (le_refl N)
  have hφK : ∀ x, φ (algebraMap K L x) = x ^ p ^ N :=
    IsPurelyInseparable.iterateFrobenius_algebraMap L p (le_refl N)
  have hroot : ∀ c : k, ∃ d : k, d ^ p ^ N = c := fun c =>
    ⟨(iterateFrobeniusEquiv k p N).symm c, by
      rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]⟩
  have hk : ∀ c : k, algebraMap k K c ∈ φ.fieldRange := fun c => by
    obtain ⟨d, rfl⟩ := hroot c
    refine RingHom.mem_fieldRange.2 ⟨algebraMap k L d, ?_⟩
    apply (algebraMap K L).injective
    rw [hφ, map_pow, map_pow, ← IsScalarTower.algebraMap_apply]
  have hK₀ : ∀ x : K, x ^ p ^ N ∈ imageField φ hk := fun x =>
    mem_imageField.2 ⟨algebraMap K L x, hφK x⟩
  refine ⟨N, imageField φ hk, hK₀, ?_⟩
  refine (hasRegularCenter_imageField φ hk (pow_ne_zero _ hp.out.ne_zero) hφ hroot h).mono ?_
  intro z hz
  rw [Finset.coe_image] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨algebraMap K L y, ⟨y, hy, rfl⟩, Subtype.ext (hφK y)⟩

end Frobenius

section Reduction

/-- Let `K` be finitely generated over `k` as a field, and let `F` be an intermediate field of `K/k` such that `K/F` is integral. Then `K/F` is finite. -/
private theorem finiteDimensional_of_isFunctionField {k K : Type*} [Field k] [Field K]
    [Algebra k K] (hK : IsFunctionField k K) (F : IntermediateField k K)
    [Algebra.IsIntegral F K] : FiniteDimensional F K := by
  obtain ⟨t, ht⟩ := hK
  have htop : IntermediateField.adjoin F (t : Set K) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ IntermediateField.adjoin k (t : Set K) := ht ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin k (t : Set K) ≤
        (IntermediateField.adjoin F (t : Set K)).restrictScalars k :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin F (t : Set K))
    exact hle hx
  have : FiniteDimensional F (IntermediateField.adjoin F (t : Set K)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  rw [htop] at this
  exact Module.Finite.equiv IntermediateField.topEquiv.toLinearEquiv

/-- **Local uniformization over a perfect field from the theorem of Temkin.** Let `k` be a perfect field of characteristic `p`, let `K` be a function field over `k` with `trdeg_k K = n`, and let `V` be a valuation of `K/k`. Assume the theorem of Temkin (`localUniformization_inseparable`) and `RegularCenterInseparableStep p n k`. These are explicit hypotheses that the library does not prove. Then `V` has local uniformization over `k`.

Let `s ⊆ V` be finite. The theorem of Temkin gives a regular centre on a finite purely inseparable extension `L` of `K`. The Frobenius descent gives a regular centre of `V ∩ K₀` that contains the elements `y ^ q` for `y ∈ s`, where `K/K₀` is finite and purely inseparable. The tower gives a regular centre of `V` that contains these elements. Then the centre also takes in `s`, because a regular local ring is integrally closed. -/
theorem hasLocalUniformization_of_regularCenterInseparableStep (p n : ℕ) [hp : Fact p.Prime]
    {k : Type u} [Field k] [CharP k p] [PerfectField k]
    (htem : localUniformization_inseparable.{u}) (hstep : RegularCenterInseparableStep.{u} p n k)
    {K : Type u} [Field K] [Algebra k K] (hK : IsFunctionField k K)
    (htr : Algebra.trdeg k K = n) (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K] :
    HasLocalUniformization k V := by
  classical
  intro s hs
  obtain ⟨L, _, _, _, _, hfin, hpi, W, hWV, h⟩ := htem k K hK V s hs
  obtain ⟨N, K₀, hK₀, h₀⟩ := exists_intermediateField_hasRegularCenter_of_isPurelyInseparable p h
  rw [hWV] at h₀
  have : CharP K₀ p := charP_of_injective_algebraMap (algebraMap k K₀).injective p
  have : ExpChar K₀ p := ExpChar.prime hp.out
  have hpi₀ : IsPurelyInseparable K₀ K :=
    (isPurelyInseparable_iff_pow_mem K₀ p).2 fun x => ⟨N, ⟨⟨_, hK₀ x⟩, rfl⟩⟩
  have : FiniteDimensional K₀ K := finiteDimensional_of_isFunctionField hK K₀
  have htr₀ : Algebra.trdeg k K₀ = n := by
    rw [← trdeg_eq_of_finiteDimensional (K := K₀) (M := K), htr]
  have h₁ := hasRegularCenter_of_isPurelyInseparable p n hstep htr₀ V _ h₀
  have h₂ := h₁.union_of_pow_mem s fun x hx => ⟨p ^ N, pow_ne_zero _ hp.out.ne_zero, by
    rw [Finset.coe_image, Set.image_image]
    exact ⟨x, hx, rfl⟩⟩
  exact h₂.mono Set.subset_union_right

end Reduction

end Singularity
