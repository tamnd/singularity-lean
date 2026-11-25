/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.DegreePSteps
import Singularity.Valuation.MonomialGroundField
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Local uniformization along towers of steps of degree p

Steps 3 and 4 of the reduction of Cossart-Piltant (Volume 6, Proposition 2.2.1 of the handbook, [CP19, Proposition 4.10]) carry local uniformization up a finite extension `L/K` one step of degree `p` at a time. In Step 3 the extension `L/K` is purely inseparable. In Step 4 the last part of the extension is a Galois extension whose group is a `p`-group. This file proves the induction on the degree. It takes the passage through one step of degree `p` as an explicit hypothesis. This hypothesis is Theorem 1.2.6 of Volume 6 [CP19, Theorem 1.5] together with the patching of [CP19, Section 4], and the library does not prove it.

Let `k` be a field of characteristic `p`, and let `K` be a function field over `k` of transcendence degree `n`.

(a) `LocalUniformizationInseparableStep p n k` is the hypothesis for one purely inseparable step: for each extension `E'/E` of degree `p` that is purely inseparable, with `trdeg_k E = n`, and for each valuation subring `W` of `E'`, local uniformization of `W ∩ E` over `k` implies local uniformization of `W` over `k`. `LocalUniformizationGaloisStep p n k` is the same hypothesis for Galois extensions of degree `p`. In characteristic `p` these are the Artin-Schreier extensions (`Singularity.exists_artinSchreier_generator`).

(b) `hasLocalUniformization_of_isPurelyInseparable`. Let `L/K` be a finite purely inseparable extension, and let `W` be a valuation subring of `L`. If `W ∩ K` has local uniformization, then `W` has local uniformization. The proof is an induction on `[L : K]`. The first step `K ⊆ E_1` of the tower of `Singularity.exists_purelyInseparable_tower_from` has degree `p`, and `L/E_1` is purely inseparable of smaller degree.

(c) `hasLocalUniformization_of_separableClosure`. Let `K/F` be a finite extension, and let `K_s` be the separable closure of `F` in `K`. Then `K/K_s` is purely inseparable, so local uniformization of `V ∩ K_s` gives local uniformization of `V`. This is Step 3 of the reduction.

(d) `hasLocalUniformization_of_isGalois`. Let `L/K` be a Galois extension of degree `p ^ r`, and let `W` be a valuation subring of `L`. If `W ∩ K` has local uniformization, then `W` has local uniformization. The Galois group `G` has order `p ^ r`. By the theorem of Sylow it has a subgroup `H` of order `p ^ (r - 1)`. The index of `H` is `p`, the smallest prime factor of `|G|`, so `H` is normal. The fixed field `M` of `H` is Galois over `K` of degree `p`, and `L/M` is Galois of degree `p ^ (r - 1)`. This is the induction of Proposition 2.1.4 of Volume 6, and it is the last part of Step 4 of the reduction.

(e) `HasLocalUniformization.of_algEquiv`: local uniformization is invariant under an isomorphism of `k`-algebras. The induction needs it for the step of degree 1.

## What is not proved

The hypotheses `LocalUniformizationInseparableStep` and `LocalUniformizationGaloisStep` are not proved. For `n = 3` they follow from Theorem 1.2.6 of Volume 6 [CP19, Theorem 1.5] and the patching [CP19, Propositions 4.4, 4.6 and 4.8], or directly from local uniformization in dimension 3 [CP08], [CP09]. The unramified and tame parts of Step 4 (the inertia and ramification fields of [ZS2, Chapter VI], [CP08, Theorem 8.1], [CP19, Proposition 4.13]) are not in this file. For `n = 4` the hypotheses are open.

## References

* [CP08] V. Cossart and O. Piltant, *Resolution of singularities of threefolds in positive characteristic I*, J. Algebra 320 (2008).
* [CP09] V. Cossart and O. Piltant, *Resolution of singularities of threefolds in positive characteristic II*, J. Algebra 321 (2009).
* [CP19] V. Cossart and O. Piltant, *Resolution of singularities of arithmetical threefolds*, J. Algebra 529 (2019).
* [ZS2] O. Zariski and P. Samuel, *Commutative Algebra*, Volume II.
-/

open IntermediateField Module

universe u v

namespace Singularity

section Transport

variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']

/-- An element `x` has value 1 for a valuation subring `V` if and only if `x ≠ 0`, `x ∈ V` and `x⁻¹ ∈ V`. -/
theorem valuation_eq_one_iff_mem (V : ValuationSubring K) (x : K) :
    V.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ V ∧ x⁻¹ ∈ V := by
  rw [← V.valuation_le_one_iff, ← V.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    refine ⟨fun h0 => ?_, h.le, by rw [h, inv_one]⟩
    rw [h0, map_zero] at h
    exact zero_ne_one h
  · rintro ⟨h0, h1, h2⟩
    have hpos : 0 < V.valuation x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0)
    exact le_antisymm h1 ((inv_le_one₀ hpos).1 h2)

/-- The value 1 is preserved by the inverse image of a valuation subring under a map of fields. -/
theorem valuation_comap_eq_one_iff (V : ValuationSubring K') (f : K →+* K') (x : K) :
    (V.comap f).valuation x = 1 ↔ V.valuation (f x) = 1 := by
  rw [valuation_eq_one_iff_mem, valuation_eq_one_iff_mem, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, map_inv₀, map_ne_zero]

/-- The subring `T_R` of `Singularity.centerSubring` commutes with an isomorphism of fields. -/
theorem centerSubring_map (e : K ≃+* K') (V' : ValuationSubring K') (R : Subring K) :
    centerSubring V' (R.map e.toRingHom) =
      (centerSubring (V'.comap e.toRingHom) R).map e.toRingHom := by
  ext z
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨c, hc, rfl⟩, hc1, hz⟩
    refine ⟨e.symm z, ⟨a, ha, c, hc, (valuation_comap_eq_one_iff V' _ c).2 hc1, ?_⟩, ?_⟩
    · apply e.injective
      rw [map_mul, RingEquiv.apply_symm_apply]
      exact hz
    · exact e.apply_symm_apply z
  · rintro ⟨y, ⟨a, ha, c, hc, hc1, hy⟩, rfl⟩
    refine ⟨e a, ⟨a, ha, rfl⟩, e c, ⟨c, hc, rfl⟩, (valuation_comap_eq_one_iff V' _ c).1 hc1, ?_⟩
    change e y * e c = e a
    rw [← map_mul, hy]

/-- A regular center moves along an isomorphism of `k`-algebras `e : K ≃ K'`: if `V'.comap e` has a regular center on an affine model of `K/k` that contains `S`, then `V'` has a regular center on an affine model of `K'/k` that contains `e(S)`. The new model is the image of the old one. -/
theorem HasRegularCenter.map (e : K ≃ₐ[k] K') {V' : ValuationSubring K'} {S : Set K}
    (h : HasRegularCenter k (V'.comap (e : K →+* K')) S) : HasRegularCenter k V' (e '' S) := by
  obtain ⟨A, hA, ⟨hfg, hfrac⟩, hS, hreg⟩ := h
  set A' : Subalgebra k K' := A.map (e : K →ₐ[k] K') with hA'def
  have hA' : ∀ a : A', (a : K') ∈ V' := by
    rintro ⟨_, a, ha, rfl⟩
    exact hA ⟨a, ha⟩
  refine ⟨A', hA', ⟨hfg.map _, ?_⟩, ?_, ?_⟩
  · refine IsFractionRing.of_field A' K' fun z => ?_
    obtain ⟨x, y, -, hz⟩ := IsFractionRing.div_surjective (A := A) (e.symm z)
    refine ⟨⟨e x, x, x.2, rfl⟩, ⟨e y, y, y.2, rfl⟩, ?_⟩
    change z = e x / e y
    rw [← map_div₀]
    change z = e ((algebraMap A K x) / (algebraMap A K y))
    rw [hz, AlgEquiv.apply_symm_apply]
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨s, hS hs, rfl⟩
  · rw [isRegularLocalRing_localization_iff A hA] at hreg
    rw [isRegularLocalRing_localization_iff A' hA']
    have hsub : A'.toSubring = A.toSubring.map e.toRingEquiv.toRingHom := by
      ext z
      rfl
    rw [hsub, centerSubring_map]
    have : IsRegularLocalRing (centerSubring (V'.comap e.toRingEquiv.toRingHom) A.toSubring) :=
      hreg
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.subringMap e.toRingEquiv)

/-- Local uniformization is invariant under an isomorphism of `k`-algebras `e : K ≃ K'`: if `V'.comap e` has local uniformization over `k`, then `V'` has local uniformization over `k`. -/
theorem HasLocalUniformization.of_algEquiv (e : K ≃ₐ[k] K') {V' : ValuationSubring K'}
    (h : HasLocalUniformization k (V'.comap (e : K →+* K'))) : HasLocalUniformization k V' := by
  classical
  intro s hs
  have hs' : ∀ x ∈ s.image e.symm, x ∈ V'.comap (e : K →+* K') := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [ValuationSubring.mem_comap]
    change e (e.symm y) ∈ V'
    rw [AlgEquiv.apply_symm_apply]
    exact hs y hy
  have h1 := (h _ hs').map e
  have h2 : (e '' ((s.image e.symm : Finset K) : Set K)) = (s : Set K') := by
    ext z
    simp
  rwa [h2] at h1

end Transport

section Trdeg

variable {k : Type*} [Field k]

/-- A finite extension does not change the transcendence degree: if `M/K` is finite, then `trdeg_k M = trdeg_k K`. -/
theorem trdeg_eq_of_finiteDimensional {K M : Type u} [Field K] [Field M] [Algebra k K] [Algebra k M]
    [Algebra K M] [IsScalarTower k K M] [FiniteDimensional K M] :
    Algebra.trdeg k M = Algebra.trdeg k K := by
  rw [← trdeg_add_eq k K (A := M), trdeg_eq_zero (R := K) (A := M), add_zero]

/-- The `k`-algebra structure of an intermediate field `M` of `L/K` is compatible with `L`. -/
theorem isScalarTower_intermediateField {K L : Type*} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] (M : IntermediateField K L) :
    IsScalarTower k M L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end Trdeg

section Hypotheses

variable (p n : ℕ) (k : Type v) [Field k]

/-- The passage of local uniformization through one purely inseparable step of degree `p`, for function fields of transcendence degree `n` over `k`. Let `E'/E` be a purely inseparable extension of degree `p`, where `E` is an extension of `k` with `trdeg_k E = n`, and let `W` be a valuation subring of `E'`. If `W ∩ E` has local uniformization over `k`, then `W` has local uniformization over `k`.

This is an explicit hypothesis. The library does not prove it. Such a step is `E' = E(θ)` with `θ ^ p ∈ E` (Lemma 2.1.2 of Volume 6 of the handbook), and by Lemma 2.2.2 one can take `θ ^ p` in a regular local ring at the center of `W ∩ E` (`Singularity.exists_inseparableStep_model`). For `n = 3`, Theorem 1.2.6 of Volume 6 [CP19, Theorem 1.5], case 1, gives local uniformization for the equation `X ^ p - θ ^ p`, and the patching of [CP19, Section 4] gives the hypothesis. -/
def LocalUniformizationInseparableStep [CharP k p] : Prop :=
  ∀ (E E' : Type u) [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E']
    [IsScalarTower k E E'], Algebra.trdeg k E = n → finrank E E' = p → IsPurelyInseparable E E' →
      ∀ W : ValuationSubring E', HasLocalUniformization k (W.comap (algebraMap E E')) →
        HasLocalUniformization k W

/-- The passage of local uniformization through one Galois step of degree `p`, for function fields of transcendence degree `n` over `k`. Let `E'/E` be a Galois extension of degree `p`, where `E` is an extension of `k` with `trdeg_k E = n`, and let `W` be a valuation subring of `E'`. If `W ∩ E` has local uniformization over `k`, then `W` has local uniformization over `k`.

This is an explicit hypothesis. The library does not prove it. In characteristic `p` such a step is an Artin-Schreier extension (`Singularity.exists_artinSchreier_generator`). For `n = 3`, Theorem 1.2.6 of Volume 6 [CP19, Theorem 1.5], case 2, together with the patching of [CP19, Section 4], gives the hypothesis. By [CP19, Remark 4.11] the deep theorem is needed only for the immediate steps. -/
def LocalUniformizationGaloisStep [CharP k p] : Prop :=
  ∀ (E E' : Type u) [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E']
    [IsScalarTower k E E'], Algebra.trdeg k E = n → finrank E E' = p → IsGalois E E' →
      ∀ W : ValuationSubring E', HasLocalUniformization k (W.comap (algebraMap E E')) →
        HasLocalUniformization k W

end Hypotheses

section GaloisTower

variable (p : ℕ) [hp : Fact p.Prime] {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The first step of the tower of Proposition 2.1.4 of Volume 6 of the handbook. Let `L/K` be a Galois extension of degree `p ^ (r + 1)`. Then there is an intermediate field `M` such that `M/K` is Galois of degree `p` and `[L : M] = p ^ r`. The Galois group has order `p ^ (r + 1)`. By the theorem of Sylow it has a subgroup `H` of order `p ^ r`. The index of `H` is `p`, the smallest prime factor of the order, so `H` is normal, and `M` is the fixed field of `H`. -/
theorem exists_isGalois_finrank_eq_prime [FiniteDimensional K L] [IsGalois K L] {r : ℕ}
    (hd : finrank K L = p ^ (r + 1)) :
    ∃ M : IntermediateField K L, IsGalois K M ∧ finrank K M = p ∧ finrank M L = p ^ r := by
  have hcard : Nat.card (L ≃ₐ[K] L) = p ^ (r + 1) := by
    rw [IsGalois.card_aut_eq_finrank, hd]
  have : Finite (L ≃ₐ[K] L) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ hp.out.ne_zero)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p
    (hcard ▸ pow_dvd_pow p (Nat.le_succ r) : p ^ r ∣ Nat.card (L ≃ₐ[K] L))
  have hindex : H.index = p := by
    have h := H.card_mul_index
    rw [hH, hcard, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos r) h
  have hminFac : (Nat.card (L ≃ₐ[K] L)).minFac = p := by
    rw [hcard]
    have hq := Nat.minFac_prime (Nat.one_lt_pow (Nat.succ_ne_zero r) hp.out.one_lt).ne'
    exact (Nat.prime_dvd_prime_iff_eq hq hp.out).1 (hq.dvd_of_dvd_pow (Nat.minFac_dvd _))
  have : H.Normal := Subgroup.normal_of_index_eq_minFac_card (hindex.trans hminFac.symm)
  have hML : finrank (IntermediateField.fixedField H) L = p ^ r := by
    rw [IntermediateField.finrank_fixedField_eq_card, hH]
  have hmul := Module.finrank_mul_finrank K (IntermediateField.fixedField H) L
  refine ⟨IntermediateField.fixedField H, inferInstance, ?_, hML⟩
  rw [hML, hd, pow_succ] at hmul
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos r) (hmul.trans (mul_comm _ _))

variable [CharP K p]

/-- Proposition 2.1.4 of Volume 6 of the handbook. Let `K` be a field of characteristic `p`, and let `L/K` be a Galois extension of degree `p ^ r`, so that its Galois group is a `p`-group. Then there is a tower `K = E_0 ⊆ E_1 ⊆ ... ⊆ E_r = L` of Artin-Schreier steps: `E_{i+1} = E_i(θ_i)` with `θ_i ∉ E_i`, `θ_i ^ p - θ_i ∈ E_i` and `[E_{i+1} : E_i] = p`.

The proof is an induction on `r`. The first step is the field `M` of `exists_isGalois_finrank_eq_prime`, with the Artin-Schreier generator of `exists_artinSchreier_generator`. The other steps come from the induction for `L/M`. -/
theorem exists_artinSchreier_tower [FiniteDimensional K L] [IsGalois K L] {r : ℕ}
    (hd : finrank K L = p ^ r) :
    ∃ (E : ℕ → IntermediateField K L) (θ : ℕ → L), E 0 = ⊥ ∧ E r = ⊤ ∧
      ∀ i < r, E (i + 1) = E i ⊔ K⟮θ i⟯ ∧ θ i ∉ E i ∧ θ i ^ p - θ i ∈ E i ∧
        (E i).relfinrank (E (i + 1)) = p := by
  induction r generalizing K with
  | zero =>
    refine ⟨fun _ => ⊥, fun _ => 0, rfl, ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    rw [eq_comm, ← IntermediateField.finrank_eq_one_iff, IntermediateField.finrank_top', hd,
      pow_zero]
  | succ r ih =>
    obtain ⟨M, hMgal, hM, hML⟩ := exists_isGalois_finrank_eq_prime p hd
    have : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
    obtain ⟨θ₀, hθ₀, hθ₀top, -⟩ := exists_artinSchreier_generator (K := K) (L := M) p hM
    obtain ⟨E', θ', hE'0, hE'r, hstep⟩ := ih (K := M) hML
    have hM1 : M = K⟮(θ₀ : L)⟯ := by
      rw [← lift_adjoin_simple, hθ₀top, lift_top]
    have hle : ∀ i, M ≤ (E' i).restrictScalars K := fun i x hx =>
      (E' i).algebraMap_mem ⟨x, hx⟩
    refine ⟨fun i => Nat.casesOn i ⊥ fun j => (E' j).restrictScalars K,
      fun i => Nat.casesOn i (θ₀ : L) θ', rfl, ?_, ?_⟩
    · change (E' r).restrictScalars K = ⊤
      rw [hE'r, restrictScalars_top]
    intro i hi
    cases i with
    | zero =>
      change (E' 0).restrictScalars K = ⊥ ⊔ K⟮(θ₀ : L)⟯ ∧ (θ₀ : L) ∉ (⊥ : IntermediateField K L) ∧
        (θ₀ : L) ^ p - θ₀ ∈ (⊥ : IntermediateField K L) ∧
          (⊥ : IntermediateField K L).relfinrank ((E' 0).restrictScalars K) = p
      rw [hE'0, restrictScalars_bot_eq_self, bot_sup_eq, relfinrank_bot_left, hM]
      refine ⟨hM1, fun h => ?_, ?_, rfl⟩
      · have hbot : M = ⊥ := by rw [hM1, adjoin_simple_eq_bot_iff.2 h]
        have h1 : finrank K M = 1 := by rw [hbot, IntermediateField.finrank_bot]
        exact hp.out.one_lt.ne' (hM ▸ h1)
      · obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hθ₀
        refine IntermediateField.mem_bot.2 ⟨a, ?_⟩
        have := congrArg (fun x : M => (x : L)) ha
        simpa using this
    | succ j =>
      obtain ⟨h1, h2, h3, h4⟩ := hstep j (by omega)
      change (E' (j + 1)).restrictScalars K = (E' j).restrictScalars K ⊔ K⟮θ' j⟯ ∧
        θ' j ∉ (E' j).restrictScalars K ∧ θ' j ^ p - θ' j ∈ (E' j).restrictScalars K ∧
          ((E' j).restrictScalars K).relfinrank ((E' (j + 1)).restrictScalars K) = p
      refine ⟨?_, h2, h3, h4⟩
      rw [h1, ← restrictScalars_sup, restrictScalars_adjoin_eq_sup, ← sup_assoc,
        sup_eq_left.2 (hle j)]

end GaloisTower

section Towers

variable (p n : ℕ) [hp : Fact p.Prime] {k : Type v} [Field k] [CharP k p]

attribute [local instance] isScalarTower_intermediateField

/-- If `K → L` is bijective, local uniformization of `W ∩ K` gives local uniformization of `W`. -/
theorem hasLocalUniformization_of_bot_eq_top {K L : Type*} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] (hbot : (⊥ : IntermediateField K L) = ⊤)
    (W : ValuationSubring L) (hW : HasLocalUniformization k (W.comap (algebraMap K L))) :
    HasLocalUniformization k W := by
  have hsurj : Function.Surjective (algebraMap K L) := fun x => by
    have hx : x ∈ (⊥ : IntermediateField K L) := hbot ▸ IntermediateField.mem_top
    exact IntermediateField.mem_bot.1 hx
  set e : K ≃ₐ[k] L := AlgEquiv.ofBijective (IsScalarTower.toAlgHom k K L)
    ⟨(algebraMap K L).injective, hsurj⟩
  have he : (e : K →+* L) = algebraMap K L := by
    ext x
    rfl
  refine HasLocalUniformization.of_algEquiv e ?_
  rwa [he]

/-- Step 3 of the reduction of Cossart-Piltant, the induction on the degree (Volume 6, Proposition 2.2.1 of the handbook). Let `k` be a field of characteristic `p`, let `K` be an extension of `k` with `trdeg_k K = n`, let `L/K` be a finite purely inseparable extension, and let `W` be a valuation subring of `L`. Assume that local uniformization passes through each purely inseparable step of degree `p` (`LocalUniformizationInseparableStep`, an explicit hypothesis that the library does not prove). If `W ∩ K` has local uniformization over `k`, then `W` has local uniformization over `k`. -/
theorem hasLocalUniformization_of_isPurelyInseparable
    (hstep : LocalUniformizationInseparableStep.{u} p n k) {K L : Type u} [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]
    [IsPurelyInseparable K L] (hK : Algebra.trdeg k K = n) (W : ValuationSubring L)
    (hW : HasLocalUniformization k (W.comap (algebraMap K L))) : HasLocalUniformization k W := by
  suffices h : ∀ d : ℕ, ∀ (K : Type u) [Field K] [Algebra k K] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional K L] [IsPurelyInseparable K L], finrank K L = d →
        Algebra.trdeg k K = n → HasLocalUniformization k (W.comap (algebraMap K L)) →
          HasLocalUniformization k W from h _ K rfl hK hW
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K _ _ _ _ _ _ hd hK hW
  by_cases hbot : (⊥ : IntermediateField K L) = ⊤
  · exact hasLocalUniformization_of_bot_eq_top hbot W hW
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
  have hWM : HasLocalUniformization k (W.comap (algebraMap M L)) := by
    refine hstep K M hK hM inferInstance _ ?_
    rwa [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]
  exact ih _ hlt M rfl hMtr hWM

/-- Step 3 of the reduction of Cossart-Piltant (Volume 6, Proposition 2.2.1 of the handbook). Let `K/F` be a finite extension of extensions of `k`, with `trdeg_k F = n`, and let `K_s` be the separable closure of `F` in `K`. Let `V` be a valuation subring of `K`. Assume `LocalUniformizationInseparableStep` (an explicit hypothesis that the library does not prove). If `V ∩ K_s` has local uniformization over `k`, then `V` has local uniformization over `k`, because `K/K_s` is purely inseparable. -/
theorem hasLocalUniformization_of_separableClosure
    (hstep : LocalUniformizationInseparableStep.{u} p n k) {F K : Type u} [Field F] [Field K]
    [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K]
    (hF : Algebra.trdeg k F = n) (V : ValuationSubring K)
    (hV : HasLocalUniformization k (V.comap (algebraMap (separableClosure F K) K))) :
    HasLocalUniformization k V := by
  have hs : Algebra.trdeg k (separableClosure F K) = n := by
    rw [trdeg_eq_of_finiteDimensional (K := F), hF]
  exact hasLocalUniformization_of_isPurelyInseparable p n hstep hs V hV

/-- The last part of Step 4 of the reduction of Cossart-Piltant (Volume 6, Proposition 2.2.1 and Proposition 2.1.4 of the handbook). Let `k` be a field of characteristic `p`, let `K` be an extension of `k` with `trdeg_k K = n`, let `L/K` be a Galois extension of degree `p ^ r`, and let `W` be a valuation subring of `L`. Assume that local uniformization passes through each Galois step of degree `p` (`LocalUniformizationGaloisStep`, an explicit hypothesis that the library does not prove). If `W ∩ K` has local uniformization over `k`, then `W` has local uniformization over `k`.

The Galois group has order `p ^ r`, so it has a normal subgroup `H` of index `p`. The fixed field `M` of `H` is Galois over `K` of degree `p`, and `L/M` is Galois of degree `p ^ (r - 1)`. -/
theorem hasLocalUniformization_of_isGalois
    (hstep : LocalUniformizationGaloisStep.{u} p n k) {K L : Type u} [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]
    [IsGalois K L] {r : ℕ} (hd : finrank K L = p ^ r) (hK : Algebra.trdeg k K = n)
    (W : ValuationSubring L) (hW : HasLocalUniformization k (W.comap (algebraMap K L))) :
    HasLocalUniformization k W := by
  induction r generalizing K with
  | zero =>
    refine hasLocalUniformization_of_bot_eq_top ?_ W hW
    rw [eq_comm, ← IntermediateField.finrank_eq_one_iff, IntermediateField.finrank_top', hd,
      pow_zero]
  | succ r ih =>
    obtain ⟨M, hMgal, hM, hML⟩ := exists_isGalois_finrank_eq_prime p hd
    have hMtr : Algebra.trdeg k M = n := by rw [trdeg_eq_of_finiteDimensional (K := K), hK]
    have hWM : HasLocalUniformization k (W.comap (algebraMap M L)) := by
      refine hstep K M hK hM inferInstance _ ?_
      rwa [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact ih hML hMtr hWM

end Towers

end Singularity
