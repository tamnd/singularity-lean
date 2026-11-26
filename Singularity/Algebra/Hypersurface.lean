/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.Regular

/-!
# A hypersurface in a regular local ring

Let `(S, 𝔪)` be a regular local ring and let `f ∈ 𝔪` with `f ≠ 0`. This file proves that `dim S/(f) + 1 = dim S`, and that `S/(f)` is regular if and only if `f ∉ 𝔪²` (Volume 1, Proposition 1.2.10 of the handbook).

The ring `S` is a domain, so `f` is a nonzerodivisor, and the dimension drops by one. If `f ∉ 𝔪²`, then `S/(f)` is regular by `Singularity.Algebra.quotient_span_singleton`. If `f ∈ 𝔪²`, then the lifts of a set of generators of the maximal ideal of `S/(f)` generate `𝔪` by the lemma of Nakayama. So `𝔪` needs no more generators than the maximal ideal of `S/(f)`, and `S/(f)` is not regular.

## Main results

* `Singularity.Algebra.spanFinrank_maximalIdeal_le_spanFinrank_maximalIdeal_quotient_of_mem_sq`: if `x ∈ 𝔪²`, then the maximal ideal of `R/(x)` needs as many generators as `𝔪`.
* `Singularity.Algebra.isRegularLocalRing_quotient_iff`: Proposition 1.2.10 of Volume 1.
-/

open IsLocalRing Ideal

universe u

namespace Singularity.Algebra

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Let `R` be a Noetherian local ring and let `x ∈ 𝔪²`. Then the maximal ideal of `R/(x)` needs at least as many generators as `𝔪`. -/
theorem spanFinrank_maximalIdeal_le_spanFinrank_maximalIdeal_quotient_of_mem_sq {x : R}
    (hx : x ∈ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank := by
  classical
  obtain ⟨t, htcard, htspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (maximalIdeal (R ⧸ span {x})).fg_of_isNoetherianRing
  have htspan : span (t : Set (R ⧸ span {x})) = maximalIdeal (R ⧸ span {x}) := htspan
  set mk := Ideal.Quotient.mk (span {x}) with hmk
  set t' : Set R := Function.surjInv Ideal.Quotient.mk_surjective '' (t : Set (R ⧸ span {x}))
    with ht'
  have himg : mk '' t' = t := by
    rw [ht', ← Set.image_comp, Function.comp_surjInv, Set.image_id]
  have ht'fin : t'.Finite := t.finite_toSet.image _
  have hsub : span t' ≤ maximalIdeal R := by
    rw [Ideal.span_le]
    rintro y ⟨q, hq, rfl⟩
    have hmkq : mk (Function.surjInv Ideal.Quotient.mk_surjective q) = q :=
      Function.surjInv_eq _ _
    by_contra hnot
    have hu : IsUnit (Function.surjInv Ideal.Quotient.mk_surjective q) :=
      IsLocalRing.notMem_maximalIdeal.mp hnot
    have hqm : q ∈ maximalIdeal (R ⧸ span {x}) := htspan ▸ Ideal.subset_span hq
    exact IsLocalRing.notMem_maximalIdeal.mpr (hmkq ▸ hu.map mk) hqm
  have hle : maximalIdeal R ≤ span t' := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (maximalIdeal R).fg_of_isNoetherianRing
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro y hy
    have hy' : mk y ∈ span (mk '' t') := by
      rw [himg, htspan, maximalIdeal_quotient_eq_map]
      exact Ideal.mem_map_of_mem _ hy
    rw [← Ideal.map_span, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hy'
    obtain ⟨y', hy'mem, hyy'⟩ := hy'
    have hd : y - y' ∈ span {x} := Ideal.Quotient.eq.mp hyy'.symm
    have hd' : y - y' ∈ maximalIdeal R • maximalIdeal R := by
      rw [Ideal.smul_eq_mul, ← pow_two]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hx hd
    rw [show y = y' + (y - y') by ring]
    exact Submodule.add_mem_sup hy'mem hd'
  have heq : maximalIdeal R = span t' := le_antisymm hle hsub
  rw [heq]
  calc (span t').spanFinrank
      ≤ t'.ncard := Submodule.spanFinrank_span_le_ncard_of_finite ht'fin
    _ ≤ (t : Set (R ⧸ span {x})).ncard := Set.ncard_image_le t.finite_toSet
    _ = t.card := Set.ncard_coe_finset t
    _ = (maximalIdeal (R ⧸ span {x})).spanFinrank := htcard

/-- A hypersurface in a regular local ring (Volume 1, Proposition 1.2.10 of the handbook). Let `(S, 𝔪)` be a regular local ring and let `f ∈ 𝔪` with `f ≠ 0`. Then `dim S/(f) + 1 = dim S`, and `S/(f)` is regular if and only if `f ∉ 𝔪²`. -/
theorem isRegularLocalRing_quotient_iff (S : Type u) [CommRing S] [IsRegularLocalRing S]
    {f : S} (hm : f ∈ maximalIdeal S) (h0 : f ≠ 0) :
    ringKrullDim (S ⧸ span {f}) + 1 = ringKrullDim S ∧
      (IsRegularLocalRing (S ⧸ span {f}) ↔ f ∉ maximalIdeal S ^ 2) := by
  have : IsDomain S := isDomain_of_isRegularLocalRing S
  have hreg : f ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero h0
  have hdim : ringKrullDim (S ⧸ span {f}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hreg hm
  refine ⟨hdim, fun hQ h2 => ?_, fun h2 => (quotient_span_singleton hm h2).1⟩
  have hle := spanFinrank_maximalIdeal_le_spanFinrank_maximalIdeal_quotient_of_mem_sq h2
  have e1 : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) = ringKrullDim S :=
    IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)
  have e2 : ((maximalIdeal (S ⧸ span {f})).spanFinrank : WithBot ℕ∞) =
      ringKrullDim (S ⧸ span {f}) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal (R := S ⧸ span {f})
  obtain ⟨m, hm'⟩ := exists_ringKrullDim_eq_natCast (S ⧸ span {f})
  rw [hm'] at e2 hdim
  rw [← hdim] at e1
  have a1 : (maximalIdeal S).spanFinrank = m + 1 := by exact_mod_cast e1
  have a2 : (maximalIdeal (S ⧸ span {f})).spanFinrank = m := by exact_mod_cast e2
  omega

end Singularity.Algebra
