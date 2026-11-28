/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.RegularCenterTowers
import Singularity.Statements.Embedded
import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.Minpoly.Finite

/-!
# Weak log monomialization along a valuation

Let `k` be a field of characteristic `p > 0`, let `E` be an extension of `k` with `trdeg_k E = n`, and let `E'/E` be a purely inseparable extension of degree `p`. The hypothesis `RegularCenterInseparableStep p n k` of `Singularity/Valuation/RegularCenterTowers.lean` says that a regular centre of a valuation of `E` passes up to `E'`. This file splits that hypothesis in two smaller hypotheses. The first hypothesis is weak log monomialization along a valuation (`WeakLogMonomialization`). It makes an element `f` of the model monomial modulo `p`-th powers in the local ring at the centre. The second hypothesis is the monomial step (`MonomialInseparableStep`). It gives a regular centre on `E' = E(θ)` when `θ ^ p = f` and `f` is monomial modulo `p`-th powers. The text is in Volume 5, Chapter 4 of the handbook.

## Main definitions

* `Singularity.IsMonomialModPow`: an element of a local ring is monomial modulo `p`-th powers.
* `Singularity.WeakLogMonomialization`: weak log monomialization along a valuation. This is a hypothesis.
* `Singularity.MonomialInseparableStep`: the monomial step of degree `p`. This is a hypothesis.

## Main results

* `Singularity.exists_not_mem_range_of_finrank_eq_prime`: an extension of prime degree has an element outside the image of the base field.
* `Singularity.pow_mem_range_of_finrank_eq`: in a purely inseparable extension of degree `p`, each `p`-th power is in the image of the base field.
* `Singularity.exists_pow_eq_mem_subalgebra`: the generator `θ` can be chosen with `θ ^ p` in a given model.
* `Singularity.regularCenterInseparableStep_of_weakLogMonomialization`: the two hypotheses give `RegularCenterInseparableStep p n k` (Theorem B1).
* `Singularity.hasLocalUniformization_of_weakLogMonomialization`: the theorem of Temkin and the two hypotheses give local uniformization over a perfect field.

## The proof

Let `V = W ∩ E` have a regular centre on an affine model `A` of `E/k`. Choose `θ ∈ E'` with `θ ∉ E`. Then `θ ^ p ∈ E`. Write `θ ^ p = a / b` with `a, b ∈ A` and `b ≠ 0`. Replace `θ` by `b θ`. Then `θ ^ p = a b ^ (p - 1) = f` and `f ∈ A`. The element `f` is not a `p`-th power in `E`. If `f = g ^ p`, then `θ ^ p = g ^ p`, so `θ = g ∈ E`, because the Frobenius map of `E'` is injective. Weak log monomialization gives a larger model `A'` with a regular centre, on which `f` is monomial modulo `p`-th powers. The monomial step for `A'` and `θ` gives a regular centre of `W` on a model that contains the image of `A'`. This model contains the image of `A`.

## What is not proved

`WeakLogMonomialization` and `MonomialInseparableStep` are hypotheses. The library does not prove them. Weak log monomialization is open in transcendence degree 4. Volume 5, Chapter 4 of the handbook proves the monomial step by a toric argument. Lean has only the definition of the monomial step here. This file does not prove local uniformization in dimension 4.

## References

* [CP19] V. Cossart and O. Piltant, *Resolution of singularities of arithmetical threefolds*, J. Algebra 529 (2019).
* [Tem13] M. Temkin, *Inseparable local uniformization*, J. Algebra 373 (2013).
* Volume 5, Chapter 4 of the handbook.
-/

open IntermediateField Module

universe u v

namespace Singularity

section Monomial

/-- The element `f` of the local ring `R` is monomial modulo `p`-th powers. There are `h, g, u ∈ R`, a regular system of parameters `s` of `R` and exponents `a : R → ℕ` with `u` a unit, `g ≠ 0` and `f = h ^ p + g ^ p * (u * ∏ x ∈ s, x ^ a x)`. The form has one of two types. In the ramified type some exponent `a x` with `x ∈ s` is not divisible by `p`. In the residual type all exponents `a x` with `x ∈ s` are zero, and the class of `u` in the residue field is not a `p`-th power. The residual type does not occur if the residue field is perfect. -/
def IsMonomialModPow (p : ℕ) {R : Type*} [CommRing R] [IsLocalRing R] (f : R) : Prop :=
  ∃ (h g u : R) (s : Finset R) (a : R → ℕ), IsRegularSystemOfParameters s ∧ IsUnit u ∧ g ≠ 0 ∧
    f = h ^ p + g ^ p * (u * ∏ x ∈ s, x ^ a x) ∧
    ((∃ x ∈ s, ¬ p ∣ a x) ∨
      ((∀ x ∈ s, a x = 0) ∧ ∀ c : IsLocalRing.ResidueField R, c ^ p ≠ IsLocalRing.residue R u))

end Monomial

section Hypothesis

variable (p n : ℕ) (k : Type v) [Field k]

/-- **Weak log monomialization along a valuation**, for extensions of transcendence degree `n` over `k`. Let `E` be an extension of `k` with `trdeg_k E = n`, and let `V` be a valuation subring of `E`. Let `A ⊆ V` be an affine model of `E/k` such that the local ring `T_A` at the centre of `V` is regular. Let `f ∈ A` be an element that is not a `p`-th power in `E`. Then there is an affine model `A'` of `E/k` with `A ⊆ A' ⊆ V` such that `T_{A'}` is regular and `f` is monomial modulo `p`-th powers in `T_{A'}`.

This is an explicit hypothesis. The library does not prove it. It is open in transcendence degree 4. -/
def WeakLogMonomialization : Prop :=
  ∀ (E : Type u) [Field E] [Algebra k E], Algebra.trdeg k E = n →
    ∀ (V : ValuationSubring E) (A : Subalgebra k E), (∀ a ∈ A, a ∈ V) → IsAffineModel A →
      IsRegularLocalRing (centerSubring V A.toSubring) →
        ∀ f ∈ A, (¬ ∃ g : E, g ^ p = f) →
          ∃ A' : Subalgebra k E, A ≤ A' ∧ (∀ a ∈ A', a ∈ V) ∧ IsAffineModel A' ∧
            ∃ _ : IsRegularLocalRing (centerSubring V A'.toSubring),
              ∃ f' : centerSubring V A'.toSubring, (f' : E) = f ∧ IsMonomialModPow p f'

/-- **The monomial step of degree `p`**, for extensions of transcendence degree `n` over `k`. Let `E'/E` be a purely inseparable extension of degree `p`, where `E` is an extension of `k` with `trdeg_k E = n`. Let `W` be a valuation subring of `E'`, and let `A ⊆ W ∩ E` be an affine model of `E/k` such that the local ring `T_A` at the centre of `W ∩ E` is regular. Let `θ ∈ E'` with `θ ∉ E`, and let `f ∈ T_A` with `θ ^ p = f`. If `f` is monomial modulo `p`-th powers in `T_A`, then `W` has a regular centre on an affine model of `E'/k` that contains the image of `A`.

This is an explicit hypothesis. The library does not prove it. Volume 5, Chapter 4 of the handbook proves it by a toric argument. -/
def MonomialInseparableStep : Prop :=
  ∀ (E E' : Type u) [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E']
    [IsScalarTower k E E'], Algebra.trdeg k E = n → finrank E E' = p → IsPurelyInseparable E E' →
      ∀ (W : ValuationSubring E') (A : Subalgebra k E),
        (∀ a ∈ A, a ∈ W.comap (algebraMap E E')) → IsAffineModel A →
          ∀ _ : IsRegularLocalRing (centerSubring (W.comap (algebraMap E E')) A.toSubring),
            ∀ θ : E', θ ∉ Set.range (algebraMap E E') →
              ∀ f : centerSubring (W.comap (algebraMap E E')) A.toSubring,
                algebraMap E E' (f : E) = θ ^ p → IsMonomialModPow p f →
                  HasRegularCenter k W (algebraMap E E' '' (A : Set E))

end Hypothesis

section Extension

variable {E E' : Type*} [Field E] [Field E'] [Algebra E E']

/-- An extension `E'/E` of prime degree has an element `θ` outside the image of `E`. If each element is in the image, then `E' = E` and the degree is `1`, and `1` is not prime. -/
theorem exists_not_mem_range_of_finrank_eq_prime {p : ℕ} (hp : p.Prime)
    (hfin : finrank E E' = p) : ∃ θ : E', θ ∉ Set.range (algebraMap E E') := by
  by_contra! h
  have htop : (⊥ : Subalgebra E E') = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, rfl⟩ := h x
    exact Subalgebra.algebraMap_mem _ y
  rw [Subalgebra.bot_eq_top_iff_finrank_eq_one, hfin] at htop
  exact hp.one_lt.ne' htop

/-- **The `p`-th powers in a step of degree `p`.** Let `E'/E` be a purely inseparable extension of degree `p` in characteristic `p`, with `p` prime. Then `θ ^ p` is in the image of `E` for each `θ ∈ E'`. The minimal polynomial of `θ` is `X ^ p ^ m - y`, and its degree `p ^ m` is at most `p`, so `m ≤ 1`. -/
theorem pow_mem_range_of_finrank_eq {p : ℕ} [hp : Fact p.Prime] [CharP E p]
    [IsPurelyInseparable E E'] (hfin : finrank E E' = p) (θ : E') :
    θ ^ p ∈ Set.range (algebraMap E E') := by
  have : ExpChar E p := ExpChar.prime hp.out
  have : FiniteDimensional E E' := Module.finite_of_finrank_pos (by rw [hfin]; exact hp.out.pos)
  obtain ⟨m, y, hmy⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C E p θ
  have hdeg : (minpoly E θ).natDegree ≤ p := hfin ▸ minpoly.natDegree_le θ
  rw [hmy, Polynomial.natDegree_X_pow_sub_C] at hdeg
  have hroot : θ ^ p ^ m = algebraMap E E' y := by
    have h0 := minpoly.aeval E θ
    rw [hmy, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h0
    exact sub_eq_zero.1 h0
  have hm : m ≤ 1 := by
    by_contra! hm
    have : p ^ 2 ≤ p ^ m := Nat.pow_le_pow_right hp.out.pos hm
    have : p < p ^ 2 := by
      rw [pow_two]
      exact lt_mul_of_one_lt_left hp.out.pos hp.out.one_lt
    omega
  interval_cases m
  · refine ⟨y ^ p, ?_⟩
    rw [map_pow, ← hroot, pow_zero, pow_one]
  · exact ⟨y, by rw [← hroot, pow_one]⟩

/-- **The generator can be chosen with its `p`-th power in the model.** Let `A` be a subring of `E` with fraction field `E`, let `θ ∈ E'` with `θ ∉ E` and `θ ^ p = y ∈ E`, and let `p ≠ 0`. Write `y = a / b` with `a, b ∈ A` and `b ≠ 0`. Then `b θ ∉ E` and `(b θ) ^ p = a b ^ (p - 1)`, and this element is in `A`. -/
theorem exists_pow_eq_mem_subalgebra {k : Type*} [CommRing k] [Algebra k E] {p : ℕ} (hp : p ≠ 0)
    (A : Subalgebra k E) [IsFractionRing A E] {θ : E'} (hθ : θ ∉ Set.range (algebraMap E E'))
    {y : E} (hy : algebraMap E E' y = θ ^ p) :
    ∃ θ' : E', θ' ∉ Set.range (algebraMap E E') ∧ ∃ f ∈ A, algebraMap E E' f = θ' ^ p := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := A) y
  have hb0 : (b : E) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨algebraMap E E' b * θ, ?_, (a : E) * (b : E) ^ (p - 1), A.mul_mem a.2 (A.pow_mem b.2 _),
    ?_⟩
  · rintro ⟨z, hz⟩
    refine hθ ⟨z / b, ?_⟩
    have hb' : algebraMap E E' b ≠ 0 := (map_ne_zero _).2 hb0
    rw [map_div₀, hz, mul_div_cancel_left₀ _ hb']
  · have hy' : y = (a : E) / (b : E) := hab.symm
    rw [mul_pow, ← hy, ← map_pow, ← map_mul, hy']
    congr 1
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    rw [Nat.succ_sub_one, pow_succ]
    field_simp

/-- If `θ ∉ E` and `θ ^ p = f` in characteristic `p`, then `f` is not a `p`-th power in `E`. If `f = g ^ p`, then `θ ^ p = g ^ p` in `E'`, so `θ = g`, because the Frobenius map of the field `E'` is injective. -/
theorem not_exists_pow_eq_of_pow_eq {p : ℕ} [ExpChar E' p] {θ : E'}
    (hθ : θ ∉ Set.range (algebraMap E E')) {f : E} (hf : algebraMap E E' f = θ ^ p) :
    ¬ ∃ g : E, g ^ p = f := by
  rintro ⟨g, rfl⟩
  refine hθ ⟨g, frobenius_inj E' p ?_⟩
  rw [frobenius_def, frobenius_def, ← map_pow, hf]

end Extension

section Step

/-- **Weak log monomialization gives the step of degree p** (Volume 5, Chapter 4 of the handbook). Let `k` be a field of characteristic `p`. Assume `WeakLogMonomialization p n k` and `MonomialInseparableStep p n k`. These are explicit hypotheses that the library does not prove. Then `RegularCenterInseparableStep p n k` holds.

Let `A` be an affine model with a regular centre that contains `s`. Choose `θ ∉ E` with `θ ^ p = f ∈ A`. Then `f` is not a `p`-th power in `E`. Weak log monomialization gives a model `A' ⊇ A` on which `f` is monomial modulo `p`-th powers. The monomial step for `A'` and `θ` gives a regular centre of `W` that contains the image of `A'`, and so the image of `s`. -/
theorem regularCenterInseparableStep_of_weakLogMonomialization (p n : ℕ) [hp : Fact p.Prime]
    {k : Type v} [Field k] [CharP k p] (hweak : WeakLogMonomialization.{u} p n k)
    (hmono : MonomialInseparableStep.{u} p n k) : RegularCenterInseparableStep.{u} p n k := by
  intro E E' _ _ _ _ _ _ htr hfin hpi W s h
  obtain ⟨A, hAV, hA, hsA, hreg⟩ := (hasRegularCenter_iff_centerSubring _ _).1 h
  have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
  have : CharP E' p := charP_of_injective_algebraMap (algebraMap k E').injective p
  have : ExpChar E' p := ExpChar.prime hp.out
  obtain ⟨θ₀, hθ₀⟩ := exists_not_mem_range_of_finrank_eq_prime hp.out hfin
  obtain ⟨y, hy⟩ := pow_mem_range_of_finrank_eq hfin θ₀
  have : IsFractionRing A E := hA.2
  obtain ⟨θ, hθ, f, hfA, hf⟩ := exists_pow_eq_mem_subalgebra hp.out.ne_zero A hθ₀ hy
  obtain ⟨A', hAA', hA'V, hA', hreg', f', rfl, hmon⟩ :=
    hweak E htr _ A hAV hA hreg f hfA (not_exists_pow_eq_of_pow_eq hθ hf)
  refine (hmono E E' htr hfin hpi W A' hA'V hA' hreg' θ hθ f' hf hmon).mono ?_
  exact Set.image_mono fun x hx => hAA' (hsA hx)

/-- **Local uniformization over a perfect field from weak log monomialization.** Let `k` be a perfect field of characteristic `p`, let `K` be a function field over `k` with `trdeg_k K = n`, and let `V` be a valuation of `K/k`. Assume the theorem of Temkin (`localUniformization_inseparable`), `WeakLogMonomialization p n k` and `MonomialInseparableStep p n k`. These are explicit hypotheses that the library does not prove. Then `V` has local uniformization over `k`. -/
theorem hasLocalUniformization_of_weakLogMonomialization (p n : ℕ) [hp : Fact p.Prime]
    {k : Type u} [Field k] [CharP k p] [PerfectField k]
    (htem : localUniformization_inseparable.{u}) (hweak : WeakLogMonomialization.{u} p n k)
    (hmono : MonomialInseparableStep.{u} p n k)
    {K : Type u} [Field K] [Algebra k K] (hK : IsFunctionField k K)
    (htr : Algebra.trdeg k K = n) (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K] :
    HasLocalUniformization k V :=
  hasLocalUniformization_of_regularCenterInseparableStep p n htem
    (regularCenterInseparableStep_of_weakLogMonomialization p n hweak hmono) hK htr V

end Step

end Singularity
