/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.WeakLogMonomialization

/-!
# Foliated monomial elements and the step of degree p

Let `k` be a field of characteristic `p > 0`, and let `E` be an extension of `k`. The file `Singularity/Valuation/WeakLogMonomialization.lean` reduces the step of degree `p` to two hypotheses. The first hypothesis, weak log monomialization (`WeakLogMonomialization`), makes an element `f` monomial modulo `p`-th powers: `f = h ^ p + g ^ p * t` with `t` a unit times a monomial. This file replaces it by a weaker hypothesis. An element `f` of a local ring `R` with fraction field `E` is foliated monomial if `f` is in the subfield `E ^ p (t)` for an element `t ∈ R` of monomial type. The hypothesis `FoliatedLogMonomialization` asks for this weaker form. The field theory of this file shows that `E(f ^ (1 / p)) = E(t ^ (1 / p))`. So the monomial step for `t` gives the step of degree `p` for `f`. The text is in Definitions 2 and 3 and the Corollary after Theorem A of the note on the foliated criterion.

## Main definitions

* `Singularity.IsMonomialType`: an element of a local ring has monomial type (ramified type or residual type).
* `Singularity.IsFoliatedMonomial`: an element `f` of a local ring `R` is in `E ^ p (t)` for an element `t ∈ R` of monomial type, where `E` is a field with a map from `R`.
* `Singularity.FoliatedLogMonomialization`: foliated log monomialization along a valuation. This is a hypothesis.

## Main results

* `Singularity.IsMonomialType.isMonomialModPow`: an element of monomial type is monomial modulo `p`-th powers, with `h = 0` and `g = 1`.
* `Singularity.IsMonomialModPow.isFoliatedMonomial`: an element that is monomial modulo `p`-th powers is foliated monomial.
* `Singularity.exists_eq_sum_of_eq_sum`: if `f ∈ E ^ p (t)` and `f ∉ E ^ p`, then `t ∈ E ^ p (f)`.
* `Singularity.adjoin_eq_adjoin_of_eq_sum`: then `E(θ) = E(θ')` in each extension of `E` when `θ ^ p = f` and `θ' ^ p = t`.
* `Singularity.foliatedLogMonomialization_of_weakLogMonomialization`: weak log monomialization gives foliated log monomialization.
* `Singularity.regularCenterInseparableStep_of_foliatedLogMonomialization`: foliated log monomialization and the monomial step give `RegularCenterInseparableStep p n k`.
* `Singularity.hasLocalUniformization_of_foliatedLogMonomialization`: the theorem of Temkin, foliated log monomialization and the monomial step give local uniformization over a perfect field.

## The proof

Let `F = E ^ p` be the image of the Frobenius map of `E`. This is a subfield of `E`. Let `x ∈ E` with `x ∉ F`. Then `x ^ p ∈ F`, and `x ^ p` is not a `p`-th power in `F`, because the Frobenius map of `E` is injective. So `X ^ p - x ^ p` is irreducible over `F`, it is the minimal polynomial of `x`, and `[F(x) : F] = p`. Let `f = Σ_{i < p} c_i ^ p t ^ i` with `f ∉ F`. Then `t ∉ F`, because `t = s ^ p` gives `f = (Σ c_i s ^ i) ^ p`. So `F(f) ⊆ F(t)` and both have degree `p` over `F`. Thus `F(f) = F(t)` and `t ∈ F[f]`. Write `t = q(f)` with `q ∈ F[X]`, and divide `q` by `X ^ p - f ^ p`. The remainder has degree less than `p` and gives `t = Σ_{i < p} d_i ^ p f ^ i`. In an extension `E'` of `E` with `θ ^ p = f`, the element `θ' = Σ d_i θ ^ i` has `θ' ^ p = t`. In the same way `Σ c_i θ' ^ i` is a `p`-th root of `f`. A `p`-th root is unique in characteristic `p`, so `E(θ) = E(θ')`.

For the step of degree `p`, choose `θ ∉ E` with `θ ^ p = f` in a model `A` as in `regularCenterInseparableStep_of_weakLogMonomialization`. Foliated log monomialization gives a model `A' ⊇ A` and `t` of monomial type in the local ring `T_{A'}` at the centre with `f ∈ E ^ p (t)`. The field theory gives `θ' ∈ E'` with `θ' ^ p = t`, and `θ' ∉ E` because `t` is not a `p`-th power in `E`. The element `t` is monomial modulo `p`-th powers in `T_{A'}`. So the hypothesis `MonomialInseparableStep` of `WeakLogMonomialization.lean` applies to `A'`, `θ'` and `t`, with no change. The element `t` is in `T_{A'}`, and the monomial step asks only for this, so the model does not change.

## What is not proved

`FoliatedLogMonomialization` and `MonomialInseparableStep` are hypotheses. The library does not prove them. Foliated log monomialization is weaker than weak log monomialization, but it is also open in transcendence degree 4. Theorem A of the note (a principal log Jacobian ideal gives a foliated monomial element) is not in Lean. The residual type of `IsMonomialType` has the same shape as in `IsMonomialModPow`: `t = u * ∏ x ∈ s, x ^ a x` with all `a x = 0`. In a regular local ring this is the same as "`t` is a unit with a class that is not a `p`-th power" (`IsMonomialType.of_isUnit` and `IsMonomialType.isUnit_of_residual`). This file does not prove local uniformization in dimension 4.

## References

* [CP19] V. Cossart and O. Piltant, *Resolution of singularities of arithmetical threefolds*, J. Algebra 529 (2019).
* [Tem13] M. Temkin, *Inseparable local uniformization*, J. Algebra 373 (2013).
* The note on the foliated criterion, Definitions 2 and 3 and the Corollary after Theorem A.
* Volume 5, Chapter 4 of the handbook.
-/
open IntermediateField Module Polynomial

universe u v

namespace Singularity

section Monomial

/-- The element `t` of the local ring `R` has monomial type. There are a unit `u`, a regular system of parameters `s` of `R` and exponents `a : R → ℕ` with `t = u * ∏ x ∈ s, x ^ a x`. The form has one of two types, as in `IsMonomialModPow`. In the ramified type some exponent `a x` with `x ∈ s` is not divisible by `p`. In the residual type all exponents `a x` with `x ∈ s` are zero, so `t = u` is a unit, and the class of `u` in the residue field is not a `p`-th power. -/
def IsMonomialType (p : ℕ) {R : Type*} [CommRing R] [IsLocalRing R] (t : R) : Prop :=
  ∃ (u : R) (s : Finset R) (a : R → ℕ), IsRegularSystemOfParameters s ∧ IsUnit u ∧
    t = u * ∏ x ∈ s, x ^ a x ∧
    ((∃ x ∈ s, ¬ p ∣ a x) ∨
      ((∀ x ∈ s, a x = 0) ∧ ∀ c : IsLocalRing.ResidueField R, c ^ p ≠ IsLocalRing.residue R u))

/-- **The residual type is a unit.** If `t = u * ∏ x ∈ s, x ^ a x` with `u` a unit and all exponents `a x` with `x ∈ s` equal to zero, then `t = u` and `t` is a unit. -/
theorem IsMonomialType.isUnit_of_residual {R : Type*} [CommRing R] [IsLocalRing R]
    {t u : R} {s : Finset R} {a : R → ℕ} (hu : IsUnit u) (ht : t = u * ∏ x ∈ s, x ^ a x)
    (ha : ∀ x ∈ s, a x = 0) : t = u ∧ IsUnit t := by
  have : ∏ x ∈ s, x ^ a x = 1 := Finset.prod_eq_one fun x hx => by rw [ha x hx, pow_zero]
  rw [this, mul_one] at ht
  exact ⟨ht, ht ▸ hu⟩

/-- **A unit with a class that is not a `p`-th power has monomial type.** Let `R` be a regular local ring and let `t ∈ R` be a unit whose class in the residue field is not a `p`-th power. Then `t` has monomial type of residual type. Take a regular system of parameters `s` and all exponents zero. -/
theorem IsMonomialType.of_isUnit {p : ℕ} {R : Type*} [CommRing R] [IsRegularLocalRing R] {t : R}
    (ht : IsUnit t)
    (hres : ∀ c : IsLocalRing.ResidueField R, c ^ p ≠ IsLocalRing.residue R t) :
    IsMonomialType p t := by
  obtain ⟨s, hs⟩ := exists_isRegularSystemOfParameters (R := R)
  refine ⟨t, s, fun _ => 0, hs, ht, ?_, Or.inr ⟨fun _ _ => rfl, hres⟩⟩
  simp

/-- **An element of monomial type is monomial modulo `p`-th powers.** Take `h = 0` and `g = 1` in `IsMonomialModPow`. -/
theorem IsMonomialType.isMonomialModPow {p : ℕ} (hp : p ≠ 0) {R : Type*} [CommRing R]
    [IsLocalRing R] {t : R} (ht : IsMonomialType p t) : IsMonomialModPow p t := by
  obtain ⟨u, s, a, hs, hu, rfl, htype⟩ := ht
  exact ⟨0, 1, u, s, a, hs, hu, one_ne_zero, by rw [zero_pow hp, one_pow, zero_add, one_mul],
    htype⟩

/-- The element `f` of the local ring `R` is foliated monomial with respect to the field `E`. There are `t ∈ R` of monomial type and `c : Fin p → E` with `f = Σ_{i < p} c_i ^ p * t ^ i` in `E`. In words, the image of `f` is in the subfield `E ^ p (t)` of `E`. In use, `E` is the fraction field of `R`. -/
def IsFoliatedMonomial (p : ℕ) {R : Type*} [CommRing R] [IsLocalRing R] (E : Type*) [Field E]
    [Algebra R E] (f : R) : Prop :=
  ∃ t : R, IsMonomialType p t ∧
    ∃ c : Fin p → E, algebraMap R E f = ∑ i, c i ^ p * algebraMap R E t ^ (i : ℕ)

/-- **An element that is monomial modulo `p`-th powers is foliated monomial.** Let `f = h ^ p + g ^ p * t` with `t = u * ∏ x ∈ s, x ^ a x`. Then `t` has monomial type, and `f = Σ_{i < p} c_i ^ p t ^ i` with `c_0 = h`, `c_1 = g` and `c_i = 0` for `i ≥ 2`. This needs `p ≥ 2`. -/
theorem IsMonomialModPow.isFoliatedMonomial {p : ℕ} (hp : 2 ≤ p) {R : Type*} [CommRing R]
    [IsLocalRing R] (E : Type*) [Field E] [Algebra R E] {f : R} (hf : IsMonomialModPow p f) :
    IsFoliatedMonomial p E f := by
  obtain ⟨h, g, u, s, a, hs, hu, -, rfl, htype⟩ := hf
  refine ⟨u * ∏ x ∈ s, x ^ a x, ⟨u, s, a, hs, hu, rfl, htype⟩, ?_⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  refine ⟨Fin.cons (algebraMap R E h) (Fin.cons (algebraMap R E g) fun _ => 0), ?_⟩
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [zero_pow (Nat.succ_ne_zero (q + 1))]

end Monomial

section Field

variable {E : Type*} [Field E] {p : ℕ} [hp : Fact p.Prime] [CharP E p]

/-- **The element `t` is not a `p`-th power.** Let `E` be a field of characteristic `p` and let `f = Σ_{i < p} c_i ^ p t ^ i`. If `f` is not a `p`-th power in `E`, then `t` is not a `p`-th power in `E`. If `t = s ^ p`, then `f = (Σ c_i s ^ i) ^ p`. -/
theorem not_exists_pow_eq_of_eq_sum {f t : E} {c : Fin p → E}
    (hf : f = ∑ i, c i ^ p * t ^ (i : ℕ)) (hnot : ¬ ∃ g : E, g ^ p = f) :
    ¬ ∃ s : E, s ^ p = t := by
  rintro ⟨s, rfl⟩
  refine hnot ⟨∑ i, c i * s ^ (i : ℕ), ?_⟩
  rw [sum_pow_char, hf]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (i : ℕ) p]

/-- **The degree of `F(x)` over `F = E ^ p`.** Let `E` be a field of characteristic `p`, let `F` be the image of the Frobenius map of `E`, and let `x ∈ E` be no `p`-th power. Then `x` is integral over `F` and `[F(x) : F] = p`. The minimal polynomial of `x` is `X ^ p - x ^ p`, and it is irreducible because `x ^ p` is not a `p`-th power in `F`. -/
theorem finrank_adjoin_frobenius {x : E} (hx : ¬ ∃ y : E, y ^ p = x) :
    IsIntegral (frobenius E p).fieldRange x ∧
      finrank (frobenius E p).fieldRange (frobenius E p).fieldRange⟮x⟯ = p := by
  set F := (frobenius E p).fieldRange
  let a : F := ⟨x ^ p, x, rfl⟩
  have hirr : Irreducible (X ^ p - C a) := by
    refine X_pow_sub_C_irreducible_of_prime hp.out fun b hb => ?_
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.1 b.2
    have : (b : E) ^ p = x ^ p := congrArg Subtype.val hb
    refine hx ⟨y, ?_⟩
    rw [← frobenius_def, hy]
    exact frobenius_inj E p (by rw [frobenius_def, frobenius_def]; exact this)
  have hint : IsIntegral F x := by
    refine ⟨X ^ p - C a, monic_X_pow_sub_C a hp.out.ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
    rfl
  have hmin : minpoly F x = X ^ p - C a := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C a hp.out.ne_zero)).symm
    rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]
    rfl
  refine ⟨hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]

/-- **`f ∈ E ^ p (t)` gives `t ∈ E ^ p (f)`.** Let `E` be a field of characteristic `p`, let `f = Σ_{i < p} c_i ^ p t ^ i`, and let `f` be no `p`-th power in `E`. Then there are `d : Fin p → E` with `t = Σ_{i < p} d_i ^ p f ^ i`. Let `F = E ^ p`. Then `F(f) ⊆ F(t)` and both have degree `p` over `F`, so `t ∈ F(f) = F[f]`. The remainder of a polynomial in `f` on division by `X ^ p - f ^ p` gives the coefficients. -/
theorem exists_eq_sum_of_eq_sum {f t : E} {c : Fin p → E}
    (hf : f = ∑ i, c i ^ p * t ^ (i : ℕ)) (hnot : ¬ ∃ g : E, g ^ p = f) :
    ∃ d : Fin p → E, t = ∑ i, d i ^ p * f ^ (i : ℕ) := by
  set F := (frobenius E p).fieldRange
  obtain ⟨hfi, hfr⟩ := finrank_adjoin_frobenius hnot
  obtain ⟨hti, htr⟩ := finrank_adjoin_frobenius (not_exists_pow_eq_of_eq_sum hf hnot)
  have hle : F⟮f⟯ ≤ F⟮t⟯ := by
    rw [adjoin_simple_le_iff, hf]
    refine sum_mem fun i _ => mul_mem ?_ (pow_mem (mem_adjoin_simple_self F t) _)
    exact IntermediateField.algebraMap_mem _ (⟨c i ^ p, c i, rfl⟩ : F)
  have : FiniteDimensional F F⟮t⟯ := IntermediateField.adjoin.finiteDimensional hti
  have heq : F⟮f⟯ = F⟮t⟯ := IntermediateField.eq_of_le_of_finrank_eq hle (by rw [hfr, htr])
  have htmem : t ∈ (F⟮f⟯).toSubalgebra := heq ▸ mem_adjoin_simple_self F t
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic hfi.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at htmem
  obtain ⟨q, hq⟩ := htmem
  let a : F := ⟨f ^ p, f, rfl⟩
  have hmon : (X ^ p - C a).Monic := monic_X_pow_sub_C a hp.out.ne_zero
  have hroot : aeval f (X ^ p - C a) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]
    rfl
  have hdeg : (q %ₘ (X ^ p - C a)).natDegree < p := by
    have := natDegree_modByMonic_lt q hmon (by
      intro h1
      have := congrArg natDegree h1
      rw [natDegree_X_pow_sub_C, natDegree_one] at this
      exact hp.out.ne_zero this)
    rwa [natDegree_X_pow_sub_C] at this
  have hd : ∀ i : ℕ, ∃ d : E, d ^ p = ((q %ₘ (X ^ p - C a)).coeff i : E) := fun i => by
    obtain ⟨d, hd⟩ := RingHom.mem_fieldRange.1 ((q %ₘ (X ^ p - C a)).coeff i).2
    exact ⟨d, hd⟩
  choose d hd using hd
  refine ⟨fun i => d i, ?_⟩
  have hq' : t = aeval f (q %ₘ (X ^ p - C a)) := by
    rw [aeval_modByMonic_eq_self_of_root hroot]
    exact hq.symm
  rw [hq', aeval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd, Algebra.smul_def]
  rfl

/-- **A `p`-th root of `t` from a `p`-th root of `f`.** Let `E'` be an extension of a field `E` of characteristic `p`, let `θ ∈ E'` with `θ ^ p = f`, and let `t = Σ_{i < p} d_i ^ p f ^ i`. Then `(Σ d_i θ ^ i) ^ p = t`. -/
theorem sum_pow_eq_of_pow_eq {E' : Type*} [Field E'] [Algebra E E'] {f t : E} {d : Fin p → E}
    (ht : t = ∑ i, d i ^ p * f ^ (i : ℕ)) {θ : E'} (hθ : θ ^ p = algebraMap E E' f) :
    (∑ i, algebraMap E E' (d i) * θ ^ (i : ℕ)) ^ p = algebraMap E E' t := by
  have : CharP E' p := charP_of_injective_algebraMap (algebraMap E E').injective p
  rw [sum_pow_char, ht, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, mul_comm (i : ℕ) p, pow_mul, hθ, map_mul, map_pow, map_pow]

/-- **A `p`-th root of `t` in `E(θ)`.** Let `f = Σ_{i < p} c_i ^ p t ^ i` in a field `E` of characteristic `p`, with `f` no `p`-th power in `E`. Let `E'` be an extension of `E` and let `θ ∈ E'` with `θ ^ p = f`. Then there is `θ' ∈ E(θ)` with `θ' ^ p = t`. -/
theorem exists_pow_eq_of_eq_sum {E' : Type*} [Field E'] [Algebra E E'] {f t : E} {c : Fin p → E}
    (hf : f = ∑ i, c i ^ p * t ^ (i : ℕ)) (hnot : ¬ ∃ g : E, g ^ p = f) {θ : E'}
    (hθ : θ ^ p = algebraMap E E' f) :
    ∃ θ' : E', θ' ^ p = algebraMap E E' t ∧ θ' ∈ E⟮θ⟯ := by
  obtain ⟨d, hd⟩ := exists_eq_sum_of_eq_sum hf hnot
  refine ⟨_, sum_pow_eq_of_pow_eq hd hθ, sum_mem fun i _ => mul_mem ?_ ?_⟩
  · exact IntermediateField.algebraMap_mem _ _
  · exact pow_mem (mem_adjoin_simple_self E θ) _

/-- **`E(f ^ (1 / p)) = E(t ^ (1 / p))`.** Let `f = Σ_{i < p} c_i ^ p t ^ i` in a field `E` of characteristic `p`, with `f` no `p`-th power in `E`. Let `E'` be an extension of `E` and let `θ, θ' ∈ E'` with `θ ^ p = f` and `θ' ^ p = t`. Then `E(θ) = E(θ')`. The element `Σ d_i θ ^ i` of `exists_eq_sum_of_eq_sum` is a `p`-th root of `t`, so it is `θ'`. The element `Σ c_i θ' ^ i` is a `p`-th root of `f`, so it is `θ`. -/
theorem adjoin_eq_adjoin_of_eq_sum {E' : Type*} [Field E'] [Algebra E E'] {f t : E}
    {c : Fin p → E} (hf : f = ∑ i, c i ^ p * t ^ (i : ℕ)) (hnot : ¬ ∃ g : E, g ^ p = f)
    {θ θ' : E'} (hθ : θ ^ p = algebraMap E E' f) (hθ' : θ' ^ p = algebraMap E E' t) :
    E⟮θ⟯ = E⟮θ'⟯ := by
  have : CharP E' p := charP_of_injective_algebraMap (algebraMap E E').injective p
  obtain ⟨θ'', hθ'', hmem⟩ := exists_pow_eq_of_eq_sum hf hnot hθ
  have h1 : θ' = θ'' := frobenius_inj E' p (by rw [frobenius_def, frobenius_def, hθ', hθ''])
  have h2 : θ = ∑ i, algebraMap E E' (c i) * θ' ^ (i : ℕ) :=
    frobenius_inj E' p (by rw [frobenius_def, frobenius_def, sum_pow_eq_of_pow_eq hf hθ', hθ])
  refine le_antisymm ((adjoin_simple_le_iff).2 ?_) ((adjoin_simple_le_iff).2 (h1 ▸ hmem))
  rw [h2]
  refine sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _) ?_
  exact pow_mem (mem_adjoin_simple_self E θ') _

end Field

section Hypothesis

variable (p n : ℕ) (k : Type v) [Field k]

/-- **Foliated log monomialization along a valuation**, for extensions of transcendence degree `n` over `k`. This is `WeakLogMonomialization p n k` with `IsFoliatedMonomial` in place of `IsMonomialModPow`. Let `E` be an extension of `k` with `trdeg_k E = n`, and let `V` be a valuation subring of `E`. Let `A ⊆ V` be an affine model of `E/k` such that the local ring `T_A` at the centre of `V` is regular. Let `f ∈ A` be an element that is not a `p`-th power in `E`. Then there is an affine model `A'` of `E/k` with `A ⊆ A' ⊆ V` such that `T_{A'}` is regular and `f` is foliated monomial in `T_{A'}`.

This is an explicit hypothesis. The library does not prove it. It is open in transcendence degree 4. -/
def FoliatedLogMonomialization : Prop :=
  ∀ (E : Type u) [Field E] [Algebra k E], Algebra.trdeg k E = n →
    ∀ (V : ValuationSubring E) (A : Subalgebra k E), (∀ a ∈ A, a ∈ V) → IsAffineModel A →
      IsRegularLocalRing (centerSubring V A.toSubring) →
        ∀ f ∈ A, (¬ ∃ g : E, g ^ p = f) →
          ∃ A' : Subalgebra k E, A ≤ A' ∧ (∀ a ∈ A', a ∈ V) ∧ IsAffineModel A' ∧
            ∃ _ : IsRegularLocalRing (centerSubring V A'.toSubring),
              ∃ f' : centerSubring V A'.toSubring, (f' : E) = f ∧ IsFoliatedMonomial p E f'

end Hypothesis

section Step

/-- **Weak log monomialization gives foliated log monomialization.** An element that is monomial modulo `p`-th powers is foliated monomial (`IsMonomialModPow.isFoliatedMonomial`). -/
theorem foliatedLogMonomialization_of_weakLogMonomialization (p n : ℕ) [hp : Fact p.Prime]
    {k : Type v} [Field k] (hweak : WeakLogMonomialization.{u} p n k) :
    FoliatedLogMonomialization.{u} p n k := by
  intro E _ _ htr V A hAV hA hreg f hfA hnot
  obtain ⟨A', hAA', hA'V, hA', hreg', f', hf', hmon⟩ := hweak E htr V A hAV hA hreg f hfA hnot
  exact ⟨A', hAA', hA'V, hA', hreg', f', hf', hmon.isFoliatedMonomial hp.out.two_le E⟩

/-- **Foliated log monomialization gives the step of degree p.** Let `k` be a field of characteristic `p`. Assume `FoliatedLogMonomialization p n k` and `MonomialInseparableStep p n k`. These are explicit hypotheses that the library does not prove. Then `RegularCenterInseparableStep p n k` holds.

Choose `θ ∉ E` with `θ ^ p = f ∈ A`, as in `regularCenterInseparableStep_of_weakLogMonomialization`. Foliated log monomialization gives a model `A' ⊇ A` and `t` of monomial type in `T_{A'}` with `f ∈ E ^ p (t)`. There is `θ' ∉ E` with `θ' ^ p = t`, and `t` is monomial modulo `p`-th powers. The monomial step for `A'`, `θ'` and `t` gives a regular centre of `W` that contains the image of `A'`. -/
theorem regularCenterInseparableStep_of_foliatedLogMonomialization (p n : ℕ)
    [hp : Fact p.Prime] {k : Type v} [Field k] [CharP k p]
    (hfol : FoliatedLogMonomialization.{u} p n k) (hmono : MonomialInseparableStep.{u} p n k) :
    RegularCenterInseparableStep.{u} p n k := by
  intro E E' _ _ _ _ _ _ htr hfin hpi W s h
  obtain ⟨A, hAV, hA, hsA, hreg⟩ := (hasRegularCenter_iff_centerSubring _ _).1 h
  have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
  have : CharP E' p := charP_of_injective_algebraMap (algebraMap k E').injective p
  have : ExpChar E' p := ExpChar.prime hp.out
  obtain ⟨θ₀, hθ₀⟩ := exists_not_mem_range_of_finrank_eq_prime hp.out hfin
  obtain ⟨y, hy⟩ := pow_mem_range_of_finrank_eq hfin θ₀
  have : IsFractionRing A E := hA.2
  obtain ⟨θ, hθ, f, hfA, hf⟩ := exists_pow_eq_mem_subalgebra hp.out.ne_zero A hθ₀ hy
  have hnot := not_exists_pow_eq_of_pow_eq hθ hf
  obtain ⟨A', hAA', hA'V, hA', hreg', f', rfl, t, ht, c, hc⟩ :=
    hfol E htr _ A hAV hA hreg f hfA hnot
  have hc' : (f' : E) = ∑ i, c i ^ p * (t : E) ^ (i : ℕ) := hc
  obtain ⟨θ', hθ', -⟩ := exists_pow_eq_of_eq_sum hc' hnot hf.symm
  have hθ'E : θ' ∉ Set.range (algebraMap E E') := by
    rintro ⟨z, rfl⟩
    refine not_exists_pow_eq_of_eq_sum hc' hnot ⟨z, (algebraMap E E').injective ?_⟩
    rw [map_pow, hθ']
  refine (hmono E E' htr hfin hpi W A' hA'V hA' hreg' θ' hθ'E t hθ'.symm
    (ht.isMonomialModPow hp.out.ne_zero)).mono ?_
  exact Set.image_mono fun x hx => hAA' (hsA hx)

/-- **Local uniformization over a perfect field from foliated log monomialization.** Let `k` be a perfect field of characteristic `p`, let `K` be a function field over `k` with `trdeg_k K = n`, and let `V` be a valuation of `K/k`. Assume the theorem of Temkin (`localUniformization_inseparable`), `FoliatedLogMonomialization p n k` and `MonomialInseparableStep p n k`. These are explicit hypotheses that the library does not prove. Then `V` has local uniformization over `k`. -/
theorem hasLocalUniformization_of_foliatedLogMonomialization (p n : ℕ) [hp : Fact p.Prime]
    {k : Type u} [Field k] [CharP k p] [PerfectField k]
    (htem : localUniformization_inseparable.{u}) (hfol : FoliatedLogMonomialization.{u} p n k)
    (hmono : MonomialInseparableStep.{u} p n k)
    {K : Type u} [Field K] [Algebra k K] (hK : IsFunctionField k K)
    (htr : Algebra.trdeg k K = n) (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K] :
    HasLocalUniformization k V :=
  hasLocalUniformization_of_regularCenterInseparableStep p n htem
    (regularCenterInseparableStep_of_foliatedLogMonomialization p n hfol hmono) hK htr V

end Step

end Singularity
