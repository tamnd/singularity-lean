/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianCriterionTransversal
import Singularity.Valuation.FoliatedMonomial

/-!
# The field step of the log-Jacobian criterion

Let `R` be a local domain of characteristic `p` over `k`, with coordinates `x i` and derivations `D i` dual to them, and let `Δ` be a finite set of indices (the divisor). The files `LogJacobianCriterion.lean` and `LogJacobianCriterionTransversal.lean` prove that a principal log-Jacobian ideal of `f` gives a first integral `t`: each log derivation that kills `f` kills `t`. This file proves the last two steps of Theorem 4.4.16 of Volume 5, Chapter 4 of the handbook. The first integral `t` has monomial type (Definition 4.4.6), and `f` is in `E ^ p (t)` for a field `E` that contains `R` (Lemma 4.4.5). So `f` is foliated monomial (`IsFoliatedMonomial`).

## Main definitions

* `Singularity.pivotDerivation`: the derivation `(D j0 t)⁻¹ • D j0` of a field, which maps `t` to `1`.
* `Singularity.leafDerivation`: the derivation `D j - (D j t * (D j0 t)⁻¹) • D j0` of a field, which kills `t`.

## Main results

* `Singularity.exists_eq_sum_pow_of_mul_eq_mul`: the field step (Lemma 4.4.5, direction 3 to 2, in coordinates). Let `E` be a field of characteristic `p` with coordinates `x j` and dual derivations `D j`, and let the elements that all `D j` kill be `p`-th powers. If `D j0 t ≠ 0` and the gradients of `f` and `t` are proportional, then `f = ∑ i < p, c i ^ p * t ^ i`.
* `Singularity.exists_eq_sum_pow_of_forall_derivation`: the same conclusion if each derivation that kills `t` kills `f`.
* `Singularity.exists_eq_sum_pow_of_first_integral`: the passage from `R` to a field `E` that contains `R`. If each log derivation of `R` that kills `f` kills `t`, and `D j0 t ≠ 0`, then `f = ∑ i < p, c i ^ p * t ^ i` in `E`.
* `Singularity.isMonomialType_of_prod` and `Singularity.isMonomialType_contact`: the first integrals of the two cases have monomial type.
* `Singularity.isFoliatedMonomial_of_derivLogJacobian_eq_span_ramified` and `Singularity.isFoliatedMonomial_of_derivLogJacobian_eq_span_transversal`: the two cases of Theorem 4.4.16 with the conclusion `IsFoliatedMonomial p E f`.
* `Singularity.isFoliatedMonomial_of_derivLogJacobian_eq_span`: if the log-Jacobian ideal of `f` is principal with a nonzero generator, then `f` is foliated monomial.

## The proof

The field step works in coordinates. Let `Δ₀ = pivotDerivation D t j0` and `F j = leafDerivation D t j0 j`. A derivation that kills `t` and all the coordinates but `x j0` is zero. So `Δ₀` commutes with each `F j`, `Δ₀ ^ p = 0` and `Δ₀ t = 1`. The proportional gradients give `F j f = 0`. The Taylor lemma `exists_taylor_of_mem` for `Δ₀` on the ring of the elements that all `F j` kill gives `f = ∑ i < p, t ^ i * b i` with `Δ₀ b i = 0` and `F j b i = 0`. Then all `D j` kill `b i`, so `b i` is a `p`-th power by the hypothesis `hconst`.

To go from `R` to `E`, the log derivation `(a i * D i f) • (a j • D j) - (a j * D j f) • (a i • D i)` with `a = logCoeff x Δ` kills `f`. So it kills `t`, and this gives `D i f * D j t = D j f * D i t` in `R`. The extensions `DE j` of the `D j` to `E` keep this equality.

In Case 1 the first integral is `u * x i0 * ∏ i ∈ Δ.erase i0, x i ^ a i` with `u` a unit, and the exponent of `x i0` is `1`, which `p` does not divide. So `t` has the ramified type. In Case 2 the first integral is `ζ * ∏ i ∈ Δ, x i ^ a i` with `D j0 ζ` a unit. If `ζ` is in the maximal ideal, then `ζ` replaces `x j0` in the regular system of parameters, and `t` has the ramified type with the exponent `1` on `ζ`. If `ζ` is a unit and some `a i` with `i ∈ Δ` is not `0`, then `0 < a i < p`, and `t` has the ramified type with the unit `ζ`. If `ζ` is a unit and all `a i` are `0`, then `t = ζ`. If the residue of `ζ` is not a `p`-th power, `t` has the residual type. Otherwise the residue of `ζ` is the residue of `e ^ p`, the element `ζ - e ^ p` is in the maximal ideal, and each derivation takes the same value on `ζ - e ^ p` and on `ζ`. So `ζ - e ^ p` is a first integral of the ramified type (Steps 10 and 11 of the proof in the handbook).

## What is not proved

* Lemma 4.4.5 is proved only in coordinates, in the direction from `df ∈ E dt` to `f ∈ E ^ p (t)`. The file does not prove it with a `p`-basis of a general field, and it does not prove the other directions.
* The hypotheses `hext`, `hdetE` and `hconstE` on the field `E` are not proved here. They hold for the fraction field `E` of `R` when `R` is a regular local ring essentially of finite type over a perfect field `k`, the residue field is algebraic over `k`, and the `x j` are a regular system of parameters. Then `hext` and `hdetE` are part 4 of Lemma 4.4.1, and `hconstE` follows from (F1) and part 4 of Lemma 4.4.1 of the handbook. The file does not prove these facts.
* All the coordinates `x j` are in the regular system of parameters. The case of coordinates `w j` that are units with residues that form a `p`-basis of the residue field (the general setting of Definition 4.4.6) is not here.
* The file does not prove that `t` is not in `E ^ p`. The conclusion `IsFoliatedMonomial` does not need it.
* The converse direction of Theorem 4.4.16 (Proposition 4.4.15) is in `LogJacobianFirstIntegral.lean` only for the ramified type at the origin of affine space. Corollary 4.4.17 is not complete.
* The existence of a model with a principal log-Jacobian ideal in dimension 4 is open, and this file does not prove it.
* Local uniformization in positive characteristic and dimension 4 or more is open, and this file does not prove it.

## References

* Volume 5, Chapter 4 of the handbook, Lemma 4.4.5, Definition 4.4.6 and Theorem 4.4.16.
* H. Matsumura, *Commutative Ring Theory*, Section 26 (`p`-bases and derivations).
-/

open IsLocalRing Finset

namespace Singularity

section FieldStep

variable {k E ι : Type*} [CommRing k] [Field E] [Algebra k E]
  {D : ι → Derivation k E E} {x : ι → E}

/-- Let `D j0 t ≠ 0`. A derivation that kills `t` and all the coordinates but `x j0` is zero. -/
theorem derivation_eq_zero_of_apply_of_ne [Fintype ι] [DecidableEq ι]
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hdet : ∀ δ : Derivation k E E, (∀ j, δ (x j) = 0) → δ = 0) {j0 : ι} {t : E}
    (ht : D j0 t ≠ 0) (δ : Derivation k E E) (h1 : ∀ j, j ≠ j0 → δ (x j) = 0)
    (h2 : δ t = 0) : δ = 0 := by
  have hδ : δ = δ (x j0) • D j0 := by
    conv_lhs => rw [derivation_eq_sum_smul hD hdet δ]
    rw [Finset.sum_eq_single j0
      (fun j _ hj => by rw [h1 j hj, zero_smul]) (fun h => absurd (mem_univ j0) h)]
  have h0 : δ (x j0) = 0 := by
    have h3 := h2
    rw [hδ, Derivation.smul_apply, smul_eq_mul] at h3
    exact (mul_eq_zero.mp h3).resolve_right ht
  rw [hδ, h0, zero_smul]

/-- The derivation `(D j0 t)⁻¹ • D j0`. It maps `t` to `1`. -/
noncomputable def pivotDerivation (D : ι → Derivation k E E) (t : E) (j0 : ι) :
    Derivation k E E :=
  (D j0 t)⁻¹ • D j0

/-- The derivation `D j - (D j t * (D j0 t)⁻¹) • D j0`. It kills `t`. -/
noncomputable def leafDerivation (D : ι → Derivation k E E) (t : E) (j0 j : ι) :
    Derivation k E E :=
  D j - (D j t * (D j0 t)⁻¹) • D j0

variable {t : E} {j0 : ι}

/-- The value of `pivotDerivation D t j0`. -/
theorem pivotDerivation_apply (a : E) :
    pivotDerivation D t j0 a = (D j0 t)⁻¹ * D j0 a := by
  simp [pivotDerivation]

/-- The value of `leafDerivation D t j0 j`. -/
theorem leafDerivation_apply (j : ι) (a : E) :
    leafDerivation D t j0 j a = D j a - D j t * (D j0 t)⁻¹ * D j0 a := by
  simp [leafDerivation, mul_assoc]

/-- If `D j0 t ≠ 0`, then `pivotDerivation D t j0` maps `t` to `1`. -/
theorem pivotDerivation_apply_self (ht : D j0 t ≠ 0) : pivotDerivation D t j0 t = 1 := by
  rw [pivotDerivation_apply, inv_mul_cancel₀ ht]

/-- If `D j0 t ≠ 0`, then `leafDerivation D t j0 j` kills `t`. -/
theorem leafDerivation_apply_self (ht : D j0 t ≠ 0) (j : ι) : leafDerivation D t j0 j t = 0 := by
  rw [leafDerivation_apply, mul_assoc, inv_mul_cancel₀ ht, mul_one, sub_self]

variable [DecidableEq ι]

/-- The derivation `pivotDerivation D t j0` kills the coordinates `x l` with `l ≠ j0`. -/
theorem pivotDerivation_apply_of_ne (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {l : ι}
    (hl : l ≠ j0) : pivotDerivation D t j0 (x l) = 0 := by
  rw [pivotDerivation_apply, hD, ite_eq_right (Ne.symm hl), mul_zero]

/-- On a coordinate `x l` with `l ≠ j0`, the derivation `leafDerivation D t j0 j` takes the value of `D j`. -/
theorem leafDerivation_apply_of_ne (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (j : ι)
    {l : ι} (hl : l ≠ j0) : leafDerivation D t j0 j (x l) = if j = l then 1 else 0 := by
  rw [leafDerivation_apply, hD, hD, ite_eq_right (Ne.symm hl), mul_zero, sub_zero]

variable [Fintype ι]

/-- The derivations `pivotDerivation D t j0` and `leafDerivation D t j0 j` commute. -/
theorem pivotDerivation_leafDerivation_comm (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hdet : ∀ δ : Derivation k E E, (∀ j, δ (x j) = 0) → δ = 0) (ht : D j0 t ≠ 0) (j : ι)
    (a : E) : pivotDerivation D t j0 (leafDerivation D t j0 j a) =
      leafDerivation D t j0 j (pivotDerivation D t j0 a) := by
  have hP : ⁅pivotDerivation D t j0, leafDerivation D t j0 j⁆ = 0 := by
    refine derivation_eq_zero_of_apply_of_ne hD hdet ht _ (fun l hl => ?_) ?_
    · rw [Derivation.commutator_apply, leafDerivation_apply_of_ne hD j hl,
        pivotDerivation_apply_of_ne hD hl, map_zero]
      split_ifs <;> simp
    · rw [Derivation.commutator_apply, leafDerivation_apply_self ht,
        pivotDerivation_apply_self ht, map_zero, Derivation.map_one_eq_zero, sub_zero]
  have h := DFunLike.congr_fun hP a
  rw [Derivation.commutator_apply] at h
  exact sub_eq_zero.mp h

/-- In characteristic `p`, the `p`-th power of `pivotDerivation D t j0` is zero. -/
theorem pivotDerivation_pow_eq_zero (p : ℕ) [Fact p.Prime] [CharP E p]
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hdet : ∀ δ : Derivation k E E, (∀ j, δ (x j) = 0) → δ = 0) (ht : D j0 t ≠ 0) :
    (pivotDerivation D t j0).toLinearMap ^ p = 0 := by
  have hp0 := (Fact.out : p.Prime).ne_zero
  have hp2 := (Fact.out : p.Prime).two_le
  have hP : powCharDerivation p (pivotDerivation D t j0) = 0 := by
    refine derivation_eq_zero_of_apply_of_ne hD hdet ht _ (fun l hl => ?_) ?_
    · rw [powCharDerivation_apply,
        derivation_pow_apply_of_eq_zero _ (pivotDerivation_apply_of_ne hD hl) hp0]
    · rw [powCharDerivation_apply]
      obtain ⟨m, hm⟩ : ∃ m, p = m + 1 + 1 := ⟨p - 2, by omega⟩
      rw [hm, pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply]
      simp only [Derivation.coeFn_coe, pivotDerivation_apply_self ht,
        Derivation.map_one_eq_zero, map_zero]
  exact LinearMap.ext fun a => DFunLike.congr_fun hP a

omit [DecidableEq ι] [Fintype ι] in
/-- An element that `pivotDerivation D t j0` and all `leafDerivation D t j0 j` kill is killed by all `D j`. -/
theorem derivation_eq_zero_of_pivot_leaf {b : E} (hp : pivotDerivation D t j0 b = 0)
    (hl : ∀ j, leafDerivation D t j0 j b = 0) (ht : D j0 t ≠ 0) (j : ι) : D j b = 0 := by
  have h0 : D j0 b = 0 := by
    rw [pivotDerivation_apply] at hp
    exact (mul_eq_zero.mp hp).resolve_left (inv_ne_zero ht)
  have h1 := hl j
  rwa [leafDerivation_apply, h0, mul_zero, sub_zero] at h1

/-- **The field step of the log-Jacobian criterion** (Lemma 4.4.5, from part 3 to part 2, in coordinates). Let `E` be a field of characteristic `p` with coordinates `x j` and dual derivations `D j`, such that a derivation is determined by its values on the coordinates and the common constants of the `D j` are the `p`-th powers. Let `D j0 t ≠ 0`, and let the gradients of `f` and `t` be proportional: `D j f * D j0 t = D j t * D j0 f` for all `j`. Then `f = ∑_{i < p} c_i ^ p * t ^ i`. -/
theorem exists_eq_sum_pow_of_mul_eq_mul (p : ℕ) [Fact p.Prime] [CharP E p]
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hdet : ∀ δ : Derivation k E E, (∀ j, δ (x j) = 0) → δ = 0)
    (hconst : ∀ g : E, (∀ j, D j g = 0) → ∃ c : E, c ^ p = g) {f : E} (ht : D j0 t ≠ 0)
    (hrank : ∀ j, D j f * D j0 t = D j t * D j0 f) :
    ∃ c : Fin p → E, f = ∑ i, c i ^ p * t ^ (i : ℕ) := by
  set B := constantsOn (leafDerivation D t j0) Set.univ
  have hB : ∀ b ∈ B, pivotDerivation D t j0 b ∈ B := by
    intro b hb j _
    rw [← pivotDerivation_leafDerivation_comm hD hdet ht, hb j (Set.mem_univ j), map_zero]
  have htB : t ∈ B := fun j _ => leafDerivation_apply_self ht j
  have hfB : f ∈ B := by
    intro j _
    rw [leafDerivation_apply, mul_right_comm, ← hrank, mul_assoc, mul_inv_cancel₀ ht, mul_one,
      sub_self]
  obtain ⟨b, hb, hfb⟩ := exists_taylor_of_mem (pivotDerivation D t j0) p
    (pivotDerivation_pow_eq_zero p hD hdet ht) (pivotDerivation_apply_self ht) B hB htB hfB
  have hc : ∀ i, ∃ c : E, c ^ p = b i := fun i =>
    hconst _ (derivation_eq_zero_of_pivot_leaf (hb i).2 (fun j => (hb i).1 j (Set.mem_univ j)) ht)
  choose c hc using hc
  refine ⟨fun i => c i, ?_⟩
  rw [hfb, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc, mul_comm]

/-- **Lemma 4.4.5, from part 3 to part 2, in coordinates.** Under the hypotheses of `exists_eq_sum_pow_of_mul_eq_mul`, if each derivation of `E` that kills `t` also kills `f`, then `f = ∑_{i < p} c_i ^ p * t ^ i`. If `t` is a `p`-th power, then `f` is a `p`-th power. -/
theorem exists_eq_sum_pow_of_forall_derivation (p : ℕ) [Fact p.Prime] [CharP E p]
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hdet : ∀ δ : Derivation k E E, (∀ j, δ (x j) = 0) → δ = 0)
    (hconst : ∀ g : E, (∀ j, D j g = 0) → ∃ c : E, c ^ p = g) {f t : E}
    (h : ∀ δ : Derivation k E E, δ t = 0 → δ f = 0) :
    ∃ c : Fin p → E, f = ∑ i, c i ^ p * t ^ (i : ℕ) := by
  by_cases ht : ∃ j0, D j0 t ≠ 0
  · obtain ⟨j0, ht⟩ := ht
    refine exists_eq_sum_pow_of_mul_eq_mul p hD hdet hconst ht fun j => ?_
    have h1 := h ((D j0 t) • D j - (D j t) • D j0) (by simp [mul_comm])
    simp only [Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul] at h1
    linear_combination h1
  · push Not at ht
    obtain ⟨c, hc⟩ := hconst f fun j => h (D j) (ht j)
    have hp := (Fact.out : p.Prime).pos
    refine ⟨fun i => if (i : ℕ) = 0 then c else 0, ?_⟩
    rw [Finset.sum_eq_single ⟨0, hp⟩ (fun i _ hi => ?_) (fun h => absurd (mem_univ _) h)]
    · simp [hc]
    · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [hi', zero_pow (Fact.out : p.Prime).ne_zero]

end FieldStep

section Link

variable {k R ι : Type*} [CommRing k] [CommRing R] [Algebra k R] [DecidableEq ι]
  {D : ι → Derivation k R R} {x : ι → R} {Δ : Finset ι}

/-- The log derivation `logCoeff x Δ i • D i` maps `x l` to `logCoeff x Δ i` if `l = i` and to `0` if not. So it maps `x l` into `(x l)` for `l ∈ Δ`. -/
theorem dvd_logCoeff_smul_apply (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (i : ι)
    {l : ι} (hl : l ∈ Δ) : x l ∣ (logCoeff x Δ i • D i) (x l) := by
  rw [Derivation.smul_apply, hD, smul_eq_mul]
  split_ifs with h
  · subst h
    rw [logCoeff, ite_eq_left hl, mul_one]
  · rw [mul_zero]
    exact dvd_zero _

/-- In a nontrivial ring, a coordinate `x i` is not zero, since `D i (x i) = 1`. -/
theorem coord_ne_zero_of_dual [Nontrivial R] (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (i : ι) : x i ≠ 0 := by
  intro h
  have h1 := hD i i
  rw [h, map_zero, ite_eq_left rfl] at h1
  exact zero_ne_one h1

/-- In a nontrivial ring, `logCoeff x Δ i ≠ 0`, since `D i (x i) = 1`. -/
theorem logCoeff_ne_zero [Nontrivial R] (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (i : ι) : logCoeff x Δ i ≠ 0 := by
  unfold logCoeff
  split_ifs
  · exact coord_ne_zero_of_dual hD i
  · exact one_ne_zero

/-- **The gradients of `f` and of a first integral are proportional.** Let `R` be a domain, and let `t` be killed by each log derivation that kills `f`. Then `D i f * D j t = D j f * D i t` for all `i` and `j`. The log derivation `(a i * D i f) • (a j • D j) - (a j * D j f) • (a i • D i)`, with `a = logCoeff x Δ`, kills `f`, so it kills `t`. -/
theorem mul_eq_mul_of_first_integral [IsDomain R]
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {f t : R}
    (hft : ∀ δ : Derivation k R R, (∀ i ∈ Δ, x i ∣ δ (x i)) → δ f = 0 → δ t = 0) (i j : ι) :
    D i f * D j t = D j f * D i t := by
  set a := logCoeff x Δ
  set δ : Derivation k R R := (a i * D i f) • (a j • D j) - (a j * D j f) • (a i • D i)
  have hδΔ : ∀ l ∈ Δ, x l ∣ δ (x l) := by
    intro l hl
    simp only [δ, Derivation.sub_apply, Derivation.smul_apply (r := a i * D i f),
      Derivation.smul_apply (r := a j * D j f), smul_eq_mul]
    exact dvd_sub (dvd_mul_of_dvd_right (dvd_logCoeff_smul_apply hD j hl) _)
      (dvd_mul_of_dvd_right (dvd_logCoeff_smul_apply hD i hl) _)
  have hδf : δ f = 0 := by
    simp only [δ, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]
    ring
  have h := hft δ hδΔ hδf
  simp only [δ, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul] at h
  have h2 : (a i * a j) * (D i f * D j t - D j f * D i t) = 0 := by
    linear_combination h
  have hne : a i * a j ≠ 0 := mul_ne_zero (logCoeff_ne_zero hD i) (logCoeff_ne_zero hD j)
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hne)

variable [Fintype ι]

/-- **From a first integral in `R` to `f ∈ E ^ p (t)`.** Let `R` be a domain of characteristic `p` with coordinates `x j` and dual derivations `D j`, and let `E` be a field with an injective map from `R`. Let `DE j` be derivations of `E` that extend the `D j`, such that a derivation of `E` is determined by its values on the coordinates and the common constants of the `DE j` are the `p`-th powers. Let `t` be killed by each log derivation that kills `f`, and let `D j0 t ≠ 0`. Then `f = ∑_{i < p} c_i ^ p * t ^ i` in `E`. -/
theorem exists_eq_sum_pow_of_first_integral [IsDomain R] (p : ℕ) [Fact p.Prime] [CharP R p]
    {E : Type*} [Field E] [Algebra R E] [Algebra k E] (hinj : Function.Injective (algebraMap R E))
    (DE : ι → Derivation k E E) (hext : ∀ j r, DE j (algebraMap R E r) = algebraMap R E (D j r))
    (hdetE : ∀ δ : Derivation k E E, (∀ j, δ (algebraMap R E (x j)) = 0) → δ = 0)
    (hconstE : ∀ g : E, (∀ j, DE j g = 0) → ∃ c : E, c ^ p = g)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {f t : R} {j0 : ι} (ht : D j0 t ≠ 0)
    (hft : ∀ δ : Derivation k R R, (∀ i ∈ Δ, x i ∣ δ (x i)) → δ f = 0 → δ t = 0) :
    ∃ c : Fin p → E, algebraMap R E f = ∑ i, c i ^ p * algebraMap R E t ^ (i : ℕ) := by
  have : CharP E p := charP_of_injective_algebraMap hinj p
  have hDE : ∀ i j, DE i (algebraMap R E (x j)) = if i = j then 1 else 0 := by
    intro i j
    rw [hext, hD]
    split_ifs <;> simp
  refine exists_eq_sum_pow_of_mul_eq_mul p hDE hdetE hconstE (j0 := j0) ?_ fun j => ?_
  · rw [hext]
    exact (map_ne_zero_iff _ hinj).mpr ht
  · rw [hext, hext, hext, hext, ← map_mul, ← map_mul, mul_eq_mul_of_first_integral hD hft j j0,
      mul_comm]

end Link

section MonomialType

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The product `∏ i, y i ^ e i` with `e i0 = 1`, `e i = a i` for `i ∈ S` and `e i = 0` otherwise, where `i0 ∉ S`, is `y i0 * ∏ i ∈ S, y i ^ a i`. -/
theorem prod_pow_ite_eq (y : ι → R) (i0 : ι) (S : Finset ι) (hS : i0 ∉ S) (a : ι → ℕ) :
    ∏ i, y i ^ (if i = i0 then 1 else if i ∈ S then a i else 0) =
      y i0 * ∏ i ∈ S, y i ^ a i := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i0), ite_eq_left rfl, pow_one]
  congr 1
  have h1 : ∏ i ∈ S, y i ^ a i =
      ∏ i ∈ S, y i ^ (if i = i0 then 1 else if i ∈ S then a i else 0) :=
    prod_congr rfl fun i hi => by
      rw [ite_eq_right (fun h : i = i0 => hS (h ▸ hi)), ite_eq_left hi]
  rw [h1]
  refine (prod_subset (fun i hi => mem_erase.mpr ⟨fun h : i = i0 => hS (h ▸ hi), mem_univ i⟩)
    fun i hi hiS => ?_).symm
  rw [ite_eq_right (ne_of_mem_erase hi), ite_eq_right hiS, pow_zero]

/-- The product `∏ i, y i ^ e i` with `e i = a i` for `i ∈ S` and `e i = 0` otherwise is `∏ i ∈ S, y i ^ a i`. -/
theorem prod_pow_ite_mem (y : ι → R) (S : Finset ι) (a : ι → ℕ) :
    ∏ i, y i ^ (if i ∈ S then a i else 0) = ∏ i ∈ S, y i ^ a i := by
  have h1 : ∏ i ∈ S, y i ^ a i = ∏ i ∈ S, y i ^ (if i ∈ S then a i else 0) :=
    prod_congr rfl fun i hi => by rw [ite_eq_left hi]
  rw [h1]
  exact (prod_subset (subset_univ S) fun i _ hiS => by rw [ite_eq_right hiS, pow_zero]).symm

variable [IsLocalRing R] [DecidableEq R]

omit [DecidableEq ι] in
/-- Let the values of an injective family `y` be a regular system of parameters. Then `u * ∏ i, y i ^ e i` with `u` a unit and `p ∤ e i1` has monomial type (the ramified type). -/
theorem isMonomialType_of_prod (p : ℕ) {y : ι → R}
    (hs : IsRegularSystemOfParameters (univ.image y)) (hy : Function.Injective y) {u : R}
    (hu : IsUnit u) (e : ι → ℕ) {i1 : ι} (he : ¬ p ∣ e i1) :
    IsMonomialType p (u * ∏ i, y i ^ e i) := by
  have : Nonempty ι := ⟨i1⟩
  refine ⟨u, univ.image y, fun r => e (Function.invFun y r), hs, hu, ?_,
    Or.inl ⟨y i1, mem_image_of_mem y (mem_univ _), by
      show ¬ p ∣ e (Function.invFun y (y i1))
      rwa [Function.leftInverse_invFun hy i1]⟩⟩
  rw [prod_image (fun i _ j _ h => hy h)]
  simp only [Function.leftInverse_invFun hy _]

variable {k : Type*} [CommRing k] [Algebra k R] {D : ι → Derivation k R R} {x : ι → R}

/-- **A parameter of contact.** Let the values of an injective family of coordinates `x` be a regular system of parameters, with dual derivations `D j`. Let `ζ` be in the maximal ideal with `D j0 ζ` a unit. Then we can replace `x j0` by `ζ`: the family `Function.update x j0 ζ` is injective, and its values are a regular system of parameters. -/
theorem isRegularSystemOfParameters_update (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hs : IsRegularSystemOfParameters (univ.image x)) (hx : Function.Injective x) {j0 : ι}
    {ζ : R} (hζm : ζ ∈ maximalIdeal R) (hζ : IsUnit (D j0 ζ)) :
    IsRegularSystemOfParameters (univ.image (Function.update x j0 ζ)) ∧
      Function.Injective (Function.update x j0 ζ) := by
  have hne : ∀ j, j ≠ j0 → ζ ≠ x j := by
    intro j hj h
    rw [h, hD, ite_eq_right (Ne.symm hj)] at hζ
    exact not_isUnit_zero hζ
  have hinj : Function.Injective (Function.update x j0 ζ) := by
    intro i j h
    by_cases hi : i = j0 <;> by_cases hj : j = j0
    · rw [hi, hj]
    · subst hi
      rw [Function.update_self, Function.update_of_ne hj] at h
      exact absurd h (hne j hj)
    · subst hj
      rw [Function.update_self, Function.update_of_ne hi] at h
      exact absurd h.symm (hne i hi)
    · rw [Function.update_of_ne hi, Function.update_of_ne hj] at h
      exact hx h
  have hcoe : ∀ y : ι → R, ((univ.image y : Finset R) : Set R) = Set.range y := by simp
  have hm : Ideal.span (Set.range x) = maximalIdeal R := by
    rw [← hcoe]
    exact hs.1
  have hxm : ∀ i, x i ∈ maximalIdeal R := fun i => hm ▸ Ideal.subset_span ⟨i, rfl⟩
  have hmem : ∀ i, i ≠ j0 → x i ∈ Ideal.span (Set.range (Function.update x j0 ζ)) :=
    fun i hi => Ideal.subset_span ⟨i, Function.update_of_ne hi _ _⟩
  have hζmem : ζ ∈ Ideal.span (Set.range (Function.update x j0 ζ)) :=
    Ideal.subset_span ⟨j0, Function.update_self _ _ _⟩
  refine ⟨⟨?_, ?_⟩, hinj⟩
  · rw [hcoe]
    refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · rintro _ ⟨i, rfl⟩
      by_cases hi : i = j0
      · rw [hi, Function.update_self]
        exact hζm
      · rw [Function.update_of_ne hi]
        exact hxm i
    · rw [← hm, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases hi : i = j0
      · subst hi
        obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hm ▸ hζm)
        have hD0 : D i ζ = g i + ∑ l, x l * D i (g l) := by
          rw [← hg, map_sum]
          simp only [Derivation.leibniz, hD, smul_eq_mul, sum_add_distrib, mul_ite, mul_one,
            mul_zero, sum_ite_eq, mem_univ, ite_true]
        have hgu : IsUnit (g i) := by
          by_contra hn
          have h1 : g i ∈ maximalIdeal R := hn
          have h2 : ∑ l, x l * D i (g l) ∈ maximalIdeal R :=
            Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hxm l)
          have h3 : D i ζ ∈ maximalIdeal R := by
            rw [hD0]
            exact Ideal.add_mem _ h1 h2
          exact h3 hζ
        have heq : g i * x i = ζ - ∑ l ∈ univ.erase i, g l * x l := by
          rw [← hg, ← add_sum_erase univ _ (mem_univ i)]
          ring
        obtain ⟨b, hb⟩ := hgu.exists_left_inv
        have hxi : x i = b * (g i * x i) := by rw [← mul_assoc, hb, one_mul]
        rw [hxi, heq]
        refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hζmem (Ideal.sum_mem _ fun l hl => ?_))
        exact Ideal.mul_mem_left _ _ (hmem l (ne_of_mem_erase hl))
      · exact hmem i hi
  · rw [card_image_of_injective _ hinj]
    have h2 := hs.2
    rwa [card_image_of_injective _ hx] at h2

/-- **The transversal first integral has monomial type** when `ζ` is in the maximal ideal. Let `j0 ∉ Δ`, let `ζ` be in the maximal ideal and let `D j0 ζ` be a unit. Then `ζ * ∏ i ∈ Δ, x i ^ a i` has monomial type, with the exponent `1` at the new parameter `ζ`. -/
theorem isMonomialType_contact (p : ℕ) [Fact p.Prime]
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hs : IsRegularSystemOfParameters (univ.image x)) (hx : Function.Injective x) {Δ : Finset ι}
    {j0 : ι} (hj0 : j0 ∉ Δ) {ζ : R} (hζm : ζ ∈ maximalIdeal R) (hζ : IsUnit (D j0 ζ))
    (a : ι → ℕ) : IsMonomialType p (ζ * ∏ i ∈ Δ, x i ^ a i) := by
  obtain ⟨hs', hinj'⟩ := isRegularSystemOfParameters_update hD hs hx hζm hζ
  have h1 : ζ * ∏ i ∈ Δ, x i ^ a i = 1 * ∏ i, Function.update x j0 ζ i ^
      (if i = j0 then 1 else if i ∈ Δ then a i else 0) := by
    rw [prod_pow_ite_eq _ j0 Δ hj0 a, Function.update_self, one_mul]
    congr 1
    exact prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (fun h : i = j0 => hj0 (h ▸ hi))]
  rw [h1]
  refine isMonomialType_of_prod p hs' hinj' isUnit_one _ (i1 := j0) ?_
  rw [ite_eq_left rfl]
  exact (Fact.out : p.Prime).not_dvd_one

end MonomialType

section Criterion

variable {k R ι : Type*} [CommRing k] [CommRing R] [Algebra k R] [IsLocalRing R] [IsDomain R]
  [DecidableEq R] [Fintype ι] [DecidableEq ι] {D : ι → Derivation k R R} {x : ι → R}
  {Δ : Finset ι} {f : R} (p : ℕ) [Fact p.Prime] [CharP R p] (E : Type*) [Field E] [Algebra R E]
  [Algebra k E]

omit [DecidableEq R] in
/-- **A first integral of monomial type gives a foliated monomial element.** Let `t` have monomial type, let `D j0 t ≠ 0`, and let `t` be killed by each log derivation that kills `f`. Under the hypotheses on `E` of `exists_eq_sum_pow_of_first_integral`, the element `f` is foliated monomial. -/
theorem isFoliatedMonomial_of_first_integral (hinj : Function.Injective (algebraMap R E))
    (DE : ι → Derivation k E E) (hext : ∀ j r, DE j (algebraMap R E r) = algebraMap R E (D j r))
    (hdetE : ∀ δ : Derivation k E E, (∀ j, δ (algebraMap R E (x j)) = 0) → δ = 0)
    (hconstE : ∀ g : E, (∀ j, DE j g = 0) → ∃ c : E, c ^ p = g)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {t : R} {j0 : ι}
    (htype : IsMonomialType p t) (ht : D j0 t ≠ 0)
    (hft : ∀ δ : Derivation k R R, (∀ i ∈ Δ, x i ∣ δ (x i)) → δ f = 0 → δ t = 0) :
    IsFoliatedMonomial p E f :=
  ⟨t, htype, exists_eq_sum_pow_of_first_integral p hinj DE hext hdetE hconstE hD ht hft⟩

/-- **The log-Jacobian criterion, ramified case, up to `f ∈ E ^ p (t)`** (Theorem 4.4.16, Case 1). Let the values of the injective family of coordinates `x` be a regular system of parameters. If `x i0 * D i0 f` with `i0 ∈ Δ` generates the log-Jacobian ideal, then `f` is foliated monomial. The element `t` is the first integral `u * x i0 * ∏ i ∈ Δ.erase i0, x i ^ a i` of `exists_first_integral_of_derivLogJacobian_eq_span`. -/
theorem isFoliatedMonomial_of_derivLogJacobian_eq_span_ramified
    (hinj : Function.Injective (algebraMap R E))
    (DE : ι → Derivation k E E) (hext : ∀ j r, DE j (algebraMap R E r) = algebraMap R E (D j r))
    (hdetE : ∀ δ : Derivation k E E, (∀ j, δ (algebraMap R E (x j)) = 0) → δ = 0)
    (hconstE : ∀ g : E, (∀ j, DE j g = 0) → ∃ c : E, c ^ p = g)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hdet : ∀ δ : Derivation k R R, (∀ j, δ (x j) = 0) → δ = 0)
    (hs : IsRegularSystemOfParameters (univ.image x)) (hxinj : Function.Injective x) {i0 : ι}
    (hi0 : i0 ∈ Δ) (hne : x i0 * D i0 f ≠ 0)
    (hJ : derivLogJacobian D x Δ f = Ideal.span {x i0 * D i0 f}) :
    IsFoliatedMonomial p E f := by
  have hx : ∀ i, x i ∈ maximalIdeal R := fun i =>
    hs.1 ▸ Ideal.subset_span (by simp)
  obtain ⟨u, a, hu, -, hδ, v, hv, hDt⟩ :=
    exists_first_integral_of_derivLogJacobian_eq_span p hD hdet hx hi0 hne hJ
  have htne : u * x i0 * ∏ i ∈ Δ.erase i0, x i ^ a i ≠ 0 :=
    mul_ne_zero (mul_ne_zero hu.ne_zero (coord_ne_zero_of_dual hD i0))
      (prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (coord_ne_zero_of_dual hD i))
  have hDt0 : D i0 (u * x i0 * ∏ i ∈ Δ.erase i0, x i ^ a i) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hDt
    exact htne ((hv.mul_right_eq_zero).mp hDt.symm)
  have htype : IsMonomialType p (u * x i0 * ∏ i ∈ Δ.erase i0, x i ^ a i) := by
    rw [mul_assoc, ← prod_pow_ite_eq x i0 (Δ.erase i0) (notMem_erase i0 Δ) a]
    refine isMonomialType_of_prod p hs hxinj hu _ (i1 := i0) ?_
    rw [ite_eq_left rfl]
    exact (Fact.out : p.Prime).not_dvd_one
  exact isFoliatedMonomial_of_first_integral p E hinj DE hext hdetE hconstE hD htype hDt0 hδ

/-- **The log-Jacobian criterion, transversal case, up to `f ∈ E ^ p (t)`** (Theorem 4.4.16, Case 2). Let the values of the injective family of coordinates `x` be a regular system of parameters. If `D j0 f` with `j0 ∉ Δ` generates the log-Jacobian ideal, then `f` is foliated monomial. Let `ζ * ∏ i ∈ Δ, x i ^ a i` be the first integral of `exists_first_integral_of_derivLogJacobian_eq_span_transversal`. If `ζ` is in the maximal ideal, then `ζ` replaces `x j0` in the regular system of parameters. If `ζ` is a unit and some `a i ≠ 0`, the first integral has the ramified type with the unit `ζ`. If `ζ` is a unit and all `a i = 0`, the first integral is `ζ`. Then either the class of `ζ` is not a `p`-th power (the residual type), or `ζ - e ^ p` is in the maximal ideal for some `e`, and `ζ - e ^ p` replaces `x j0`. -/
theorem isFoliatedMonomial_of_derivLogJacobian_eq_span_transversal
    (hinj : Function.Injective (algebraMap R E))
    (DE : ι → Derivation k E E) (hext : ∀ j r, DE j (algebraMap R E r) = algebraMap R E (D j r))
    (hdetE : ∀ δ : Derivation k E E, (∀ j, δ (algebraMap R E (x j)) = 0) → δ = 0)
    (hconstE : ∀ g : E, (∀ j, DE j g = 0) → ∃ c : E, c ^ p = g)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hdet : ∀ δ : Derivation k R R, (∀ j, δ (x j) = 0) → δ = 0)
    (hs : IsRegularSystemOfParameters (univ.image x)) (hxinj : Function.Injective x) {j0 : ι}
    (hj0 : j0 ∉ Δ) (hne : D j0 f ≠ 0) (hJ : derivLogJacobian D x Δ f = Ideal.span {D j0 f}) :
    IsFoliatedMonomial p E f := by
  have hx : ∀ i, x i ∈ maximalIdeal R := fun i =>
    hs.1 ▸ Ideal.subset_span (by simp)
  obtain ⟨ζ, a, hζ, ha, hδ, hDt⟩ :=
    exists_first_integral_of_derivLogJacobian_eq_span_transversal p hD hdet hx hj0 hne hJ
  have hM0 : ∏ i ∈ Δ, x i ^ a i ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (coord_ne_zero_of_dual hD i)
  have hDt0 : D j0 (ζ * ∏ i ∈ Δ, x i ^ a i) ≠ 0 := by
    rw [hDt]
    exact mul_ne_zero hζ.ne_zero hM0
  have hfol : ∀ {t : R}, IsMonomialType p t → D j0 t ≠ 0 →
      (∀ δ : Derivation k R R, (∀ i ∈ Δ, x i ∣ δ (x i)) → δ f = 0 → δ t = 0) →
      IsFoliatedMonomial p E f := fun htype ht hft =>
    isFoliatedMonomial_of_first_integral p E hinj DE hext hdetE hconstE hD htype ht hft
  by_cases hζm : ζ ∈ maximalIdeal R
  · exact hfol (isMonomialType_contact p hD hs hxinj hj0 hζm hζ a) hDt0 hδ
  have hζu : IsUnit ζ := by
    by_contra h
    exact hζm h
  by_cases hai : ∃ i ∈ Δ, a i ≠ 0
  · obtain ⟨i1, hi1, hai1⟩ := hai
    have htype : IsMonomialType p (ζ * ∏ i ∈ Δ, x i ^ a i) := by
      rw [← prod_pow_ite_mem x Δ a]
      refine isMonomialType_of_prod p hs hxinj hζu _ (i1 := i1) ?_
      rw [ite_eq_left hi1]
      exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hai1) (ha i1)
    exact hfol htype hDt0 hδ
  push Not at hai
  have hM1 : ∏ i ∈ Δ, x i ^ a i = 1 := prod_eq_one fun i hi => by rw [hai i hi, pow_zero]
  rw [hM1, mul_one] at hDt0 hδ
  by_cases hres : ∀ c : ResidueField R, c ^ p ≠ residue R ζ
  · exact hfol ⟨ζ, univ.image x, fun _ => 0, hs, hζu, by simp, Or.inr ⟨fun _ _ => rfl, hres⟩⟩
      hDt0 hδ
  push Not at hres
  obtain ⟨c, hc⟩ := hres
  obtain ⟨e, rfl⟩ := residue_surjective c
  have hsub : ∀ δ : Derivation k R R, δ (ζ - e ^ p) = δ ζ := fun δ => by
    rw [map_sub, derivation_pow_char (p := p) δ e, sub_zero]
  have hζ'm : ζ - e ^ p ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_pow, hc, sub_self]
  have htype : IsMonomialType p (ζ - e ^ p) := by
    have h1 := isMonomialType_contact p hD hs hxinj (notMem_empty j0) hζ'm
      (by rw [hsub]; exact hζ) a
    rwa [prod_empty, mul_one] at h1
  exact hfol htype (by rw [hsub]; exact hDt0) fun δ h1 h2 => by rw [hsub]; exact hδ δ h1 h2

/-- **The log-Jacobian criterion, up to `f ∈ E ^ p (t)`** (Theorem 4.4.16). Let the values of the injective family of coordinates `x` be a regular system of parameters. If the log-Jacobian ideal of `f` is principal with a nonzero generator, then `f` is foliated monomial. The proof finds a generator of the form `x i * D i f` with `i ∈ Δ` or `D j f` with `j ∉ Δ`, and it applies the ramified or the transversal case. -/
theorem isFoliatedMonomial_of_derivLogJacobian_eq_span
    (hinj : Function.Injective (algebraMap R E))
    (DE : ι → Derivation k E E) (hext : ∀ j r, DE j (algebraMap R E r) = algebraMap R E (D j r))
    (hdetE : ∀ δ : Derivation k E E, (∀ j, δ (algebraMap R E (x j)) = 0) → δ = 0)
    (hconstE : ∀ g : E, (∀ j, DE j g = 0) → ∃ c : E, c ^ p = g)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hdet : ∀ δ : Derivation k R R, (∀ j, δ (x j) = 0) → δ = 0)
    (hs : IsRegularSystemOfParameters (univ.image x)) (hxinj : Function.Injective x) {g : R}
    (hg : g ≠ 0) (hJ : derivLogJacobian D x Δ f = Ideal.span {g}) :
    IsFoliatedMonomial p E f := by
  obtain ⟨i, ⟨hi, hJi⟩ | ⟨hi, hJi⟩⟩ := exists_derivLogJacobian_eq_span_generator hg hJ
  · have hne : x i * D i f ≠ 0 := fun h => hg (by
      rw [← Ideal.span_singleton_eq_bot, ← hJ, hJi, h, Ideal.span_singleton_eq_bot])
    exact isFoliatedMonomial_of_derivLogJacobian_eq_span_ramified p E hinj DE hext hdetE hconstE
      hD hdet hs hxinj hi hne hJi
  · have hne : D i f ≠ 0 := fun h => hg (by
      rw [← Ideal.span_singleton_eq_bot, ← hJ, hJi, h, Ideal.span_singleton_eq_bot])
    exact isFoliatedMonomial_of_derivLogJacobian_eq_span_transversal p E hinj DE hext hdetE
      hconstE hD hdet hs hxinj hi hne hJi

end Criterion

end Singularity
