/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Surface.IdealChart
import Singularity.Surface.WhitneyUmbrella
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Tactic.LinearCombination

/-!
# Algebraic cores of blowups, normalization and rational singularities

This file proves the ring theoretic cores of several results of Volume 4 of the handbook.
None of them is proved on schemes. The main declarations are as follows.

Definition 1.1.1 (the Rees algebra and the charts of the blowup). The Rees algebra is
Mathlib's `reesAlgebra I`, the graded algebra `⊕ I^n t^n` inside `R[t]`.

* `Singularity.reesChartMap`: the map `S → R_f` with `a t^n ↦ a / f^n`.
* `Singularity.reesChartMap_monomial`, `Singularity.reesChartMap_monomial_one_self`: its values,
  and `f t ↦ 1`.
* `Singularity.range_reesChartMap`: its image is the chart `R[I/f]`.

Definition 1.1.4 (the strict transform in a chart).

* `Singularity.awaySaturation`: the ideal `(𝔞 : g^∞)` of the `b` with `g^k b ∈ 𝔞` for some `k`.
* `Singularity.mem_awaySaturation_iff_algebraMap_eq_zero`: it is the kernel of `B → (B/𝔞)_g`.
  This is the ideal of the scheme theoretic closure of `D(g) ∩ V(𝔞)` in `Spec B`.
* `Singularity.le_awaySaturation`, `Singularity.mem_awaySaturation_of_mul_mem`: it contains `𝔞`,
  and `g` is a nonzerodivisor modulo it.
* `Singularity.chartStrictTransform`, `Singularity.mem_chartStrictTransform_iff`: the ideal
  `(J B : f^∞)` of the strict transform of `V(J)` in the chart `B = R[I/f]`. It is `B ∩ J R_f`.
* `Singularity.awaySaturation_span_pow_mul_eq_span`: in a domain, if `x` is prime and `x` does
  not divide `F'`, then `(x^m F' : x^∞) = (F')`. This is the step in the proof of Lemma 1.1.6.

Definition 1.2.1 and Corollary 1.2.5 (normalization, affine case).

* `Singularity.affineNormalization`: the integral closure of a domain `R` in its fraction field.
* `Singularity.isIntegrallyClosed_affineNormalization`: the normalization is normal.
* `Singularity.affineNormalization_eq_bot_iff`: it is `R` if and only if `R` is normal. So the
  normalization does not change a normal scheme, as used over `Reg(X)` in Corollary 1.2.5.
* `Singularity.isDomain_idealChart`, `Singularity.algebraMap_idealChart_injective`: over a
  domain `R` and `f ≠ 0`, the chart `R[I/f]` is a domain that contains `R`. Thus the chart is
  a ring between `R` and the function field, as in the proof of Corollary 1.2.5.

Lemmas 2.1.5 and 2.1.8 (the algebraic steps).

* `Singularity.subsingleton_of_exact`: in an exact sequence `M → N → P` with `M = 0` and
  `P = 0` we have `N = 0`. This is the step `h_* R^1 g_* O = 0` of the proof of Lemma 2.1.5.
* `Singularity.subsingleton_of_forall_pi_subsingleton`: if the products of the stalks of a
  family over the sets of a cover are all zero, then each stalk is zero. This is the last step
  of the proof of Lemma 2.1.5.
* `Singularity.isIntegrallyClosed_localization_of_le`: a localization `B_Σ` of an integrally
  closed domain is integrally closed. This is the step in the proof of Lemma 2.1.8 that
  `Y_x` is normal.

Example 2.2.4 and Lemma 2.2.5.

* `Singularity.whitneyNormalization_finite`: the normalization `k[x, y, z] → k[s, t]` of the
  Whitney umbrella is finite.
* `Singularity.whitneyNormalization_eq_of_comap_eq`: two primes `P ≤ Q` of `k[s, t]` with the
  same image are equal. So no curve of `A^2` maps to a point.
* `Singularity.isRegularLocalRing_localization_atPrime_iff`: for a prime `P` of `B_Σ`, the local
  ring of `B_Σ` at `P` is regular if and only if the local ring of `B` at `P ∩ B` is regular.
  This is the claim `Sing(Y_W) = Sing(Y) ∩ Y_W` in the proof of Lemma 2.2.5, part 1.

Lemma 2.3.9, part 2 (the count of zeros of a form on `P^1`). Let `G` be a nonzero form of degree
`n` in `X_0, X_1`, and let `p = G(1, T)`. Then `reflect n p = G(S, 1)`.

* `Singularity.natTrailingDegree_reflect_of_natDegree_le`: the order of `G(S, 1)` at `S = 0`
  is `n - deg p`.
* `Singularity.finrank_add_finrank_eq_of_natDegree_le`: the length of the zero scheme of `G` on
  `X_0 ≠ 0` plus its length at the point `X_0 = 0` is `n`. Thus a section of `O(n)` has `n`
  zeros, counted with length.

Not proved. Definitions 1.1.1 and 1.1.4 are not formalized on schemes: there is no `Proj` and no
scheme theoretic closure here. Definition 1.1.8, Corollary 1.1.9 and Remark 1.1.10 (the
self-intersection `E · E = -1`) need line bundles on `P^1` and their degree, and they are not
proved. The statement on schemes of Definition 1.2.1 and Corollary 1.2.5 is not proved; in
particular the finiteness of normalization, the dimension bound and properness are missing.
Definitions 2.1.1 and 2.1.3 (normal modifications, rational singularities) and the statements of
Lemmas 2.1.5 and 2.1.8 need higher direct images of coherent sheaves, and they are not proved.
Only the steps listed above are proved. In Example 2.2.4 the claims that the map is the
normalization and that `A^2` is regular are not proved. In Lemma 2.2.5 the commutation of the
process with base change is not proved. Definition 2.3.8 and parts 1 and 3 of Lemma 2.3.9 are not
formalized.
-/

namespace Singularity

open Polynomial

section Rees

variable {R : Type*} [CommRing R]

/-- The map from the Rees algebra `S = ⊕ I^n t^n` to `R_f` that sends `a t^n` to `a / f^n`.
It is the evaluation at `t = 1/f` (Volume 4, Definition 1.1.1 of the handbook). -/
noncomputable def reesChartMap (I : Ideal R) (f : R) :
    reesAlgebra I →ₐ[R] Localization.Away f :=
  (aeval (IsLocalization.Away.invSelf f)).comp (reesAlgebra I).val

/-- The map `S → R_f` sends `a t^n` to `a / f^n` (Volume 4, Definition 1.1.1 of the handbook). -/
theorem reesChartMap_monomial {I : Ideal R} {f : R} {n : ℕ} {a : R} (ha : a ∈ I ^ n) :
    reesChartMap I f ⟨monomial n a, reesAlgebra.monomial_mem.mpr ha⟩ =
      algebraMap R (Localization.Away f) a * IsLocalization.Away.invSelf f ^ n := by
  simp [reesChartMap, aeval_monomial]

/-- For `f ∈ I`, the map `S → R_f` sends the element `f t` of degree 1 to `1`
(Volume 4, Definition 1.1.1 of the handbook). -/
theorem reesChartMap_monomial_one_self {I : Ideal R} {f : R} (hf : f ∈ I) :
    reesChartMap I f ⟨monomial 1 f, reesAlgebra.monomial_mem.mpr (by simpa using hf)⟩ = 1 := by
  rw [reesChartMap_monomial (by simpa using hf), pow_one, IsLocalization.Away.mul_invSelf]

/-- The image of the Rees algebra in `R_f` is the chart `R[I/f]` of the blowup
(Volume 4, Definition 1.1.1 of the handbook). -/
theorem range_reesChartMap (I : Ideal R) (f : R) : (reesChartMap I f).range = idealChart I f := by
  rw [reesChartMap, AlgHom.range_comp, Subalgebra.range_val, ← adjoin_monomial_eq_reesAlgebra,
    AlgHom.map_adjoin, idealChart, Submodule.map_coe, ← Set.image_comp]
  congr 1
  apply Set.image_congr
  intro a _
  simp [aeval_monomial]

end Rees

section Saturation

variable {B : Type*} [CommRing B]

/-- The saturation `(𝔞 : g^∞)`: the ideal of the `b` with `g^k b ∈ 𝔞` for some `k`
(Volume 4, Definition 1.1.4 of the handbook). -/
def awaySaturation (𝔞 : Ideal B) (g : B) : Ideal B where
  carrier := {b | ∃ k : ℕ, g ^ k * b ∈ 𝔞}
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have h : g ^ (k + l) * (a + b) = g ^ l * (g ^ k * a) + g ^ k * (g ^ l * b) := by ring
    rw [h]
    exact 𝔞.add_mem (𝔞.mul_mem_left _ hk) (𝔞.mul_mem_left _ hl)
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c b ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact 𝔞.mul_mem_left _ hk

theorem mem_awaySaturation {𝔞 : Ideal B} {g b : B} :
    b ∈ awaySaturation 𝔞 g ↔ ∃ k : ℕ, g ^ k * b ∈ 𝔞 :=
  Iff.rfl

/-- The saturation `(𝔞 : g^∞)` is the kernel of `B → (B/𝔞)_g`. So `Spec (B / (𝔞 : g^∞))` is the
scheme theoretic closure of `D(g) ∩ V(𝔞)` (Volume 4, Definition 1.1.4 of the handbook). -/
theorem mem_awaySaturation_iff_algebraMap_eq_zero {𝔞 : Ideal B} {g b : B} :
    b ∈ awaySaturation 𝔞 g ↔
      algebraMap (B ⧸ 𝔞) (Localization.Away (Ideal.Quotient.mk 𝔞 g))
        (Ideal.Quotient.mk 𝔞 b) = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk 𝔞 g))]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    show Ideal.Quotient.mk 𝔞 g ^ k * Ideal.Quotient.mk 𝔞 b = 0
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hk
  · rintro ⟨⟨_, k, rfl⟩, hk⟩
    refine ⟨k, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
    exact hk

/-- The saturation contains `𝔞` (Volume 4, Definition 1.1.4 of the handbook). -/
theorem le_awaySaturation (𝔞 : Ideal B) (g : B) : 𝔞 ≤ awaySaturation 𝔞 g :=
  fun b hb => ⟨0, by simpa using hb⟩

/-- The element `g` is a nonzerodivisor modulo `(𝔞 : g^∞)` (Volume 4, Definition 1.1.4 of the
handbook). -/
theorem mem_awaySaturation_of_mul_mem {𝔞 : Ideal B} {g b : B}
    (h : g * b ∈ awaySaturation 𝔞 g) : b ∈ awaySaturation 𝔞 g := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [pow_succ, mul_assoc]; exact hk⟩

/-- In a domain, let `x` be prime with `x ∤ F`. If `x^k b = F c`, then `F` divides `b`. -/
theorem dvd_of_pow_mul_eq_mul [IsDomain B] {x F : B} (hx : Prime x) (hF : ¬ x ∣ F) :
    ∀ (k : ℕ) {b c : B}, x ^ k * b = F * c → F ∣ b := by
  intro k
  induction k with
  | zero =>
    intro b c h
    exact ⟨c, by simpa using h⟩
  | succ k ih =>
    intro b c h
    have hxc : x ∣ F * c := ⟨x ^ k * b, by linear_combination -h⟩
    obtain ⟨c', rfl⟩ := (hx.dvd_or_dvd hxc).resolve_left hF
    exact ih (c := c') (mul_left_cancel₀ hx.ne_zero (by linear_combination h))

/-- In a domain, let `x` be prime with `x ∤ F'`. Then `(x^m F' : x^∞) = (F')`. This is the step
in the proof of Volume 4, Lemma 1.1.6 of the handbook: the strict transform of `V(x^m F')` is
`V(F')`. -/
theorem awaySaturation_span_pow_mul_eq_span [IsDomain B] {x F : B} (hx : Prime x)
    (hF : ¬ x ∣ F) (m : ℕ) :
    awaySaturation (Ideal.span {x ^ m * F}) x = Ideal.span {F} := by
  ext b
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hk
    exact Ideal.mem_span_singleton.mpr
      (dvd_of_pow_mul_eq_mul hx hF k (c := c * x ^ m) (by rw [← hc]; ring))
  · intro hb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
    exact ⟨m, Ideal.mem_span_singleton.mpr ⟨c, by ring⟩⟩

end Saturation

section Chart

variable {R : Type*} [CommRing R]

/-- The ideal `(J B : f^∞)` of the strict transform of `V(J)` in the chart `B = R[I/f]`
(Volume 4, Definition 1.1.4 of the handbook and the discussion after it). -/
noncomputable def chartStrictTransform (I J : Ideal R) (f : R) : Ideal (idealChart I f) :=
  awaySaturation (J.map (algebraMap R (idealChart I f))) (algebraMap R (idealChart I f) f)

/-- The ideal of the strict transform in the chart `B = R[I/f]` is `B ∩ J R_f`
(Volume 4, Definition 1.1.4 of the handbook). -/
theorem mem_chartStrictTransform_iff {I J : Ideal R} {f : R} (b : idealChart I f) :
    b ∈ chartStrictTransform I J f ↔
      (b : Localization.Away f) ∈ J.map (algebraMap R (Localization.Away f)) :=
  (coe_mem_map_iff_idealChart b).symm

/-- Over a domain `R` and for `f ≠ 0`, the chart `R[I/f]` is a domain (Volume 4, proof of
Corollary 1.2.5 of the handbook). -/
theorem isDomain_idealChart [IsDomain R] (I : Ideal R) {f : R} (hf : f ≠ 0) :
    IsDomain (idealChart I f) := by
  have : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  infer_instance

/-- Over a domain `R` and for `f ≠ 0`, the map `R → R[I/f]` is injective. So the chart is a ring
between `R` and the function field (Volume 4, proof of Corollary 1.2.5 of the handbook). -/
theorem algebraMap_idealChart_injective [IsDomain R] (I : Ideal R) {f : R} (hf : f ≠ 0) :
    Function.Injective (algebraMap R (idealChart I f)) := by
  intro a b h
  apply IsLocalization.injective (M := Submonoid.powers f) (S := Localization.Away f)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  simpa using congrArg Subtype.val h

end Chart

section Normalization

variable (R : Type*) [CommRing R]

/-- The normalization of an affine integral scheme `Spec R`: the integral closure of `R` in its
fraction field (Volume 4, Definition 1.2.1 of the handbook). -/
abbrev affineNormalization : Subalgebra R (FractionRing R) :=
  integralClosure R (FractionRing R)

/-- The normalization is normal (Volume 4, the remark after Definition 1.2.1 of the
handbook). -/
theorem isIntegrallyClosed_affineNormalization [IsDomain R] :
    IsIntegrallyClosed (affineNormalization R) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)

/-- The normalization of `R` is `R` if and only if `R` is normal (Volume 4, Definition 1.2.1 and
the proof of Corollary 1.2.5 of the handbook). -/
theorem affineNormalization_eq_bot_iff : affineNormalization R = ⊥ ↔ IsIntegrallyClosed R :=
  IsIntegrallyClosed.integralClosure_eq_bot_iff (FractionRing R)

end Normalization

section Rational

/-- In an exact sequence `M → N → P` with `M = 0` and `P = 0`, we have `N = 0`. This is the step
`h_* R^1 g_* O_{Y'} = 0` in the proof of Volume 4, Lemma 2.1.5 of the handbook. -/
theorem subsingleton_of_exact {A M N P : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P] {u : M →ₗ[A] N}
    {v : N →ₗ[A] P} (h : Function.Exact u v) [Subsingleton M] [Subsingleton P] :
    Subsingleton N := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ n : N, n = 0 := by
    intro n
    obtain ⟨m, rfl⟩ := (h n).mp (Subsingleton.elim _ _)
    rw [Subsingleton.elim m 0, map_zero]
  rw [key a, key b]

/-- Let `G y` be a family of groups indexed by the points `y` of a space, and let `W i` be a
cover. If the product of the `G y` over `y ∈ W i` is zero for each `i`, then each `G y` is zero.
For a sheaf supported at finitely many closed points, the sections over `W` are this product.
This is the last step of the proof of Volume 4, Lemma 2.1.5 of the handbook. -/
theorem subsingleton_of_forall_pi_subsingleton {Y ι : Type*} (G : Y → Type*)
    [∀ y, Zero (G y)] (W : ι → Set Y) (hW : ∀ y, ∃ i, y ∈ W i)
    (h : ∀ i, Subsingleton (∀ y : W i, G y)) (y : Y) : Subsingleton (G y) := by
  classical
  obtain ⟨i, hi⟩ := hW y
  refine ⟨fun a b => ?_⟩
  have hab := congrFun (Subsingleton.elim (h := h i)
    (Function.update (0 : ∀ z : W i, G z) ⟨y, hi⟩ a)
    (Function.update (0 : ∀ z : W i, G z) ⟨y, hi⟩ b)) ⟨y, hi⟩
  simpa using hab

/-- A localization `B_Σ` of an integrally closed domain `B` is integrally closed. This is the
step in the proof of Volume 4, Lemma 2.1.8 of the handbook that `Y_x` is normal. -/
theorem isIntegrallyClosed_localization_of_le {B : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] (M : Submonoid B) (hM : M ≤ nonZeroDivisors B) :
    IsIntegrallyClosed (Localization M) :=
  isIntegrallyClosed_of_isLocalization _ M hM

/-- For a prime `P` of `B_Σ`, the local ring of `B_Σ` at `P` is regular if and only if the local
ring of `B` at `P ∩ B` is regular. Thus `Sing(Y_W)` is the inverse image of `Sing(Y)`
(Volume 4, proof of Lemma 2.2.5, part 1 of the handbook). -/
theorem isRegularLocalRing_localization_atPrime_iff {B : Type*} [CommRing B] (M : Submonoid B)
    (P : Ideal (Localization M)) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) ↔
      IsRegularLocalRing (Localization.AtPrime (P.comap (algebraMap B (Localization M)))) := by
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M P
  constructor
  · intro _
    exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm
  · intro _
    exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

end Rational

section Whitney

open MvPolynomial

variable {k : Type*} [CommRing k]

/-- The normalization `ν : k[x, y, z] → k[s, t]` of the Whitney umbrella is finite: `k[s, t]` is
generated by `1` and `t` as a module (Volume 4, Example 2.2.4 of the handbook). -/
theorem whitneyNormalization_finite : (whitneyNormalization k).toRingHom.Finite := by
  classical
  let := (whitneyNormalization k).toRingHom.toAlgebra
  refine ⟨⟨({1, X 1} : Finset (MvPolynomial (Fin 2) k)), eq_top_iff.mpr fun g _ => ?_⟩⟩
  obtain ⟨a, b, rfl⟩ := whitney_exists_eq_add_mul g
  rw [Finset.coe_insert, Finset.coe_singleton, Submodule.mem_span_pair]
  exact ⟨a, b, by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]⟩

/-- Let `P ≤ Q` be primes of `k[s, t]` with the same inverse image under the normalization `ν`
of the Whitney umbrella. Then `P = Q`. So the fibres of `ν` have dimension 0, and no curve of
`A^2` maps to a point (Volume 4, Example 2.2.4 of the handbook). -/
theorem whitneyNormalization_eq_of_comap_eq {P Q : Ideal (MvPolynomial (Fin 2) k)} [P.IsPrime]
    (hPQ : P ≤ Q) (h : P.comap (whitneyNormalization k) = Q.comap (whitneyNormalization k)) :
    P = Q := by
  let := (whitneyNormalization k).toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin 3) k) (MvPolynomial (Fin 2) k) :=
    whitneyNormalization_finite
  by_contra hne
  have hlt := Ideal.IsIntegral.under_lt_under (R := MvPolynomial (Fin 3) k)
    (lt_of_le_of_ne hPQ hne)
  apply hlt.ne
  ext x
  exact SetLike.ext_iff.mp h x

end Whitney

section ProjectiveLine

variable {K : Type*} [Field K]

/-- Let `p ≠ 0` with `deg p ≤ n`. Then the order at `0` of `reflect n p` is `n - deg p`. If
`p = G(1, T)` for a form `G` of degree `n`, then `reflect n p = G(S, 1)`, and this is the order
of `G` at the point `X_0 = 0` (Volume 4, proof of Lemma 2.3.9, part 2 of the handbook). -/
theorem natTrailingDegree_reflect_of_natDegree_le {R : Type*} [Semiring R] {p : R[X]}
    (hp : p ≠ 0) {n : ℕ} (hn : p.natDegree ≤ n) :
    (p.reflect n).natTrailingDegree = n - p.natDegree := by
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [coeff_reflect, revAt_le (Nat.sub_le n _), Nat.sub_sub_self hn]
    exact leadingCoeff_ne_zero.mpr hp
  · apply le_natTrailingDegree (mt reflect_eq_zero_iff.mp hp)
    intro m hm
    rw [coeff_reflect, revAt_le (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Let `G` be a nonzero form of degree `n` in `X_0, X_1`, let `p = G(1, T)` and let `e` be the
order of `G(S, 1) = reflect n p` at `S = 0`. The zero scheme of `G` is `Spec K[T]/(p)` on
`X_0 ≠ 0`, and it is `Spec K[S]/(S^e)` near the point `X_0 = 0`. The sum of their lengths is `n`.
Thus a nonzero section of `O(n)` on `P^1` has `n` zeros counted with length (Volume 4, proof of
Lemma 2.3.9, part 2 of the handbook). -/
theorem finrank_add_finrank_eq_of_natDegree_le {p : K[X]} (hp : p ≠ 0) {n : ℕ}
    (hn : p.natDegree ≤ n) :
    Module.finrank K (K[X] ⧸ Ideal.span {p}) +
      Module.finrank K (K[X] ⧸ Ideal.span {(X : K[X]) ^ (p.reflect n).natTrailingDegree}) =
        n := by
  rw [finrank_quotient_span_eq_natDegree, finrank_quotient_span_eq_natDegree, natDegree_X_pow,
    natTrailingDegree_reflect_of_natDegree_le hp hn]
  omega

end ProjectiveLine

end Singularity
