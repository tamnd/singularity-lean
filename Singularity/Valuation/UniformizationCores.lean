/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.PerronMatrix
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Algebraic cores of results of Volume 5, Chapters 1 to 4

This file proves algebraic cores of several results of Volume 5 of the handbook.

## Section 1.2, the quadratic sequence

* `Singularity.length_ker_eq_length_quotient_range`: for an endomorphism of a module of finite
  length, the kernel and the cokernel have the same length. This is a step of the proof of
  Lemma 1.2.3.
* `Singularity.length_quotient_smul_eq_of_finiteLength`: let `N ⊆ M` be modules, let `h` act
  injectively on `M`, and let `M / N` have finite length. Then `N / hN` and `M / hM` have the
  same length. With `N = C` and `M` the integral closure of `C`, this is the first half of the
  proof of Lemma 1.2.3: `λ(C / hC) = λ(C̄ / hC̄)`.
* `Singularity.natDegree_add_natTrailingDegree_reflect`: for a nonzero polynomial `f` of degree
  at most `b`, the degree of `f` plus the order of `X^b f(1/X)` is `b`. This is the last step of
  the proof of Lemma 1.2.4, with `f = P(1, Y)` and `X^b f(1/X) = P(X, 1)`.
* `Singularity.sum_mul_min_eq_of_branches`: the branch sums of the two charts add up to `b`.
  This is the final count of Lemma 1.2.4.
* `Singularity.noether_inequality_of_branches`: the numerical part of the proof of
  Proposition 1.2.5. From the branch formulas and Lemma 1.2.4 it gives
  `i_{R₁}(f', p') + a b ≤ i_R(f, p)`.

The second half of Lemma 1.2.3 (the Chinese remainder theorem for the branches and the length of
`W / hW` over `C`) and the geometric parts of Lemma 1.2.4 and Proposition 1.2.5 (the charts, the
strict transforms and the branches) are not proved here.

## Section 1.3, étale generators

* `Singularity.valuation_eq_one_of_isAlgebraic`: if a valuation subring `V` of `K` contains `k`,
  then each nonzero element of `K` that is algebraic over `k` has valuation `1`. This is the step
  of the proof of Corollary 1.3.6 that shows that `x` is transcendental over `k`.

Theorem 1.3.5 and the rest of Corollary 1.3.6 are not proved here. They need the henselization,
the defect and the Abhyankar inequality.

## Section 2.3, the Perron algorithm

* `Singularity.Perron.transpose_runMatrix_eq_prod`: the matrix `C = A_lᵀ` of Proposition 2.3.10,
  part 3, is the product of the elementary matrices `1 + E_{ji}` of the steps. The other parts of
  Proposition 2.3.10 are in `Singularity.Valuation.PerronMatrix`, and the algebraic part of
  Corollary 2.3.11 is in `Singularity.Valuation.PerronCoordinates`.

## Section 3.2, Example 3.2.1

* `Singularity.minpoly_eq_X_pow_sub_C_of_pow_eq`, `Singularity.finrank_adjoin_of_pow_eq`: in
  characteristic `p`, if `y^p ∈ F` and `y ∉ F`, then `X^p - y^p` is the minimal polynomial of `y`
  and `[F(y) : F] = p`. With `F = K₀ = k(x, y^p)` this is part 1. With `F = K₀^h` it is the
  degree count of part 3.
* `Singularity.not_isSeparable_of_pow_eq`: such a `y` is not separable over `F`.
* `Singularity.not_mem_of_isSeparable_of_pow_eq`: such a `y` lies in no separable subextension.
  This is the step `y ∉ K₀^h` of part 3.

The model `K = k(x, y)`, the fact `y ∉ k(x, y^p)`, and parts 2 and 4 are not proved here.

## Section 4.2, the open case

* `Singularity.isHomeomorph_comap_integralClosure`: Proposition 4.2.1, the homeomorphism
  part. Let `A` be integrally closed with fraction field `K`, and let `L / K` be purely
  inseparable. Then `Spec B → Spec A` is a homeomorphism for the integral closure `B` of `A`
  in `L`. The finiteness of `B` over `A` is not proved here.
* `Singularity.add_pow_pow_succ_char`: part 1 of Example 4.2.2, `z^p = x^{p+1} + y^{p+1}`.
* `Singularity.surface_relation_mem_sq`: the step of part 4 of Example 4.2.2. The relation
  `Z^p - X^{p+1} - Y^{p+1}` lies in the square of `(X, Y, Z)`.

Parts 2 and 3 of Example 4.2.2 and the conclusion that the point is singular are not proved.
-/

namespace Singularity

open Polynomial
open scoped Pointwise

/-! ### Lemma 1.2.3: lengths -/

section Length

variable {R : Type*} [CommRing R]

/-- **Kernel and cokernel of an endomorphism** (Volume 5, proof of Lemma 1.2.3). For an
endomorphism of a module of finite length, the kernel and the cokernel have the same length. -/
theorem length_ker_eq_length_quotient_range {Q : Type*} [AddCommGroup Q] [Module R Q]
    (hQ : Module.length R Q ≠ ⊤) (f : Q →ₗ[R] Q) :
    Module.length R (LinearMap.ker f) = Module.length R (Q ⧸ LinearMap.range f) := by
  have hex : Function.Exact (LinearMap.ker f).subtype f.rangeRestrict := by
    intro x
    simp [Subtype.ext_iff]
  have h1 := Module.length_eq_add_of_exact _ _ (Submodule.subtype_injective _)
    f.surjective_rangeRestrict hex
  have h2 := Module.length_eq_add_of_exact _ _ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ (LinearMap.range f))
  have hr : Module.length R (LinearMap.range f) ≠ ⊤ := by
    intro h
    rw [h, top_add] at h2
    exact hQ h2
  rw [h1, add_comm] at h2
  exact WithTop.add_left_cancel hr h2

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- **The length of `M / hN`, first count.** Multiplication by `h` gives an exact sequence
`0 → M / N → M / hN → M / hM → 0`. -/
theorem length_quotient_smul_eq_add_left (N : Submodule R M) (h : R) (hreg : IsSMulRegular M h) :
    Module.length R (M ⧸ (h • N)) =
      Module.length R (M ⧸ N) + Module.length R (M ⧸ (h • (⊤ : Submodule R M))) := by
  have hle : N ≤ (h • N).comap (LinearMap.lsmul R M h) := fun x hx =>
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx, rfl⟩
  have hle' : h • N ≤ (h • (⊤ : Submodule R M)).comap LinearMap.id := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨b, trivial, rfl⟩
  refine Module.length_eq_add_of_exact (Submodule.mapQ N (h • N) _ hle)
    (Submodule.mapQ (h • N) (h • ⊤) LinearMap.id hle') ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H m =>
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      obtain ⟨b, hb, hbm⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hq
      have : b = m := hreg hbm
      subst this
      exact (Submodule.Quotient.mk_eq_zero N).2 hb
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H m => exact ⟨Submodule.Quotient.mk m, rfl⟩
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H m =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hm
        obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
        exact ⟨Submodule.Quotient.mk b, rfl⟩
      · rintro ⟨q', hq'⟩
        induction q' using Submodule.Quotient.induction_on with
        | H b =>
          rw [Submodule.mapQ_apply] at hq'
          have := (Submodule.Quotient.eq _).1 hq'
          have hb : h • b ∈ h • (⊤ : Submodule R M) :=
            (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨b, trivial, rfl⟩
          have h2 := Submodule.sub_mem _ hb (hle' this)
          simpa using h2

/-- **The length of `M / hN`, second count.** The inclusion gives an exact sequence
`0 → N / hN → M / hN → M / N → 0`. -/
theorem length_quotient_smul_eq_add_right (N : Submodule R M) (h : R) :
    Module.length R (M ⧸ (h • N)) =
      Module.length R (N ⧸ (h • (⊤ : Submodule R N))) + Module.length R (M ⧸ N) := by
  have hle : h • (⊤ : Submodule R N) ≤ (h • N).comap N.subtype := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨b, b.2, rfl⟩
  have hle' : h • N ≤ N.comap LinearMap.id := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact N.smul_mem h hb
  refine Module.length_eq_add_of_exact (Submodule.mapQ _ (h • N) N.subtype hle)
    (Submodule.mapQ (h • N) N LinearMap.id hle') ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      obtain ⟨b, hb, hbx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hq
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨⟨b, hb⟩, trivial, ?_⟩
      exact Subtype.ext hbx
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H m => exact ⟨Submodule.Quotient.mk m, rfl⟩
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H m =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hm
        exact ⟨Submodule.Quotient.mk ⟨m, hm⟩, rfl⟩
      · rintro ⟨q', hq'⟩
        induction q' using Submodule.Quotient.induction_on with
        | H b =>
          rw [Submodule.mapQ_apply] at hq'
          have := (Submodule.Quotient.eq _).1 hq'
          have h2 := Submodule.sub_mem _ b.2 (hle' this)
          simpa using h2

/-- **The first half of the branch formula** (Volume 5, proof of Lemma 1.2.3). Let `N ⊆ M` be
modules, let `h` act injectively on `M`, and let `M / N` have finite length. Then `N / hN` and
`M / hM` have the same length. For `N = C` and `M = C̄`, this is `λ(C / hC) = λ(C̄ / hC̄)`. -/
theorem length_quotient_smul_eq_of_finiteLength (N : Submodule R M) (h : R)
    (hreg : IsSMulRegular M h) (hfin : Module.length R (M ⧸ N) ≠ ⊤) :
    Module.length R (N ⧸ (h • (⊤ : Submodule R N))) =
      Module.length R (M ⧸ (h • (⊤ : Submodule R M))) := by
  have h1 := length_quotient_smul_eq_add_left N h hreg
  have h2 := length_quotient_smul_eq_add_right N h
  rw [h2, add_comm (Module.length R (M ⧸ N))] at h1
  exact WithTop.add_right_cancel hfin h1

end Length

/-! ### Lemma 1.2.4 and Proposition 1.2.5: the counts -/

section Counts

/-- **Degree and order of a binary form** (Volume 5, proof of Lemma 1.2.4). Let `f` be a nonzero
polynomial of degree at most `b`, and let `g = X^b f(1/X)` be its reflection. Then
`deg f + ord g = b`. For a binary form `P` of degree `b`, take `f = P(1, Y)`, so `g = P(X, 1)`. -/
theorem natDegree_add_natTrailingDegree_reflect {K : Type*} [Semiring K] {f : K[X]} (hf : f ≠ 0)
    {b : ℕ} (hb : f.natDegree ≤ b) : f.natDegree + (reflect b f).natTrailingDegree = b := by
  have hcoeff : (reflect b f).coeff (b - f.natDegree) ≠ 0 := by
    rw [coeff_reflect, revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hb]
    exact leadingCoeff_ne_zero.mpr hf
  have h1 : (reflect b f).natTrailingDegree ≤ b - f.natDegree :=
    natTrailingDegree_le_of_ne_zero hcoeff
  have h2 : b - f.natDegree ≤ (reflect b f).natTrailingDegree := by
    refine le_natTrailingDegree (mt reflect_eq_zero_iff.mp hf) fun m hm => ?_
    rw [coeff_reflect, revAt_le (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  omega

/-- **The final count of Lemma 1.2.4** (Volume 5). Let `s` be the set of branches, and let `I ⊆ s`
be the branches with `v_i(x) ≤ v_i(y)`. If the branches in `I` give `deg P(1, Y)`, and the other
branches give `ord_X P(X, 1)`, then `∑ e_i min(v_i(x), v_i(y)) = b`. -/
theorem sum_mul_min_eq_of_branches {ι K : Type*} [DecidableEq ι] [Semiring K] (s I : Finset ι)
    (hI : I ⊆ s) (e vx vy : ι → ℕ) (hIv : ∀ i ∈ I, vx i ≤ vy i) (hJv : ∀ i ∈ s, i ∉ I → vy i ≤ vx i)
    {P : K[X]} (hP : P ≠ 0) {b : ℕ} (hb : P.natDegree ≤ b)
    (hIsum : ∑ i ∈ I, e i * vx i = P.natDegree)
    (hJsum : ∑ i ∈ s \ I, e i * vy i = (reflect b P).natTrailingDegree) :
    ∑ i ∈ s, e i * min (vx i) (vy i) = b := by
  rw [← Finset.sum_sdiff hI, ← natDegree_add_natTrailingDegree_reflect hP hb, ← hIsum, ← hJsum,
    add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [min_eq_left (hIv i hi)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_sdiff] at hi
    rw [min_eq_right (hJv i hi.1 hi.2)]

/-- **The numerical part of the inequality of Noether** (Volume 5, proof of Proposition 1.2.5).
Let `s` be the branches of `C = R/pR`, with weights `e_i = [κ_i : κ]`. Let `I ⊆ s` be the branches
with `v_i(x) ≤ v_i(y)`, and let `T ⊆ I` be the branches over the point of `R₁`, with weights
`e'_i = [κ_i : κ(𝔫)]` and `e_i = d_i e'_i`. Assume the branch formula
`i_R(f, p) = ∑_s e_i v_i(f)`, Lemma 1.2.4, the bounds `v_i(f) = a v_i(x) + v_i(f')` on `I` and
`v_i(f) ≥ a v_i(y)` off `I`, and the branch formula `i_{R₁}(f', p') = ∑_T e'_i v_i(f')`.
Then `i_{R₁}(f', p') + a b ≤ i_R(f, p)`. -/
theorem noether_inequality_of_branches {ι : Type*} [DecidableEq ι] (s I T : Finset ι)
    (hI : I ⊆ s) (hT : T ⊆ I) (e e' d vx vy vf vf' : ι → ℕ) (a b iR iR₁ : ℕ)
    (hiR : iR = ∑ i ∈ s, e i * vf i) (hiR₁ : iR₁ = ∑ i ∈ T, e' i * vf' i)
    (hb : ∑ i ∈ s, e i * min (vx i) (vy i) = b)
    (hIv : ∀ i ∈ I, vx i ≤ vy i) (hIf : ∀ i ∈ I, vf i = a * vx i + vf' i)
    (hJ : ∀ i ∈ s, i ∉ I → vy i ≤ vx i ∧ a * vy i ≤ vf i)
    (he : ∀ i ∈ T, e i = d i * e' i) (hd : ∀ i ∈ T, 1 ≤ d i) :
    iR₁ + a * b ≤ iR := by
  subst hiR hiR₁ hb
  rw [← Finset.sum_sdiff hI, ← Finset.sum_sdiff hI, mul_add]
  have hT' : ∑ i ∈ T, e' i * vf' i ≤ ∑ i ∈ I, e i * vf' i := by
    calc ∑ i ∈ T, e' i * vf' i ≤ ∑ i ∈ T, e i * vf' i := by
          refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_right _ ?_
          rw [he i hi]
          exact Nat.le_mul_of_pos_left _ (hd i hi)
      _ ≤ ∑ i ∈ I, e i * vf' i := Finset.sum_le_sum_of_subset hT
  have hIeq : a * ∑ i ∈ I, e i * min (vx i) (vy i) + ∑ i ∈ I, e i * vf' i =
      ∑ i ∈ I, e i * vf i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [min_eq_left (hIv i hi), hIf i hi]
    ring
  have hJle : a * ∑ i ∈ s \ I, e i * min (vx i) (vy i) ≤ ∑ i ∈ s \ I, e i * vf i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_sdiff] at hi
    obtain ⟨h1, h2⟩ := hJ i hi.1 hi.2
    rw [min_eq_right h1]
    calc a * (e i * vy i) = e i * (a * vy i) := by ring
      _ ≤ e i * vf i := Nat.mul_le_mul_left _ h2
  omega

end Counts

/-! ### Corollary 1.3.6: algebraic elements have value zero -/

/-- **Algebraic elements are units of the valuation ring** (Volume 5, proof of Corollary 1.3.6).
Let `V` be a valuation subring of `K` that contains `k`. Then each nonzero element of `K` that is
algebraic over `k` has valuation `1`. So an element of nonzero value is transcendental over `k`. -/
theorem valuation_eq_one_of_isAlgebraic {k K : Type*} [Field k] [Field K] [Algebra k K]
    (V : ValuationSubring K) (hk : ∀ c : k, algebraMap k K c ∈ V) {x : K} (hx : IsAlgebraic k x)
    (hx0 : x ≠ 0) : V.valuation x = 1 := by
  set v := V.valuation
  have hint : ∀ y : K, IsAlgebraic k y → v y ≤ 1 := by
    intro y hy
    obtain ⟨p, hpm, hp⟩ := hy.isIntegral
    let f : k →+* v.integer := (algebraMap k K).codRestrict v.integer fun c =>
      (Valuation.mem_integer_iff _ _).2 ((V.valuation_le_one_iff _).2 (hk c))
    have hcomp : (algebraMap v.integer K).comp f = algebraMap k K := by
      ext c
      rfl
    have hyint : IsIntegral v.integer y := ⟨p.map f, hpm.map f, by rw [eval₂_map, hcomp]; exact hp⟩
    exact (Valuation.integer.integers v).mem_of_integral hyint
  have h1 := hint x hx
  have h2 := hint x⁻¹ hx.inv
  rw [map_inv₀] at h2
  have hpos : 0 < v x := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).2 hx0
  refine le_antisymm h1 ?_
  calc (1 : _) = v x * (v x)⁻¹ := (mul_inv_cancel₀ hpos.ne').symm
    _ ≤ v x * 1 := by gcongr
    _ = v x := mul_one _

/-! ### Example 3.2.1: an inseparable extension of degree `p` -/

section Inseparable

open IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (p : ℕ) [hp : Fact p.Prime]

/-- **The minimal polynomial of a `p`-th root** (Volume 5, Example 3.2.1, part 1). In
characteristic `p`, let `y^p = c ∈ F` with `y ∉ F`. Then `X^p - c` is the minimal polynomial of
`y` over `F`. -/
theorem minpoly_eq_X_pow_sub_C_of_pow_eq [CharP E p] {y : E} {c : F}
    (hc : algebraMap F E c = y ^ p) (hy : y ∉ (algebraMap F E).range) :
    minpoly F y = X ^ p - C c := by
  have hirr : Irreducible (X ^ p - C c) := by
    refine X_pow_sub_C_irreducible_of_prime hp.out fun b hb => hy ⟨b, ?_⟩
    apply frobenius_inj E p
    simp only [frobenius_def, ← map_pow, hb, hc]
  exact (minpoly.eq_of_irreducible_of_monic hirr (by simp [hc])
    (monic_X_pow_sub_C c hp.out.ne_zero)).symm

/-- **The degree of a `p`-th root** (Volume 5, Example 3.2.1, parts 1 and 3). In characteristic
`p`, let `y^p ∈ F` with `y ∉ F`. Then `[F(y) : F] = p`. -/
theorem finrank_adjoin_of_pow_eq [CharP E p] {y : E} {c : F}
    (hc : algebraMap F E c = y ^ p) (hy : y ∉ (algebraMap F E).range) :
    Module.finrank F F⟮y⟯ = p := by
  have hint : IsIntegral F y :=
    ⟨X ^ p - C c, monic_X_pow_sub_C c hp.out.ne_zero, by simp [eval₂_eq_eval_map, hc]⟩
  rw [IntermediateField.adjoin.finrank hint, minpoly_eq_X_pow_sub_C_of_pow_eq p hc hy,
    natDegree_X_pow_sub_C]

/-- **A `p`-th root is not separable** (Volume 5, Example 3.2.1, part 3). In characteristic `p`,
let `y^p ∈ F` with `y ∉ F`. Then `y` is not separable over `F`. -/
theorem not_isSeparable_of_pow_eq [CharP F p] [CharP E p] {y : E} {c : F}
    (hc : algebraMap F E c = y ^ p) (hy : y ∉ (algebraMap F E).range) : ¬ IsSeparable F y := by
  intro hsep
  have hsep' : (X ^ p - C c).Separable := by
    rw [← minpoly_eq_X_pow_sub_C_of_pow_eq p hc hy]
    exact hsep
  have hder : derivative (X ^ p - C c : F[X]) = 0 := by
    simp [derivative_X_pow, CharP.cast_eq_zero]
  rw [Polynomial.Separable, hder, isCoprime_zero_right] at hsep'
  have := natDegree_eq_zero_of_isUnit hsep'
  rw [natDegree_X_pow_sub_C] at this
  exact hp.out.ne_zero this

/-- **A `p`-th root lies in no separable subextension** (Volume 5, Example 3.2.1, part 3). In
characteristic `p`, let `y^p ∈ F` with `y ∉ F`, and let `F'` be a separable intermediate field.
Then `y ∉ F'`. With `F = K₀` and `F'` the henselization, this is `y ∉ K₀^h`. -/
theorem not_mem_of_isSeparable_of_pow_eq [CharP F p] [CharP E p] {y : E} {c : F}
    (hc : algebraMap F E c = y ^ p) (hy : y ∉ (algebraMap F E).range)
    (F' : IntermediateField F E) [Algebra.IsSeparable F F'] : y ∉ F' := by
  intro hyF
  apply not_isSeparable_of_pow_eq p hc hy
  have h := Algebra.IsSeparable.isSeparable F (⟨y, hyF⟩ : F')
  show (minpoly F y).Separable
  have hm : minpoly F (algebraMap F' E ⟨y, hyF⟩) = minpoly F (⟨y, hyF⟩ : F') :=
    minpoly.algebraMap_eq (algebraMap F' E).injective _
  rw [show y = algebraMap F' E ⟨y, hyF⟩ from rfl, hm]
  exact h

end Inseparable

/-! ### Proposition 4.2.1 and Example 4.2.2 -/

section OpenCase

/-- **Purely inseparable normalization is a homeomorphism** (Volume 5, Proposition 4.2.1, the
homeomorphism part). Let `A` be an integrally closed domain with fraction field `K`, let `L / K`
be purely inseparable of exponential characteristic `q`, and let `B` be the integral closure of
`A` in `L`. Then `Spec B → Spec A` is a homeomorphism. -/
theorem isHomeomorph_comap_integralClosure {A K L : Type*} [CommRing A] [IsDomain A] [Field K]
    [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsIntegrallyClosed A] (q : ℕ) [ExpChar K q]
    [IsPurelyInseparable K L] :
    IsHomeomorph (PrimeSpectrum.comap (algebraMap A (integralClosure A L))) := by
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  refine PrimeSpectrum.isHomeomorph_comap _ (fun b => ?_) ?_
  · obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem K q (b : L)
    have hb : IsIntegral A ((b : L) ^ q ^ n) := b.2.pow _
    rw [← hc] at hb
    have hcint : IsIntegral A c :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L) (algebraMap K L).injective).1 hb
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hcint
    refine ⟨q ^ n, pow_pos (expChar_pos K q) n, a, Subtype.ext ?_⟩
    rw [← IsScalarTower.algebraMap_apply A K L] at hc
    simpa using hc
  · intro a ha
    rw [RingHom.mem_ker] at ha
    have : algebraMap A L a = 0 := congrArg Subtype.val ha
    rw [hinj (this.trans (map_zero _).symm)]
    exact zero_mem _

/-- **The equation of the surface** (Volume 5, Example 4.2.2, part 1). In characteristic `p`,
`(a^{p+1} + b^{p+1})^p = (a^p)^{p+1} + (b^p)^{p+1}`. So `z^p = x^{p+1} + y^{p+1}`. -/
theorem add_pow_pow_succ_char {S : Type*} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    (a b : S) : (a ^ (p + 1) + b ^ (p + 1)) ^ p = (a ^ p) ^ (p + 1) + (b ^ p) ^ (p + 1) := by
  rw [add_pow_char, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm (p + 1) p]

/-- **The relation lies in the square of the maximal ideal** (Volume 5, Example 4.2.2, part 4).
For `p ≥ 2`, the polynomial `Z^p - X^{p+1} - Y^{p+1}` lies in `(X, Y, Z)^2`. So the cotangent
space of the surface at the origin has dimension 3. -/
theorem surface_relation_mem_sq (k : Type*) [CommRing k] {p : ℕ} (hp : 2 ≤ p) :
    (MvPolynomial.X 2 ^ p - MvPolynomial.X 0 ^ (p + 1) - MvPolynomial.X 1 ^ (p + 1) :
      MvPolynomial (Fin 3) k) ∈
      Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2} ^ 2 := by
  set I : Ideal (MvPolynomial (Fin 3) k) :=
    Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2}
  have hX : ∀ i : Fin 3, (MvPolynomial.X i : MvPolynomial (Fin 3) k) ∈ I := by
    intro i
    fin_cases i <;> exact Ideal.subset_span (by simp)
  have hpow : ∀ (i : Fin 3) (n : ℕ), 2 ≤ n →
      (MvPolynomial.X i : MvPolynomial (Fin 3) k) ^ n ∈ I ^ 2 := by
    intro i n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, pow_two, pow_two]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (hX i) (hX i))
  exact Ideal.sub_mem _ (Ideal.sub_mem _ (hpow 2 p hp) (hpow 0 _ (by omega)))
    (hpow 1 _ (by omega))

end OpenCase

end Singularity

/-! ### Proposition 2.3.10: the transpose of the matrix of a run -/

namespace Singularity.Perron

open Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- **The transpose is a product of elementary matrices** (Volume 5, Proposition 2.3.10,
part 3). For a run `l = (s_1, …, s_m)`, `A_lᵀ = A_{s_1}ᵀ ⋯ A_{s_m}ᵀ`, and `A_sᵀ = 1 + E_{ji}`
for `s = (i, j)`. So the matrix `C = A_lᵀ` of the lattice lemma is a product of matrices
`1 + E_{ji}`, in the order of the run. -/
theorem transpose_runMatrix_eq_prod (l : List (ι × ι)) :
    (runMatrix l)ᵀ = (l.map fun s => transvection s.2 s.1 (1 : ℤ)).prod := by
  induction l with
  | nil => simp [runMatrix]
  | cons s l ih =>
    rw [runMatrix, transpose_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    simp [stepMatrix, transvection, transpose_add, transpose_single]

end Singularity.Perron
