/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.FrobeniusNewton
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# The Frobenius-Newton criterion for `z^p + g`, weight form

Let `K` be a field of characteristic `p`, let `g ∈ K[x_σ]` with `g ≠ 0` and `g(0) = 0`, and let
`f = z^p + g` (`purelyInseparable p g`). This file proves Theorem 5.3 of research note 05 in the
weight form of Theorem 2.8 of research note 55, as corrected by research note 60. If `K` is
perfect, then `f` is Newton nondegenerate over `K` if and only if no initial form `in_w g` with
`w > 0` has a critical point in the torus `(K^*)^σ`
(`newtonNondegenerate_purelyInseparable_iff`).

Newton nondegenerate over `K` (`NewtonNondegenerate`, Definition 2.1 of note 55) means: for each
weight `W` with `W_i > 0` for each `i`, the initial form `in_W F` has no singular point in the
torus `(K^*)^τ`. The definition uses weights and not the compact faces of the Newton polyhedron.
For `K` algebraically closed, Lemma 2.2 of note 55 identifies the initial forms `in_W F` with the
initial forms `F_Δ` of the compact faces `Δ`, and the theorem is then Theorem 5.3 of note 05.
Lemma 2.2 is not formalized here.

The proof follows Section 2 of note 55.

* For `W` on `Option σ`, put `w = W ∘ some`, `c = W none` and `m = m_w(g)`. Then `in_W f` is `z^p`
  if `p c < m`, `in_w g` if `p c > m`, and `z^p + in_w g` if `p c = m`
  (`initialForm_purelyInseparable_of_lt`, `initialForm_purelyInseparable_of_gt`,
  `initialForm_purelyInseparable_of_eq`, Lemma 2.3 of note 55). The proof uses
  `initialForm_rename` (the initial form of `g` with the variables renamed) and two facts on the
  initial form of a sum.
* `in_{n w} g = in_w g` and `m_{n w}(g) = n m_w(g)` for `n ≠ 0` (`initialForm_nsmul`,
  `toNat_weightedOrd_nsmul`), and `m_w(g) ≥ 1` if `w > 0` and `g(0) = 0` (`one_le_weightedOrd`).
  This is Lemma 2.7 of note 55.
* `(z, v)` is a singular point of `g` seen in `K[z, x]` if and only if `v` is a singular point of
  `g` (`isSingularPoint_rename_some_iff`, Lemma 2.5 of note 55).

For the converse, a torus critical point `v` of `in_w g` gives the weight `W = (w, m + 1)` if
`in_w g (v) = 0`, and the weight `W = (p w, m)` if `in_w g (v) ≠ 0`. In the second case the
`p`-th root of `-in_w g (v)` gives the `z` coordinate. This is the only place where the theorem
uses that `K` is perfect.

The hypothesis that `K` is perfect cannot be dropped. Over `K = F_p(t)`, the polynomial
`z^p + t x^p` is Newton nondegenerate, but each point of the torus is a critical point of the
initial form `t x^p` (`newtonNondegenerate_ratFunc_example`, the remark of note 60 on Section 2
of note 55). The general form is `newtonNondegenerate_purelyInseparable_monomial`: if `a ≠ 0` and
`-a` is not a `p`-th power in `K`, then `z^p + a x^p` is Newton nondegenerate.

## Main definitions

* `Singularity.NewtonNondegenerate F`: no initial form `in_W F` with `W > 0` has a singular point
  in the torus.

## Main results

* `newtonNondegenerate_purelyInseparable_iff`: Theorem 5.3 of research note 05, weight form, over
  a perfect field (Theorem 2.8 of research note 55).
* `initialForm_purelyInseparable_of_lt`, `initialForm_purelyInseparable_of_gt`,
  `initialForm_purelyInseparable_of_eq`: the initial forms of `z^p + g` (Lemma 2.3 of note 55).
* `weightedOrd_rename`, `initialForm_rename`: the weighted order and the initial form after an
  injective renaming of the variables.
* `initialForm_nsmul`, `toNat_weightedOrd_nsmul`, `one_le_weightedOrd`: Lemma 2.7 of note 55.
* `isSingularPoint_rename_some_iff`: Lemma 2.5 of note 55.
* `newtonNondegenerate_purelyInseparable_monomial`, `newtonNondegenerate_ratFunc_example`: the
  theorem is false over the field `F_p(t)`, which is not perfect.

## References

* A. N. Varchenko, *Zeta-function of monodromy and Newton's diagram*, Invent. Math. 37 (1976).
* A. G. Khovanskii, *Newton polyhedra and toroidal varieties*, Funct. Anal. Appl. 11 (1977).
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### Weighted orders and initial forms -/

section Weights

variable {σ τ R : Type*} [CommSemiring R]

@[simp]
theorem weightedOrd_zero (w : σ → ℕ) : weightedOrd w (0 : MvPolynomial σ R) = ⊤ :=
  weightedOrd_eq_top_iff.mpr rfl

/-- A lower bound for the weighted order: each monomial of weight less than `n` has the
coefficient `0`. -/
theorem le_weightedOrd {w : σ → ℕ} {f : MvPolynomial σ R} {n : ℕ∞}
    (h : ∀ d : σ →₀ ℕ, (weight w d : ℕ∞) < n → f.coeff d = 0) : n ≤ weightedOrd w f :=
  MvPowerSeries.le_weightedOrder w fun d hd => by rw [coeff_coe]; exact h d hd

theorem weight_mapDomain {f : σ → τ} (W : τ → ℕ) (d : σ →₀ ℕ) :
    weight W (d.mapDomain f) = weight (W ∘ f) d := by
  rw [weight_apply, weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • W i) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)]
  rfl

/-- The weighted order does not change under an injective renaming of the variables. -/
theorem weightedOrd_rename {f : σ → τ} (hf : Function.Injective f) (W : τ → ℕ)
    (g : MvPolynomial σ R) : weightedOrd W (rename f g) = weightedOrd (W ∘ f) g := by
  refine le_antisymm (le_weightedOrd fun d hd => ?_) (le_weightedOrd fun b hb => ?_)
  · rw [← coeff_rename_mapDomain f hf g d]
    exact coeff_eq_zero_of_lt_weightedOrd (w := W) (by rwa [weight_mapDomain])
  · refine coeff_rename_eq_zero f g b fun u hu => ?_
    subst hu
    exact coeff_eq_zero_of_lt_weightedOrd (w := W ∘ f) (by rwa [← weight_mapDomain])

/-- The initial form commutes with an injective renaming of the variables. -/
theorem initialForm_rename {f : σ → τ} (hf : Function.Injective f) (W : τ → ℕ)
    (g : MvPolynomial σ R) : initialForm W (rename f g) = rename f (initialForm (W ∘ f) g) := by
  ext b
  by_cases hb : ∃ d : σ →₀ ℕ, d.mapDomain f = b
  · obtain ⟨d, rfl⟩ := hb
    rw [coeff_initialForm, coeff_rename_mapDomain f hf, coeff_rename_mapDomain f hf,
      coeff_initialForm, weight_mapDomain, weightedOrd_rename hf]
  · push Not at hb
    rw [coeff_initialForm, coeff_rename_eq_zero f g b fun u hu => absurd hu (hb u),
      coeff_rename_eq_zero f _ b fun u hu => absurd hu (hb u), ite_self]

/-- A weighted homogeneous `P ≠ 0` of degree `n` has the weighted order `n`. -/
theorem weightedOrd_of_isWeightedHomogeneous {w : σ → ℕ} {P : MvPolynomial σ R} {n : ℕ}
    (hP : IsWeightedHomogeneous w P n) (hP0 : P ≠ 0) : weightedOrd w P = n := by
  refine le_antisymm ?_ (le_weightedOrd fun d hd => ?_)
  · obtain ⟨d, hd⟩ := support_nonempty.mpr hP0
    have hd' := MvPolynomial.mem_support_iff.mp hd
    exact (weightedOrd_le hd').trans_eq (by rw [hP hd'])
  · by_contra h
    rw [hP h] at hd
    exact lt_irrefl _ hd

/-- A weighted homogeneous `P ≠ 0` is its own initial form. -/
theorem initialForm_of_isWeightedHomogeneous {w : σ → ℕ} {P : MvPolynomial σ R} {n : ℕ}
    (hP : IsWeightedHomogeneous w P n) (hP0 : P ≠ 0) : initialForm w P = P := by
  simpa using initialForm_add_of_lt hP hP0 (Q := 0) (by simp)

theorem isWeightedHomogeneous_X_pow (W : τ → ℕ) (i : τ) (n : ℕ) :
    IsWeightedHomogeneous W (X i ^ n : MvPolynomial τ R) (n * W i) := by
  rw [X_pow_eq_monomial]
  exact isWeightedHomogeneous_monomial W _ _ (by rw [weight_single, smul_eq_mul])

/-- If `P` has a smaller weighted order than `Q`, then `P + Q` and `P` have the same initial
form. -/
theorem initialForm_add_of_weightedOrd_lt {w : σ → ℕ} {P Q : MvPolynomial σ R}
    (h : weightedOrd w P < weightedOrd w Q) : initialForm w (P + Q) = initialForm w P := by
  have hord : weightedOrd w (P + Q) = weightedOrd w P := by
    rw [weightedOrd, MvPolynomial.coe_add, MvPowerSeries.weightedOrder_add_of_weightedOrder_ne]
    · exact min_eq_left h.le
    · exact h.ne
  ext d
  rw [coeff_initialForm, coeff_initialForm, hord, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  split_ifs with hd
  · rw [coeff_eq_zero_of_lt_weightedOrd (f := Q) (w := w) ?_, add_zero]
    rw [hd, ENat.natCast_toNat h.ne_top]
    exact h
  · rfl

/-- If `P` and `Q` have the same weighted order and no common monomial, then the initial form of
`P + Q` is the sum of the initial forms. -/
theorem initialForm_add_of_disjoint {w : σ → ℕ} {P Q : MvPolynomial σ R}
    (h : weightedOrd w P = weightedOrd w Q) (hPQ : ∀ d, P.coeff d = 0 ∨ Q.coeff d = 0) :
    initialForm w (P + Q) = initialForm w P + initialForm w Q := by
  have hord : weightedOrd w (P + Q) = weightedOrd w P := by
    refine le_antisymm ?_ (le_weightedOrd fun d hd => ?_)
    · rcases eq_or_ne P 0 with rfl | hP
      · rw [weightedOrd_zero]
        exact le_top
      · obtain ⟨d, hd, hdeg⟩ := exists_coeff_ne_zero_and_weightedOrd_eq w hP
        rw [hdeg]
        refine weightedOrd_le ?_
        rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, (hPQ d).resolve_left hd, add_zero]
        exact hd
    · rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_eq_zero_of_lt_weightedOrd hd,
        coeff_eq_zero_of_lt_weightedOrd (lt_of_lt_of_eq hd h), add_zero]
  ext d
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_initialForm, coeff_initialForm,
    coeff_initialForm, hord, ← h, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  split_ifs <;> simp

/-- The weight of `d` for `n • w` is `n` times the weight of `d` for `w`. -/
theorem weight_nsmul (n : ℕ) (w : σ → ℕ) (d : σ →₀ ℕ) : weight (n • w) d = n * weight w d := by
  simp only [weight_apply, Finsupp.sum, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Lemma 2.7(a) of research note 55: `m_{n w}(g) = n m_w(g)`. -/
theorem toNat_weightedOrd_nsmul (n : ℕ) (w : σ → ℕ) (g : MvPolynomial σ R) :
    (weightedOrd (n • w) g).toNat = n * (weightedOrd w g).toNat := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  obtain ⟨d, hd, hdeg⟩ := exists_coeff_ne_zero_and_weightedOrd_eq w hg
  rw [hdeg, ENat.toNat_natCast]
  suffices h : weightedOrd (n • w) g = ((n * weight w d : ℕ) : ℕ∞) by
    rw [h, ENat.toNat_natCast]
  refine le_antisymm ((weightedOrd_le (w := n • w) hd).trans_eq (by rw [weight_nsmul]))
    (le_weightedOrd fun e he => ?_)
  rw [weight_nsmul, Nat.cast_lt] at he
  exact coeff_eq_zero_of_lt_weightedOrd (w := w)
    (by rw [hdeg, Nat.cast_lt]; exact Nat.lt_of_mul_lt_mul_left he)

/-- Lemma 2.7(a) of research note 55 in `ℕ∞`: `m_{n w}(g) = n m_w(g)` for `g ≠ 0`. -/
theorem weightedOrd_nsmul (n : ℕ) (w : σ → ℕ) {g : MvPolynomial σ R} (hg : g ≠ 0) :
    weightedOrd (n • w) g = n * weightedOrd w g := by
  rw [← ENat.natCast_toNat (fun h => hg (weightedOrd_eq_top_iff.mp h)),
    ← ENat.natCast_toNat (n := weightedOrd w g) (fun h => hg (weightedOrd_eq_top_iff.mp h)),
    toNat_weightedOrd_nsmul, Nat.cast_mul]

/-- Lemma 2.7(a) of research note 55: `in_{n w} g = in_w g` for `n ≠ 0`. -/
theorem initialForm_nsmul {n : ℕ} (hn : n ≠ 0) (w : σ → ℕ) (g : MvPolynomial σ R) :
    initialForm (n • w) g = initialForm w g := by
  ext d
  rw [coeff_initialForm, coeff_initialForm, weight_nsmul, toNat_weightedOrd_nsmul]
  exact if_congr (Nat.mul_left_cancel_iff (Nat.pos_of_ne_zero hn)) rfl rfl

/-- Lemma 2.7(b) of research note 55: if `w_i > 0` for each `i` and `g(0) = 0`, then
`m_w(g) ≥ 1`. -/
theorem one_le_weightedOrd {w : σ → ℕ} (hw : ∀ i, 0 < w i) {g : MvPolynomial σ R}
    (hg0 : constantCoeff g = 0) : 1 ≤ weightedOrd w g := by
  refine le_weightedOrd fun d hd => ?_
  have hd0 : d = 0 := by
    by_contra hd0
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
    have h1 := le_weight_of_ne_zero' w (Finsupp.mem_support_iff.mp hi)
    have h2 : weight w d < 1 := by exact_mod_cast hd
    have h3 := hw i
    omega
  rw [hd0]
  exact hg0

theorem one_le_toNat_weightedOrd {w : σ → ℕ} (hw : ∀ i, 0 < w i) {g : MvPolynomial σ R}
    (hg : g ≠ 0) (hg0 : constantCoeff g = 0) : 1 ≤ (weightedOrd w g).toNat := by
  have h := one_le_weightedOrd hw hg0
  rw [← ENat.natCast_toNat (fun h' => hg (weightedOrd_eq_top_iff.mp h'))] at h
  exact_mod_cast h

end Weights

/-! ### The initial forms of `z^p + g` -/

section InitialForm

variable {σ K : Type*} [CommSemiring K] [Nontrivial K] (p : ℕ)

theorem X_pow_ne_zero (i : σ) : (X i ^ p : MvPolynomial σ K) ≠ 0 := by
  rw [X_pow_eq_monomial, Ne, monomial_eq_zero]
  exact one_ne_zero

omit [Nontrivial K] in
theorem weightedOrd_rename_some (W : Option σ → ℕ) {g : MvPolynomial σ K} (hg : g ≠ 0) :
    weightedOrd W (rename Option.some g) = ((weightedOrd (W ∘ Option.some) g).toNat : ℕ∞) := by
  rw [weightedOrd_rename (Option.some_injective σ),
    ENat.natCast_toNat (fun h => hg (weightedOrd_eq_top_iff.mp h))]

omit [Nontrivial K] in
/-- The initial form commutes with the inclusion `K[x] → K[z, x]`. -/
theorem initialForm_rename_some (W : Option σ → ℕ) (g : MvPolynomial σ K) :
    initialForm W (rename Option.some g) = rename Option.some (initialForm (W ∘ Option.some) g) :=
  initialForm_rename (Option.some_injective σ) W g

/-- Lemma 2.3(a) of research note 55: if `p W(z) < m_w(g)`, then `in_W(z^p + g) = z^p`. -/
theorem initialForm_purelyInseparable_of_lt (W : Option σ → ℕ) {g : MvPolynomial σ K}
    (hg : g ≠ 0) (h : p * W none < (weightedOrd (W ∘ Option.some) g).toNat) :
    initialForm W (purelyInseparable p g) = X none ^ p := by
  rw [purelyInseparable]
  exact initialForm_add_of_lt (isWeightedHomogeneous_X_pow W none p) (X_pow_ne_zero p none)
    (by rw [weightedOrd_rename_some W hg]; exact_mod_cast h)

/-- Lemma 2.3(b) of research note 55: if `p W(z) > m_w(g)`, then `in_W(z^p + g) = in_w g`, with
`w = W ∘ some`. -/
theorem initialForm_purelyInseparable_of_gt (W : Option σ → ℕ) {g : MvPolynomial σ K}
    (hg : g ≠ 0) (h : (weightedOrd (W ∘ Option.some) g).toNat < p * W none) :
    initialForm W (purelyInseparable p g) =
      rename Option.some (initialForm (W ∘ Option.some) g) := by
  rw [purelyInseparable, add_comm, initialForm_add_of_weightedOrd_lt,
    initialForm_rename (Option.some_injective σ)]
  rw [weightedOrd_rename_some W hg,
    weightedOrd_of_isWeightedHomogeneous (isWeightedHomogeneous_X_pow W none p)
      (X_pow_ne_zero p none)]
  exact_mod_cast h

/-- Lemma 2.3(c) of research note 55: if `p W(z) = m_w(g)`, then `in_W(z^p + g) = z^p + in_w g`,
with `w = W ∘ some`. -/
theorem initialForm_purelyInseparable_of_eq (W : Option σ → ℕ) {g : MvPolynomial σ K}
    (hg : g ≠ 0) (hp : p ≠ 0) (h : p * W none = (weightedOrd (W ∘ Option.some) g).toNat) :
    initialForm W (purelyInseparable p g) =
      purelyInseparable p (initialForm (W ∘ Option.some) g) := by
  have hX := isWeightedHomogeneous_X_pow (R := K) W none p
  rw [purelyInseparable, initialForm_add_of_disjoint, initialForm_of_isWeightedHomogeneous hX
    (X_pow_ne_zero p none), initialForm_rename (Option.some_injective σ), purelyInseparable]
  · rw [weightedOrd_rename_some W hg, weightedOrd_of_isWeightedHomogeneous hX
      (X_pow_ne_zero p none), h]
  · intro b
    by_cases hb : b = single none p
    · right
      refine coeff_rename_eq_zero _ _ _ fun u hu => ?_
      exfalso
      have h0 : u.mapDomain Option.some none = b none := by rw [hu]
      rw [mapDomain_of_notMem_range _ _ fun ⟨i, hi⟩ => Option.some_ne_none i hi, hb,
        single_eq_same] at h0
      exact hp h0.symm
    · left
      classical
      rw [X_pow_eq_monomial, coeff_monomial, ite_eq_right_iff.mpr fun h' => absurd h'.symm hb]

end InitialForm

/-! ### Newton nondegeneracy -/

section Nondegenerate

variable {σ K : Type*} [CommSemiring K]

/-- A polynomial `F` is Newton nondegenerate over `K` if, for each weight `W` with `W_i > 0` for
each `i`, the initial form `in_W F` has no singular point in the torus `(K^*)^τ`. This is
Definition 2.1 of research note 55. Over an algebraically closed field it is Definition 5.1 of
research note 05, by Lemma 2.2 of note 55. -/
def NewtonNondegenerate {τ : Type*} (F : MvPolynomial τ K) : Prop :=
  ∀ W : τ → ℕ, (∀ i, 0 < W i) → ∀ u : τ → K, (∀ i, u i ≠ 0) →
    ¬ IsSingularPoint (initialForm W F) u

/-- Lemma 2.5 of research note 55: `(z, v)` is a singular point of `h` seen in `K[z, x]` if and
only if `v` is a singular point of `h`. -/
theorem isSingularPoint_rename_some_iff (h : MvPolynomial σ K) (z : K) (v : σ → K) :
    IsSingularPoint (rename Option.some h) (fun o => Option.elim o z v) ↔
      IsSingularPoint h v := by
  rw [IsSingularPoint, IsSingularPoint, IsCriticalPoint, IsCriticalPoint, Option.forall,
    pderiv_none_rename, map_zero, eval_rename]
  simp only [pderiv_rename (Option.some_injective σ), eval_rename, true_and]
  rfl

end Nondegenerate

/-! ### The criterion -/

section Criterion

variable {σ K : Type*} [CommRing K] [IsReduced K] [Nontrivial K] (p : ℕ) [Fact p.Prime]
  [CharP K p]

/-- The direction from right to left of Theorem 5.3 of research note 05. It holds without the
hypothesis that `K` is perfect, and without the hypothesis `g(0) = 0`. -/
theorem newtonNondegenerate_purelyInseparable_of_forall {g : MvPolynomial σ K} (hg : g ≠ 0)
    (hC : ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ v : σ → K, (∀ i, v i ≠ 0) →
      ¬ IsCriticalPoint (initialForm w g) v) :
    NewtonNondegenerate (purelyInseparable p g) := by
  have hp := (Fact.out : p.Prime)
  intro W hW u hu hs
  have hu' : u = fun o => Option.elim o (u none) (u ∘ Option.some) := by
    funext o
    cases o <;> rfl
  have hw : ∀ i, 0 < (W ∘ Option.some) i := fun i => hW (some i)
  have hv : ∀ i, (u ∘ Option.some) i ≠ 0 := fun i => hu (some i)
  rcases lt_trichotomy (p * W none) (weightedOrd (W ∘ Option.some) g).toNat with h | h | h
  · rw [initialForm_purelyInseparable_of_lt p W hg h] at hs
    exact not_isSingularPoint_X_pow none p (hu none) hs
  · rw [initialForm_purelyInseparable_of_eq p W hg hp.ne_zero h, hu',
      isSingularPoint_purelyInseparable_iff] at hs
    exact hC _ hw _ hv hs.2
  · rw [initialForm_purelyInseparable_of_gt p W hg h, hu',
      isSingularPoint_rename_some_iff] at hs
    exact hC _ hw _ hv hs.2

/-- Theorem 5.3 of research note 05, weight form (Theorem 2.8 of research note 55, with the
hypotheses of research note 60). Let `K` be a perfect reduced ring of characteristic `p`, for
example a perfect field, and let `g ≠ 0` with `g(0) = 0`. Then `z^p + g` is Newton nondegenerate
over `K` if and only if, for each weight `w` with `w_i > 0` for each `i`, the initial form `in_w g`
has no critical point in the torus `(K^*)^σ`. Only the direction from right to left holds without
the hypothesis that `K` is perfect (`newtonNondegenerate_purelyInseparable_of_forall`). -/
theorem newtonNondegenerate_purelyInseparable_iff [PerfectRing K p] {g : MvPolynomial σ K}
    (hg : g ≠ 0) (hg0 : constantCoeff g = 0) :
    NewtonNondegenerate (purelyInseparable p g) ↔
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ v : σ → K, (∀ i, v i ≠ 0) →
        ¬ IsCriticalPoint (initialForm w g) v := by
  have hp := (Fact.out : p.Prime)
  constructor
  · intro hN w hw v hv hc
    by_cases h0 : eval v (initialForm w g) = 0
    · -- The weight `W = (w, m + 1)`: the initial form of `z^p + g` is `in_w g`.
      obtain ⟨W, hWn, hW⟩ : ∃ W : Option σ → ℕ,
          W none = (weightedOrd w g).toNat + 1 ∧ W ∘ Option.some = w :=
        ⟨fun o => Option.elim o ((weightedOrd w g).toNat + 1) w, rfl, rfl⟩
      refine hN W ?_ (fun o => Option.elim o 1 v) ?_ ?_
      · rintro (_ | i)
        · rw [hWn]
          exact Nat.succ_pos _
        · show 0 < (W ∘ Option.some) i
          rw [hW]
          exact hw i
      · rintro (_ | i)
        exacts [one_ne_zero, hv i]
      · rw [initialForm_purelyInseparable_of_gt p W hg (by rw [hW, hWn]; nlinarith [hp.two_le]),
          hW, isSingularPoint_rename_some_iff]
        exact ⟨h0, hc⟩
    · -- The weight `W = (p w, m)`: the initial form of `z^p + g` is `z^p + in_w g`.
      obtain ⟨W, hWn, hW⟩ : ∃ W : Option σ → ℕ,
          W none = (weightedOrd w g).toNat ∧ W ∘ Option.some = p • w :=
        ⟨fun o => Option.elim o (weightedOrd w g).toNat (p • w), rfl, rfl⟩
      obtain ⟨z, hz, hs⟩ :=
        (exists_isSingularPoint_purelyInseparable_iff p (initialForm w g) v).mpr ⟨h0, hc⟩
      refine hN W ?_ (fun o => Option.elim o z v) ?_ ?_
      · rintro (_ | i)
        · rw [hWn]
          exact one_le_toNat_weightedOrd hw hg hg0
        · have hi : W (some i) = p * w i := by
            rw [← Function.comp_apply (f := W), hW, Pi.smul_apply, smul_eq_mul]
          rw [hi]
          exact Nat.mul_pos hp.pos (hw i)
      · rintro (_ | i)
        exacts [hz, hv i]
      · rw [initialForm_purelyInseparable_of_eq p W hg hp.ne_zero
          (by rw [hW, hWn, toNat_weightedOrd_nsmul]), hW, initialForm_nsmul hp.ne_zero]
        exact hs
  · intro hC
    exact newtonNondegenerate_purelyInseparable_of_forall p hg hC
end Criterion

/-! ### The hypothesis that `K` is perfect is needed -/

section NotPerfect

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Let `a ≠ 0` and assume that `-a` is not a `p`-th power in `K`. Then `z^p + a x^p` is Newton
nondegenerate over `K`. Its initial forms are `z^p`, `a x^p` and `z^p + a x^p`. The first two have
no zero in the torus, and a singular point `(z, v)` of the third in the torus gives
`(z / v)^p = -a`. -/
theorem newtonNondegenerate_purelyInseparable_monomial {a : K} (ha : a ≠ 0)
    (hpow : ∀ b : K, b ^ p ≠ -a) :
    NewtonNondegenerate (purelyInseparable p (monomial (single () p) a : MvPolynomial Unit K)) := by
  have hp := (Fact.out : p.Prime)
  set g : MvPolynomial Unit K := monomial (single () p) a with hgdef
  have hg : g ≠ 0 := by rw [hgdef, Ne, monomial_eq_zero]; exact ha
  have hin : ∀ w : Unit → ℕ, initialForm w g = g := fun w =>
    initialForm_of_isWeightedHomogeneous (isWeightedHomogeneous_monomial w _ a rfl) hg
  have heval : ∀ v : Unit → K, eval v g = a * v () ^ p := fun v => by
    simp [hgdef, eval_monomial]
  intro W hW u hu hs
  have hu' : u = fun o => Option.elim o (u none) (u ∘ Option.some) := by
    funext o
    cases o <;> rfl
  rcases lt_trichotomy (p * W none) (weightedOrd (W ∘ Option.some) g).toNat with h | h | h
  · rw [initialForm_purelyInseparable_of_lt p W hg h] at hs
    exact not_isSingularPoint_X_pow none p (hu none) hs
  · rw [initialForm_purelyInseparable_of_eq p W hg hp.ne_zero h, hin, hu',
      isSingularPoint_purelyInseparable_iff, heval] at hs
    have hv : u (some ()) ≠ 0 := hu (some ())
    refine hpow (u none / u (some ())) ?_
    rw [div_pow, div_eq_iff (pow_ne_zero _ hv)]
    simp only [Function.comp_apply] at hs
    linear_combination hs.1
  · rw [initialForm_purelyInseparable_of_gt p W hg h, hin, hu',
      isSingularPoint_rename_some_iff, IsSingularPoint, heval] at hs
    exact mul_ne_zero ha (pow_ne_zero _ (hu (some ()))) hs.1

omit [Fact p.Prime] in
/-- For `z^p + a x^p`, each point is a critical point of each initial form `in_w (a x^p)`. So the
right side of `newtonNondegenerate_purelyInseparable_iff` fails for `g = a x^p`. -/
theorem isCriticalPoint_initialForm_monomial (a : K) (w : Unit → ℕ) (v : Unit → K) :
    IsCriticalPoint (initialForm w (monomial (single () p) a : MvPolynomial Unit K)) v := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [IsCriticalPoint]
  rw [initialForm_of_isWeightedHomogeneous (isWeightedHomogeneous_monomial w _ a rfl)
    (by rw [Ne, monomial_eq_zero]; exact ha)]
  exact isCriticalPoint_monomial_of_dvd p (fun _ => by simp) a v

end NotPerfect

section RatFunc

variable (p : ℕ) [Fact p.Prime]

theorem ratFunc_intDegree_pow {F : Type*} [Field F] {b : RatFunc F} (hb : b ≠ 0) (n : ℕ) :
    (b ^ n).intDegree = n * b.intDegree := by
  induction n with
  | zero => simp [RatFunc.intDegree_one]
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hb) hb, ih]
    push_cast
    ring

/-- `-t` is not a `p`-th power in `F_p(t)`: a `p`-th power has degree divisible by `p`, and `-t`
has degree `1`. -/
theorem ratFunc_pow_ne_neg_X (b : RatFunc (ZMod p)) : b ^ p ≠ -RatFunc.X := by
  have hp := (Fact.out : p.Prime)
  intro h
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero, eq_comm, neg_eq_zero] at h
    exact RatFunc.X_ne_zero h
  have hdeg := congrArg RatFunc.intDegree h
  rw [ratFunc_intDegree_pow hb, RatFunc.intDegree_neg, RatFunc.intDegree_X] at hdeg
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdeg with h1 | h1
  · have : p = 1 := by exact_mod_cast h1
    exact hp.one_lt.ne' this
  · omega

/-- The remark of research note 60 on Section 2 of research note 55: Theorem 5.3 of research note
05 is false over the field `F_p(t)`, which is not perfect. The polynomial `z^p + t x^p` is Newton
nondegenerate over `F_p(t)`, but each point of the torus is a critical point of each initial form
`in_w (t x^p)`. -/
theorem newtonNondegenerate_ratFunc_example :
    NewtonNondegenerate (purelyInseparable p
      (monomial (single () p) RatFunc.X : MvPolynomial Unit (RatFunc (ZMod p)))) ∧
    ∀ w : Unit → ℕ, ∀ v : Unit → RatFunc (ZMod p),
      IsCriticalPoint (initialForm w
        (monomial (single () p) RatFunc.X : MvPolynomial Unit (RatFunc (ZMod p)))) v :=
  ⟨newtonNondegenerate_purelyInseparable_monomial p RatFunc.X_ne_zero (ratFunc_pow_ne_neg_X p),
    isCriticalPoint_initialForm_monomial p _⟩

end RatFunc

end Singularity
