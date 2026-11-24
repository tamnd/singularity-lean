/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Newton
import Singularity.Invariant.Residual
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The Frobenius-Newton criterion for `z^p + g`

The Newton criterion of Varchenko and Khovanskii gives a toric resolution of a hypersurface
`{F = 0}`. It asks that, for each compact face `τ` of the Newton polyhedron of `F`, the initial
form `F_τ` defines a hypersurface with no singular point in the torus: the point has no
coordinate `0`, and `F_τ` and all its partial derivatives vanish there.

Let `k` have characteristic `p` and let `f = z^p + g(x)`. The compact faces of the Newton
polyhedron of `f` are of three kinds: the vertex `z^p`, the faces of `g` alone with initial form
`g_σ`, and the faces that join `z^p` and a face of `g`, with initial form `z^p + g_σ`. The vertex
gives no condition, because `z^p` does not vanish in the torus. A face of the second kind asks
that `g_σ` has no critical point in the torus on its zero set. The partial derivative of `z^p`
with respect to `z` is `p z^(p-1) = 0`. So a singular point of `z^p + g_σ` is a critical point
`v` of `g_σ` and a `z` with `z^p = -g_σ(v)`. A face of the third kind thus asks that `g_σ` has
no critical point in the torus off its zero set. The two kinds together give the condition: no
initial form of `g` has a critical point in the torus. This file proves this, face by face
(`exists_torus_isCriticalPoint_iff`). The faces are not formalized here: the statements are for
one polynomial `h`, which plays the role of `g_σ`.

In characteristic `0`, a critical point of a weighted homogeneous polynomial lies on its zero
set, by the Euler identity. In characteristic `p` this can fail. The mod `p` Euler identity
(`eq_sum_smul_X_mul_pderiv`) shows that it fails only for a resonant support
(`IsResonant`): if some `w` with values in `ZMod p` has `∑ w_i a_i = 1` for each exponent `a` of
`h`, then `h = ∑ w_i x_i ∂_i h`, and each critical point of `h` lies on `{h = 0}`. A weighted
homogeneous polynomial of degree `D` with `p ∤ D` is not resonant.

A vertex `c x^a` with `a ∈ p ℕ^σ` is a degenerate face: each partial derivative of `x^a` is `0`,
so each point is critical (`pderiv_monomial_eq_zero_of_dvd`). This is why the cleaning of
`Residual.lean` must come before a Newton test.

The source is Volume 7, Chapter 3 of the handbook (to be written), sections 5.1 to 5.4 of the
research note on Frobenius and Newton polyhedra.

## Main definitions

* `Singularity.IsCriticalPoint h v`: each partial derivative of `h` vanishes at `v`.
* `Singularity.IsSingularPoint h v`: `h` and each partial derivative of `h` vanish at `v`.
* `Singularity.IsResonant p S`: no `w : σ → ZMod p` has `∑ w_i a_i = 1` for each `a ∈ S`.

## Main results

* `isSingularPoint_purelyInseparable_iff`: `(z, v)` is a singular point of `z^p + h` if and only
  if `z^p + h(v) = 0` and `v` is a critical point of `h`.
* `exists_isSingularPoint_purelyInseparable_iff`: over a perfect reduced ring, some `z ≠ 0`
  makes `(z, v)` a singular point of `z^p + h` if and only if `h(v) ≠ 0` and `v` is a critical
  point of `h`.
* `exists_torus_isCriticalPoint_iff`: `h` has a critical point in the torus if and only if
  `{h = 0}` or `{z^p + h = 0}` has a singular point in the torus (Theorem 5.3, face by face).
* `not_isSingularPoint_X_pow`: the vertex `z^p` has no singular point in the torus.
* `eq_sum_smul_X_mul_pderiv`: the mod `p` Euler identity `h = ∑ w_i x_i ∂_i h` (Proposition 5.6).
* `eq_inv_smul_sum_X_mul_pderiv`: `h = D⁻¹ ∑ w_i x_i ∂_i h` for `h` weighted homogeneous of degree
  `D` with `D ≠ 0` in `k`, so a critical point of `h` lies on `{h = 0}` (Corollary 5.7).
* `pderiv_monomial_eq_zero_of_dvd`, `exists_torus_isSingularPoint_purelyInseparable_monomial`:
  a vertex `c x^a` with `a ∈ p ℕ^σ` makes each point critical, and `z^p + c x^a` has a singular
  point in the torus (Corollary 5.5).
* `exists_eq_sum_smul_X_mul_pderiv_of_not_isResonant`,
  `eval_eq_zero_of_isCriticalPoint_of_not_isResonant`: a polynomial with a support that is not
  resonant satisfies an Euler identity, and its critical points lie on its zero set
  (Definition 5.8).
* `not_isResonant_of_isWeightedHomogeneous`, `not_isResonant_initialForm`: a weighted
  homogeneous polynomial of degree `D` with `p ∤ D` is not resonant.

## References

* A. N. Varchenko, *Zeta-function of monodromy and Newton's diagram*, Invent. Math. 37 (1976).
* A. G. Khovanskii, *Newton polyhedra and toroidal varieties*, Funct. Anal. Appl. 11 (1977).
* Y. Boubakri, G.-M. Greuel, T. Markwig, *Invariants of hypersurface singularities in positive
  characteristic*, Rev. Mat. Complut. 25 (2012).
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### Critical points and singular points -/

section Points

variable {σ k : Type*} [CommSemiring k]

/-- The point `v` is a critical point of `h`: each partial derivative of `h` vanishes at `v`.
Volume 7, Chapter 3 of the handbook. -/
def IsCriticalPoint (h : MvPolynomial σ k) (v : σ → k) : Prop :=
  ∀ i, eval v (pderiv i h) = 0

/-- The point `v` is a singular point of the hypersurface `{h = 0}`: `h` and each partial
derivative of `h` vanish at `v`. Volume 7, Chapter 3 of the handbook. -/
def IsSingularPoint (h : MvPolynomial σ k) (v : σ → k) : Prop :=
  eval v h = 0 ∧ IsCriticalPoint h v

/-- A singular point of `{h = 0}` is a critical point of `h` on the zero set of `h`. -/
theorem isSingularPoint_iff (h : MvPolynomial σ k) (v : σ → k) :
    IsSingularPoint h v ↔ eval v h = 0 ∧ IsCriticalPoint h v :=
  Iff.rfl

theorem eval_purelyInseparable (q : ℕ) (h : MvPolynomial σ k) (z : k) (v : σ → k) :
    eval (fun o => Option.elim o z v) (purelyInseparable q h) = z ^ q + eval v h := by
  simp only [purelyInseparable, map_add, map_pow, eval_X, Option.elim_none, eval_rename]
  rfl

theorem pderiv_none_rename (h : MvPolynomial σ k) :
    pderiv none (rename Option.some h) = 0 := by
  classical
  refine pderiv_eq_zero_of_notMem_vars fun hn => ?_
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (vars_rename _ _ hn)
  exact Option.some_ne_none i hi

/-- The partial derivative of `z^p + h` with respect to `z` is `0` in characteristic `p`. -/
theorem pderiv_none_purelyInseparable (p : ℕ) [CharP k p] (h : MvPolynomial σ k) :
    pderiv none (purelyInseparable p h) = 0 := by
  rw [purelyInseparable, map_add, pderiv_none_rename, pderiv_pow,
    CharP.cast_eq_zero (MvPolynomial (Option σ) k) p]
  simp

theorem pderiv_some_purelyInseparable (q : ℕ) (h : MvPolynomial σ k) (i : σ) :
    pderiv (some i) (purelyInseparable q h) = rename Option.some (pderiv i h) := by
  rw [purelyInseparable, map_add, pderiv_rename (Option.some_injective σ), pderiv_pow,
    pderiv_X_of_ne (Option.some_ne_none i).symm]
  simp

/-- The point `(z, v)` is a singular point of `z^p + h` if and only if `z^p + h(v) = 0` and `v` is
a critical point of `h`. This holds over each commutative semiring of characteristic `p`. -/
theorem isSingularPoint_purelyInseparable_iff (p : ℕ) [CharP k p] (h : MvPolynomial σ k) (z : k)
    (v : σ → k) :
    IsSingularPoint (purelyInseparable p h) (fun o => Option.elim o z v) ↔
      z ^ p + eval v h = 0 ∧ IsCriticalPoint h v := by
  rw [IsSingularPoint, eval_purelyInseparable, IsCriticalPoint, Option.forall,
    pderiv_none_purelyInseparable, map_zero]
  simp only [pderiv_some_purelyInseparable, eval_rename, true_and]
  rfl

end Points

/-! ### The torus criterion for one face -/

section Torus

variable {σ k : Type*} [CommRing k] [IsReduced k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Over a perfect reduced ring of characteristic `p`, some `z ≠ 0` makes `(z, v)` a singular
point of `z^p + h` if and only if `h(v) ≠ 0` and `v` is a critical point of `h`. This is the
content of a face of the third kind in Theorem 5.3 of Volume 7, Chapter 3 of the handbook. The
ring is perfect, so `z` with `z^p = -h(v)` exists. -/
theorem exists_isSingularPoint_purelyInseparable_iff [PerfectRing k p] (h : MvPolynomial σ k)
    (v : σ → k) :
    (∃ z ≠ 0, IsSingularPoint (purelyInseparable p h) (fun o => Option.elim o z v)) ↔
      eval v h ≠ 0 ∧ IsCriticalPoint h v := by
  have hp := (Fact.out : p.Prime)
  simp_rw [isSingularPoint_purelyInseparable_iff]
  constructor
  · rintro ⟨z, hz, hzv, hc⟩
    refine ⟨fun h0 => hz ?_, hc⟩
    rw [h0, add_zero] at hzv
    exact IsNilpotent.eq_zero ⟨p, hzv⟩
  · rintro ⟨h0, hc⟩
    obtain ⟨z, hz⟩ := surjective_frobenius k p (-eval v h)
    rw [frobenius_def] at hz
    refine ⟨z, fun hz0 => h0 ?_, by rw [hz, neg_add_cancel], hc⟩
    rw [hz0, zero_pow hp.ne_zero] at hz
    exact neg_eq_zero.mp hz.symm

/-- Over a perfect reduced ring of characteristic `p`, `v` is a critical point of `h` if and only
if `v` is a singular point of `{h = 0}` or some `z ≠ 0` makes `(z, v)` a singular point of
`{z^p + h = 0}`. -/
theorem isCriticalPoint_iff_isSingularPoint_or [PerfectRing k p] (h : MvPolynomial σ k)
    (v : σ → k) :
    IsCriticalPoint h v ↔ IsSingularPoint h v ∨
      ∃ z ≠ 0, IsSingularPoint (purelyInseparable p h) (fun o => Option.elim o z v) := by
  rw [exists_isSingularPoint_purelyInseparable_iff p, isSingularPoint_iff]
  constructor
  · intro hc
    by_cases h0 : eval v h = 0
    · exact Or.inl ⟨h0, hc⟩
    · exact Or.inr ⟨h0, hc⟩
  · rintro (⟨-, hc⟩ | ⟨-, hc⟩) <;> exact hc

/-- The torus criterion for one face (Theorem 5.3 of Volume 7, Chapter 3 of the handbook, face by
face). Let `k` be a perfect reduced ring of characteristic `p`, for example a perfect field. Then
`h` has a critical point in the torus if and only if `{h = 0}` has a singular point in the torus
or `{z^p + h = 0}` has a singular point in the torus of the variables `(z, x)`. Apply it to
`h = g_σ` for each compact face `σ` of the Newton polyhedron of `g`: the faces `g_σ` and
`z^p + g_σ` of `z^p + g` are smooth in the torus if and only if `g_σ` has no critical point in the
torus. -/
theorem exists_torus_isCriticalPoint_iff [PerfectRing k p] (h : MvPolynomial σ k) :
    (∃ v : σ → k, (∀ i, v i ≠ 0) ∧ IsCriticalPoint h v) ↔
      (∃ v : σ → k, (∀ i, v i ≠ 0) ∧ IsSingularPoint h v) ∨
        ∃ u : Option σ → k, (∀ o, u o ≠ 0) ∧ IsSingularPoint (purelyInseparable p h) u := by
  constructor
  · rintro ⟨v, hv, hc⟩
    rcases (isCriticalPoint_iff_isSingularPoint_or p h v).mp hc with hs | ⟨z, hz, hs⟩
    · exact Or.inl ⟨v, hv, hs⟩
    · refine Or.inr ⟨fun o => Option.elim o z v, ?_, hs⟩
      rintro (_ | i)
      exacts [hz, hv i]
  · rintro (⟨v, hv, hs⟩ | ⟨u, hu, hs⟩)
    · exact ⟨v, hv, hs.2⟩
    · have hu' : u = fun o => Option.elim o (u none) (u ∘ Option.some) := by
        funext o
        cases o <;> rfl
      rw [hu'] at hs
      exact ⟨u ∘ Option.some, fun i => hu (some i),
        ((isCriticalPoint_iff_isSingularPoint_or p h _).mpr (Or.inr ⟨u none, hu none, hs⟩))⟩

/-- The vertex `z^p` of the Newton polyhedron of `z^p + g` gives no condition: over a reduced
ring, `x_i^n` does not vanish at a point `u` with `u_i ≠ 0`. -/
theorem not_isSingularPoint_X_pow {τ : Type*} (i : τ) (n : ℕ) {u : τ → k} (hu : u i ≠ 0) :
    ¬ IsSingularPoint (X i ^ n) u := by
  rintro ⟨h0, -⟩
  rw [map_pow, eval_X] at h0
  exact hu (IsNilpotent.eq_zero ⟨n, h0⟩)

end Torus

/-! ### The mod `p` Euler identity -/

section Euler

variable {σ k : Type*} [Fintype σ]

/-- The mod `p` Euler identity (Proposition 5.6 of Volume 7, Chapter 3 of the handbook). Let
`w : σ → k` with `∑ w_i a_i = 1` in `k` for each exponent `a` of `h`. Then
`h = ∑ w_i x_i ∂_i h`. The proof uses `x_i ∂_i (c x^a) = a_i c x^a`. No homogeneity is needed. -/
theorem eq_sum_smul_X_mul_pderiv [CommSemiring k] (w : σ → k) {h : MvPolynomial σ k}
    (hw : ∀ a ∈ h.support, ∑ i ∈ a.support, w i * (a i : k) = 1) :
    h = ∑ i, w i • (X i * pderiv i h) := by
  symm
  calc ∑ i, w i • (X i * pderiv i h)
      = ∑ i, ∑ a ∈ h.support, w i • (X i * pderiv i (monomial a (h.coeff a))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [h.as_sum]
        rw [map_sum, Finset.mul_sum, Finset.smul_sum]
    _ = ∑ a ∈ h.support, (∑ i, w i * (a i : k)) • monomial a (h.coeff a) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [X_mul_pderiv_monomial, mul_smul, Nat.cast_smul_eq_nsmul]
    _ = ∑ a ∈ h.support, monomial a (h.coeff a) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [← Finset.sum_subset (Finset.subset_univ a.support), hw a ha, one_smul]
        intro i _ hi
        rw [Finsupp.notMem_support_iff.mp hi, Nat.cast_zero, mul_zero]
    _ = h := h.as_sum.symm

/-- If `h = ∑ w_i x_i ∂_i h` and each `x_i ∂_i h` vanishes at `v`, then `h` vanishes at `v`. -/
theorem eval_eq_zero_of_eq_sum [CommSemiring k] (w : σ → k) {h : MvPolynomial σ k}
    (hw : h = ∑ i, w i • (X i * pderiv i h)) {v : σ → k}
    (hv : ∀ i, eval v (X i * pderiv i h) = 0) : eval v h = 0 := by
  rw [hw, map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [smul_eval, hv i, mul_zero]

/-- If `h = ∑ w_i x_i ∂_i h`, then each critical point of `h` lies on `{h = 0}`. -/
theorem eval_eq_zero_of_isCriticalPoint_of_eq_sum [CommSemiring k] (w : σ → k)
    {h : MvPolynomial σ k} (hw : h = ∑ i, w i • (X i * pderiv i h)) {v : σ → k}
    (hv : IsCriticalPoint h v) : eval v h = 0 :=
  eval_eq_zero_of_eq_sum w hw fun i => by rw [eval_mul, hv i, mul_zero]

/-- The Euler identity for a weighted homogeneous polynomial (Corollary 5.7 of Volume 7,
Chapter 3 of the handbook). If `h` is weighted homogeneous of degree `D` for the weight `w` and
`D ≠ 0` in `k`, then `h = D⁻¹ ∑ w_i x_i ∂_i h`. -/
theorem eq_inv_smul_sum_X_mul_pderiv [Field k] {w : σ → ℕ} {D : ℕ} {h : MvPolynomial σ k}
    (hh : IsWeightedHomogeneous w h D) (hD : (D : k) ≠ 0) :
    h = (D : k)⁻¹ • ∑ i, (w i : k) • (X i * pderiv i h) := by
  simp_rw [Nat.cast_smul_eq_nsmul]
  rw [hh.sum_weight_X_mul_pderiv, ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hD,
    one_smul]

/-- A weighted homogeneous `h` of degree `D` with `D ≠ 0` in `k` has its critical points on its
zero set. -/
theorem eval_eq_zero_of_isCriticalPoint_of_isWeightedHomogeneous [Field k] {w : σ → ℕ} {D : ℕ}
    {h : MvPolynomial σ k} (hh : IsWeightedHomogeneous w h D) (hD : (D : k) ≠ 0) {v : σ → k}
    (hv : IsCriticalPoint h v) : eval v h = 0 := by
  refine eval_eq_zero_of_isCriticalPoint_of_eq_sum (fun i => (D : k)⁻¹ * w i) ?_ hv
  conv_lhs => rw [eq_inv_smul_sum_X_mul_pderiv hh hD]
  rw [Finset.smul_sum]
  simp_rw [smul_smul]

end Euler

/-! ### Monomials with exponents in `p ℕ^σ` -/

section Vertex

variable {σ k : Type*}

/-- If each exponent of `x^a` is divisible by `p`, then each partial derivative of `c x^a` is `0`
in characteristic `p` (Corollary 5.5 of Volume 7, Chapter 3 of the handbook). -/
theorem pderiv_monomial_eq_zero_of_dvd [CommSemiring k] (p : ℕ) [CharP k p] {a : σ →₀ ℕ}
    (ha : ∀ i, p ∣ a i) (c : k) (i : σ) : pderiv i (monomial a c) = 0 := by
  rw [pderiv_monomial, (CharP.cast_eq_zero_iff k p (a i)).mpr (ha i), mul_zero, monomial_zero]

/-- A monomial `c x^a` with `a ∈ p ℕ^σ` has each point as a critical point. -/
theorem isCriticalPoint_monomial_of_dvd [CommSemiring k] (p : ℕ) [CharP k p] {a : σ →₀ ℕ}
    (ha : ∀ i, p ∣ a i) (c : k) (v : σ → k) : IsCriticalPoint (monomial a c) v := fun i => by
  rw [pderiv_monomial_eq_zero_of_dvd p ha, map_zero]

/-- If the initial form of `g` for the weight `w` is a monomial `c x^a` with `a ∈ p ℕ^σ`, then each
point is a critical point of the initial form. -/
theorem isCriticalPoint_initialForm_of_eq_monomial [CommSemiring k] (p : ℕ) [CharP k p]
    {w : σ → ℕ} {g : MvPolynomial σ k} {a : σ →₀ ℕ} {c : k} (hg : initialForm w g = monomial a c)
    (ha : ∀ i, p ∣ a i) (v : σ → k) : IsCriticalPoint (initialForm w g) v := by
  rw [hg]
  exact isCriticalPoint_monomial_of_dvd p ha c v

variable [CommRing k] [IsReduced k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- Cleaning is necessary (Corollary 5.5 of Volume 7, Chapter 3 of the handbook). Let `k` be a
perfect reduced ring of characteristic `p`, let `c ≠ 0`, and let `a ∈ p ℕ^σ`. Then `z^p + c x^a`
has a singular point in the torus. So a vertex `c x^a` of the Newton polyhedron of `g` with
`a ∈ p ℕ^σ` makes `z^p + g` degenerate. -/
theorem exists_torus_isSingularPoint_purelyInseparable_monomial {a : σ →₀ ℕ} (ha : ∀ i, p ∣ a i)
    {c : k} (hc : c ≠ 0) :
    ∃ u : Option σ → k, (∀ o, u o ≠ 0) ∧ IsSingularPoint (purelyInseparable p (monomial a c)) u := by
  have : Nontrivial k := nontrivial_of_ne c 0 hc
  obtain ⟨z, hz, hs⟩ := (exists_isSingularPoint_purelyInseparable_iff p (monomial a c) 1).mpr
    ⟨by simpa [eval_monomial] using hc, isCriticalPoint_monomial_of_dvd p ha c 1⟩
  refine ⟨fun o => Option.elim o z 1, ?_, hs⟩
  rintro (_ | i)
  exacts [hz, one_ne_zero]

/-- If the initial form of `g` for `w` is `c x^a` with `c ≠ 0` and `a ∈ p ℕ^σ`, then the face
`z^p + c x^a` of `z^p + g` has a singular point in the torus. -/
theorem exists_torus_isSingularPoint_purelyInseparable_initialForm {w : σ → ℕ}
    {g : MvPolynomial σ k} {a : σ →₀ ℕ} {c : k} (hg : initialForm w g = monomial a c)
    (ha : ∀ i, p ∣ a i) (hc : c ≠ 0) :
    ∃ u : Option σ → k, (∀ o, u o ≠ 0) ∧
      IsSingularPoint (purelyInseparable p (initialForm w g)) u := by
  rw [hg]
  exact exists_torus_isSingularPoint_purelyInseparable_monomial p ha hc

end Vertex

/-! ### Resonance -/

section Resonance

variable {σ : Type*}

/-- A finite set `S` of exponents is resonant in characteristic `p` if no `w : σ → ZMod p` has
`∑ w_i a_i = 1` in `ZMod p` for each `a ∈ S` (Definition 5.8 of Volume 7, Chapter 3 of the
handbook). The definition uses the exponents themselves and not their classes mod `p`, which
gives the same condition. An exponent in `p ℕ^σ` makes `S` resonant, because `∑ w_i a_i = 0` for
it. So the support of a polynomial that is not clean is resonant. -/
def IsResonant (p : ℕ) (S : Finset (σ →₀ ℕ)) : Prop :=
  ¬ ∃ w : σ → ZMod p, ∀ a ∈ S, ∑ i ∈ a.support, w i * (a i : ZMod p) = 1

instance [Fintype σ] [DecidableEq σ] (p : ℕ) [NeZero p] (S : Finset (σ →₀ ℕ)) :
    Decidable (IsResonant p S) := by
  unfold IsResonant
  infer_instance

/-- A weighted homogeneous polynomial of degree `D` with `p ∤ D` has a support that is not
resonant: take `w_i / D` in `ZMod p`. -/
theorem not_isResonant_of_isWeightedHomogeneous {R : Type*} [CommSemiring R] (p : ℕ)
    [Fact p.Prime] {w : σ → ℕ} {D : ℕ} {h : MvPolynomial σ R} (hh : IsWeightedHomogeneous w h D)
    (hD : ¬ p ∣ D) : ¬ IsResonant p h.support := by
  have hD' : (D : ZMod p) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  refine not_not.mpr ⟨fun i => (D : ZMod p)⁻¹ * w i, fun a ha => ?_⟩
  have hwa : weight w a = D := hh (MvPolynomial.mem_support_iff.mp ha)
  rw [weight_apply, Finsupp.sum] at hwa
  have hcast : ∑ i ∈ a.support, (w i : ZMod p) * (a i : ZMod p) = D := by
    rw [← hwa]
    push_cast [smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hcast, inv_mul_cancel₀ hD']

/-- The initial form of `g` for `w` is not resonant when `p` does not divide the weighted order
of `g`. -/
theorem not_isResonant_initialForm {R : Type*} [CommSemiring R] (p : ℕ) [Fact p.Prime]
    (w : σ → ℕ) (g : MvPolynomial σ R) (hD : ¬ p ∣ (weightedOrd w g).toNat) :
    ¬ IsResonant p (initialForm w g).support :=
  not_isResonant_of_isWeightedHomogeneous p (isWeightedHomogeneous_initialForm w g) hD

variable {k : Type*} [CommRing k] (p : ℕ) [CharP k p]

/-- A polynomial with a support that is not resonant satisfies a mod `p` Euler identity
`h = ∑ w_i x_i ∂_i h`, with `w_i` in the image of `ZMod p` (Proposition 5.6 of Volume 7,
Chapter 3 of the handbook). -/
theorem exists_eq_sum_smul_X_mul_pderiv_of_not_isResonant [Fintype σ] {h : MvPolynomial σ k}
    (hh : ¬ IsResonant p h.support) :
    ∃ w : σ → k, h = ∑ i, w i • (X i * pderiv i h) := by
  rw [IsResonant, not_not] at hh
  obtain ⟨w, hw⟩ := hh
  refine ⟨fun i => ZMod.castHom (dvd_refl p) k (w i), eq_sum_smul_X_mul_pderiv _ fun a ha => ?_⟩
  have := congrArg (ZMod.castHom (dvd_refl p) k) (hw a ha)
  simpa only [map_sum, map_mul, map_natCast, map_one] using this

/-- Each critical point of a polynomial with a support that is not resonant lies on its zero
set. So the critical points off the zero set, which are special to characteristic `p`, come
only from resonant faces. -/
theorem eval_eq_zero_of_isCriticalPoint_of_not_isResonant [Fintype σ] {h : MvPolynomial σ k}
    (hh : ¬ IsResonant p h.support) {v : σ → k} (hv : IsCriticalPoint h v) : eval v h = 0 := by
  obtain ⟨w, hw⟩ := exists_eq_sum_smul_X_mul_pderiv_of_not_isResonant p hh
  exact eval_eq_zero_of_isCriticalPoint_of_eq_sum w hw hv

end Resonance

end Singularity
