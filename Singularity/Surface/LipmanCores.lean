/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Numerical cores of intersection numbers and of the embedded resolution of curves

This file proves algebraic and numerical cores of several results of Volume 4 of the handbook.
No intersection theory on schemes is formalized here. The main declarations are as follows.

Definition 1.1.8 and Corollary 1.1.9 (the self-intersection `E · E = -1`).

* `Singularity.IsPOneTransition`: a line bundle on `P^1` that is trivial on the two charts
  `Spec k[T]` and `Spec k[T⁻¹]` is given by a transition function `c T^d` with `c ≠ 0`. Then
  `d` is its degree.
* `Singularity.IsPOneTransition.unique`: the degree is determined by the transition function.
* `Singularity.IsPOneTransition.unit_change`: a change of the two trivializations multiplies
  the transition function by a unit of `k[T]` and a unit of `k[T⁻¹]`. This does not change the
  degree.
* `Singularity.IsPOneTransition.inv`: the dual line bundle has the inverse transition function,
  and its degree is `-d`.
* `Singularity.conormal_dual_degree`: the conormal sheaf of `E` has the generators `[u]` and
  `[v]` on the two charts, with `[v] = t [u]`. So its transition function is `T`, of degree
  `1`, and the dual `O(E)|_E` has degree `-1`. This is the computation of Corollary 1.1.9.
* `Singularity.exceptional_selfIntersection_eq_neg_one`: the second proof by Lemma 2.3.9. We
  have `div(u) = E + L`, where `L` meets `E` in the point `k[s]/(s)` of length `1`. So
  `E · E + 1 = 0`.

Remark 1.1.10 (the numerical part of [Har, Section V.3]).

* `Singularity.strictTransform_selfIntersection`: for a symmetric pairing, if `π^* C · E = 0`
  and `E · E = -1`, then the strict transform `C' = π^* C - E` has `C' · C' = C · C - 1` and
  `C' · E = 1`. So a blowup of a point of a curve lowers its self-intersection by `1`.

Definition 2.3.8 (intersection numbers, the numerical part).

* `Singularity.IsPrincipalRelation`: the relation `∑_j a_j C_j · C_i + G · C_i = 0` of the
  remark after Lemma 2.3.9.
* `Singularity.diag_eq_of_isPrincipalRelation`: if all `a_i ≠ 0`, this relation and the
  intersections of distinct curves determine the self-intersections.
* `Singularity.cuspPairChainMatrix_isPrincipalRelation`: the chain `E_1, E_4, E_2, E_5, E_3` of
  Example 3.1.10 with self-intersections `-3, -1, -4, -1, -2`, the orders `4, 12, 7, 16, 8` of
  `f` and the curves `C_1`, `C_2` satisfy the relation. By `decide`.
* `Singularity.aFourMatrix_isPrincipalRelation_z`, `Singularity.aFourMatrix_isPrincipalRelation_x`:
  the chain `A_4` of Proposition 2.3.10 for `m = 5`, with the orders of `z` and of `x`.
* `Singularity.eEightMatrix_mulVec_fundamentalCycle`: the `E_8` matrix and the cycle
  `Z = (2, 4, 6, 5, 4, 3, 2, 3)` have `Z · E_i ≤ 0` for all `i`, and `Z · Z = -2`.

Remark 2.3.3 (the surfaces `xy = z^p` in characteristic `p`).

* `Singularity.derivative_C_sub_X_pow_eq_zero`: if `n = 0` in `R`, then `∂/∂z (a - z^n) = 0`.
* `Singularity.pow_ne_X_mul_C_X`: for `p ≥ 2`, the element `xy` is not a `p`-th power in the
  field `k(x, y)`. Here `k(x, y)` is the fraction field of `k[y][x]`.
* `Singularity.irreducible_X_pow_sub_xy`: for `p` prime, `T^p - xy` is irreducible over
  `k(x, y)`. So the extension `k(x, y)(z)` has degree `p`.
* `Singularity.X_pow_sub_C_eq_sub_pow`: in characteristic `p`, if `z^p = a`, then
  `T^p - a = (T - z)^p`. So the extension is purely inseparable.

Theorem 3.1.8, part 1, and Corollary 3.1.9 (the count of `δ`).

* `Singularity.delta_eq_sum_add`: if each blowup lowers `δ` by `m(m - 1)/2` (Lemma 3.1.7,
  part 5), then `δ_0 = ∑ m_i (m_i - 1)/2 + δ_n`.
* `Singularity.delta_eq_sum_of_blowups`: if `δ_n = 0`, then `δ_0 = ∑ m_i (m_i - 1)/2`. This is
  Corollary 3.1.9, given Lemma 3.1.7, part 5.
* `Singularity.blowups_le_delta`: if each center has multiplicity at least `2`, then the number
  of blowups is at most `δ_0`.
* `Singularity.exists_iterate_eq_zero_le`: if a step lowers a natural number invariant while it
  is positive, then after at most `δ` steps it is `0`. With `δ = 0` if and only if the curve is
  regular, this is part 1 of Theorem 3.1.8. The same lemma ends Steps 3 and 4 of its proof.

Definition 2.1.1 (normal modifications).

* `Singularity.IsNormalModification`: a proper morphism `f : Y → X` with `Y` integral, with
  integrally closed stalks, and an isomorphism over a dense open `U` with dense inverse image.
* `Singularity.isNormalModification_id`: the identity of a normal integral scheme is one.

Not proved. There are no line bundles on `P^1_κ` and no degree of line bundles here. So the
identification of line bundles on `P^1` with transition functions `c T^d`, the computation of
`I_E/I_E^2` on schemes (Theorem 1.1.7) and Lemma 2.3.9 are not proved; they are only modelled.
The projection formula `π^* C · E = 0` and the theorem of Castelnuovo in Remark 1.1.10 are not
proved. Lemma 3.1.7, part 5, and the facts that `δ = 0` exactly at regular points and that the
centers have multiplicity at least `2` are hypotheses, not theorems. Part 2 of Theorem 3.1.8 is
not proved. Definition 2.1.3, Remark 2.1.4 and Theorem 2.1.6 need the cohomology of coherent
sheaves, and they are not formalized. Corollary 1.2.5 and Remark 2.2.3 are not treated here.
-/

universe u

namespace Singularity

/-! ### Line bundles on `P^1` by transition functions -/

section Transition

open LaurentPolynomial

variable {k : Type*}

/-- The Laurent polynomial `g` is a transition function `c T^d` with `c ≠ 0` of a line bundle
on `P^1` with the charts `Spec k[T]` and `Spec k[T⁻¹]`. Then `d` is the degree. -/
def IsPOneTransition [Semiring k] (g : k[T;T⁻¹]) (d : ℤ) : Prop :=
  ∃ c : k, c ≠ 0 ∧ g = C c * T d

/-- The degree is determined by the transition function. -/
theorem IsPOneTransition.unique [Semiring k] {g : k[T;T⁻¹]} {d d' : ℤ}
    (h : IsPOneTransition g d) (h' : IsPOneTransition g d') : d = d' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', h'⟩ := h'
  have hdeg := degree_C_mul_T d c hc
  rw [h', degree_C_mul_T d' c' hc'] at hdeg
  exact (WithBot.coe_inj.mp hdeg).symm

/-- A change of the two trivializations does not change the degree. A unit `a` of `k[T]` and
a unit `b` of `k[T⁻¹]` multiply the transition function. -/
theorem IsPOneTransition.unit_change [Field k] {g : k[T;T⁻¹]} {d : ℤ}
    (h : IsPOneTransition g d) {a b : Polynomial k} (ha : IsUnit a) (hb : IsUnit b) :
    IsPOneTransition (Polynomial.toLaurent a * g * invert (Polynomial.toLaurent b)) d := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨α, hα, rfl⟩ := Polynomial.isUnit_iff.mp ha
  obtain ⟨β, hβ, rfl⟩ := Polynomial.isUnit_iff.mp hb
  refine ⟨α * c * β, mul_ne_zero (mul_ne_zero hα.ne_zero hc) hβ.ne_zero, ?_⟩
  have hinv : invert (C β : k[T;T⁻¹]) = C β := invert.commutes β
  rw [Polynomial.toLaurent_C, Polynomial.toLaurent_C, hinv, map_mul, map_mul]
  ring

/-- The dual line bundle has the inverse transition function, of degree `-d`. -/
theorem IsPOneTransition.inv [Field k] {g g' : k[T;T⁻¹]} {d : ℤ}
    (h : IsPOneTransition g d) (hg : g * g' = 1) : IsPOneTransition g' (-d) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  have h1 : C c⁻¹ * T (-d) * (C c * T d) = (1 : k[T;T⁻¹]) := by
    calc C c⁻¹ * T (-d) * (C c * T d) = C (c⁻¹ * c) * T (-d + d) := by
          rw [map_mul, T_add]; ring
      _ = 1 := by rw [inv_mul_cancel₀ hc, neg_add_cancel, T_zero, map_one, one_mul]
  calc g' = C c⁻¹ * T (-d) * (C c * T d) * g' := by rw [h1, one_mul]
    _ = C c⁻¹ * T (-d) := by rw [mul_assoc, hg, mul_one]

/-- Corollary 1.1.9 in the model. On the chart with coordinate `t = v/u` the conormal sheaf
`I_E/I_E^2` has the generator `[u]`, on the other chart the generator `[v]`, and `[v] = t [u]`.
So its transition function is `T`, of degree `1`. Each inverse `g'` of `T`, the transition
function of the dual `O(E)|_E`, has degree `-1`. -/
theorem conormal_dual_degree [Field k] {g' : k[T;T⁻¹]} (hg : (T 1 : k[T;T⁻¹]) * g' = 1) :
    IsPOneTransition (T 1 : k[T;T⁻¹]) 1 ∧ IsPOneTransition g' (-1) := by
  have h1 : IsPOneTransition (T 1 : k[T;T⁻¹]) 1 := ⟨1, one_ne_zero, by rw [map_one, one_mul]⟩
  exact ⟨h1, h1.inv hg⟩

end Transition

/-! ### The self-intersection by Lemma 2.3.9 -/

section Principal

open Polynomial

/-- The point where the strict transform `L = V(s)` of `V(u)` meets `E ≅ Spec k[s]` has length
`1`: the ring `k[s]/(s)` has dimension `1`. -/
theorem finrank_quotient_span_X (k : Type*) [Field k] :
    Module.finrank k (k[X] ⧸ Ideal.span {(X : k[X])}) = 1 := by
  rw [finrank_quotient_span_eq_natDegree, natDegree_X]

/-- Corollary 1.1.9 by Lemma 2.3.9. In the chart `Spec k[v, s]` with `u = v s`, the divisor of
`u` is `E + L` with `E = V(v)` and `L = V(s)`. If `E · E + L · E = 0` and `L · E` is the length
of `k[s]/(s)`, then `E · E = -1`. -/
theorem exceptional_selfIntersection_eq_neg_one (k : Type*) [Field k] {e : ℤ}
    (hdiv : e + (Module.finrank k (k[X] ⧸ Ideal.span {(X : k[X])}) : ℤ) = 0) : e = -1 := by
  rw [finrank_quotient_span_X] at hdiv
  omega

end Principal

/-! ### The strict transform of a curve through the center -/

/-- The numerical part of [Har, Section V.3] in Remark 1.1.10. Let `p = π^* C` and let `e = E`.
If `p · E = 0` and `E · E = -1`, then the strict transform `p - e` has self-intersection
`C · C - 1` and meets `E` with multiplicity `1`. -/
theorem strictTransform_selfIntersection {M : Type*} [AddCommGroup M]
    (B : M →+ M →+ ℤ) {p e : M} (hpe : B p e = 0) (hep : B e p = 0) (hee : B e e = -1) :
    B (p - e) (p - e) = B p p - 1 ∧ B (p - e) e = 1 := by
  simp only [map_sub, AddMonoidHom.sub_apply]
  constructor <;> omega

/-! ### Intersection matrices -/

section Matrices

/-- The relation `∑_j a_j C_j · C_i + G · C_i = 0` for `div(g) = ∑_j a_j C_j + G`, from
Lemma 2.3.9, part 3. Here `M` is the matrix of the `C_i · C_j` and `g i = G · C_i`. -/
def IsPrincipalRelation {ι : Type*} [Fintype ι] (M : Matrix ι ι ℤ) (a g : ι → ℤ) : Prop :=
  ∀ i, M.mulVec a i + g i = 0

/-- If `a_i ≠ 0`, the principal relation and the intersections of distinct curves determine the
self-intersection `C_i · C_i`. -/
theorem diag_eq_of_isPrincipalRelation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M M' : Matrix ι ι ℤ} {a g : ι → ℤ} (hoff : ∀ i j, i ≠ j → M i j = M' i j)
    (h : IsPrincipalRelation M a g) (h' : IsPrincipalRelation M' a g) {i : ι} (hai : a i ≠ 0) :
    M i i = M' i i := by
  have e : ∀ N : Matrix ι ι ℤ,
      N.mulVec a i = N i i * a i + ∑ j ∈ Finset.univ.erase i, N i j * a j := by
    intro N
    simp only [Matrix.mulVec, dotProduct]
    exact (Finset.add_sum_erase _ (fun j => N i j * a j) (Finset.mem_univ i)).symm
  have hs : ∑ j ∈ Finset.univ.erase i, M i j * a j = ∑ j ∈ Finset.univ.erase i, M' i j * a j :=
    Finset.sum_congr rfl fun j hj => by rw [hoff i j (Finset.ne_of_mem_erase hj).symm]
  have h1 := h i
  have h2 := h' i
  rw [e] at h1 h2
  have h3 : M i i * a i = M' i i * a i := by linarith
  exact mul_right_cancel₀ hai h3

/-- The chain `E_1, E_4, E_2, E_5, E_3` of Example 3.1.10, with self-intersections
`-3, -1, -4, -1, -2`. -/
def cuspPairChainMatrix : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-3, 1, 0, 0, 0;
      1, -1, 1, 0, 0;
      0, 1, -4, 1, 0;
      0, 0, 1, -1, 1;
      0, 0, 0, 1, -2]

/-- Example 3.1.10, part 3, numerically: `div(f) = C_1 + C_2 + 4E_1 + 7E_2 + 8E_3 + 12E_4 +
16E_5`, with `C_1` on `E_4` and `C_2` on `E_5`, satisfies the principal relation. -/
theorem cuspPairChainMatrix_isPrincipalRelation :
    IsPrincipalRelation cuspPairChainMatrix ![4, 12, 7, 16, 8] ![0, 1, 0, 1, 0] := by
  unfold IsPrincipalRelation
  decide

/-- The chain `A_4` of Proposition 2.3.10 for `m = 5`: four curves with self-intersection `-2`.
-/
def aFourMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-2, 1, 0, 0;
      1, -2, 1, 0;
      0, 1, -2, 1;
      0, 0, 1, -2]

/-- The function `z` has order `1` along each `E_i`, and the strict transforms of the two lines
`{x = z = 0}` and `{y = z = 0}` meet `E_1` and `E_4`. -/
theorem aFourMatrix_isPrincipalRelation_z :
    IsPrincipalRelation aFourMatrix ![1, 1, 1, 1] ![1, 0, 0, 1] := by
  unfold IsPrincipalRelation
  decide

/-- The function `x` has order `m - i = 4, 3, 2, 1` along `E_i`, and `div(x)` has the
component `5 L` with `L` the strict transform of `{x = z = 0}`, which meets `E_1`. -/
theorem aFourMatrix_isPrincipalRelation_x :
    IsPrincipalRelation aFourMatrix ![4, 3, 2, 1] ![5, 0, 0, 0] := by
  unfold IsPrincipalRelation
  decide

/-- The intersection matrix of the `E_8` configuration. The chain is `0 - 1 - 2 - ... - 6`, and
the curve `7` meets the curve `2`. -/
def eEightMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  !![-2, 1, 0, 0, 0, 0, 0, 0;
      1, -2, 1, 0, 0, 0, 0, 0;
      0, 1, -2, 1, 0, 0, 0, 1;
      0, 0, 1, -2, 1, 0, 0, 0;
      0, 0, 0, 1, -2, 1, 0, 0;
      0, 0, 0, 0, 1, -2, 1, 0;
      0, 0, 0, 0, 0, 1, -2, 0;
      0, 0, 1, 0, 0, 0, 0, -2]

/-- The cycle `Z = (2, 4, 6, 5, 4, 3, 2, 3)` on `E_8` has `Z · E_i = 0` except `Z · E_6 = -1`,
and `Z · Z = -2`. -/
theorem eEightMatrix_mulVec_fundamentalCycle :
    eEightMatrix.mulVec ![2, 4, 6, 5, 4, 3, 2, 3] = ![0, 0, 0, 0, 0, 0, -1, 0] ∧
      dotProduct ![2, 4, 6, 5, 4, 3, 2, 3] (eEightMatrix.mulVec ![2, 4, 6, 5, 4, 3, 2, 3]) =
        -2 := by
  decide

end Matrices

/-! ### The surfaces `xy = z^p` -/

section Inseparable

open Polynomial

/-- If `n = 0` in `R`, then the derivative of `a - z^n` in `z` is `0`. -/
theorem derivative_C_sub_X_pow_eq_zero {R : Type*} [CommRing R] (a : R) {n : ℕ}
    (hn : (n : R) = 0) : derivative (C a - X ^ n : R[X]) = 0 := by
  rw [derivative_sub, derivative_C, derivative_X_pow, hn, map_zero, zero_mul, sub_zero]

variable {k : Type*} [Field k]

/-- For `p ≥ 2`, the element `xy` is not a `p`-th power in `k(x, y)`, the fraction field of
`k[y][x]` with `x = X` and `y = C X`. -/
theorem pow_ne_X_mul_C_X {p : ℕ} (hp : 2 ≤ p) (w : FractionRing k[X][X]) :
    w ^ p ≠ algebraMap k[X][X] (FractionRing k[X][X]) (X * C X) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := k[X][X]) w
  intro h
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap k[X][X] (FractionRing k[X][X]) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  rw [div_pow, div_eq_iff (pow_ne_zero _ hb'), ← map_pow, ← map_pow, ← map_mul] at h
  have h2 : a ^ p = X * C X * b ^ p := IsFractionRing.injective _ _ h
  have hX : (X * C X : k[X][X]) ≠ 0 := mul_ne_zero X_ne_zero (C_ne_zero.mpr X_ne_zero)
  have hd := congrArg natDegree h2
  rw [natDegree_pow, natDegree_mul hX (pow_ne_zero _ hb0), natDegree_pow, mul_comm X,
    natDegree_C_mul_X _ X_ne_zero] at hd
  have hm := congrArg (· % p) hd
  simp only [Nat.mul_mod_right, Nat.add_mul_mod_self_left] at hm
  rw [Nat.mod_eq_of_lt (by omega : 1 < p)] at hm
  omega

/-- For a prime `p`, the polynomial `T^p - xy` is irreducible over `k(x, y)`. So the function
field `k(x, y)(z)` of `X_p` has degree `p` over `k(x, y)`. -/
theorem irreducible_X_pow_sub_xy {p : ℕ} (hp : p.Prime) :
    Irreducible (X ^ p - C (algebraMap k[X][X] (FractionRing k[X][X]) (X * C X))) :=
  X_pow_sub_C_irreducible_of_prime hp fun w => pow_ne_X_mul_C_X hp.two_le w

/-- In characteristic `p`, if `z^p = a`, then `T^p - a = (T - z)^p`. So `z` is the only root of
`T^p - a`, and the extension is purely inseparable. -/
theorem X_pow_sub_C_eq_sub_pow {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    {z a : R} (hz : z ^ p = a) : (X ^ p - C a : R[X]) = (X - C z) ^ p := by
  rw [sub_pow_char, ← map_pow, hz]

end Inseparable

/-! ### The count of the delta invariant -/

section Delta

open Finset

/-- If the `i`-th blowup lowers `δ` by `m_i (m_i - 1)/2`, then
`δ_0 = ∑_{i < n} m_i (m_i - 1)/2 + δ_n`. -/
theorem delta_eq_sum_add {δ m : ℕ → ℕ} {n : ℕ}
    (hstep : ∀ i < n, δ i = m i * (m i - 1) / 2 + δ (i + 1)) :
    δ 0 = ∑ i ∈ range n, m i * (m i - 1) / 2 + δ n := by
  suffices H : ∀ j ≤ n, δ 0 = ∑ i ∈ range j, m i * (m i - 1) / 2 + δ j from H n le_rfl
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih (by omega), hstep j (by omega), sum_range_succ]
    ring

/-- Corollary 3.1.9, given Lemma 3.1.7, part 5: if `δ_n = 0` at the end, then
`δ_0 = ∑_{i < n} m_i (m_i - 1)/2`. -/
theorem delta_eq_sum_of_blowups {δ m : ℕ → ℕ} {n : ℕ}
    (hstep : ∀ i < n, δ i = m i * (m i - 1) / 2 + δ (i + 1)) (hend : δ n = 0) :
    δ 0 = ∑ i ∈ range n, m i * (m i - 1) / 2 := by
  rw [delta_eq_sum_add hstep, hend, add_zero]

/-- If each center has multiplicity at least `2`, then there are at most `δ_0` blowups. This is
the bound of Theorem 3.1.8, part 1. -/
theorem blowups_le_delta {δ m : ℕ → ℕ} {n : ℕ}
    (hstep : ∀ i < n, δ i = m i * (m i - 1) / 2 + δ (i + 1)) (hm : ∀ i < n, 2 ≤ m i) :
    n ≤ δ 0 := by
  rw [delta_eq_sum_add hstep]
  have h1 : ∀ i ∈ range n, 1 ≤ m i * (m i - 1) / 2 := by
    intro i hi
    have h2 := hm i (mem_range.mp hi)
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : 2 * 1 ≤ m i * (m i - 1) := Nat.mul_le_mul h2 (by omega)
    omega
  have h3 := sum_le_sum h1
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at h3
  omega

/-- If a step `b` lowers the invariant `δ` while it is positive, then `δ` is `0` after at most
`δ s` steps. -/
theorem exists_iterate_eq_zero_le {S : Type*} (δ : S → ℕ) (b : S → S)
    (h : ∀ s, 0 < δ s → δ (b s) < δ s) (s : S) : ∃ n ≤ δ s, δ (b^[n] s) = 0 := by
  induction hN : δ s using Nat.strong_induction_on generalizing s with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · exact ⟨0, by omega, by simpa [hN] using h0⟩
    · have hlt : δ (b s) < N := hN ▸ h s (hN ▸ hpos)
      obtain ⟨n, hn, hz⟩ := ih (δ (b s)) hlt (b s) rfl
      exact ⟨n + 1, by omega, by rwa [Function.iterate_succ_apply]⟩

/-- Example 3.1.10: the two centers over the origin have multiplicities `4` and `3`, so
`δ = 6 + 3 = 9`. -/
theorem cuspPair_delta {δ : ℕ → ℕ}
    (hstep : ∀ i < 2, δ i = [4, 3].getD i 0 * ([4, 3].getD i 0 - 1) / 2 + δ (i + 1))
    (hend : δ 2 = 0) : δ 0 = 9 := by
  rw [delta_eq_sum_of_blowups (m := fun i => [4, 3].getD i 0) hstep hend]
  decide

end Delta

/-! ### Normal modifications -/

section Modification

open AlgebraicGeometry CategoryTheory

/-- Definition 2.1.1. A normal modification of `X` is a proper morphism `f : Y → X` such that
`Y` is integral with integrally closed stalks, and `f` is an isomorphism over a dense open `U`
with dense inverse image. -/
structure IsNormalModification {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop where
  isProper : IsProper f
  isIntegral : IsIntegral Y
  isIntegrallyClosed_stalk : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)
  birational : ∃ U : X.Opens, Dense (U : Set X) ∧ Dense ((f ⁻¹ᵁ U : Y.Opens) : Set Y) ∧
    IsIso (f ∣_ U)

/-- The identity of an integral scheme with integrally closed stalks is a normal
modification. -/
theorem isNormalModification_id (X : Scheme.{u}) [IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsNormalModification (𝟙 X) where
  isProper := inferInstance
  isIntegral := inferInstance
  isIntegrallyClosed_stalk := hX
  birational := ⟨⊤, by simp, by simp, inferInstance⟩

end Modification

end Singularity
