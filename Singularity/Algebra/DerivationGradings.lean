/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Prime.Factorial

/-!
# The Taylor lemma and the grading lemma for derivations in characteristic `p`

This file proves the Taylor lemma and the grading lemma for derivations in characteristic `p`. The two lemmas are the algebraic tools of the proof of the log-Jacobian criterion (Volume 5, Chapter 4 of the handbook).

Let `A` be a commutative ring of characteristic `p`, with `p` prime. Let `δ_1, …, δ_s` be commuting derivations of `A` over a base ring `k` with `δ_j^p = 0`, and let `y_1, …, y_s ∈ A` with `δ_j y_l = 1` if `j = l` and `0` if not. Let `A'` be the subalgebra of common constants. The Taylor lemma says that the monomials `y^c` with `c_j < p` are a basis of `A` over `A'`.

Let `R` be a commutative ring of characteristic `p` and let `δ_1, …, δ_q` be commuting derivations of `R` with `δ_l^p = δ_l`. For `χ : ι → ZMod p` let `R_χ` be the common eigenspace `{g | δ_l g = χ_l g for all l}`. The grading lemma says that `R` is the direct sum of the `R_χ`, that `R_χ R_ψ ⊆ R_(χ+ψ)`, and that an ideal is stable under all `δ_l` if and only if it is graded. If `R` is local and `δ_l(R) ⊆ 𝔪` for all `l`, then `R_χ ⊆ 𝔪` for `χ ≠ 0`, the component of weight `0` of a unit is a unit, and a stable principal ideal has a homogeneous generator.

## Main definitions

* `Singularity.constantsOn δ T`: the subalgebra of the elements that the derivations `δ_l`, `l ∈ T`, kill. `Singularity.constants δ` is the subalgebra `A'` of common constants.
* `Singularity.taylorMonomial y c`: the monomial `Π_l y_l^(c_l)`.
* `Singularity.taylorBasis`: the basis of `A` over `A'` by the monomials `y^c`, `c : ι → Fin p`.
* `Singularity.weightSpace δ i`: the eigenspace `R_i = {g | δ g = i g}` for `i : ZMod p`.
* `Singularity.gradingProj δ i`: the projection `π_i = 1 - (δ - i)^(p-1)`, a polynomial in `δ`.
* `Singularity.commonWeightSpace δ χ`: the common eigenspace `R_χ` of a family of derivations.

## Main results

* `Singularity.exists_taylor`, `Singularity.taylor_coeff_unique`: the Taylor formula for one derivation, `a = Σ_(i<p) y^i a_i` with `δ a_i = 0`, and the uniqueness of the `a_i`.
* `Singularity.linearIndependent_taylorMonomial`, `Singularity.span_taylorMonomial`: the monomials `y^c` are linearly independent over `A'` and span `A` over `A'`.
* `Singularity.taylorBasis`, `Singularity.taylorBasis_apply`: the Taylor lemma as a `Module.Basis`.
* `Singularity.sum_gradingProj_apply`, `Singularity.gradingProj_mem`: `g = Σ_i π_i g` and `π_i g ∈ R_i`.
* `Singularity.gradingProj_apply_of_mem`, `Singularity.eq_gradingProj_of_sum`, `Singularity.eq_zero_of_sum_weightSpace`: the sum of the `R_i` is direct and the components are unique.
* `Singularity.mul_mem_weightSpace`, `Singularity.one_mem_weightSpace_zero`: `R_i R_j ⊆ R_(i+j)` and `1 ∈ R_0`.
* `Singularity.exists_sum_commonWeightSpace`, `Singularity.eq_zero_of_sum_commonWeightSpace`, `Singularity.eq_of_sum_commonWeightSpace`: each element is a sum of components in the `R_χ`, and the components are unique.
* `Singularity.mul_mem_commonWeightSpace`, `Singularity.one_mem_commonWeightSpace_zero`: `R_χ R_ψ ⊆ R_(χ+ψ)` and `1 ∈ R_0`.
* `Singularity.forall_derivation_mem_iff`: an ideal is stable under all `δ_l` if and only if it contains the components of each of its elements.
* `Singularity.mem_maximalIdeal_of_mem_commonWeightSpace`: `R_χ ⊆ 𝔪` for `χ ≠ 0`.
* `Singularity.isUnit_zero_of_sum_commonWeightSpace`, `Singularity.exists_isUnit_zero_component`: the component of weight `0` of a unit is a unit.
* `Singularity.exists_mem_commonWeightSpace_span_eq`: a principal ideal of a local ring that is stable under all `δ_l` has a generator in some `R_χ`.

## The proof

The Taylor formula for one derivation uses induction on the least `m` with `δ^m a = 0`. The element `c = δ^(m-1) a` is a constant, and `a - y^(m-1) c / (m-1)!` is killed by `δ^(m-1)`, because `δ^(m-1) (y^(m-1)) = (m-1)!` is a unit for `m ≤ p`. This gives the same formula as the proof with the operator `1 - y δ + y^2 δ^2 / 2! - …`. The proof is relative to a subalgebra `B` that is stable under `δ` and contains `y`, so that the coefficients stay in `B`. The independence applies `δ^(m-1)` to a relation of length `m`: it kills `y^i` for `i < m - 1` and gives `(m-1)!` times the last coefficient.

The general case uses induction on a finite set `S` of indices. For the spanning, `B` is the subalgebra of the elements that the `δ_l` with `l ∉ S ∪ {j}` kill. It is stable under `δ_j` because the derivations commute, and it contains `y_j`. For the independence, a relation is split by the exponent of `y_j` into a relation of length `p` for `δ_j`, with coefficients in `ker δ_j`.

For the grading lemma, `X^p - X = (X - i)^p - (X - i)` in characteristic `p` gives `(δ - i) π_i = (δ - i) - (δ - i)^p = 0`. The identity `Σ_i (1 - (X - i)^(p-1)) = 1` holds in `F_p[X]`, because the polynomial has degree less than `p` and takes the value `1` at each point of `F_p`. On `R_j` the map `π_i` is multiplication by `1 - (j - i)^(p-1)`, which is `1` if `i = j` and `0` if not. For a family of derivations, the projections `π_(l, i)` lie in the subalgebra of the endomorphisms that the `δ_l` generate. This subalgebra is commutative, so `π_χ = Π_l π_(l, χ_l)` satisfies `Σ_χ π_χ = Π_l Σ_i π_(l, i) = 1`. A stable ideal is stable under this subalgebra, so it contains the components of its elements.

For the homogeneous generator, write `g = Σ_χ g_χ` with `g_χ = h_χ g`. Then `(1 - Σ_χ h_χ) g = 0`. If `g ≠ 0`, then `1 - Σ_χ h_χ` is not a unit, so `Σ_χ h_χ` is a unit and some `h_χ` is a unit. Then `g_χ` generates the ideal. The simpler relation `Σ h_χ = 1` holds only if `g` is not a zero divisor, so the proof does not use it.

## What is not proved

All the statements of the Taylor lemma and of the grading lemma are proved. The decomposition is stated with `Finset.sum` over all weights `χ : ι → ZMod p`, and not with `DirectSum.IsInternal`. The derivations are `k`-derivations for a base ring `k`, so the statements apply to additive derivations with `k = ℤ`. The uses of the lemmas in the proof of the log-Jacobian criterion (the regularity of the ring of constants and the construction of the monomial first integral) are not in this file.

## References

* Volume 5, Chapter 4 of the handbook.
* H. Matsumura, Commutative ring theory, Cambridge University Press, 1986.
-/

namespace Singularity

open Finset

section Taylor

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- In a ring of characteristic `p`, the factorial `m!` with `m < p` has an inverse that is the image of a natural number. -/
theorem exists_natCast_mul_factorial_eq_one (p : ℕ) [Fact p.Prime] [CharP A p] {m : ℕ}
    (hm : m < p) : ∃ n : ℕ, (n : A) * (m.factorial : A) = 1 := by
  have hp := (Fact.out : p.Prime)
  have h0 : (m.factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, Nat.Prime.dvd_factorial hp]
    omega
  refine ⟨((m.factorial : ZMod p)⁻¹).val, ?_⟩
  have h1 : (((m.factorial : ZMod p)⁻¹).val : ZMod p) * (m.factorial : ZMod p) = 1 := by
    rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ h0]
  simpa using congrArg (ZMod.castHom (dvd_refl p) A) h1

variable (δ : Derivation k A A)

/-- The iterates of a derivation `δ` are linear over the kernel of `δ`. -/
theorem derivation_pow_apply_mul_of_eq_zero (n : ℕ) (x : A) {b : A} (hb : δ b = 0) :
    (δ.toLinearMap ^ n) (x * b) = (δ.toLinearMap ^ n) x * b := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply]
    have h : δ.toLinearMap (x * b) = δ.toLinearMap x * b := by
      simp [Derivation.leibniz, hb, mul_comm]
    rw [h, ih]

/-- If `δ y = 1`, then `δ^m (y^m) = m!`. -/
theorem derivation_pow_apply_pow_self {y : A} (hy : δ y = 1) (m : ℕ) :
    (δ.toLinearMap ^ m) (y ^ m) = (m.factorial : A) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply]
    have h : δ.toLinearMap (y ^ (m + 1)) = y ^ m * ((m + 1 : ℕ) : A) := by
      simp [Derivation.leibniz_pow, hy, mul_comm]
    rw [h, derivation_pow_apply_mul_of_eq_zero δ _ _ (δ.map_natCast _), ih, Nat.factorial_succ]
    push_cast
    ring

/-- If `δ y = 1` and `i < j`, then `δ^j (y^i) = 0`. -/
theorem derivation_pow_apply_pow_of_lt {y : A} (hy : δ y = 1) {i j : ℕ} (h : i < j) :
    (δ.toLinearMap ^ j) (y ^ i) = 0 := by
  induction i generalizing j with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [pow_succ, Module.End.mul_apply]
    simp
  | succ i ih =>
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [pow_succ, Module.End.mul_apply]
    have h' : δ.toLinearMap (y ^ (i + 1)) = y ^ i * ((i + 1 : ℕ) : A) := by
      simp [Derivation.leibniz_pow, hy, mul_comm]
    rw [h', derivation_pow_apply_mul_of_eq_zero δ _ _ (δ.map_natCast _), ih (by omega), zero_mul]

/-- Let `δ y = 1`. Let `m ≤ p` and let `b_0, …, b_(m-1)` be constants of `δ`. If `Σ_(i<m) y^i b_i = 0`, then all `b_i` are zero. -/
theorem taylor_coeff_eq_zero (p : ℕ) [Fact p.Prime] [CharP A p] {y : A} (hy : δ y = 1) :
    ∀ m ≤ p, ∀ b : ℕ → A, (∀ i, δ (b i) = 0) → ∑ i ∈ range m, y ^ i * b i = 0 →
      ∀ i < m, b i = 0 := by
  intro m
  induction m with
  | zero => intro _ _ _ _ i hi; omega
  | succ m ih =>
    intro hm b hb hsum
    have hlast : b m = 0 := by
      have h := congrArg (δ.toLinearMap ^ m) hsum
      rw [map_sum, map_zero, sum_range_succ, sum_eq_zero fun i hi => by
        rw [derivation_pow_apply_mul_of_eq_zero δ _ _ (hb i),
          derivation_pow_apply_pow_of_lt δ hy (mem_range.mp hi), zero_mul],
        zero_add, derivation_pow_apply_mul_of_eq_zero δ _ _ (hb m),
        derivation_pow_apply_pow_self δ hy] at h
      obtain ⟨n, hn⟩ := exists_natCast_mul_factorial_eq_one (A := A) p (m := m) (by omega)
      calc b m = (n : A) * ((m.factorial : A) * b m) := by rw [← mul_assoc, hn, one_mul]
        _ = 0 := by rw [h, mul_zero]
    have hsum' : ∑ i ∈ range m, y ^ i * b i = 0 := by
      rw [sum_range_succ, hlast, mul_zero, add_zero] at hsum
      exact hsum
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih (by omega) b hb hsum' i hi
    · exact hlast

/-- The iterates of `δ` map a subalgebra `B` that is stable under `δ` into `B`. -/
theorem derivation_pow_apply_mem (B : Subalgebra k A) (hB : ∀ b ∈ B, δ b ∈ B) (n : ℕ) {a : A}
    (ha : a ∈ B) : (δ.toLinearMap ^ n) a ∈ B := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hB _ ih

/-- The Taylor formula for one derivation, relative to a subalgebra. Let `δ` be a derivation of `A` with `δ^p = 0`, let `δ y = 1`, and let `B` be a subalgebra that is stable under `δ` and contains `y`. Then each `a ∈ B` is `Σ_(i<p) y^i b_i` with `b_i ∈ B` and `δ b_i = 0`. -/
theorem exists_taylor_of_mem (p : ℕ) [Fact p.Prime] [CharP A p] (hδ : δ.toLinearMap ^ p = 0)
    {y : A} (hy : δ y = 1) (B : Subalgebra k A) (hB : ∀ b ∈ B, δ b ∈ B) (hyB : y ∈ B) {a : A}
    (ha : a ∈ B) :
    ∃ b : ℕ → A, (∀ i, b i ∈ B ∧ δ (b i) = 0) ∧ a = ∑ i ∈ range p, y ^ i * b i := by
  suffices h : ∀ m ≤ p, ∀ a ∈ B, (δ.toLinearMap ^ m) a = 0 →
      ∃ b : ℕ → A, (∀ i, b i ∈ B ∧ δ (b i) = 0) ∧ a = ∑ i ∈ range m, y ^ i * b i from
    h p le_rfl a ha (by rw [hδ, LinearMap.zero_apply])
  intro m
  induction m with
  | zero =>
    intro _ a _ h0
    refine ⟨0, fun i => ⟨B.zero_mem, map_zero δ⟩, ?_⟩
    simpa using h0
  | succ m ih =>
    intro hm a ha h0
    set c := (δ.toLinearMap ^ m) a with hc
    have hc0 : δ c = 0 := by
      rw [pow_succ', Module.End.mul_apply] at h0
      exact h0
    have hcB : c ∈ B := derivation_pow_apply_mem δ B hB m ha
    obtain ⟨n, hn⟩ := exists_natCast_mul_factorial_eq_one (A := A) p (m := m) (by omega)
    have hnc : δ ((n : A) * c) = 0 := by simp [Derivation.leibniz, hc0]
    have hncB : (n : A) * c ∈ B := B.mul_mem (B.natCast_mem n) hcB
    have h1 : (δ.toLinearMap ^ m) (a - y ^ m * ((n : A) * c)) = 0 := by
      rw [map_sub, derivation_pow_apply_mul_of_eq_zero δ _ _ hnc,
        derivation_pow_apply_pow_self δ hy, ← hc, ← mul_assoc, mul_comm (m.factorial : A),
        hn, one_mul, sub_self]
    have hB' : a - y ^ m * ((n : A) * c) ∈ B :=
      B.sub_mem ha (B.mul_mem (B.pow_mem hyB m) hncB)
    obtain ⟨b, hb, hsum⟩ := ih (by omega) _ hB' h1
    refine ⟨Function.update b m ((n : A) * c), fun i => ?_, ?_⟩
    · rcases eq_or_ne i m with rfl | hi
      · simp only [Function.update_self]
        exact ⟨hncB, hnc⟩
      · simp only [Function.update_of_ne hi]
        exact hb i
    · rw [sum_range_succ, Function.update_self]
      have h2 : ∑ i ∈ range m, y ^ i * Function.update b m ((n : A) * c) i =
          ∑ i ∈ range m, y ^ i * b i :=
        sum_congr rfl fun i hi => by
          rw [Function.update_of_ne (Nat.ne_of_lt (mem_range.mp hi))]
      rw [h2, ← hsum]
      ring

/-- The Taylor formula for one derivation: if `δ^p = 0` and `δ y = 1`, then each `a ∈ A` is `Σ_(i<p) y^i a_i` with `δ a_i = 0`. -/
theorem exists_taylor (p : ℕ) [Fact p.Prime] [CharP A p] (hδ : δ.toLinearMap ^ p = 0)
    {y : A} (hy : δ y = 1) (a : A) :
    ∃ b : ℕ → A, (∀ i, δ (b i) = 0) ∧ a = ∑ i ∈ range p, y ^ i * b i := by
  obtain ⟨b, hb, h⟩ := exists_taylor_of_mem δ p hδ hy ⊤ (fun _ _ => Algebra.mem_top)
    Algebra.mem_top (Algebra.mem_top (x := a))
  exact ⟨b, fun i => (hb i).2, h⟩

/-- The uniqueness in the Taylor formula for one derivation: if `δ y = 1`, `δ a_i = δ b_i = 0` and `Σ_(i<p) y^i a_i = Σ_(i<p) y^i b_i`, then `a_i = b_i` for `i < p`. -/
theorem taylor_coeff_unique (p : ℕ) [Fact p.Prime] [CharP A p] {y : A} (hy : δ y = 1)
    {a b : ℕ → A} (ha : ∀ i, δ (a i) = 0) (hb : ∀ i, δ (b i) = 0)
    (h : ∑ i ∈ range p, y ^ i * a i = ∑ i ∈ range p, y ^ i * b i) : ∀ i < p, a i = b i := by
  intro i hi
  have := taylor_coeff_eq_zero δ p hy p le_rfl (fun i => a i - b i)
    (fun i => by rw [map_sub, ha, hb, sub_self])
    (by simp only [mul_sub, sum_sub_distrib, h, sub_self]) i hi
  exact sub_eq_zero.mp this

end Taylor

section TaylorFamily

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The common constants of the derivations `δ_l` with `l ∈ T`, as a subalgebra of `A`. -/
def constantsOn (δ : ι → Derivation k A A) (T : Set ι) : Subalgebra k A where
  carrier := {a | ∀ l ∈ T, δ l a = 0}
  mul_mem' := by
    intro a b ha hb l hl
    simp [Derivation.leibniz, ha l hl, hb l hl]
  add_mem' := by
    intro a b ha hb l hl
    simp [ha l hl, hb l hl]
  algebraMap_mem' := by
    intro c l _
    exact (δ l).map_algebraMap c

/-- The subalgebra `A' = ⋂_l ker δ_l` of common constants of a family of derivations. -/
abbrev constants (δ : ι → Derivation k A A) : Subalgebra k A := constantsOn δ Set.univ

/-- An element is in `constantsOn δ T` if and only if each `δ_l` with `l ∈ T` kills it. -/
theorem mem_constantsOn {δ : ι → Derivation k A A} {T : Set ι} {a : A} :
    a ∈ constantsOn δ T ↔ ∀ l ∈ T, δ l a = 0 :=
  Iff.rfl

variable [Fintype ι] [DecidableEq ι]

/-- The monomial `y^c = Π_l y_l^(c_l)`. -/
def taylorMonomial (y : ι → A) (c : ι → ℕ) : A := ∏ l, y l ^ c l

/-- If `c_j = 0`, then setting the exponent of `y_j` to `i` multiplies `y^c` by `y_j^i`. -/
theorem taylorMonomial_update (y : ι → A) (c : ι → ℕ) (j : ι) (i : ℕ) (hc : c j = 0) :
    taylorMonomial y (Function.update c j i) = y j ^ i * taylorMonomial y c := by
  unfold taylorMonomial
  rw [← Finset.mul_prod_erase _ _ (mem_univ j), ← Finset.mul_prod_erase _ _ (mem_univ j)]
  simp only [Function.update_self, hc, pow_zero, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

/-- The factor `y_j^(c_j)` of the monomial `y^c`. -/
theorem taylorMonomial_eq_mul (y : ι → A) (c : ι → ℕ) (j : ι) :
    taylorMonomial y c = y j ^ c j * taylorMonomial y (Function.update c j 0) := by
  rw [← taylorMonomial_update y _ j (c j) (Function.update_self j 0 c)]
  simp

variable (δ : ι → Derivation k A A) (y : ι → A)

/-- If `δ_j y_l = 0` for `l ≠ j` and `c_j = 0`, then `δ_j (y^c) = 0`. -/
theorem derivation_taylorMonomial_eq_zero (hy : ∀ j l, δ j (y l) = if j = l then 1 else 0)
    (c : ι → ℕ) (j : ι) (hc : c j = 0) : δ j (taylorMonomial y c) = 0 := by
  have : taylorMonomial y c ∈ constantsOn δ {j} := by
    refine Subalgebra.prod_mem _ fun l _ => ?_
    rcases eq_or_ne l j with rfl | hl
    · rw [hc, pow_zero]
      exact Subalgebra.one_mem _
    · refine Subalgebra.pow_mem _ ?_ _
      intro m hm
      rw [Set.mem_singleton_iff.mp hm, hy j l]
      simp [Ne.symm hl]
  exact this j rfl

variable (p : ℕ) [Fact p.Prime] [CharP A p]

/-- The linear independence of the monomials, in an inductive form. Let `S` be a finite set of indices, and let `F` be a finite family of exponents `e t` with `e t l < p` and `e t l = 0` for `l ∉ S`. If `Σ_(t ∈ F) g_t y^(e t) = 0` with all `g_t` constants, then all `g_t` are zero. -/
theorem taylor_indep_aux (hy : ∀ j l, δ j (y l) = if j = l then 1 else 0) (T : Type*)
    (S : Finset ι) :
    ∀ (F : Finset T) (e : T → ι → ℕ) (g : T → A), Set.InjOn e F → (∀ t ∈ F, ∀ l, e t l < p) →
      (∀ t ∈ F, ∀ l ∉ S, e t l = 0) → (∀ t ∈ F, ∀ l, δ l (g t) = 0) →
      ∑ t ∈ F, g t * taylorMonomial y (e t) = 0 → ∀ t ∈ F, g t = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro F e g hinj _ hsupp _ hsum t ht
    have he : ∀ t' ∈ F, e t' = 0 := fun t' ht' =>
      funext fun l => hsupp t' ht' l (Finset.notMem_empty l)
    rw [Finset.sum_eq_single t] at hsum
    · simpa [he t ht, taylorMonomial] using hsum
    · intro t' ht' hne
      exact absurd (hinj ht' ht ((he t' ht').trans (he t ht).symm)) hne
    · intro h
      exact absurd ht h
  | insert j S hj ih =>
    intro F e g hinj hlt hsupp hg hsum
    have hsplit : ∑ t ∈ F, g t * taylorMonomial y (e t) = ∑ i ∈ range p, y j ^ i *
        ∑ t ∈ F with e t j = i, g t * taylorMonomial y (Function.update (e t) j 0) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun t => e t j) (t := range p)
        (fun t ht => mem_range.mpr (hlt t ht j))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [taylorMonomial_eq_mul y (e t) j, (Finset.mem_filter.mp ht).2]
      ring
    have hb0 : ∀ i, δ j (∑ t ∈ F with e t j = i,
        g t * taylorMonomial y (Function.update (e t) j 0)) = 0 := by
      intro i
      rw [map_sum]
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [Derivation.leibniz, derivation_taylorMonomial_eq_zero δ y hy _ j
        (Function.update_self j 0 _), hg t (Finset.mem_filter.mp ht).1 j]
      simp
    have hb := taylor_coeff_eq_zero (δ j) p (by simp [hy j j]) p le_rfl _ hb0
      (hsplit ▸ hsum)
    intro t ht
    refine ih (F.filter fun t' => e t' j = e t j) (fun t' => Function.update (e t') j 0) g
      ?_ ?_ ?_ ?_ (hb (e t j) (hlt t ht j)) t (Finset.mem_filter.mpr ⟨ht, rfl⟩)
    · intro t₁ h₁ t₂ h₂ h
      have h₁' := Finset.mem_filter.mp h₁
      have h₂' := Finset.mem_filter.mp h₂
      refine hinj h₁'.1 h₂'.1 (funext fun l => ?_)
      rcases eq_or_ne l j with rfl | hl
      · rw [h₁'.2, h₂'.2]
      · have := congrFun h l
        simp only [Function.update_of_ne hl] at this
        exact this
    · intro t' ht' l
      rcases eq_or_ne l j with rfl | hl
      · simp only [Function.update_self]
        exact (Fact.out : p.Prime).pos
      · simp only [Function.update_of_ne hl]
        exact hlt t' (Finset.mem_filter.mp ht').1 l
    · intro t' ht' l hl
      rcases eq_or_ne l j with rfl | hlj
      · simp only [Function.update_self]
      · simp only [Function.update_of_ne hlj]
        exact hsupp t' (Finset.mem_filter.mp ht').1 l (by simp [hlj, hl])
    · intro t' ht'
      exact hg t' (Finset.mem_filter.mp ht').1

/-- The Taylor lemma, the linear independence. Let `δ_1, …, δ_s` be derivations of `A` and let `y_1, …, y_s ∈ A` with `δ_j y_l = 1` if `j = l` and `0` if not. Then the monomials `y^c` with `c_j < p` are linearly independent over the common constants `A'`. -/
theorem linearIndependent_taylorMonomial
    (hy : ∀ j l, δ j (y l) = if j = l then 1 else 0) :
    LinearIndependent (constants δ) (fun c : ι → Fin p => taylorMonomial y fun l => (c l : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  have h := taylor_indep_aux δ y p hy (ι → Fin p) Finset.univ Finset.univ
    (fun c l => (c l : ℕ)) (fun c => (g c : A))
    (fun c₁ _ c₂ _ h => funext fun l => Fin.ext (congrFun h l))
    (fun c _ l => (c l).isLt) (fun _ _ l hl => absurd (mem_univ l) hl)
    (fun c _ l => (g c).2 l (Set.mem_univ l))
    (by simpa [Subalgebra.smul_def] using hg) c (mem_univ c)
  exact Subtype.ext h

/-- The monomials `y^c` with `c_l < p` for all `l` and `c_l = 0` for `l ∉ S`. -/
def taylorMonomials (S : Finset ι) : Set A :=
  {x | ∃ c : ι → ℕ, (∀ l, c l < p) ∧ (∀ l ∉ S, c l = 0) ∧ x = taylorMonomial y c}

omit [Fact p.Prime] [CharP A p] in
/-- Multiplication by `y_j^i` with `i < p` and `j ∉ S` maps the span of the monomials for `S` into the span of the monomials for `S ∪ {j}`. -/
theorem pow_mul_mem_span_taylorMonomials {S : Finset ι} {j : ι} (hj : j ∉ S) {i : ℕ} (hi : i < p)
    {x : A} (hx : x ∈ Submodule.span (constants δ) (taylorMonomials y p S)) :
    y j ^ i * x ∈ Submodule.span (constants δ) (taylorMonomials y p (insert j S)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hlt, hsupp, rfl⟩ := hx
    refine Submodule.subset_span ⟨Function.update c j i, fun l => ?_, fun l hl => ?_, ?_⟩
    · rcases eq_or_ne l j with rfl | hl
      · simpa using hi
      · simpa [Function.update_of_ne hl] using hlt l
    · rcases eq_or_ne l j with rfl | hlj
      · exact absurd (mem_insert_self l S) hl
      · rw [Function.update_of_ne hlj]
        exact hsupp l (by simp [hlj] at hl; exact hl)
    · rw [taylorMonomial_update y c j i (hsupp j hj)]
  | zero => simp
  | add x z _ _ hx hz =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hz
  | smul a x _ hx =>
    rw [Subalgebra.smul_def, smul_eq_mul, mul_left_comm, ← smul_eq_mul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ a hx

/-- The spanning part of the Taylor lemma, in an inductive form. If `δ_l a = 0` for all `l ∉ S`, then `a` is in the span over `A'` of the monomials `y^c` with `c_l < p` and `c_l = 0` for `l ∉ S`. -/
theorem taylor_span_aux (hcomm : ∀ l j a, δ l (δ j a) = δ j (δ l a))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = 0) (hy : ∀ j l, δ j (y l) = if j = l then 1 else 0)
    (S : Finset ι) :
    ∀ a : A, (∀ l ∉ S, δ l a = 0) →
      a ∈ Submodule.span (constants δ) (taylorMonomials y p S) := by
  induction S using Finset.induction_on with
  | empty =>
    intro a ha
    have h1 : (1 : A) ∈ taylorMonomials y p ∅ :=
      ⟨0, fun _ => (Fact.out : p.Prime).pos, fun _ _ => rfl, by simp [taylorMonomial]⟩
    have h2 := Submodule.smul_mem _ (⟨a, fun l _ => ha l (Finset.notMem_empty l)⟩ :
      constants δ) (Submodule.subset_span h1)
    simpa [Subalgebra.smul_def] using h2
  | insert j S hj ih =>
    intro a ha
    set B := constantsOn δ (↑(insert j S) : Set ι)ᶜ
    have hB : ∀ b ∈ B, δ j b ∈ B := by
      intro b hb l hl
      rw [hcomm l j b, hb l hl, map_zero]
    have hyB : y j ∈ B := by
      intro l hl
      have hlj : l ≠ j := fun h => hl (by simp [h])
      simp [hy l j, hlj]
    obtain ⟨b, hb, rfl⟩ := exists_taylor_of_mem (δ j) p (hδ j) (by simp [hy j j]) B hB hyB
      (fun l hl => ha l (by simpa using hl))
    refine Submodule.sum_mem _ fun i hi => pow_mul_mem_span_taylorMonomials δ y p hj
      (mem_range.mp hi) (ih (b i) fun l hl => ?_)
    rcases eq_or_ne l j with rfl | hlj
    · exact (hb i).2
    · exact (hb i).1 l (by simp [hlj, hl])

/-- The Taylor lemma, the spanning. Let `δ_1, …, δ_s` be commuting derivations of `A` with `δ_j^p = 0`, and let `y_1, …, y_s ∈ A` with `δ_j y_l = 1` if `j = l` and `0` if not. Then the monomials `y^c` with `c_j < p` span `A` over the common constants `A'`. -/
theorem span_taylorMonomial (hcomm : ∀ l j a, δ l (δ j a) = δ j (δ l a))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = 0) (hy : ∀ j l, δ j (y l) = if j = l then 1 else 0) :
    Submodule.span (constants δ)
      (Set.range fun c : ι → Fin p => taylorMonomial y fun l => (c l : ℕ)) = ⊤ := by
  refine eq_top_iff.mpr fun a _ => ?_
  refine Submodule.span_mono ?_ (taylor_span_aux δ y p hcomm hδ hy Finset.univ a
    fun l hl => absurd (mem_univ l) hl)
  rintro x ⟨c, hlt, -, rfl⟩
  exact ⟨fun l => ⟨c l, hlt l⟩, rfl⟩

/-- The Taylor lemma. Let `A` be a commutative ring of characteristic `p`, let `δ_1, …, δ_s` be commuting derivations of `A` with `δ_j^p = 0`, and let `y_1, …, y_s ∈ A` with `δ_j y_l = 1` if `j = l` and `0` if not. Then the monomials `y^c`, `c : ι → Fin p`, are a basis of `A` over the subalgebra `A' = ⋂_j ker δ_j`. -/
noncomputable def taylorBasis (hcomm : ∀ l j a, δ l (δ j a) = δ j (δ l a))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = 0) (hy : ∀ j l, δ j (y l) = if j = l then 1 else 0) :
    Module.Basis (ι → Fin p) (constants δ) A :=
  Module.Basis.mk (linearIndependent_taylorMonomial δ y p hy)
    (span_taylorMonomial δ y p hcomm hδ hy).ge

/-- The basis vector of `taylorBasis` with index `c` is the monomial `y^c`. -/
theorem taylorBasis_apply (hcomm : ∀ l j a, δ l (δ j a) = δ j (δ l a))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = 0) (hy : ∀ j l, δ j (y l) = if j = l then 1 else 0)
    (c : ι → Fin p) : taylorBasis δ y p hcomm hδ hy c = taylorMonomial y fun l => (c l : ℕ) :=
  Module.Basis.mk_apply _ _ _

end TaylorFamily

section Grading

open Polynomial

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] {p : ℕ} [Fact p.Prime] [CharP R p]

omit [Fact p.Prime] in
/-- The ring of `k`-linear endomorphisms of a ring of characteristic `p` has characteristic `p`. -/
theorem charP_moduleEnd : CharP (Module.End k R) p := by
  refine ⟨fun n => ?_⟩
  rw [← CharP.cast_eq_zero_iff R p n]
  constructor
  · intro h
    simpa [Module.End.natCast_apply] using LinearMap.congr_fun h 1
  · intro h
    exact LinearMap.ext fun x => by simp [Module.End.natCast_apply, nsmul_eq_mul, h]

attribute [local instance] charP_moduleEnd

/-- The image of `i : ZMod p` in the endomorphisms of `R` is multiplication by `i`. -/
theorem castHom_moduleEnd_apply (i : ZMod p) (g : R) :
    ZMod.castHom (dvd_refl p) (Module.End k R) i g = (ZMod.cast i : R) * g := by
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, Module.End.natCast_apply, nsmul_eq_mul,
    ZMod.natCast_val]

/-- The image of `i : ZMod p` in the endomorphisms of `R` commutes with each endomorphism. -/
theorem commute_castHom_moduleEnd (i : ZMod p) (f : Module.End k R) :
    Commute (ZMod.castHom (dvd_refl p) (Module.End k R) i) f := by
  rw [ZMod.castHom_apply, ← ZMod.natCast_val]
  exact Nat.cast_commute _ _

/-- The Lagrange identity `Σ_(i ∈ F_p) (1 - (X - i)^(p-1)) = 1` in `F_p[X]`. -/
theorem sum_one_sub_X_sub_C_pow :
    ∑ i : ZMod p, (1 - (X - C i) ^ (p - 1) : (ZMod p)[X]) = 1 := by
  have hp2 := (Fact.out : p.Prime).two_le
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := id)
    Function.injective_id (fun x => ?_) ?_
  · simp only [eval_sub, eval_finsetSum, eval_one, eval_pow, eval_X, eval_C, id]
    rw [Finset.sum_eq_single x]
    · simp [zero_pow (by omega : p - 1 ≠ 0)]
    · intro i _ hi
      rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr (Ne.symm hi)), sub_self]
    · simp
  · rw [ZMod.card]
    calc natDegree _ ≤ p - 1 := ?_
      _ < p := by omega
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    refine natDegree_pow_le.trans ?_
    simp

/-- The weight space `R_i = {g | δ g = i g}` of a derivation `δ`, for `i ∈ ZMod p`. -/
def weightSpace (δ : Derivation k R R) (i : ZMod p) : Submodule k R where
  carrier := {g | δ g = (ZMod.cast i : R) * g}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha, hb, mul_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c g hg
    simp only [Set.mem_ofPred_eq] at *
    rw [δ.map_smul, hg, mul_smul_comm]

omit [Fact p.Prime] [CharP R p] in
/-- An element `g` is in `R_i` if and only if `δ g = i g`. -/
theorem mem_weightSpace {δ : Derivation k R R} {i : ZMod p} {g : R} :
    g ∈ weightSpace δ i ↔ δ g = (ZMod.cast i : R) * g :=
  Iff.rfl

/-- The projection `π_i = 1 - (δ - i)^(p-1)` to the weight space `R_i`. It is the Lagrange polynomial of `i` for the roots of `X^p - X`, evaluated at `δ`. -/
def gradingProj (δ : Derivation k R R) (i : ZMod p) : Module.End k R :=
  1 - (δ.toLinearMap - ZMod.castHom (dvd_refl p) (Module.End k R) i) ^ (p - 1)

variable (δ : Derivation k R R)

/-- `(δ - i) π_i = 0` if `δ^p = δ`. -/
theorem sub_castHom_mul_gradingProj (hδ : δ.toLinearMap ^ p = δ.toLinearMap) (i : ZMod p) :
    (δ.toLinearMap - ZMod.castHom (dvd_refl p) (Module.End k R) i) * gradingProj δ i = 0 := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hX : (δ.toLinearMap - ZMod.castHom (dvd_refl p) (Module.End k R) i) ^ p =
      δ.toLinearMap - ZMod.castHom (dvd_refl p) (Module.End k R) i := by
    rw [sub_pow_char_of_commute p (commute_castHom_moduleEnd i _).symm, hδ, ← map_pow,
      ZMod.pow_card]
  unfold gradingProj
  rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega), hX, sub_self]

/-- The projections add up to the identity: `Σ_i π_i = 1`. -/
theorem sum_gradingProj : ∑ i : ZMod p, gradingProj δ i = 1 := by
  let φ := Polynomial.eval₂RingHom' (ZMod.castHom (dvd_refl p) (Module.End k R))
    δ.toLinearMap (fun a => commute_castHom_moduleEnd a _)
  have h := congrArg φ (sum_one_sub_X_sub_C_pow (p := p))
  have hX : φ X = δ.toLinearMap := eval₂_X _ _
  have hC : ∀ a, φ (C a) = ZMod.castHom (dvd_refl p) (Module.End k R) a := fun a => eval₂_C _ _
  simp only [map_sum, map_sub, map_one, map_pow, hX, hC] at h
  exact h

/-- Each element is the sum of its components: `g = Σ_i π_i g`. -/
theorem sum_gradingProj_apply (g : R) : ∑ i : ZMod p, gradingProj δ i g = g := by
  have h := LinearMap.congr_fun (sum_gradingProj δ) g
  rw [LinearMap.sum_apply] at h
  exact h

/-- The component `π_i g` is in `R_i` if `δ^p = δ`. -/
theorem gradingProj_mem (hδ : δ.toLinearMap ^ p = δ.toLinearMap) (i : ZMod p) (g : R) :
    gradingProj δ i g ∈ weightSpace δ i := by
  have h := LinearMap.congr_fun (sub_castHom_mul_gradingProj δ hδ i) g
  rw [Module.End.mul_apply, LinearMap.sub_apply, castHom_moduleEnd_apply, LinearMap.zero_apply,
    sub_eq_zero] at h
  exact h

/-- On `R_j` the map `δ - i` is multiplication by `j - i`. -/
theorem sub_castHom_apply_of_mem {j : ZMod p} {g : R} (hg : g ∈ weightSpace δ j) (i : ZMod p) :
    (δ.toLinearMap - ZMod.castHom (dvd_refl p) (Module.End k R) i) g =
      (ZMod.cast (j - i) : R) * g := by
  rw [LinearMap.sub_apply, castHom_moduleEnd_apply, ZMod.cast_sub', sub_mul]
  exact congrArg (· - _) hg

omit [CharP R p] in
/-- The weight space `R_j` is stable under multiplication by the elements of `ZMod p`. -/
theorem cast_mul_mem_weightSpace {j : ZMod p} {g : R} (hg : g ∈ weightSpace δ j) (z : ZMod p) :
    (ZMod.cast z : R) * g ∈ weightSpace δ j := by
  rw [← ZMod.natCast_val, ← nsmul_eq_mul]
  exact nsmul_mem hg _

/-- On `R_j` the map `(δ - i)^n` is multiplication by `(j - i)^n`. -/
theorem pow_sub_castHom_apply_of_mem {j : ZMod p} {g : R} (hg : g ∈ weightSpace δ j)
    (i : ZMod p) (n : ℕ) :
    ((δ.toLinearMap - ZMod.castHom (dvd_refl p) (Module.End k R) i) ^ n) g =
      (ZMod.cast ((j - i) ^ n) : R) * g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih,
      sub_castHom_apply_of_mem δ (cast_mul_mem_weightSpace δ hg _) i, pow_succ',
      ZMod.cast_mul', mul_assoc]

/-- `π_i` is the identity on `R_i` and zero on `R_j` for `j ≠ i`. -/
theorem gradingProj_apply_of_mem {j : ZMod p} {g : R} (hg : g ∈ weightSpace δ j) (i : ZMod p) :
    gradingProj δ i g = if j = i then g else 0 := by
  have hp2 := (Fact.out : p.Prime).two_le
  unfold gradingProj
  rw [LinearMap.sub_apply, Module.End.one_apply, pow_sub_castHom_apply_of_mem δ hg]
  split_ifs with h
  · rw [h, sub_self, zero_pow (by omega), ZMod.cast_zero, zero_mul, sub_zero]
  · rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr h), ZMod.cast_one', one_mul, sub_self]

/-- The uniqueness of the decomposition: if `g = Σ_i g_i` with `g_i ∈ R_i`, then `g_i = π_i g`. -/
theorem eq_gradingProj_of_sum {c : ZMod p → R} (hc : ∀ i, c i ∈ weightSpace δ i) {g : R}
    (hg : g = ∑ i, c i) (i : ZMod p) : c i = gradingProj δ i g := by
  rw [hg, map_sum]
  simp [gradingProj_apply_of_mem δ (hc _)]

/-- The sum of the weight spaces is direct: if `Σ_i g_i = 0` with `g_i ∈ R_i`, then all `g_i` are zero. -/
theorem eq_zero_of_sum_weightSpace {c : ZMod p → R} (hc : ∀ i, c i ∈ weightSpace δ i)
    (h : ∑ i, c i = 0) (i : ZMod p) : c i = 0 := by
  rw [eq_gradingProj_of_sum δ hc h.symm, map_zero]

/-- The Leibniz rule gives `R_i R_j ⊆ R_(i+j)`. -/
theorem mul_mem_weightSpace {i j : ZMod p} {g h : R} (hg : g ∈ weightSpace δ i)
    (hh : h ∈ weightSpace δ j) : g * h ∈ weightSpace δ (i + j) := by
  rw [mem_weightSpace] at *
  rw [Derivation.leibniz, hg, hh, ZMod.cast_add', smul_eq_mul, smul_eq_mul]
  ring

omit [CharP R p] in
/-- `1 ∈ R_0`. -/
theorem one_mem_weightSpace_zero : (1 : R) ∈ weightSpace δ (0 : ZMod p) := by
  simp [mem_weightSpace]

end Grading

section MultiGrading

open scoped IsMulCommutative

variable {k R ι : Type*} [CommRing k] [CommRing R] [Algebra k R] {p : ℕ} [Fact p.Prime]
  [CharP R p]

/-- The common weight space `R_χ = {g | δ_l g = χ_l g for all l}` of a family of derivations, for a weight `χ : ι → ZMod p`. -/
def commonWeightSpace (δ : ι → Derivation k R R) (χ : ι → ZMod p) : Submodule k R :=
  ⨅ l, weightSpace (δ l) (χ l)

omit [Fact p.Prime] [CharP R p] in
/-- An element `g` is in `R_χ` if and only if `δ_l g = χ_l g` for all `l`. -/
theorem mem_commonWeightSpace {δ : ι → Derivation k R R} {χ : ι → ZMod p} {g : R} :
    g ∈ commonWeightSpace δ χ ↔ ∀ l, δ l g = (ZMod.cast (χ l) : R) * g := by
  simp [commonWeightSpace, Submodule.mem_iInf, mem_weightSpace]

variable (δ : ι → Derivation k R R)

/-- The Leibniz rule gives `R_χ R_ψ ⊆ R_(χ+ψ)`. -/
theorem mul_mem_commonWeightSpace {χ ψ : ι → ZMod p} {g h : R}
    (hg : g ∈ commonWeightSpace δ χ) (hh : h ∈ commonWeightSpace δ ψ) :
    g * h ∈ commonWeightSpace δ (χ + ψ) := by
  rw [commonWeightSpace, Submodule.mem_iInf] at *
  exact fun l => mul_mem_weightSpace (δ l) (hg l) (hh l)

omit [CharP R p] in
/-- `1 ∈ R_0`. -/
theorem one_mem_commonWeightSpace_zero : (1 : R) ∈ commonWeightSpace δ (0 : ι → ZMod p) := by
  rw [commonWeightSpace, Submodule.mem_iInf]
  exact fun l => one_mem_weightSpace_zero (δ l)

attribute [local instance] charP_moduleEnd

variable [Fintype ι] [DecidableEq ι]

/-- The projections to the common weight spaces. For commuting `δ_l` with `δ_l^p = δ_l` there are `k`-linear maps `π_χ` with `Σ_χ π_χ = 1`, `π_χ g ∈ R_χ`, `π_ψ g = g` for `g ∈ R_ψ` and `π_ψ g = 0` for `g ∈ R_χ` with `χ ≠ ψ`. Each `π_χ` maps each `k`-submodule that is stable under all `δ_l` into itself, because `π_χ = Π_l π_(l, χ_l)` is a polynomial in the `δ_l`. -/
theorem exists_commonWeightSpace_proj (hcomm : ∀ l j g, δ l (δ j g) = δ j (δ l g))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = (δ l).toLinearMap) :
    ∃ π : (ι → ZMod p) → Module.End k R, (∑ χ, π χ = 1) ∧
      (∀ χ g, π χ g ∈ commonWeightSpace δ χ) ∧
      (∀ χ ψ g, g ∈ commonWeightSpace δ χ → π ψ g = if χ = ψ then g else 0) ∧
      (∀ N : Submodule k R, (∀ l, ∀ g ∈ N, δ l g ∈ N) → ∀ χ, ∀ g ∈ N, π χ g ∈ N) := by
  set s : Set (Module.End k R) := Set.range fun l => (δ l).toLinearMap with hs_def
  have hs : s.Pairwise Commute := by
    rintro _ ⟨l, rfl⟩ _ ⟨m, rfl⟩ _
    exact LinearMap.ext fun g => hcomm l m g
  set B := Algebra.adjoin k s
  have : IsMulCommutative B := Algebra.isMulCommutative_adjoin k hs
  have hDB : ∀ l, (δ l).toLinearMap ∈ B := fun l => Algebra.subset_adjoin ⟨l, rfl⟩
  have hmem : ∀ l i, gradingProj (δ l) i ∈ B := by
    intro l i
    unfold gradingProj
    refine B.sub_mem B.one_mem (B.pow_mem (B.sub_mem (hDB l) ?_) _)
    rw [ZMod.castHom_apply, ← ZMod.natCast_val]
    exact B.natCast_mem _
  let π' : ι → ZMod p → B := fun l i => ⟨gradingProj (δ l) i, hmem l i⟩
  have hsum : ∀ l, ∑ i, π' l i = 1 := fun l => Subtype.ext (by simp [π', sum_gradingProj])
  let P : (ι → ZMod p) → B := fun χ => ∏ l, π' l (χ l)
  have hPsum : ∑ χ, P χ = 1 := by
    have h := Finset.prod_univ_sum (fun _ : ι => (univ : Finset (ZMod p))) (fun l i => π' l i)
    rw [Fintype.piFinset_univ] at h
    simp only [P, ← h, hsum, prod_const_one]
  have hfac : ∀ χ l, ((P χ : B) : Module.End k R) =
      gradingProj (δ l) (χ l) * ((∏ m ∈ univ.erase l, π' m (χ m) : B) : Module.End k R) := by
    intro χ l
    show ((∏ m, π' m (χ m) : B) : Module.End k R) = _
    rw [← Finset.mul_prod_erase _ _ (mem_univ l)]
    rfl
  have hind : ∀ (χ ψ : ι → ZMod p) (g : R), g ∈ commonWeightSpace δ χ → ∀ S : Finset ι,
      ((∏ l ∈ S, π' l (ψ l) : B) : Module.End k R) g =
        if (∀ l ∈ S, χ l = ψ l) then g else 0 := by
    intro χ ψ g hg S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      rw [Finset.prod_insert hj]
      change gradingProj (δ j) (ψ j) (((∏ l ∈ S, π' l (ψ l) : B) : Module.End k R) g) = _
      rw [ih]
      have hgj : g ∈ weightSpace (δ j) (χ j) := by
        rw [commonWeightSpace, Submodule.mem_iInf] at hg
        exact hg j
      by_cases hS : ∀ l ∈ S, χ l = ψ l
      · rw [ite_eq_left hS, gradingProj_apply_of_mem (δ j) hgj]
        by_cases hj' : χ j = ψ j
        · rw [ite_eq_left hj', ite_eq_left]
          intro l hl
          rcases Finset.mem_insert.mp hl with rfl | hl
          · exact hj'
          · exact hS l hl
        · rw [ite_eq_right hj', ite_eq_right]
          exact fun h => hj' (h j (mem_insert_self j S))
      · rw [ite_eq_right hS, map_zero, ite_eq_right]
        exact fun h => hS fun l hl => h l (mem_insert_of_mem hl)
  refine ⟨fun χ => (P χ : Module.End k R), ?_, ?_, ?_, ?_⟩
  · have h := congrArg Subtype.val hPsum
    simpa using h
  · intro χ g
    rw [mem_commonWeightSpace]
    intro l
    have h := LinearMap.congr_fun (sub_castHom_mul_gradingProj (δ l) (hδ l) (χ l))
      (((∏ m ∈ univ.erase l, π' m (χ m) : B) : Module.End k R) g)
    rw [Module.End.mul_apply, LinearMap.sub_apply, castHom_moduleEnd_apply, LinearMap.zero_apply,
      sub_eq_zero] at h
    show δ l ((P χ : Module.End k R) g) = (ZMod.cast (χ l) : R) * (P χ : Module.End k R) g
    rw [hfac χ l, Module.End.mul_apply]
    exact h
  · intro χ ψ g hg
    have h := hind χ ψ g hg univ
    simp only [mem_univ, true_implies] at h
    rw [h]
    exact if_congr funext_iff.symm rfl rfl
  · intro N hN χ g hg
    let T : Subalgebra k (Module.End k R) :=
      { carrier := {f | ∀ x ∈ N, f x ∈ N}
        mul_mem' := fun ha hb x hx => ha _ (hb x hx)
        add_mem' := fun ha hb x hx => N.add_mem (ha x hx) (hb x hx)
        algebraMap_mem' := fun c x hx => by
          rw [Module.algebraMap_end_apply]
          exact N.smul_mem c hx }
    have hBT : B ≤ T := Algebra.adjoin_le (by rintro _ ⟨l, rfl⟩ x hx; exact hN l x hx)
    exact hBT (P χ).2 g hg

/-- The grading lemma, the existence of the decomposition. For commuting `δ_l` with `δ_l^p = δ_l`, each `g ∈ R` is a sum `Σ_χ g_χ` with `g_χ ∈ R_χ`. -/
theorem exists_sum_commonWeightSpace (hcomm : ∀ l j g, δ l (δ j g) = δ j (δ l g))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = (δ l).toLinearMap) (g : R) :
    ∃ c : (ι → ZMod p) → R, (∀ χ, c χ ∈ commonWeightSpace δ χ) ∧ g = ∑ χ, c χ := by
  obtain ⟨π, h1, h2, -, -⟩ := exists_commonWeightSpace_proj δ hcomm hδ
  refine ⟨fun χ => π χ g, fun χ => h2 χ g, ?_⟩
  have h := LinearMap.congr_fun h1 g
  rw [LinearMap.sum_apply] at h
  exact h.symm

/-- The grading lemma, the sum is direct. If `Σ_χ g_χ = 0` with `g_χ ∈ R_χ`, then all `g_χ` are zero. -/
theorem eq_zero_of_sum_commonWeightSpace (hcomm : ∀ l j g, δ l (δ j g) = δ j (δ l g))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = (δ l).toLinearMap) {c : (ι → ZMod p) → R}
    (hc : ∀ χ, c χ ∈ commonWeightSpace δ χ) (h : ∑ χ, c χ = 0) (χ : ι → ZMod p) : c χ = 0 := by
  obtain ⟨π, -, -, h3, -⟩ := exists_commonWeightSpace_proj δ hcomm hδ
  have h' := congrArg (π χ) h
  rw [map_sum, map_zero] at h'
  simpa [h3 _ χ _ (hc _)] using h'

/-- The grading lemma, the uniqueness of the decomposition. -/
theorem eq_of_sum_commonWeightSpace (hcomm : ∀ l j g, δ l (δ j g) = δ j (δ l g))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = (δ l).toLinearMap) {c d : (ι → ZMod p) → R}
    (hc : ∀ χ, c χ ∈ commonWeightSpace δ χ) (hd : ∀ χ, d χ ∈ commonWeightSpace δ χ)
    (h : ∑ χ, c χ = ∑ χ, d χ) : c = d := by
  funext χ
  refine sub_eq_zero.mp (eq_zero_of_sum_commonWeightSpace δ hcomm hδ
    (c := fun χ => c χ - d χ) (fun χ => Submodule.sub_mem _ (hc χ) (hd χ)) ?_ χ)
  rw [sum_sub_distrib, h, sub_self]

/-- An ideal is stable under all `δ_l` if and only if it contains the components of each of its elements, that is, if and only if it is a graded ideal. -/
theorem forall_derivation_mem_iff (hcomm : ∀ l j g, δ l (δ j g) = δ j (δ l g))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = (δ l).toLinearMap) (I : Ideal R) :
    (∀ l, ∀ g ∈ I, δ l g ∈ I) ↔ ∀ g ∈ I, ∀ c : (ι → ZMod p) → R,
      (∀ χ, c χ ∈ commonWeightSpace δ χ) → g = ∑ χ, c χ → ∀ χ, c χ ∈ I := by
  constructor
  · intro hI g hg c hc hgc χ
    obtain ⟨π, -, -, h3, h4⟩ := exists_commonWeightSpace_proj δ hcomm hδ
    have h := congrArg (π χ) hgc
    rw [map_sum] at h
    simp only [h3 _ χ _ (hc _), sum_ite_eq', mem_univ, ite_true] at h
    rw [← h]
    exact h4 (I.restrictScalars k) hI χ g hg
  · intro hI l g hg
    obtain ⟨c, hc, hgc⟩ := exists_sum_commonWeightSpace δ hcomm hδ g
    have hcI := hI g hg c hc hgc
    rw [hgc, map_sum]
    refine I.sum_mem fun χ _ => ?_
    rw [mem_commonWeightSpace.mp (hc χ) l]
    exact I.mul_mem_left _ (hcI χ)

omit [Fintype ι] [DecidableEq ι] in
open IsLocalRing in
/-- If `R` is local and `δ_l(R) ⊆ 𝔪` for all `l`, then `R_χ ⊆ 𝔪` for `χ ≠ 0`. -/
theorem mem_maximalIdeal_of_mem_commonWeightSpace [IsLocalRing R]
    (hm : ∀ l g, δ l g ∈ maximalIdeal R) {χ : ι → ZMod p} (hχ : χ ≠ 0) {g : R}
    (hg : g ∈ commonWeightSpace δ χ) : g ∈ maximalIdeal R := by
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hχ
  have h1 : (ZMod.cast (χ l) : R) * g ∈ maximalIdeal R := by
    rw [← mem_commonWeightSpace.mp hg l]
    exact hm l g
  have h2 : (ZMod.cast (χ l)⁻¹ : R) * (ZMod.cast (χ l) : R) = 1 := by
    rw [← ZMod.cast_mul', inv_mul_cancel₀ hl, ZMod.cast_one']
  have h3 := (maximalIdeal R).mul_mem_left (ZMod.cast (χ l)⁻¹ : R) h1
  rwa [← mul_assoc, h2, one_mul] at h3

open IsLocalRing in
/-- If `R` is local and `δ_l(R) ⊆ 𝔪` for all `l`, then in each decomposition `u = Σ_χ u_χ` of a unit `u` with `u_χ ∈ R_χ`, the component `u_0` of weight `0` is a unit. -/
theorem isUnit_zero_of_sum_commonWeightSpace [IsLocalRing R]
    (hm : ∀ l g, δ l g ∈ maximalIdeal R) {u : R} (hu : IsUnit u) {c : (ι → ZMod p) → R}
    (hc : ∀ χ, c χ ∈ commonWeightSpace δ χ) (h : u = ∑ χ, c χ) : IsUnit (c 0) := by
  by_contra h0
  have h0' : c 0 ∈ maximalIdeal R := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h0)
  have hall : ∀ χ, c χ ∈ maximalIdeal R := by
    intro χ
    rcases eq_or_ne χ 0 with rfl | hχ
    · exact h0'
    · exact mem_maximalIdeal_of_mem_commonWeightSpace δ hm hχ (hc χ)
  have hu' : u ∈ maximalIdeal R := h ▸ Ideal.sum_mem _ fun χ _ => hall χ
  exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hu')) hu

open IsLocalRing in
/-- If `R` is local and `δ_l(R) ⊆ 𝔪` for all `l`, then each unit `u` has a decomposition `u = Σ_χ u_χ` with `u_χ ∈ R_χ`, and its component `u_0` of weight `0` is a unit. -/
theorem exists_isUnit_zero_component [IsLocalRing R] (hcomm : ∀ l j g, δ l (δ j g) = δ j (δ l g))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = (δ l).toLinearMap) (hm : ∀ l g, δ l g ∈ maximalIdeal R)
    {u : R} (hu : IsUnit u) :
    ∃ c : (ι → ZMod p) → R, (∀ χ, c χ ∈ commonWeightSpace δ χ) ∧ u = ∑ χ, c χ ∧ IsUnit (c 0) := by
  obtain ⟨c, hc, h⟩ := exists_sum_commonWeightSpace δ hcomm hδ u
  exact ⟨c, hc, h, isUnit_zero_of_sum_commonWeightSpace δ hm hu hc h⟩

open IsLocalRing in
/-- If `R` is local, a principal ideal that is stable under all `δ_l` has a generator in some `R_χ`. -/
theorem exists_mem_commonWeightSpace_span_eq [IsLocalRing R]
    (hcomm : ∀ l j g, δ l (δ j g) = δ j (δ l g))
    (hδ : ∀ l, (δ l).toLinearMap ^ p = (δ l).toLinearMap) {g : R}
    (hI : ∀ l, ∀ x ∈ Ideal.span {g}, δ l x ∈ Ideal.span {g}) :
    ∃ χ : ι → ZMod p, ∃ h ∈ commonWeightSpace δ χ, Ideal.span {g} = Ideal.span {h} := by
  by_cases hg0 : g = 0
  · exact ⟨0, 0, Submodule.zero_mem _, by rw [hg0]⟩
  obtain ⟨c, hc, hgc⟩ := exists_sum_commonWeightSpace δ hcomm hδ g
  have hcI := (forall_derivation_mem_iff δ hcomm hδ _).mp hI g (Ideal.mem_span_singleton_self g)
    c hc hgc
  choose a ha using fun χ => Ideal.mem_span_singleton'.mp (hcI χ)
  have hsum : (1 - ∑ χ, a χ) * g = 0 := by
    rw [sub_mul, one_mul, sum_mul]
    simp only [ha]
    rw [← hgc, sub_self]
  have hnot : ∑ χ, a χ ∉ maximalIdeal R := by
    intro hmem
    have hunit : IsUnit (1 - ∑ χ, a χ) := by
      by_contra hnu
      have h1 : 1 - ∑ χ, a χ ∈ maximalIdeal R := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
      have h2 := (maximalIdeal R).add_mem h1 hmem
      rw [sub_add_cancel] at h2
      exact (maximalIdeal R).ne_top_iff_one.mp (maximalIdeal.isMaximal R).ne_top h2
    exact hg0 ((hunit.mul_right_eq_zero).mp hsum)
  obtain ⟨χ, hχ⟩ : ∃ χ, a χ ∉ maximalIdeal R := by
    by_contra hall
    exact hnot (Ideal.sum_mem _ fun χ _ => not_not.mp fun h => hall ⟨χ, h⟩)
  have hunit : IsUnit (a χ) := by
    by_contra hnu
    exact hχ ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
  refine ⟨χ, c χ, hc χ, ?_⟩
  rw [← ha χ, Ideal.span_singleton_mul_left_unit hunit]

end MultiGrading

end Singularity
