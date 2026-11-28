/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogDerivations
import Singularity.Valuation.LatticeLemmaOrdered
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Order.Monoid.Lex
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The toric step and the log Jacobian criterion in monomial models

This file proves parts of Volume V, Lemma 4.3.12 (the toric step) and of Volume V,
Corollary 4.4.17 (the log Jacobian criterion) of the handbook. Both are done in a monomial or
polynomial model.

## The toric step (Lemma 4.3.12)

The lattice is `M = ℤ^n`, with the coordinates of the basis `e_z, e_i (i ≠ z₀)`. The index `z₀`
also names the parameter `x_1`, so `e_1 = p e_z - ∑_{i ≠ z₀} r_i e_i` is stored at `z₀`. The
valuation enters only through an additive map `ℓ : ℤ^n → Γ` to an ordered group. In the
handbook `ℓ = w ∘ χ`.

* `toricParamVec`: the vectors `e_1, ..., e_d` of Step 1.
* `nsmul_single_eq_toricParamVec`: `p e_z = e_1 + ∑_{i ≠ z₀} r_i e_i` (Step 1).
* `toric_pos_single`: `ℓ(e_i) > 0` for all `i` gives `ℓ(e_z) > 0` (Step 1).
* `toricMonomial`, `toricChar`, `toricMonomial_toricParamVec`: the character `χ` in a
  commutative group, and `χ(e_i) = x_i` when `z^p = x_1 ∏ x_i^{r_i}` (Step 1).
* `toricOrderHom`, `toricOrderHom_pos_iff`: the order of Step 2, as the map `a ↦ (ℓ(a), a)`
  to a lexicographic product, and its set `P` of positive elements (Step 2).
* `exists_toric_basis`: the basis of Step 3, from the lattice lemma
  (`Singularity.latticeLemma_of_injective`, Volume V, Lemma 2.1.4).
* `toricMonomial_vecMul`, `toricMonomial_eq_prod_pow`: the toric substitution on Laurent
  monomials. If `a = ∑_l c_l u_l` with `c_l ≥ 0`, then `χ(a) = ∏_l U_l^{c_l}` with `U_l = χ(u_l)`.
* `exists_toric_chart`: Steps 1 to 3 together. There are `U_l = χ(u_l)` with `ℓ(u_l) ≥ 0` such
  that `z` and each `x_i` are monomials in the `U_l` with exponents in `ℕ`.
* `toric_sum_pos_of_prod_mem`, `toric_prod_mem_sq`, `toric_prod_eq_of_sum_eq_one`: the three
  cases `δ_i ≥ 1`, `δ_i ≥ 2` and `δ_i = 1` of Step 6, for monomials in a commutative ring.
* `nsmul_mem_span_toricParamVec`, `exists_toricParamVec_vecMul_ne_zero`: `p M ⊆ M_1`, and each
  `Y_l` divides some `Y^{c_i}` (the combinatorial part of Step 7).
* `toricExample_mul`, `toricExample_mul'`, `toricExample_coords`, `toricExample_monomials`: the
  basis, the coordinates and the monomials of Example 4.3.13.

Not proved for Lemma 4.3.12:

* The link of `ℓ` with a valuation `w` of a field `E'`: the file does not show that `ℓ = w ∘ χ`
  is additive, and it does not show `U_l ∈ O_w` from `ℓ(u_l) ≥ 0`.
* Step 4 (the rings `T`, `P_Y`, `B`, `C` and the surjection `C_{Q_C} → T_Q`).
* Step 5 (`B` is regular, with the regular sequence `x_1, ..., x_d, Y_j (j ∈ J)`).
* Step 6 beyond the monomial cases: the linear independence of the classes of the `g_i` in
  `n / n^2`, and the regularity of `C_{Q_C}`.
* Step 7 beyond the combinatorics: `C ⊗_R E ≅ E'`, the irreducibility of `Z^p - z^p`, and the
  degree count.
* Step 8 (injectivity of `C_{Q_C} → T_Q`) and Step 9 (the affine model).
* In Example 4.3.13 the ring `T_Q` and the discrete valuation ring are not done.

There is no invariant that decreases in Lemma 4.3.12, so no decrease is proved here.

## The log Jacobian criterion (Corollary 4.4.17)

The model is `k[x_i : i ∈ σ]` with the divisor `x_i = 0` for `i ∈ Δ`, as in
`Singularity.Invariant.LogDerivations`.

* `logJacobian_eq_span_of_monomial_unit`: Proposition 4.4.15, part 1, for `t = u x^a` with a
  constant `u`. The file `LogDerivations.lean` has the case `u = 1`.
* `IsFoliatedMonomialPoly`: the ramified type of a foliated monomial element (Definition 4.4.6)
  in the polynomial model, with coefficients `c_i ∈ k[x]`.
* `IsFoliatedMonomialPoly.exists_logJacobian_eq_span`: a foliated monomial element has a
  principal log Jacobian ideal for some divisor (Corollary 4.4.17, first direction).
* `IsFoliatedMonomialPoly.exists_derivationIdeal_eq_span`: the same with a nonzero generator,
  for the ideal `J_Δ(f)` of values of the tangent derivations, over a perfect field, if `f` is
  not a `p`-th power in `k[x]` (Corollary 4.4.17, first direction).

Not proved for Corollary 4.4.17:

* The second direction: a principal `J_D(f)` gives a first integral of monomial type. This is
  Theorem 4.4.16. Only its first step is in Lean (`span_eq_top_of_span_eq_span_singleton`).
* The regular local ring `R` of the handbook. The model here is a polynomial ring, which is not
  local. The coefficients `c_i` are in `k[x]`, not in the fraction field `E`. The condition
  `f ∉ E^p` is replaced by the condition that `f` is not a `p`-th power in `k[x]`.
* The unit `u` is a constant of `k`, not a general unit of `R`. The residual type
  (Proposition 4.4.15, part 2) does not occur in this model and is not treated.
-/

open MvPolynomial

namespace Singularity

/-! ### The toric step: the lattice and the characters (Lemma 4.3.12, Steps 1 to 3) -/

section ToricLattice

open Matrix

variable {n : ℕ}

/-- The vectors `e_i` of Volume V, Lemma 4.3.12, Step 1, in the coordinates of the basis
`e_z, e_i (i ≠ z₀)` of `M = ℤ^n`. The index `z₀` plays two roles. As a coordinate it is `e_z`.
As a value of the family it is `e_1 = p e_z - ∑_{i ≠ z₀} r_i e_i`. For `i ≠ z₀` the vector is
the basis vector `e_i`. -/
def toricParamVec (p : ℕ) (r : Fin n → ℕ) (z₀ : Fin n) (i : Fin n) : Fin n → ℤ :=
  if i = z₀ then
    p • (Pi.single z₀ 1 : Fin n → ℤ) - ∑ j ∈ Finset.univ.erase z₀, r j • Pi.single j 1
  else Pi.single i 1

theorem toricParamVec_of_ne {p : ℕ} {r : Fin n → ℕ} {z₀ i : Fin n} (h : i ≠ z₀) :
    toricParamVec p r z₀ i = Pi.single i 1 := by
  simp [toricParamVec, h]

theorem toricParamVec_self (p : ℕ) (r : Fin n → ℕ) (z₀ : Fin n) :
    toricParamVec p r z₀ z₀ =
      p • (Pi.single z₀ 1 : Fin n → ℤ) - ∑ j ∈ Finset.univ.erase z₀, r j • Pi.single j 1 := by
  simp only [toricParamVec, ↓reduceIte]

/-- The relation `p e_z = e_1 + ∑_{i ≠ z₀} r_i e_i` of Step 1. -/
theorem nsmul_single_eq_toricParamVec (p : ℕ) (r : Fin n → ℕ) (z₀ : Fin n) :
    p • (Pi.single z₀ 1 : Fin n → ℤ) =
      toricParamVec p r z₀ z₀ + ∑ j ∈ Finset.univ.erase z₀, r j • toricParamVec p r z₀ j := by
  have hs : ∑ j ∈ Finset.univ.erase z₀, r j • toricParamVec p r z₀ j =
      ∑ j ∈ Finset.univ.erase z₀, r j • (Pi.single j 1 : Fin n → ℤ) :=
    Finset.sum_congr rfl fun j hj => by rw [toricParamVec_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hs, toricParamVec_self, sub_add_cancel]

/-- **Step 1 of the toric step.** Let `ℓ : M → Γ` be additive, with values in an ordered group.
If `ℓ(e_i) > 0` for each `i`, then `ℓ(e_z) > 0`. In the handbook `ℓ = w ∘ χ`. -/
theorem toric_pos_single {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    {p : ℕ} (r : Fin n → ℕ) (z₀ : Fin n) (ℓ : (Fin n → ℤ) →+ Γ)
    (h : ∀ i, 0 < ℓ (toricParamVec p r z₀ i)) : 0 < ℓ (Pi.single z₀ 1) := by
  have key := congrArg ℓ (nsmul_single_eq_toricParamVec p r z₀)
  rw [map_nsmul, map_add, map_sum] at key
  have hsum : 0 ≤ ∑ j ∈ Finset.univ.erase z₀, ℓ (r j • toricParamVec p r z₀ j) :=
    Finset.sum_nonneg fun j _ => by rw [map_nsmul]; exact nsmul_nonneg (h j).le _
  have hpos : 0 < p • ℓ (Pi.single z₀ 1) := by
    rw [key]; exact add_pos_of_pos_of_nonneg (h z₀) hsum
  by_contra hle
  push Not at hle
  exact absurd hpos (not_lt.2 (nsmul_nonpos hle p))

/-- The Laurent monomial `y^a = ∏ y_i ^ a_i` in a commutative group, for `a ∈ ℤ^n`. With
`y = (z, x_i (i ≠ z₀))` this is the character `χ` of Step 1. -/
def toricMonomial {G : Type*} [CommGroup G] (y : Fin n → G) (a : Fin n → ℤ) : G :=
  ∏ i, y i ^ a i

/-- The character `χ` as an additive map to `Additive G`. -/
def toricChar {G : Type*} [CommGroup G] (y : Fin n → G) : (Fin n → ℤ) →+ Additive G where
  toFun a := Additive.ofMul (toricMonomial y a)
  map_zero' := by simp [toricMonomial]
  map_add' a b := by
    simp only [toricMonomial, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
    rfl

theorem toricChar_apply {G : Type*} [CommGroup G] (y : Fin n → G) (a : Fin n → ℤ) :
    Additive.toMul (toricChar y a) = toricMonomial y a := rfl

theorem toricMonomial_single {G : Type*} [CommGroup G] (y : Fin n → G) (j : Fin n) :
    toricMonomial y (Pi.single j 1) = y j := by
  rw [toricMonomial, Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, zpow_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **The character of Step 1.** Let `y = (z at z₀, x_i at i ≠ z₀)`, and let
`z^p = x_{z₀} ∏_{i ≠ z₀} x_i^{r_i}`. Then `χ(e_i) = x_i` for each `i`, and `χ(e_z) = z`. -/
theorem toricMonomial_toricParamVec {G : Type*} [CommGroup G] {p : ℕ} {r : Fin n → ℕ}
    {z₀ : Fin n} {x : Fin n → G} {z : G}
    (hz : z ^ p = x z₀ * ∏ j ∈ Finset.univ.erase z₀, x j ^ r j) (i : Fin n) :
    toricMonomial (Function.update x z₀ z) (toricParamVec p r z₀ i) = x i := by
  by_cases hi : i = z₀
  · subst hi
    have h1 : ∀ j ∈ Finset.univ.erase i,
        toricMonomial (Function.update x i z) (Pi.single j 1) = x j := fun j hj => by
      rw [toricMonomial_single, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have h2 : ∏ j ∈ Finset.univ.erase i,
        toricMonomial (Function.update x i z) (Pi.single j 1) ^ r j =
          ∏ j ∈ Finset.univ.erase i, x j ^ r j :=
      Finset.prod_congr rfl fun j hj => by rw [h1 j hj]
    rw [← toricChar_apply, toricParamVec_self, map_sub, map_nsmul, map_sum, toMul_sub,
      toMul_nsmul, toricChar_apply, toricMonomial_single, Function.update_self, hz,
      toMul_sum]
    simp only [map_nsmul, toMul_nsmul, toricChar_apply]
    rw [h2, mul_div_cancel_right]
  · rw [toricParamVec_of_ne hi, toricMonomial_single, Function.update_of_ne hi]

/-- **The toric substitution on monomials.** If `a = c B` (the row vector `c` times the matrix
`B` whose rows are the `u_l`), then `y^a = ∏_l (y^{u_l})^{c_l}`. -/
theorem toricMonomial_vecMul {G : Type*} [CommGroup G] (y : Fin n → G) (c : Fin n → ℤ)
    (B : Matrix (Fin n) (Fin n) ℤ) :
    toricMonomial y (c ᵥ* B) = ∏ l, toricMonomial y (B l) ^ c l := by
  rw [Matrix.vecMul_eq_sum, ← toricChar_apply, map_sum, toMul_sum]
  simp only [map_zsmul, toMul_zsmul, toricChar_apply]

/-- If `C B = 1` and the coordinates `a C` of `a` are `≥ 0`, then `y^a` is the monomial
`∏_l U_l^{c_l}` in `U_l = y^{u_l}` with exponents `c_l = (a C)_l ∈ ℕ`. -/
theorem toricMonomial_eq_prod_pow {G : Type*} [CommGroup G] (y : Fin n → G)
    {B C : Matrix (Fin n) (Fin n) ℤ} (hCB : C * B = 1) {a : Fin n → ℤ}
    (ha : ∀ l, 0 ≤ (a ᵥ* C) l) :
    toricMonomial y a = ∏ l, toricMonomial y (B l) ^ ((a ᵥ* C) l).toNat := by
  have hBa : (a ᵥ* C) ᵥ* B = a := by rw [Matrix.vecMul_vecMul, hCB, Matrix.vecMul_one]
  conv_lhs => rw [← hBa]
  rw [toricMonomial_vecMul]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← zpow_natCast, Int.toNat_of_nonneg (ha l)]

/-- The additive map `a ↦ (ℓ(a), a)` to the lexicographic product. Its order on `M` is the
order of Step 2: `a > 0` if `ℓ(a) > 0`, or `ℓ(a) = 0` and `a > 0` in the lexicographic order. -/
def toricOrderHom {Γ : Type*} [AddCommGroup Γ] (ℓ : (Fin n → ℤ) →+ Γ) :
    (Fin n → ℤ) →+ Γ ×ₗ Lex (Fin n → ℤ) where
  toFun a := toLex (ℓ a, toLex a)
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add]; rfl

theorem toricOrderHom_injective {Γ : Type*} [AddCommGroup Γ] (ℓ : (Fin n → ℤ) →+ Γ) :
    Function.Injective (toricOrderHom ℓ) := fun a b h => by
  have h2 := congrArg (fun q => ofLex (ofLex q).2) h
  simpa [toricOrderHom] using h2

/-- **Step 2 of the toric step.** An element is positive for the order of Step 2 if and only if
`ℓ(a) > 0`, or `ℓ(a) = 0` and `a > 0` for the tie-break order. -/
theorem toricOrderHom_pos_iff {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (ℓ : (Fin n → ℤ) →+ Γ) (a : Fin n → ℤ) :
    0 < toricOrderHom ℓ a ↔ 0 < ℓ a ∨ (ℓ a = 0 ∧ 0 < toLex a) := by
  rw [Prod.Lex.lt_iff]
  simp only [toricOrderHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ofLex_toLex]
  rw [eq_comm (a := (ofLex (0 : Γ ×ₗ Lex (Fin n → ℤ))).1)]
  rfl

/-- **Steps 2 and 3 of the toric step.** Let `ℓ : ℤ^n → Γ` be additive, and let `F` be a finite
set with `ℓ > 0` on `F`. Then there is a basis of `ℤ^n`, the rows of `B`, with the inverse
matrix `C`, such that `ℓ(u_l) ≥ 0` for each row `u_l`, and each element of `F` has
coordinates `≥ 0` in this basis. The proof applies the lattice lemma (Volume V, Lemma 2.1.4,
`Singularity.latticeLemma_of_injective`) to the order of Step 2. -/
theorem exists_toric_basis {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (ℓ : (Fin n → ℤ) →+ Γ) (F : Finset (Fin n → ℤ)) (hF : ∀ a ∈ F, 0 < ℓ a) :
    ∃ B C : Matrix (Fin n) (Fin n) ℤ, B * C = 1 ∧ C * B = 1 ∧ (∀ l, 0 ≤ ℓ (B l)) ∧
      ∀ a ∈ F, ∀ l, 0 ≤ (a ᵥ* C) l := by
  obtain ⟨B, C, hBC, hCB, hB, hC⟩ := latticeLemma_of_injective (toricOrderHom ℓ)
    (toricOrderHom_injective ℓ) F fun a ha =>
      ((toricOrderHom_pos_iff ℓ a).2 (Or.inl (hF a ha))).le
  refine ⟨B, C, hBC, hCB, fun l => ?_, hC⟩
  rcases (toricOrderHom_pos_iff ℓ (B l)).1 (hB l) with h | h
  · exact h.le
  · exact h.1.ge

/-- **Steps 1 to 3 of the toric step (Volume V, Lemma 4.3.12).** Let `G` be a commutative group
(the units of `E'`), let `z, x_i ∈ G` with `z^p = x_{z₀} ∏_{i ≠ z₀} x_i^{r_i}`. Let
`ℓ : ℤ^n → Γ` be additive with `ℓ(e_i) > 0` for each `i` (in the handbook `ℓ = w ∘ χ`). Then
there are a basis `u_l` of `ℤ^n` (the rows of `B`, with `C B = 1`) and the Laurent monomials
`U_l = χ(u_l)` in `z, x_i (i ≠ z₀)` with `ℓ(u_l) ≥ 0`, such that `z` and each `x_i` are
monomials in the `U_l` with exponents in `ℕ`. -/
theorem exists_toric_chart {G Γ : Type*} [CommGroup G] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] {p : ℕ} (r : Fin n → ℕ) (z₀ : Fin n) {x : Fin n → G}
    {z : G} (hz : z ^ p = x z₀ * ∏ j ∈ Finset.univ.erase z₀, x j ^ r j)
    (ℓ : (Fin n → ℤ) →+ Γ) (hℓ : ∀ i, 0 < ℓ (toricParamVec p r z₀ i)) :
    ∃ B C : Matrix (Fin n) (Fin n) ℤ, B * C = 1 ∧ C * B = 1 ∧ (∀ l, 0 ≤ ℓ (B l)) ∧
      (∀ l, 0 ≤ (Pi.single z₀ 1 ᵥ* C) l) ∧ (∀ i l, 0 ≤ (toricParamVec p r z₀ i ᵥ* C) l) ∧
      z = ∏ l, toricMonomial (Function.update x z₀ z) (B l) ^
        ((Pi.single z₀ 1 ᵥ* C) l).toNat ∧
      ∀ i, x i = ∏ l, toricMonomial (Function.update x z₀ z) (B l) ^
        ((toricParamVec p r z₀ i ᵥ* C) l).toNat := by
  classical
  let F : Finset (Fin n → ℤ) :=
    insert (Pi.single z₀ 1) (Finset.univ.image (toricParamVec p r z₀))
  have hF : ∀ a ∈ F, 0 < ℓ a := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact toric_pos_single r z₀ ℓ hℓ
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
      exact hℓ i
  obtain ⟨B, C, hBC, hCB, hB, hC⟩ := exists_toric_basis ℓ F hF
  have hz' : ∀ l, 0 ≤ (Pi.single z₀ 1 ᵥ* C) l := hC _ (Finset.mem_insert_self _ _)
  have hx' : ∀ i l, 0 ≤ (toricParamVec p r z₀ i ᵥ* C) l := fun i =>
    hC _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  refine ⟨B, C, hBC, hCB, hB, hz', hx', ?_, fun i => ?_⟩
  · rw [← toricMonomial_eq_prod_pow _ hCB hz', toricMonomial_single, Function.update_self]
  · rw [← toricMonomial_eq_prod_pow _ hCB (hx' i), toricMonomial_toricParamVec hz]

/-! ### The toric step: the combinatorics of Steps 6 and 7 -/

/-- **Step 7, first part.** `p M ⊆ M_1`, where `M_1` is generated by `e_1, ..., e_d`. -/
theorem nsmul_mem_span_toricParamVec (p : ℕ) (r : Fin n → ℕ) (z₀ : Fin n) (a : Fin n → ℤ) :
    p • a ∈ Submodule.span ℤ (Set.range (toricParamVec p r z₀)) := by
  have hsingle : ∀ i, p • (Pi.single i 1 : Fin n → ℤ) ∈
      Submodule.span ℤ (Set.range (toricParamVec p r z₀)) := by
    intro i
    by_cases hi : i = z₀
    · subst hi
      rw [nsmul_single_eq_toricParamVec]
      exact add_mem (Submodule.subset_span ⟨i, rfl⟩)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _
          (Submodule.subset_span ⟨j, rfl⟩))
    · rw [← toricParamVec_of_ne (r := r) (p := p) hi]
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have ha : a = ∑ i, a i • (Pi.single i 1 : Fin n → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [ha, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  exact Submodule.smul_mem _ _ (hsingle i)

/-- **Step 7, second part.** Let the rows `u_l` of `B` be a basis with inverse `C`, so that the
coordinates of `e_i` are `c_i = e_i C`. If `p ≠ 0`, then for each `l` some `c_{i,l}` is not `0`.
So each `Y_l` divides some `Y^{c_i}`. -/
theorem exists_toricParamVec_vecMul_ne_zero {p : ℕ} (hp : p ≠ 0) (r : Fin n → ℕ) (z₀ : Fin n)
    {B C : Matrix (Fin n) (Fin n) ℤ} (hBC : B * C = 1) (l : Fin n) :
    ∃ i, (toricParamVec p r z₀ i ᵥ* C) l ≠ 0 := by
  by_contra h
  push Not at h
  let φ : (Fin n → ℤ) →ₗ[ℤ] ℤ := (LinearMap.proj l) ∘ₗ Matrix.vecMulLinear C
  have hφ : ∀ a, φ a = (a ᵥ* C) l := fun a => rfl
  have hle : Submodule.span ℤ (Set.range (toricParamVec p r z₀)) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  have hmem := hle (nsmul_mem_span_toricParamVec p r z₀ (B l))
  rw [LinearMap.mem_ker, map_nsmul, hφ] at hmem
  have hrow : (B l ᵥ* C) l = 1 := by
    have := congrFun (congrFun hBC l) l
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    simpa [Matrix.vecMul, dotProduct] using this
  rw [hrow, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at hmem
  exact hp hmem

/-- **Step 6, the bound `δ_i ≥ 1`.** Let `Q` be a prime ideal, and let `Y_j ∉ Q` for `j ∉ J`.
If `∏_j Y_j^{c_j} ∈ Q`, then `∑_{j ∈ J} c_j ≥ 1`. -/
theorem toric_sum_pos_of_prod_mem {R : Type*} [CommRing R] {Q : Ideal R} (hQ : Q.IsPrime)
    (Y : Fin n → R) (c : Fin n → ℕ) (J : Finset (Fin n)) (hJ : ∀ j ∉ J, Y j ∉ Q)
    (h : ∏ j, Y j ^ c j ∈ Q) : 0 < ∑ j ∈ J, c j := by
  obtain ⟨j, -, hj⟩ := (hQ.prod_mem_iff).1 h
  have hc : c j ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hj
    exact hQ.ne_top ((Ideal.eq_top_iff_one Q).2 hj)
  have hjJ : j ∈ J := by
    by_contra hn
    exact hJ j hn (hQ.mem_of_pow_mem _ hj)
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero hc)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hjJ)

/-- **Step 6, the case `δ_i ≥ 2`.** If `Y_j ∈ I` for `j ∈ J` and `∑_{j ∈ J} c_j ≥ 2`, then
`∏_j Y_j^{c_j} ∈ I^2`. -/
theorem toric_prod_mem_sq {R : Type*} [CommRing R] {I : Ideal R} (Y : Fin n → R)
    (c : Fin n → ℕ) (J : Finset (Fin n)) (hJ : ∀ j ∈ J, Y j ∈ I) (h2 : 2 ≤ ∑ j ∈ J, c j) :
    ∏ j, Y j ^ c j ∈ I ^ 2 := by
  rw [← Finset.prod_sdiff (Finset.subset_univ J)]
  refine Ideal.mul_mem_left _ _ ?_
  have hmem : ∏ j ∈ J, Y j ^ c j ∈ ∏ j ∈ J, I ^ c j :=
    Ideal.prod_mem_prod fun j hj => Ideal.pow_mem_pow (hJ j hj) _
  rw [Finset.prod_pow_eq_pow_sum] at hmem
  exact Ideal.pow_le_pow_right h2 hmem

/-- **Step 6, the case `δ_i = 1`.** If `∑_{j ∈ J} c_j = 1`, then there is `j₀ ∈ J` with
`∏_j Y_j^{c_j} = (∏_{j ∉ J} Y_j^{c_j}) Y_{j₀}`. -/
theorem toric_prod_eq_of_sum_eq_one {R : Type*} [CommRing R] (Y : Fin n → R)
    (c : Fin n → ℕ) (J : Finset (Fin n)) (h1 : ∑ j ∈ J, c j = 1) :
    ∃ j₀ ∈ J, ∏ j, Y j ^ c j = (∏ j ∈ Finset.univ \ J, Y j ^ c j) * Y j₀ := by
  classical
  have hne : ∑ j ∈ J, c j ≠ 0 := by rw [h1]; exact one_ne_zero
  obtain ⟨j₀, hj₀, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hle : c j₀ ≤ ∑ j ∈ J, c j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj₀
  rw [h1] at hle
  have hc1 : c j₀ = 1 := by omega
  have hrest : ∀ j ∈ J, j ≠ j₀ → c j = 0 := by
    intro j hj hne
    have h2 : c j + c j₀ ≤ ∑ i ∈ J, c i := by
      rw [← Finset.sum_pair hne]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.insert_subset hj (Finset.singleton_subset_iff.2 hj₀)) fun _ _ _ => Nat.zero_le _
    omega
  have hJ : ∏ j ∈ J, Y j ^ c j = Y j₀ := by
    rw [Finset.prod_eq_single j₀]
    · rw [hc1, pow_one]
    · intro j hj hne
      rw [hrest j hj hne, pow_zero]
    · intro h
      exact absurd hj₀ h
  exact ⟨j₀, hj₀, by rw [← Finset.prod_sdiff (Finset.subset_univ J), hJ]⟩

/-! ### Example 4.3.13 -/

/-- The basis `u_1 = 3 e_z - e_2`, `u_2 = e_2 - 2 e_z` of Example 4.3.13 and its inverse. -/
theorem toricExample_mul :
    !![3, -1; -2, 1] * !![1, 1; 2, 3] = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem toricExample_mul' :
    !![1, 1; 2, 3] * !![3, -1; -2, 1] = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The coordinates of Example 4.3.13: `e_z = u_1 + u_2`, `e_1 = u_1`, `e_2 = 2 u_1 + 3 u_2`. -/
theorem toricExample_coords :
    ![1, 0] ᵥ* !![1, 1; 2, 3] = (![1, 1] : Fin 2 → ℤ) ∧
      ![3, -1] ᵥ* !![1, 1; 2, 3] = (![1, 0] : Fin 2 → ℤ) ∧
      ![0, 1] ᵥ* !![1, 1; 2, 3] = (![2, 3] : Fin 2 → ℤ) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [Matrix.vecMul, dotProduct]

/-- The monomials of Example 4.3.13: if `z^3 = x_1 x_2`, then `U_1 = x_1` and `U_2 = x_2 / z^2`
satisfy `z = U_1 U_2` and `x_2 = U_1^2 U_2^3`. -/
theorem toricExample_monomials {K : Type*} [Field K] {z x₁ x₂ : K} (hz0 : z ≠ 0)
    (hz : z ^ 3 = x₁ * x₂) : z = x₁ * (x₂ / z ^ 2) ∧ x₂ = x₁ ^ 2 * (x₂ / z ^ 2) ^ 3 := by
  constructor
  · field_simp
    linear_combination hz
  · field_simp
    linear_combination (x₂ * (z ^ 3 + x₁ * x₂)) * hz

end ToricLattice

/-! ### The log Jacobian criterion in the polynomial model (Corollary 4.4.17) -/

section FoliatedPoly

variable {σ k : Type*} [Field k] {p : ℕ} [CharP k p]

/-- **A first integral of monomial type gives a principal ideal**, with a unit. Let
`t = u x^a` with `u ∈ k`, let `Δ` contain each `i` with `p ∤ a_i`, and let `p ∤ a_{i₀}` for some
`i₀ ∈ Δ`. Let `f = ∑_{i < p} c_i^p t^i`. Then `J_Δ(f) = (c t)` with
`c = ∑_{i < p} i c_i^p t^(i-1)` (Volume V, Proposition 4.4.15, part 1, polynomial model). -/
theorem logJacobian_eq_span_of_monomial_unit {a : σ →₀ ℕ} {Δ : Finset σ}
    (hout : ∀ i, i ∉ Δ → p ∣ a i) {i₀ : σ} (hi₀ : i₀ ∈ Δ) (hp : ¬ p ∣ a i₀) (u : k)
    (c : Fin p → MvPolynomial σ k) :
    logJacobian Δ (∑ i : Fin p, c i ^ p * monomial a u ^ (i : ℕ)) =
      Ideal.span {(∑ i : Fin p, ((i : ℕ) : MvPolynomial σ k) * c i ^ p *
        monomial a u ^ ((i : ℕ) - 1)) * monomial a u} := by
  set t : MvPolynomial σ k := monomial a u with ht
  set cf : MvPolynomial σ k :=
    ∑ i : Fin p, ((i : ℕ) : MvPolynomial σ k) * c i ^ p * t ^ ((i : ℕ) - 1) with hcf
  set f : MvPolynomial σ k := ∑ i : Fin p, c i ^ p * t ^ (i : ℕ) with hf
  have hd : ∀ j, pderiv j f = cf * pderiv j t := fun j => derivation_sum_pow_mul_pow _ c t
  have hx : ∀ j, X j * pderiv j t = ((a j : ℕ) : MvPolynomial σ k) * t := fun j => by
    rw [ht, X_mul_pderiv_monomial, nsmul_eq_mul]
  have hz : ∀ j, j ∉ Δ → pderiv j t = 0 := fun j hj => by
    rw [ht, pderiv_monomial, (CharP.cast_eq_zero_iff k p _).2 (hout j hj), mul_zero,
      monomial_zero]
  refine le_antisymm (Ideal.span_le.2 ?_) ?_
  · rintro _ (⟨j, -, rfl⟩ | ⟨j, hj, rfl⟩)
    · show X j * pderiv j f ∈ Ideal.span {cf * t}
      rw [hd, mul_left_comm, hx, Ideal.mem_span_singleton]
      exact ⟨((a j : ℕ) : MvPolynomial σ k), by ring⟩
    · show pderiv j f ∈ Ideal.span {cf * t}
      rw [hd, hz j hj, mul_zero]
      exact zero_mem _
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hmem : X i₀ * pderiv i₀ f ∈ logJacobian Δ f := Ideal.subset_span (Or.inl ⟨i₀, hi₀, rfl⟩)
    rw [hd, mul_left_comm, hx] at hmem
    have hu : ((a i₀ : ℕ) : k) ≠ 0 := fun h => hp ((CharP.cast_eq_zero_iff k p _).1 h)
    have hC : ((a i₀ : ℕ) : MvPolynomial σ k) = C ((a i₀ : ℕ) : k) := (map_natCast C _).symm
    have hinv : C ((a i₀ : ℕ) : k)⁻¹ * C ((a i₀ : ℕ) : k) = (1 : MvPolynomial σ k) := by
      rw [← C_mul, inv_mul_cancel₀ hu, C_1]
    have heq : cf * t = C ((a i₀ : ℕ) : k)⁻¹ * (cf * (((a i₀ : ℕ) : MvPolynomial σ k) * t)) := by
      rw [hC]
      linear_combination -(cf * t) * hinv
    show cf * t ∈ logJacobian Δ f
    rw [heq]
    exact Ideal.mul_mem_left _ _ hmem

variable (p) in
/-- An element `f` of `k[x]` is *foliated monomial* in the polynomial model if
`f = ∑_{i < p} c_i^p t^i` with polynomials `c_i` and a monomial `t = u x^a` with `u ≠ 0` and
`p ∤ a_i` for some `i`. This is the ramified type of Volume V, Definition 4.4.6, with the
variables `x_i` as the parameters and with coefficients `c_i` in `k[x]` in place of `E`. -/
def IsFoliatedMonomialPoly (f : MvPolynomial σ k) : Prop :=
  ∃ (a : σ →₀ ℕ) (u : k) (c : Fin p → MvPolynomial σ k), u ≠ 0 ∧ (∃ i, ¬ p ∣ a i) ∧
    f = ∑ i : Fin p, c i ^ p * monomial a u ^ (i : ℕ)

/-- **The log Jacobian criterion, the direction from a foliated monomial element**, polynomial
model. If `f` is foliated monomial, then `J_Δ(f)` is principal for the divisor `Δ` of the
indices `i` with `p ∤ a_i` (Volume V, Corollary 4.4.17, first direction). -/
theorem IsFoliatedMonomialPoly.exists_logJacobian_eq_span {f : MvPolynomial σ k}
    (h : IsFoliatedMonomialPoly p f) : ∃ (Δ : Finset σ) (g : MvPolynomial σ k),
      logJacobian Δ f = Ideal.span {g} := by
  classical
  obtain ⟨a, u, c, -, ⟨i₀, hi₀⟩, rfl⟩ := h
  refine ⟨a.support.filter (fun i => ¬ p ∣ a i), _,
    logJacobian_eq_span_of_monomial_unit (fun i hi => ?_) ?_ hi₀ u c⟩
  · by_contra hn
    have ha : a i ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero p)
    exact hi (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 ha, hn⟩)
  · have ha : a i₀ ≠ 0 := fun h0 => hi₀ (h0 ▸ dvd_zero p)
    exact Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 ha, hi₀⟩

/-- **The log Jacobian criterion, the direction from a foliated monomial element**, polynomial
model, with a nonzero generator. Over a perfect field, if `f` is foliated monomial and not a
`p`-th power in `k[x]`, then `J_Δ(f) = (g)` with `g ≠ 0` for some divisor `Δ`. The ideal
`J_Δ(f)` is the ideal of the values of the derivations tangent to `x_i = 0`, `i ∈ Δ`
(Volume V, Corollary 4.4.17, first direction). -/
theorem IsFoliatedMonomialPoly.exists_derivationIdeal_eq_span [Fact p.Prime] [PerfectRing k p]
    [DecidableEq σ] [Fintype σ] {f : MvPolynomial σ k} (h : IsFoliatedMonomialPoly p f)
    (hf : ¬ ∃ g, f = g ^ p) : ∃ (Δ : Finset σ) (g : MvPolynomial σ k), g ≠ 0 ∧
      derivationIdeal k (tangentDerivations k (X '' (Δ : Set σ))) f = Ideal.span {g} := by
  obtain ⟨Δ, g, hg⟩ := h.exists_logJacobian_eq_span
  refine ⟨Δ, g, fun h0 => hf ?_, by rw [derivationIdeal_tangentDerivations_X, hg]⟩
  rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at hg
  exact logJacobian_eq_bot_iff.1 hg

end FoliatedPoly

end Singularity
