/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.MonomialValuationConstruction
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.MvPolynomial.Division

/-!
# The rank 2 valuation of Example 1.6.4 and its coarsening

This file proves Volume 3, Example 1.6.8 of the handbook, in a large part. Let `k` be a field and
let `K = k(x, y)`. Let `v` be the monomial valuation of Lemma 1.6.1 with `v(x) = (0, 1)` and
`v(y) = (1, 0)` in `ℤ ×ₗ ℤ`, with the lexicographic order. Let `v_1` be the monomial valuation
with `v_1(x) = 0` and `v_1(y) = 1`. In Lean, `x = X 0` and `y = X 1`.

The file proves these claims:

* The value of `x^i y^j` is `(j, i)`, and distinct monomials have distinct values.
* `v_1 = pr_1 ∘ v` on all of `K` (`fstTop_v`).
* For a polynomial `f`, `v_1(f)` is the order of `f` in `y` (`vOne_algebraMap`).
* Let `v(z) = (a, b)`. Then `z ∈ 𝒪_v` if and only if `a > 0`, or `a = 0` and `b ≥ 0`. Also
  `z ∈ W` if and only if `a ≥ 0`, and `z ∈ 𝔪_W` if and only if `a > 0`.
* `𝒪_v ⊆ W` and `𝔪_W ⊆ 𝔪_v`.
* The middle prime meets `k[x, y]` in `(y)`: `v_1(f) > 0` if and only if `y ∣ f`.
* The center of `v` on `𝔸^2` is the origin: `v(f) > 0` if and only if `f(0, 0) = 0`.

The file does not prove that `W` is the local ring `k[x, y]_(y)`, that the residue field of `W`
is `k(x)`, or the residue form `𝒪_v = {f ∈ W : f̄ ∈ k[x]_(x)}` of the composite.

The proof of `v_1 = pr_1 ∘ v` on polynomials uses that `pr_1` is monotone, so it commutes with
the minimum over the support. On `K`, write `z = f / g` and cancel the finite value of `g`.
-/

namespace Singularity

open MvPolynomial Finsupp

namespace RankTwoExample

variable {k : Type*} [Field k]

/-- The weights of Example 1.6.4: `v(x) = (0, 1)` and `v(y) = (1, 0)` in `ℤ ×ₗ ℤ`. -/
def gamma : Fin 2 → ℤ ×ₗ ℤ := ![toLex (0, 1), toLex (1, 0)]

/-- The weights of the coarsening `v_1 = pr_1 ∘ v`: `v_1(x) = 0` and `v_1(y) = 1`. -/
def gammaOne : Fin 2 → ℤ := ![0, 1]

/-- The function field `K = k(x, y)`, with `x = X 0` and `y = X 1`. -/
abbrev K (k : Type*) [Field k] := FractionRing (MvPolynomial (Fin 2) k)

/-- The rank 2 valuation `v` of Example 1.6.4. -/
noncomputable def v : AddValuation (K k) (WithTop (ℤ ×ₗ ℤ)) := monomialAddValuationFrac gamma

/-- The valuation `v_1` of Example 1.6.8, the order along the line `y = 0`. -/
noncomputable def vOne : AddValuation (K k) (WithTop ℤ) := monomialAddValuationFrac gammaOne

/-- The first coordinate `pr_1`, extended to `WithTop`. -/
def fstTop (t : WithTop (ℤ ×ₗ ℤ)) : WithTop ℤ := WithTop.map (fun g => (ofLex g).1) t

theorem fstTop_coe (g : ℤ ×ₗ ℤ) : fstTop (g : WithTop (ℤ ×ₗ ℤ)) = ((ofLex g).1 : WithTop ℤ) :=
  rfl

theorem fstTop_top : fstTop ⊤ = ⊤ := rfl

theorem fstTop_add (s t : WithTop (ℤ ×ₗ ℤ)) : fstTop (s + t) = fstTop s + fstTop t := by
  induction s using WithTop.recTopCoe <;> induction t using WithTop.recTopCoe <;>
    simp [fstTop, ← WithTop.coe_add]

theorem monotone_fstTop : Monotone fstTop := by
  intro s t h
  induction t using WithTop.recTopCoe
  · simp [fstTop_top]
  induction s using WithTop.recTopCoe
  · simp at h
  rw [fstTop_coe, fstTop_coe, WithTop.coe_le_coe]
  exact Prod.Lex.monotone_fst_ofLex (WithTop.coe_le_coe.mp h)

/-- Example 1.6.4. The value of the monomial `x^i y^j` is `(j, i)`. -/
theorem weight_gamma (a : Fin 2 →₀ ℕ) :
    weight gamma a = toLex ((a 1 : ℤ), (a 0 : ℤ)) := by
  rw [weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_two, gamma, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  apply ofLex.injective
  ext <;> simp

theorem weight_gammaOne (a : Fin 2 →₀ ℕ) : weight gammaOne a = (a 1 : ℤ) := by
  rw [weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two, gammaOne]

/-- Example 1.6.4. Distinct monomials have distinct values. -/
theorem weight_gamma_injective : Function.Injective (weight gamma : (Fin 2 →₀ ℕ) → ℤ ×ₗ ℤ) := by
  intro a b h
  rw [weight_gamma, weight_gamma] at h
  have h' := congrArg ofLex h
  simp only [ofLex_toLex, Prod.mk.injEq, Nat.cast_inj] at h'
  ext i
  fin_cases i
  · exact h'.2
  · exact h'.1

theorem fstTop_monomialWeight (f : MvPolynomial (Fin 2) k) :
    fstTop (monomialWeight gamma f) = monomialWeight gammaOne f := by
  classical
  apply le_antisymm
  · rw [le_monomialWeight_iff]
    intro a ha
    calc fstTop (monomialWeight gamma f) ≤ fstTop (weight gamma a : WithTop (ℤ ×ₗ ℤ)) :=
          monotone_fstTop (monomialWeight_le ha)
      _ = (weight gammaOne a : WithTop ℤ) := by
          rw [fstTop_coe, weight_gamma, weight_gammaOne]; rfl
  · by_cases hf : f = 0
    · subst hf; simp [monomialWeight_zero, fstTop_top]
    obtain ⟨a, ha, hva⟩ := exists_monomialWeight_eq (γ := gamma) hf
    rw [hva, fstTop_coe, weight_gamma]
    calc monomialWeight gammaOne f ≤ (weight gammaOne a : WithTop ℤ) := monomialWeight_le ha
      _ = _ := by rw [weight_gammaOne]; rfl

/-- Example 1.6.8. The valuation `v_1` is the first coordinate of `v` on all of `K`. -/
theorem fstTop_v (z : K k) : fstTop (v z) = vOne z := by
  obtain ⟨⟨f, g⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (MvPolynomial (Fin 2) k)) z
  dsimp only
  have hz : IsLocalization.mk' (K k) f g * algebraMap _ (K k) (g : MvPolynomial (Fin 2) k) =
      algebraMap _ (K k) f := IsLocalization.mk'_spec _ _ _
  have h1 := congrArg (fun t => fstTop (v t)) hz
  have h2 := congrArg (fun t => vOne t) hz
  simp only [AddValuation.map_mul, fstTop_add] at h1 h2
  have hg0 : (g : MvPolynomial (Fin 2) k) ≠ 0 := nonZeroDivisors.ne_zero g.2
  have e1 : ∀ p : MvPolynomial (Fin 2) k,
      fstTop (v (algebraMap _ (K k) p)) = vOne (algebraMap _ (K k) p) := by
    intro p
    simp only [v, vOne, monomialAddValuationFrac_algebraMap]
    exact fstTop_monomialWeight _
  have hne : vOne (algebraMap _ (K k) (g : MvPolynomial (Fin 2) k)) ≠ ⊤ := by
    simp only [vOne, monomialAddValuationFrac_algebraMap]
    rw [Ne, monomialWeight_eq_top_iff]
    exact hg0
  rw [e1, e1, ← h2] at h1
  exact WithTop.add_right_cancel hne h1

/-- For a polynomial `f`, `v_1(f)` is the order of `f` in `y`: the least `j` with a monomial
`x^i y^j` in `f`. -/
theorem vOne_algebraMap (f : MvPolynomial (Fin 2) k) :
    vOne (algebraMap _ (K k) f) = f.support.inf fun a => ((a 1 : ℤ) : WithTop ℤ) := by
  rw [vOne, monomialAddValuationFrac_algebraMap, monomialWeight]
  simp only [weight_gammaOne]

/-- For a polynomial `f`, `v(f)` is the least value `(j, i)` of a monomial `x^i y^j` in `f`. -/
theorem v_algebraMap (f : MvPolynomial (Fin 2) k) :
    v (algebraMap _ (K k) f) =
      f.support.inf fun a => ((toLex ((a 1 : ℤ), (a 0 : ℤ)) : ℤ ×ₗ ℤ) : WithTop (ℤ ×ₗ ℤ)) := by
  rw [v, monomialAddValuationFrac_algebraMap, monomialWeight]
  simp only [weight_gamma]

/-- A lexicographic pair is positive if its first coordinate is positive. -/
theorem lt_of_fstTop_pos {t : WithTop (ℤ ×ₗ ℤ)} (h : 0 < fstTop t) : 0 < t := by
  induction t using WithTop.recTopCoe
  · exact WithTop.coe_lt_top 0
  case coe g =>
    rw [fstTop_coe] at h
    have h' : (0 : ℤ) < (ofLex g).1 := by exact_mod_cast h
    have : (0 : ℤ ×ₗ ℤ) < g := by
      change toLex ((0 : ℤ), (0 : ℤ)) < g
      rw [← toLex_ofLex g, Prod.Lex.toLex_lt_toLex]
      exact Or.inl h'
    exact_mod_cast this

/-- Example 1.6.8. The ring of `v` lies in the ring `W` of `v_1`. -/
theorem vOne_nonneg_of_v_nonneg {z : K k} (h : 0 ≤ v z) : 0 ≤ vOne z := by
  rw [← fstTop_v]
  have := monotone_fstTop h
  rwa [show fstTop (0 : WithTop (ℤ ×ₗ ℤ)) = 0 from rfl] at this

/-- Example 1.6.8. The maximal ideal of `W` lies in the maximal ideal of `v`. -/
theorem v_pos_of_vOne_pos {z : K k} (h : 0 < vOne z) : 0 < v z := by
  rw [← fstTop_v] at h
  exact lt_of_fstTop_pos h

/-- Example 1.6.8. Let `v(z) = (a, b)`. Then `z ∈ 𝒪_v` if and only if `a > 0`, or `a = 0` and
`b ≥ 0`. -/
theorem v_nonneg_iff (z : K k) (a b : ℤ)
    (h : v z = ((toLex (a, b) : ℤ ×ₗ ℤ) : WithTop (ℤ ×ₗ ℤ))) :
    0 ≤ v z ↔ 0 < a ∨ (a = 0 ∧ 0 ≤ b) := by
  rw [h]
  have e : (0 : WithTop (ℤ ×ₗ ℤ)) ≤ ((toLex (a, b) : ℤ ×ₗ ℤ) : WithTop (ℤ ×ₗ ℤ)) ↔
      toLex ((0 : ℤ), (0 : ℤ)) ≤ toLex (a, b) := WithTop.coe_le_coe
  rw [e, Prod.Lex.toLex_le_toLex]
  exact or_congr Iff.rfl (and_congr eq_comm Iff.rfl)

/-- The first coordinate of `v(z)` is `v_1(z)`. -/
theorem vOne_eq_of_v_eq (z : K k) (a b : ℤ)
    (h : v z = ((toLex (a, b) : ℤ ×ₗ ℤ) : WithTop (ℤ ×ₗ ℤ))) :
    vOne z = a := by
  rw [← fstTop_v, h, fstTop_coe]
  rfl

/-- Example 1.6.8. Let `v(z) = (a, b)`. Then `z ∈ W` if and only if `a ≥ 0`, and `z` is in the
maximal ideal of `W` if and only if `a > 0`. -/
theorem vOne_nonneg_iff_and_pos_iff (z : K k) (a b : ℤ)
    (h : v z = ((toLex (a, b) : ℤ ×ₗ ℤ) : WithTop (ℤ ×ₗ ℤ))) :
    (0 ≤ vOne z ↔ 0 ≤ a) ∧ (0 < vOne z ↔ 0 < a) := by
  rw [vOne_eq_of_v_eq z a b h]
  exact ⟨by exact_mod_cast Iff.rfl, by exact_mod_cast Iff.rfl⟩

/-- Example 1.6.8. The middle prime meets `k[x, y]` in `(y)`: a polynomial `f` has
`v_1(f) > 0` if and only if `y` divides `f`. -/
theorem vOne_pos_iff_X_one_dvd (f : MvPolynomial (Fin 2) k) :
    0 < vOne (algebraMap _ (K k) f) ↔ X 1 ∣ f := by
  classical
  have h0 : (0 : WithTop ℤ) < ⊤ := WithTop.coe_lt_top 0
  rw [vOne_algebraMap, Finset.lt_inf_iff h0]
  constructor
  · intro h
    rw [X_dvd_iff_modMonomial_eq_zero]
    ext s
    rw [AddMonoidAlgebra.coeff_zero]
    by_cases hs : Finsupp.single (1 : Fin 2) 1 ≤ s
    · exact coeff_modMonomial_of_le _ hs
    · rw [coeff_modMonomial_of_not_le _ hs]
      by_contra hc
      have h1 := h s (MvPolynomial.mem_support_iff.mpr hc)
      have h0 : s 1 = 0 := by
        by_contra h0
        exact hs (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))
      rw [h0] at h1
      exact absurd h1 (by simp)
  · rintro ⟨g, rfl⟩ b hb
    rw [MvPolynomial.mem_support_iff, coeff_X_mul'] at hb
    split_ifs at hb with hb1
    · have : b 1 ≠ 0 := Finsupp.mem_support_iff.mp hb1
      have : (0 : ℤ) < (b 1 : ℤ) := by omega
      exact_mod_cast this
    · exact absurd rfl hb

/-- Example 1.6.8. The center of `v` on `𝔸^2 = Spec k[x, y]` is the origin: a polynomial `f` has
`v(f) > 0` if and only if `f(0, 0) = 0`. -/
theorem v_pos_iff_constantCoeff_eq_zero (f : MvPolynomial (Fin 2) k) :
    0 < v (algebraMap _ (K k) f) ↔ constantCoeff f = 0 := by
  classical
  have h0 : (0 : WithTop (ℤ ×ₗ ℤ)) < ⊤ := WithTop.coe_lt_top 0
  rw [v_algebraMap, Finset.lt_inf_iff h0, MvPolynomial.constantCoeff_eq]
  have key : ∀ a : Fin 2 →₀ ℕ, ((0 : WithTop (ℤ ×ₗ ℤ)) <
      ((toLex ((a 1 : ℤ), (a 0 : ℤ)) : ℤ ×ₗ ℤ) : WithTop (ℤ ×ₗ ℤ))) ↔ a ≠ 0 := by
    intro a
    have e : (0 : WithTop (ℤ ×ₗ ℤ)) < ((toLex ((a 1 : ℤ), (a 0 : ℤ)) : ℤ ×ₗ ℤ) : WithTop (ℤ ×ₗ ℤ)) ↔
        toLex ((0 : ℤ), (0 : ℤ)) < toLex ((a 1 : ℤ), (a 0 : ℤ)) := WithTop.coe_lt_coe
    rw [e, Prod.Lex.toLex_lt_toLex]
    simp only
    constructor
    · rintro (h | ⟨h1, h2⟩) rfl
      · simp at h
      · simp at h2
    · intro ha
      by_cases h1 : a 1 = 0
      · right
        refine ⟨by simp [h1], ?_⟩
        have h0 : a 0 ≠ 0 := by
          intro h0
          apply ha
          ext i
          fin_cases i
          · exact h0
          · exact h1
        omega
      · left
        omega
  simp only [key]
  constructor
  · intro h
    by_contra hc
    exact h 0 (MvPolynomial.mem_support_iff.mpr hc) rfl
  · intro h a ha ha0
    rw [ha0, MvPolynomial.mem_support_iff] at ha
    exact ha h

end RankTwoExample

end Singularity
