/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Example.ThreefoldPolyhedronExamples
import Singularity.Invariant.OriginChartIota
import Singularity.Invariant.CossartPiltantOmegaBounds
import Singularity.Invariant.LogJacobianDirectrix

/-!
# The invariants of Examples 3.2.8, 3.2.15, 3.2.16, 3.3.5 and 3.3.6

This file computes the invariants `ε`, `ω` and `ι` of five examples of Volume 6 of the handbook
from the definitions `residualFactor`, `cpOmega` and `cpIota`. The variables `u_1, u_2, u_3` are
`X 0, X 1, X 2` of the polynomial ring `k[X 0, X 1, X 2]` over a field `k`, and the divisor
`E = div(∏_{i ∈ Δ} u_i)` is given by a finset `Δ` of indices. The residual order
`ε = ord (residualFactor Δ f)` is computed on the polynomial `f`. The ring identities are stated in
a commutative ring of characteristic `2` or `3`.

What the file proves:

* Example 3.2.8: for `f = u_1 u_2 u_3` and `E = div(u_1 u_2 u_3)`, `G = 1`, `ω = 0`,
  `ord f = 3` and `ι = (3, 0, 1)`. The `u_1`-chart sends `f` to `u_1^3 (u_2 + t_2)(u_3 + t_3)`,
  and in characteristic `3` the translation by `-c` with `c^3 = t_2 t_3` gives
  `Z^3 + u_2 u_3 + t_3 u_2 + t_2 u_3`.
* Example 3.2.15: the cleaning `g^2 + f = f^cl` in characteristic `2`, `ord f^cl = 4`,
  `in(f^cl) = U_1^3 U_2`, and `ε = 3, 4, 4` and `ω = 3, 3, 3` for the three divisors.
* Example 3.2.16: `ord f = 3`, `ε = 1` for both divisors, `ω = 0` and `ι = (3, 0, 1)` for
  `E = div(u_1)`, and `ω = 1` and `ι = (3, 1, 2)` for `E = div(u_1 u_2)`.
* Example 3.3.5: at `x`, `G = u_2^3 - u_1^3 + u_3^4`, `ε = ω = 3`, `ord f = 6` and
  `ι = (3, 3, 2)`. In characteristic `3` the chart at `t = (1, 0)` gives the series of the handbook,
  the new divisor is `div(u_1 u_3)`, and at `x'` the clean part `f'` has `ε = 4`, `ω = 3`,
  `ord f' = 7` and `ι = (3, 3, 2)`. Also the identities in characteristic `3` that the example uses.
* Example 3.3.6: at `x`, `ε = 1`, `ω = 0`, `ord f = 3` and `ι = (3, 0, 1)`. The `u_3`-chart at the
  origin gives `u_1'^2 (u_2' + u_3)`, the new divisor is `div(u_1' u_3)`, and at `x'` the same
  values hold. Also the chart identities of the blowup of the curve `Y`.

The value `2` of `κ` stands for `κ ≥ 2`, as in `cpKappa`. What is not proved: the polyhedra and
`δ` of these examples, the vertices in Example 3.2.15, the table of the 13 points of Example 3.3.5
apart from the point `t = (1, 0)`, the cleaning of `u_1^{-3} f` as a statement on `IsClean`,
condition (E), the permissibility of the centers, and the blowups as schemes. The series ring
`k[[u_1, u_2, u_3]]` is replaced by the polynomial ring.
-/

open MvPolynomial Finsupp

namespace Singularity.Examples

/-! ### General facts -/

section General

variable {k : Type*} [Field k]

private theorem tie_mon (a b : Fin 3 →₀ ℕ) :
    monomial (a + b) (1 : k) = monomial a 1 * monomial b 1 := by
  rw [monomial_mul_monomial, mul_one]

private theorem tie_ne {a b : Fin 3 →₀ ℕ} (i : Fin 3) (h : a i ≠ b i) : a ≠ b :=
  fun hab => h (by rw [hab])

private theorem tie_ord_X (i : Fin 3) : ord (X i : MvPolynomial (Fin 3) k) = ((1 : ℕ) : ℕ∞) := by
  rw [ord_X, Nat.cast_one]

private theorem tie_ord_mul {A B : MvPolynomial (Fin 3) k} {a b : ℕ} (hA : ord A = a)
    (hB : ord B = b) : ord (A * B) = ((a + b : ℕ) : ℕ∞) := by
  rw [ord_mul, hA, hB, Nat.cast_add]

private theorem tie_le_ord {A : MvPolynomial (Fin 3) k} {a b : ℕ} (h : ord A = a) (hab : b ≤ a) :
    (b : ℕ∞) ≤ ord A := by
  rw [h]
  exact_mod_cast hab

private theorem tie_ord_add {A B : MvPolynomial (Fin 3) k} {n m : ℕ} (hA : ord A = n)
    (hB : (m : ℕ∞) ≤ ord B) (hnm : n < m) : ord (A + B) = n := by
  have h : ord A < ord B := by
    rw [hA]
    exact lt_of_lt_of_le (by exact_mod_cast hnm) hB
  rw [ord_add_of_lt h, hA]

private theorem tie_hc_add {A B : MvPolynomial (Fin 3) k} {n m : ℕ} (hA : A.IsHomogeneous n)
    (hB : (m : ℕ∞) ≤ ord B) (hnm : n < m) : homogeneousComponent n (A + B) = A := by
  have h : (n : ℕ∞) < ord B := lt_of_lt_of_le (by exact_mod_cast hnm) hB
  rw [map_add, homogeneousComponent_eq_self hA, homogeneousComponent_eq_zero_of_lt_ord h, add_zero]

private theorem tie_ord_eq_of_coeff {G : MvPolynomial (Fin 3) k} {i : Fin 3} {n : ℕ}
    (hc : G.coeff (single i n) ≠ 0) (hn : (n : ℕ∞) ≤ ord G) : ord G = n := by
  have h := ord_le hc
  rw [degree_single] at h
  exact le_antisymm h hn

private theorem tie_eq_of_add_one {w : ℕ∞} {n : ℕ} (h : w + 1 = ((n + 1 : ℕ) : ℕ∞)) : w = n := by
  cases w using ENat.recTopCoe with
  | top => rw [top_add] at h; exact absurd h (ENat.top_ne_natCast _)
  | coe m =>
    have hm : m + 1 = n + 1 := by exact_mod_cast h
    exact_mod_cast (by omega : m = n)

/-- The first case of Definition 3.2.5: if `ε = d + 1` and `∂_j in(G) ≠ 0` for a free `j`, then
`ω = d`. -/
private theorem tie_cpOmega_of_pderiv_ne {Δ : Finset (Fin 3)} {g G : MvPolynomial (Fin 3) k}
    {d e : ℕ} (hG : residualFactor Δ g = G) (he : e = d + 1) (hd : ord G = e) {j : Fin 3}
    (hj : j ∉ Δ) (hne : pderiv j (homogeneousComponent e G) ≠ 0) : cpOmega Δ g = d := by
  subst he
  have hd' : ord (residualFactor Δ g) = ((d + 1 : ℕ) : ℕ∞) := by rw [hG, hd]
  have hex := (exists_pderiv_initialForm_ne_zero_iff hd').mpr ⟨j, hj, by rw [hG]; exact hne⟩
  have h1 := cpOmega_add_one_of_exists hex
  rw [hd'] at h1
  exact tie_eq_of_add_one h1

/-- The second case of Definition 3.2.5: if `ε = d` and `∂_j in(G) = 0` for each free `j`, then
`ω = d`. -/
private theorem tie_cpOmega_of_pderiv_eq {Δ : Finset (Fin 3)} {g G : MvPolynomial (Fin 3) k}
    {d : ℕ} (hG : residualFactor Δ g = G) (hd : ord G = d)
    (h : ∀ j ∉ Δ, pderiv j (homogeneousComponent d G) = 0) : cpOmega Δ g = d := by
  have hd' : ord (residualFactor Δ g) = d := by rw [hG, hd]
  have hall : ∀ j ∉ Δ, pderiv j (homogeneousComponent (ord g).toNat g) = 0 := by
    intro j hj
    by_contra hne
    obtain ⟨l, hl, hl'⟩ := (exists_pderiv_initialForm_ne_zero_iff hd').mp ⟨j, hj, hne⟩
    rw [hG] at hl'
    exact hl' (h l hl)
  rw [cpOmega_of_forall hall, hd']

private theorem tie_cpIota_zero {p : ℕ} {Δ : Finset (Fin 3)} {g : MvPolynomial (Fin 3) k}
    (hm : (p : ℕ∞) ≤ ord g) (hω : cpOmega Δ g = 0) :
    cpIota p Δ g = toLex ((p : ℕ∞), toLex ((0 : ℕ∞), 1)) := by
  have hκ : cpKappa p Δ g = 1 := cpKappa_eq_one_iff.mpr (by rw [cpOmegaAt_of_le Δ hm, hω])
  rw [cpIota, cpMult_of_le hm, cpOmegaAt_of_le Δ hm, hω, hκ]

private theorem tie_cpIota_ne {p w : ℕ} {Δ : Finset (Fin 3)} {g : MvPolynomial (Fin 3) k}
    (hm : (p : ℕ∞) ≤ ord g) (hω : cpOmega Δ g = w) (hw : w ≠ 0) :
    cpIota p Δ g = toLex ((p : ℕ∞), toLex ((w : ℕ∞), 2)) := by
  have h0 : cpOmegaAt p Δ g ≠ 0 := by
    rw [cpOmegaAt_of_le Δ hm, hω]
    exact fun h => hw (by exact_mod_cast h)
  have hκ : cpKappa p Δ g = 2 := by
    unfold cpKappa
    exact if_neg h0
  rw [cpIota, cpMult_of_le hm, cpOmegaAt_of_le Δ hm, hω, hκ]

/-- If no `x_i` with `i ∈ Δ` divides `G`, then `G` is its own residual factor. -/
private theorem tie_residualFactor_self {Δ : Finset (Fin 3)} {G : MvPolynomial (Fin 3) k}
    (hG : ∀ i ∈ Δ, ∃ d ∈ G.support, d i = 0) : residualFactor Δ G = G := by
  have h := residualFactor_monomial_mul (r := 0) (fun i _ => Finsupp.zero_apply) hG
  rwa [monomial_zero', C_1, one_mul] at h

end General

/-! ### Example 3.2.8 -/

section Example328

variable {k : Type*} [Field k]

private theorem tie_328_eq : (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) k) =
    monomial (single 0 1 + single 1 1 + single 2 1) 1 * 1 := by
  rw [tie_mon, tie_mon, ← X_pow_eq_monomial, ← X_pow_eq_monomial, ← X_pow_eq_monomial]
  ring

/-- The residual factor of `u_1 u_2 u_3` for `E = div(u_1 u_2 u_3)` is `G = 1`. Volume 6,
Example 3.2.8 of the handbook. -/
theorem example_3_2_8_residualFactor :
    residualFactor Finset.univ (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) k) = 1 := by
  rw [tie_328_eq]
  exact residualFactor_monomial_mul (fun i hi => absurd (Finset.mem_univ i) hi)
    (fun i _ => ⟨0, MvPolynomial.mem_support_iff.mpr (by simp), by simp⟩)

/-- `ε = 0` and `ω = 0` for `f = u_1 u_2 u_3` and `E = div(u_1 u_2 u_3)`. Volume 6,
Example 3.2.8 of the handbook. -/
theorem example_3_2_8_cpOmega :
    cpOmega Finset.univ (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) k) = 0 := by
  rw [cpOmega_eq_of_forall_mem Finset.mem_univ, example_3_2_8_residualFactor, ord_one]

private theorem tie_328_ord : ord (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) k) = ((3 : ℕ) : ℕ∞) :=
  tie_ord_mul (tie_ord_mul (tie_ord_X 0) (tie_ord_X 1)) (tie_ord_X 2)

/-- `ord (u_1 u_2 u_3) = 3`. Volume 6, Example 3.2.8 of the handbook. -/
theorem example_3_2_8_ord : ord (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) k) = 3 :=
  tie_328_ord

/-- `ι(x) = (3, 0, 1)` for `h = Z^3 + u_1 u_2 u_3` and `E = div(u_1 u_2 u_3)`. Volume 6,
Example 3.2.8 of the handbook. -/
theorem example_3_2_8_cpIota :
    cpIota 3 Finset.univ (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) k) =
      toLex ((3 : ℕ∞), toLex ((0 : ℕ∞), 1)) :=
  tie_cpIota_zero (le_of_eq tie_328_ord.symm) example_3_2_8_cpOmega

/-- The `u_1`-chart with translations `t` sends `u_1 u_2 u_3` to `u_1^3 (u_2 + t_2)(u_3 + t_3)`.
Volume 6, Example 3.2.8 of the handbook. -/
theorem example_3_2_8_chart (t : Fin 3 → k) :
    pointChart 0 t (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) k) =
      X 0 ^ 3 * ((X 1 + C (t 1)) * (X 2 + C (t 2))) := by
  rw [map_mul, map_mul, pointChart_X_self, pointChart_X_of_ne t (by decide : (1 : Fin 3) ≠ 0),
    pointChart_X_of_ne t (by decide : (2 : Fin 3) ≠ 0)]
  ring

/-- In characteristic `3`, if `c^3 = s t`, the translation `Z ↦ Z - c` sends
`Z^3 + (u_2 + s)(u_3 + t)` to `Z^3 + u_2 u_3 + t u_2 + s u_3`. Volume 6, Example 3.2.8 of the
handbook. -/
theorem example_3_2_8_translate {R : Type*} [CommRing R] [CharP R 3] {s t c : R}
    (hc : c ^ 3 = s * t) (z a b : R) :
    (z - c) ^ 3 + (a + s) * (b + t) = z ^ 3 + a * b + t * a + s * b := by
  linear_combination (-z ^ 2 * c + z * c ^ 2) * three_eq_zero_of_charP (R := R) - hc

end Example328

/-! ### Example 3.2.15 -/

/-- The cleaning of Example 3.2.15. In characteristic `2`, for `g = u_1 + u_1 u_2`,
`g^2 + f = u_1^3 u_2 + u_2^5 + u_2^3 u_3^2`. Volume 6, Example 3.2.15 of the handbook. -/
theorem example_3_2_15_clean {R : Type*} [CommRing R] [CharP R 2] (a b c : R) :
    (a + a * b) ^ 2 + (a ^ 2 + a ^ 2 * b ^ 2 + a ^ 3 * b + b ^ 5 + b ^ 3 * c ^ 2) =
      a ^ 3 * b + b ^ 5 + b ^ 3 * c ^ 2 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination (a ^ 2 + a ^ 2 * b + a ^ 2 * b ^ 2) * h2

section Example3215

variable {k : Type*} [Field k]

private theorem tie_3215_B : ((5 : ℕ) : ℕ∞) ≤
    ord (X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) :=
  le_ord_add (tie_le_ord (ord_X_pow 1 5) le_rfl)
    (tie_le_ord (tie_ord_mul (ord_X_pow 1 3) (ord_X_pow 2 2)) (by norm_num))

private theorem tie_3215_ord :
    ord (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
      ((4 : ℕ) : ℕ∞) := by
  rw [add_assoc]
  exact tie_ord_add (n := 4) (m := 5) (tie_ord_mul (ord_X_pow 0 3) (tie_ord_X 1)) tie_3215_B
    (by norm_num)

/-- `ord f^cl = 4` for `f^cl = u_1^3 u_2 + u_2^5 + u_2^3 u_3^2`. Volume 6, Example 3.2.15 of the
handbook. -/
theorem example_3_2_15_ord :
    ord (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = 4 :=
  tie_3215_ord

/-- The initial form of `f^cl` is `U_1^3 U_2`. Volume 6, Example 3.2.15 of the handbook. -/
theorem example_3_2_15_initialForm :
    homogeneousComponent 4 (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
      X 0 ^ 3 * X 1 := by
  rw [add_assoc]
  exact tie_hc_add (n := 4) (m := 5) ((isHomogeneous_X_pow 0 3).mul (isHomogeneous_X _ 1))
    tie_3215_B (by norm_num)

private theorem tie_3215_mon :
    (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
    monomial (single 0 3 + single 1 1) 1 + monomial (single 1 5) 1 +
      monomial (single 1 3 + single 2 2) 1 := by
  simp only [tie_mon, ← X_pow_eq_monomial] <;> ring

private theorem tie_3215_mem : (single 1 5 : Fin 3 →₀ ℕ) ∈
    (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k).support := by
  rw [tie_3215_mon, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tie_ne (a := single 0 3 + single 1 1) (b := single 1 5) 1 (by simp),
    tie_ne (a := single 1 3 + single 2 2) (b := single 1 5) 1 (by simp)]

/-- The residual factor for `E = div(u_1 u_2)`. -/
private theorem tie_3215_eq :
    (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
    monomial (single 1 1) 1 * (X 0 ^ 3 + X 1 ^ 4 + X 1 ^ 2 * X 2 ^ 2) := by
  rw [← X_pow_eq_monomial]
  ring

private theorem tie_3215_G_mon : (X 0 ^ 3 + X 1 ^ 4 + X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
    monomial (single 0 3) 1 + monomial (single 1 4) 1 + monomial (single 1 2 + single 2 2) 1 := by
  simp only [tie_mon, ← X_pow_eq_monomial] <;> ring

private theorem tie_3215_G_mem1 : (single 1 4 : Fin 3 →₀ ℕ) ∈
    (X 0 ^ 3 + X 1 ^ 4 + X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k).support := by
  rw [tie_3215_G_mon, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tie_ne (a := single 0 3) (b := single 1 4) 1 (by simp),
    tie_ne (a := single 1 2 + single 2 2) (b := single 1 4) 1 (by simp)]

private theorem tie_3215_G_mem0 : (single 0 3 : Fin 3 →₀ ℕ) ∈
    (X 0 ^ 3 + X 1 ^ 4 + X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k).support := by
  rw [tie_3215_G_mon, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tie_ne (a := single 1 4) (b := single 0 3) 0 (by simp),
    tie_ne (a := single 1 2 + single 2 2) (b := single 0 3) 0 (by simp)]

/-- For `E = div(u_1 u_2)` the residual factor of `f^cl` is `u_1^3 + u_2^4 + u_2^2 u_3^2`.
Volume 6, Example 3.2.15 of the handbook. -/
theorem example_3_2_15_residualFactor_01 :
    residualFactor {0, 1} (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
      X 0 ^ 3 + X 1 ^ 4 + X 1 ^ 2 * X 2 ^ 2 := by
  rw [tie_3215_eq]
  refine residualFactor_monomial_mul ?_ ?_
  · intro i hi
    fin_cases i <;> simp at hi ⊢
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨_, tie_3215_G_mem1, by simp⟩
    · exact ⟨_, tie_3215_G_mem0, by simp⟩

private theorem tie_3215_G_ord :
    ord (X 0 ^ 3 + X 1 ^ 4 + X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = ((3 : ℕ) : ℕ∞) := by
  rw [add_assoc]
  exact tie_ord_add (n := 3) (m := 4) (ord_X_pow 0 3)
    (le_ord_add (tie_le_ord (ord_X_pow 1 4) le_rfl)
      (tie_le_ord (tie_ord_mul (ord_X_pow 1 2) (ord_X_pow 2 2)) (by norm_num))) (by norm_num)

private theorem tie_3215_G_hc :
    homogeneousComponent 3 (X 0 ^ 3 + X 1 ^ 4 + X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
      X 0 ^ 3 := by
  rw [add_assoc]
  exact tie_hc_add (n := 3) (m := 4) (isHomogeneous_X_pow 0 3)
    (le_ord_add (tie_le_ord (ord_X_pow 1 4) le_rfl)
      (tie_le_ord (tie_ord_mul (ord_X_pow 1 2) (ord_X_pow 2 2)) (by norm_num))) (by norm_num)

/-- `ε = 3` for `E = div(u_1 u_2)`. Volume 6, Example 3.2.15 of the handbook. -/
theorem example_3_2_15_epsilon_01 :
    ord (residualFactor {0, 1}
      (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k)) = 3 := by
  rw [example_3_2_15_residualFactor_01]
  exact tie_3215_G_ord

/-- `ω = 3` for `E = div(u_1 u_2)`. Volume 6, Example 3.2.15 of the handbook. -/
theorem example_3_2_15_cpOmega_01 :
    cpOmega {0, 1} (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = 3 := by
  refine tie_cpOmega_of_pderiv_eq example_3_2_15_residualFactor_01 tie_3215_G_ord ?_
  intro j hj
  rw [tie_3215_G_hc]
  revert hj
  fin_cases j <;> simp [Derivation.leibniz_pow, pderiv_X]

private theorem tie_3215_pderiv :
    pderiv 1 (homogeneousComponent 4
      (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k)) ≠ 0 := by
  rw [example_3_2_15_initialForm]
  have h : pderiv 1 (X 0 ^ 3 * X 1 : MvPolynomial (Fin 3) k) = X 0 ^ 3 := by
    simp [Derivation.leibniz, Derivation.leibniz_pow, pderiv_X]
  rw [h]
  exact pow_ne_zero 3 (X_ne_zero 0)

/-- For `E = div(u_1)` the residual factor of `f^cl` is `f^cl`. Volume 6, Example 3.2.15 of the
handbook. -/
theorem example_3_2_15_residualFactor_0 :
    residualFactor {0} (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
      X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 := by
  refine tie_residualFactor_self ?_
  intro i hi
  rw [Finset.mem_singleton] at hi
  subst hi
  exact ⟨_, tie_3215_mem, by simp⟩

/-- `ε = 4` for `E = div(u_1)`. Volume 6, Example 3.2.15 of the handbook. -/
theorem example_3_2_15_epsilon_0 :
    ord (residualFactor {0}
      (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k)) = 4 := by
  rw [example_3_2_15_residualFactor_0]
  exact tie_3215_ord

/-- `ω = 3` for `E = div(u_1)`, since `∂F/∂U_2 = U_1^3 ≠ 0`. Volume 6, Example 3.2.15 of the
handbook. -/
theorem example_3_2_15_cpOmega_0 :
    cpOmega {0} (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = 3 :=
  tie_cpOmega_of_pderiv_ne (d := 3) (e := 4) example_3_2_15_residualFactor_0 rfl tie_3215_ord
    (j := 1) (by simp) tie_3215_pderiv

/-- For `E = ∅` the residual factor of `f^cl` is `f^cl`. Volume 6, Example 3.2.15 of the
handbook. -/
theorem example_3_2_15_residualFactor_empty :
    residualFactor ∅ (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
      X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 :=
  tie_residualFactor_self fun i hi => absurd hi (by simp)

/-- `ε = 4` for `E = ∅`. Volume 6, Example 3.2.15 of the handbook. -/
theorem example_3_2_15_epsilon_empty :
    ord (residualFactor ∅
      (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k)) = 4 := by
  rw [example_3_2_15_residualFactor_empty]
  exact tie_3215_ord

/-- `ω = 3` for `E = ∅`. Volume 6, Example 3.2.15 of the handbook. -/
theorem example_3_2_15_cpOmega_empty :
    cpOmega ∅ (X 0 ^ 3 * X 1 + X 1 ^ 5 + X 1 ^ 3 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = 3 :=
  tie_cpOmega_of_pderiv_ne (d := 3) (e := 4) example_3_2_15_residualFactor_empty rfl tie_3215_ord
    (j := 1) (by simp) tie_3215_pderiv

end Example3215

/-! ### Example 3.2.16 -/

section Example3216

variable {k : Type*} [Field k]

private theorem tie_3216_eq : (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) =
    monomial (single 0 2) 1 * (X 1 + X 0 * X 2) := by
  rw [← X_pow_eq_monomial]
  ring

private theorem tie_3216_G_mon : (X 1 + X 0 * X 2 : MvPolynomial (Fin 3) k) =
    monomial (single 1 1) 1 + monomial (single 0 1 + single 2 1) 1 := by
  simp only [tie_mon, ← X_pow_eq_monomial, pow_one] <;> ring

private theorem tie_3216_G_mem1 : (single 1 1 : Fin 3 →₀ ℕ) ∈
    (X 1 + X 0 * X 2 : MvPolynomial (Fin 3) k).support := by
  rw [tie_3216_G_mon, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tie_ne (a := single 0 1 + single 2 1) (b := single 1 1) 1 (by simp)]

private theorem tie_3216_G_mem2 : (single 0 1 + single 2 1 : Fin 3 →₀ ℕ) ∈
    (X 1 + X 0 * X 2 : MvPolynomial (Fin 3) k).support := by
  rw [tie_3216_G_mon, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tie_ne (a := single 1 1) (b := single 0 1 + single 2 1) 1 (by simp)]

private theorem tie_3216_B : ((2 : ℕ) : ℕ∞) ≤ ord (X 0 * X 2 : MvPolynomial (Fin 3) k) :=
  tie_le_ord (tie_ord_mul (tie_ord_X 0) (tie_ord_X 2)) (by norm_num)

private theorem tie_3216_G_ord : ord (X 1 + X 0 * X 2 : MvPolynomial (Fin 3) k) = ((1 : ℕ) : ℕ∞) :=
  tie_ord_add (n := 1) (m := 2) (tie_ord_X 1) tie_3216_B (by norm_num)

private theorem tie_3216_G_hc :
    homogeneousComponent 1 (X 1 + X 0 * X 2 : MvPolynomial (Fin 3) k) = X 1 :=
  tie_hc_add (n := 1) (m := 2) (isHomogeneous_X _ 1) tie_3216_B (by norm_num)

private theorem tie_3216_ord :
    ord (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) = ((3 : ℕ) : ℕ∞) :=
  tie_ord_add (n := 3) (m := 4) (tie_ord_mul (ord_X_pow 0 2) (tie_ord_X 1))
    (tie_le_ord (tie_ord_mul (ord_X_pow 0 3) (tie_ord_X 2)) (by norm_num)) (by norm_num)

/-- `ord f = 3` for `f = u_1^2 u_2 + u_1^3 u_3`. Volume 6, Example 3.2.16 of the handbook. -/
theorem example_3_2_16_ord : ord (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) = 3 :=
  tie_3216_ord

/-- For `E = div(u_1)` the residual factor is `G = u_2 + u_1 u_3`. Volume 6, Example 3.2.16 of
the handbook. -/
theorem example_3_2_16_residualFactor_0 :
    residualFactor {0} (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) =
      X 1 + X 0 * X 2 := by
  rw [tie_3216_eq]
  refine residualFactor_monomial_mul ?_ ?_
  · intro i hi
    fin_cases i <;> simp at hi ⊢
  · intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨_, tie_3216_G_mem1, by simp⟩

/-- For `E = div(u_1 u_2)` the residual factor is again `G = u_2 + u_1 u_3`. Volume 6,
Example 3.2.16 of the handbook. -/
theorem example_3_2_16_residualFactor_01 :
    residualFactor {0, 1} (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) =
      X 1 + X 0 * X 2 := by
  rw [tie_3216_eq]
  refine residualFactor_monomial_mul ?_ ?_
  · intro i hi
    fin_cases i <;> simp at hi ⊢
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨_, tie_3216_G_mem1, by simp⟩
    · exact ⟨_, tie_3216_G_mem2, by simp⟩

/-- `ε = 1` for `E = div(u_1)`. Volume 6, Example 3.2.16 of the handbook. -/
theorem example_3_2_16_epsilon_0 :
    ord (residualFactor {0} (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k)) = 1 := by
  rw [example_3_2_16_residualFactor_0, tie_3216_G_ord, Nat.cast_one]

/-- `ε = 1` for `E = div(u_1 u_2)`. Volume 6, Example 3.2.16 of the handbook. -/
theorem example_3_2_16_epsilon_01 :
    ord (residualFactor {0, 1} (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k)) = 1 := by
  rw [example_3_2_16_residualFactor_01, tie_3216_G_ord, Nat.cast_one]

private theorem tie_3216_omega_0 :
    cpOmega {0} (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) = ((0 : ℕ) : ℕ∞) :=
  tie_cpOmega_of_pderiv_ne (d := 0) (e := 1) example_3_2_16_residualFactor_0 rfl tie_3216_G_ord
    (j := 1) (by simp) (by rw [tie_3216_G_hc]; simp [pderiv_X])

/-- `ω = 0` for `E = div(u_1)`, since `in(G) = U_2` is not in the span of `U_1`. Volume 6,
Example 3.2.16 of the handbook. -/
theorem example_3_2_16_cpOmega_0 :
    cpOmega {0} (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) = 0 :=
  tie_3216_omega_0.trans Nat.cast_zero

/-- `ι(x) = (3, 0, 1)` for `E = div(u_1)`. Volume 6, Example 3.2.16 of the handbook. -/
theorem example_3_2_16_cpIota_0 :
    cpIota 3 {0} (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) =
      toLex ((3 : ℕ∞), toLex ((0 : ℕ∞), 1)) :=
  tie_cpIota_zero (le_of_eq tie_3216_ord.symm) example_3_2_16_cpOmega_0

private theorem tie_3216_omega_01 :
    cpOmega {0, 1} (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) = ((1 : ℕ) : ℕ∞) := by
  refine tie_cpOmega_of_pderiv_eq example_3_2_16_residualFactor_01 tie_3216_G_ord ?_
  intro j hj
  rw [tie_3216_G_hc]
  revert hj
  fin_cases j <;> simp [pderiv_X]

/-- `ω = 1` for `E = div(u_1 u_2)`, since `U_2` is in the span of `U_1, U_2` and `∂F/∂U_3 = 0`.
Volume 6, Example 3.2.16 of the handbook. -/
theorem example_3_2_16_cpOmega_01 :
    cpOmega {0, 1} (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) = 1 :=
  tie_3216_omega_01.trans Nat.cast_one

/-- `ι(x) = (3, 1, κ)` with `κ ≥ 2` for `E = div(u_1 u_2)`. The value `2` of `cpKappa` stands for
`κ ≥ 2`. Volume 6, Example 3.2.16 of the handbook. -/
theorem example_3_2_16_cpIota_01 :
    cpIota 3 {0, 1} (X 0 ^ 2 * X 1 + X 0 ^ 3 * X 2 : MvPolynomial (Fin 3) k) =
      toLex ((3 : ℕ∞), toLex ((1 : ℕ∞), 2)) := by
  rw [tie_cpIota_ne (le_of_eq tie_3216_ord.symm) tie_3216_omega_01 one_ne_zero, Nat.cast_one]
    <;> rfl

end Example3216

/-! ### Example 3.3.5 -/

section CharThreeRing

variable {R : Type*} [CommRing R] [CharP R 3]

/-- In characteristic `3`, `(u_2 + 1)^4 - (u_2 + 1) = u_2^4 + u_2^3`. Volume 6, Example 3.3.5 of
the handbook. -/
theorem example_3_3_5_chart_identity (b : R) : (b + 1) ^ 4 - (b + 1) = b ^ 4 + b ^ 3 := by
  linear_combination (b ^ 3 + 2 * b ^ 2 + b) * three_eq_zero_of_charP (R := R)

/-- In characteristic `3`, `(z + w)^3 = z^3 + w^3`. With `w = u_1 u_2` this is the cleaning step of
Example 3.3.5 of Volume 6 of the handbook. -/
theorem example_3_3_5_cube (z w : R) : (z + w) ^ 3 = z ^ 3 + w ^ 3 := by
  linear_combination (z ^ 2 * w + z * w ^ 2) * three_eq_zero_of_charP (R := R)

/-- In characteristic `3`, `U_2^3 - U_1^3 = (U_2 - U_1)^3`. Volume 6, Example 3.3.5 of the
handbook. -/
theorem example_3_3_5_initialForm_cube (a b : R) : (b - a) ^ 3 = b ^ 3 - a ^ 3 := by
  linear_combination (-b ^ 2 * a + b * a ^ 2) * three_eq_zero_of_charP (R := R)

/-- In characteristic `3`, `(u_2 - 1)^4 - (u_2 - 1) = u_2^4 + 2 u_2^3 + u_2 + 2`. This is the
point `t = (2, 0)` of Example 3.3.5 of Volume 6 of the handbook. -/
theorem example_3_3_5_chart_identity_two (b : R) :
    (b - 1) ^ 4 - (b - 1) = b ^ 4 + 2 * b ^ 3 + b + 2 := by
  linear_combination (-2 * b ^ 3 + 2 * b ^ 2 - 2 * b) * three_eq_zero_of_charP (R := R)

end CharThreeRing

section Example335

variable {k : Type*} [Field k]

private theorem tie_335_eq :
    (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      monomial (single 0 2 + single 1 1) 1 * (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4) := by
  rw [tie_mon, ← X_pow_eq_monomial, ← X_pow_eq_monomial]
  ring

private theorem tie_335_G_mon : (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 : MvPolynomial (Fin 3) k) =
    monomial (single 1 3) 1 - monomial (single 0 3) 1 + monomial (single 2 4) 1 := by
  simp only [← X_pow_eq_monomial] <;> ring

private theorem tie_335_G_mem1 : (single 1 3 : Fin 3 →₀ ℕ) ∈
    (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 : MvPolynomial (Fin 3) k).support := by
  rw [tie_335_G_mon, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tie_ne (a := single 0 3) (b := single 1 3) 1 (by simp),
    tie_ne (a := single 2 4) (b := single 1 3) 1 (by simp)]

private theorem tie_335_G_mem0 : (single 0 3 : Fin 3 →₀ ℕ) ∈
    (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 : MvPolynomial (Fin 3) k).support := by
  rw [tie_335_G_mon, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tie_ne (a := single 1 3) (b := single 0 3) 0 (by simp),
    tie_ne (a := single 2 4) (b := single 0 3) 0 (by simp)]

/-- The residual factor of `f = u_1^2 u_2^4 - u_1^5 u_2 + u_1^2 u_2 u_3^4` for
`E = div(u_1 u_2 u_3)` is `G = u_2^3 - u_1^3 + u_3^4`. Volume 6, Example 3.3.5 of the handbook. -/
theorem example_3_3_5_residualFactor :
    residualFactor Finset.univ
      (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 := by
  rw [tie_335_eq]
  refine residualFactor_monomial_mul (fun i hi => absurd (Finset.mem_univ i) hi) ?_
  intro i _
  fin_cases i
  · exact ⟨_, tie_335_G_mem1, by simp⟩
  · exact ⟨_, tie_335_G_mem0, by simp⟩
  · exact ⟨_, tie_335_G_mem1, by simp⟩

private theorem tie_335_G_ord :
    ord (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4 : MvPolynomial (Fin 3) k) = ((3 : ℕ) : ℕ∞) := by
  refine tie_ord_eq_of_coeff (i := 1) (MvPolynomial.mem_support_iff.mp tie_335_G_mem1) ?_
  rw [sub_eq_add_neg]
  exact le_ord_add (le_ord_add (ord_X_pow 1 3).ge ((ord_neg _).trans (ord_X_pow 0 3)).ge)
    (tie_le_ord (ord_X_pow 2 4) (by norm_num))

/-- `ε = 3` at `x`. Volume 6, Example 3.3.5 of the handbook. -/
theorem example_3_3_5_epsilon :
    ord (residualFactor Finset.univ
      (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 : MvPolynomial (Fin 3) k)) =
      3 := by
  rw [example_3_3_5_residualFactor]
  exact tie_335_G_ord

/-- `ω = ε = 3` at `x`, since all three coordinates belong to `E`. Volume 6, Example 3.3.5 of the
handbook. -/
theorem example_3_3_5_cpOmega :
    cpOmega Finset.univ
      (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      3 := by
  rw [cpOmega_eq_of_forall_mem Finset.mem_univ]
  exact example_3_3_5_epsilon

private theorem tie_335_ord :
    ord (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      ((6 : ℕ) : ℕ∞) := by
  rw [show (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
    X 0 ^ 2 * X 1 * (X 1 ^ 3 - X 0 ^ 3 + X 2 ^ 4) by ring]
  exact tie_ord_mul (tie_ord_mul (ord_X_pow 0 2) (tie_ord_X 1)) tie_335_G_ord

/-- `ord f = 6` at `x`. Volume 6, Example 3.3.5 of the handbook. -/
theorem example_3_3_5_ord :
    ord (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      6 :=
  tie_335_ord

/-- `ι(x) = (3, 3, κ)` with `κ ≥ 2`. The value `2` of `cpKappa` stands for `κ ≥ 2`. Volume 6,
Example 3.3.5 of the handbook. -/
theorem example_3_3_5_cpIota :
    cpIota 3 Finset.univ
      (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      toLex ((3 : ℕ∞), toLex ((3 : ℕ∞), 2)) :=
  tie_cpIota_ne (w := 3) (tie_le_ord tie_335_ord (by norm_num)) example_3_3_5_cpOmega
    (by norm_num)

private theorem tie_three [CharP k 3] : (3 : MvPolynomial (Fin 3) k) = 0 := by
  rw [← map_ofNat (C : k →+* MvPolynomial (Fin 3) k) 3, three_eq_zero_of_charP (R := k), map_zero]

/-- In characteristic `3`, the `u_1`-chart at `t_2 = 1`, `t_3 = 0` sends `f` to
`u_1^3 (u_1^3 u_2^4 + u_1^3 u_2^3 + u_1^4 u_2 u_3^4 + u_1^4 u_3^4)`. Volume 6, Example 3.3.5 of the
handbook. -/
theorem example_3_3_5_chart [CharP k 3] {t : Fin 3 → k} (ht1 : t 1 = 1) (ht2 : t 2 = 0) :
    pointChart 0 t
      (X 0 ^ 2 * X 1 ^ 4 - X 0 ^ 5 * X 1 + X 0 ^ 2 * X 1 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      X 0 ^ 3 * (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 3 * X 1 ^ 3 + X 0 ^ 4 * X 1 * X 2 ^ 4 +
        X 0 ^ 4 * X 2 ^ 4) := by
  have h1 : pointChart 0 t (X 1 : MvPolynomial (Fin 3) k) = X 0 * (X 1 + 1) := by
    rw [pointChart_X_of_ne t (by decide : (1 : Fin 3) ≠ 0), ht1, C_1]
  have h2 : pointChart 0 t (X 2 : MvPolynomial (Fin 3) k) = X 0 * X 2 := by
    rw [pointChart_X_of_ne t (by decide : (2 : Fin 3) ≠ 0), ht2, C_0, add_zero]
  simp only [map_add, map_sub, map_mul, map_pow, pointChart_X_self, h1, h2]
  linear_combination (X 0 ^ 6 * (X 1 ^ 3 + 2 * X 1 ^ 2 + X 1)) * tie_three (k := k)

/-- The new divisor at `t_2 = 1`, `t_3 = 0` is `E' = div(u_1 u_3)`. Volume 6, Example 3.3.5 of the
handbook. -/
theorem example_3_3_5_blowupDivisor [DecidableEq k] {t : Fin 3 → k} (ht1 : t 1 = 1)
    (ht2 : t 2 = 0) : blowupDivisor Finset.univ 0 t = {0, 2} := by
  ext i
  fin_cases i <;> simp [blowupDivisor, ht1, ht2]

private theorem tie_335'_eq :
    (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      monomial (single 0 3) 1 * (X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 2 ^ 4) := by
  rw [← X_pow_eq_monomial]
  ring

private theorem tie_335'_G_mon :
    (X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      monomial (single 1 4) 1 + monomial (single 0 1 + single 1 1 + single 2 4) 1 +
        monomial (single 0 1 + single 2 4) 1 := by
  simp only [tie_mon, ← X_pow_eq_monomial, pow_one] <;> ring

private theorem tie_335'_G_mem : (single 1 4 : Fin 3 →₀ ℕ) ∈
    (X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 2 ^ 4 : MvPolynomial (Fin 3) k).support := by
  rw [tie_335'_G_mon, MvPolynomial.mem_support_iff]
  simp [coeff_monomial,
    tie_ne (a := single 0 1 + single 1 1 + single 2 4) (b := single 1 4) 0 (by simp),
    tie_ne (a := single 0 1 + single 2 4) (b := single 1 4) 0 (by simp)]

/-- At `x'` the residual factor of the clean part `f' = u_1^3 u_2^4 + u_1^4 u_2 u_3^4 + u_1^4 u_3^4`
for `E' = div(u_1 u_3)` is `G' = u_2^4 + u_1 u_2 u_3^4 + u_1 u_3^4`. Volume 6, Example 3.3.5 of the
handbook. -/
theorem example_3_3_5_residualFactor' :
    residualFactor {0, 2}
      (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 2 ^ 4 := by
  rw [tie_335'_eq]
  refine residualFactor_monomial_mul ?_ ?_
  · intro i hi
    fin_cases i <;> simp at hi ⊢
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨_, tie_335'_G_mem, by simp⟩
    · exact ⟨_, tie_335'_G_mem, by simp⟩

private theorem tie_335'_B : ((5 : ℕ) : ℕ∞) ≤
    ord (X 0 * X 1 * X 2 ^ 4 + X 0 * X 2 ^ 4 : MvPolynomial (Fin 3) k) :=
  le_ord_add (tie_le_ord (tie_ord_mul (tie_ord_mul (tie_ord_X 0) (tie_ord_X 1)) (ord_X_pow 2 4))
      (by norm_num))
    (tie_le_ord (tie_ord_mul (tie_ord_X 0) (ord_X_pow 2 4)) (by norm_num))

private theorem tie_335'_G_ord :
    ord (X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      ((4 : ℕ) : ℕ∞) := by
  rw [add_assoc]
  exact tie_ord_add (n := 4) (m := 5) (ord_X_pow 1 4) tie_335'_B (by norm_num)

private theorem tie_335'_G_hc :
    homogeneousComponent 4
      (X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      X 1 ^ 4 := by
  rw [add_assoc]
  exact tie_hc_add (n := 4) (m := 5) (isHomogeneous_X_pow 1 4) tie_335'_B (by norm_num)

/-- `ε(x') = 4`. Volume 6, Example 3.3.5 of the handbook. -/
theorem example_3_3_5_epsilon' :
    ord (residualFactor {0, 2}
      (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 2 ^ 4 : MvPolynomial (Fin 3) k)) =
      4 := by
  rw [example_3_3_5_residualFactor']
  exact tie_335'_G_ord

/-- In characteristic `3`, `ω(x') = ε(x') - 1 = 3`, since `U_2` is not in `E'` and
`∂U_2^4/∂U_2 = U_2^3 ≠ 0`. Volume 6, Example 3.3.5 of the handbook. -/
theorem example_3_3_5_cpOmega' [CharP k 3] :
    cpOmega {0, 2}
      (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      3 := by
  refine tie_cpOmega_of_pderiv_ne (d := 3) (e := 4) example_3_3_5_residualFactor' rfl
    tie_335'_G_ord (j := 1) (by simp) ?_
  rw [tie_335'_G_hc]
  have h4 : (4 : k) = 1 := by linear_combination three_eq_zero_of_charP (R := k)
  rw [X_pow_eq_monomial, pderiv_monomial, ne_eq, monomial_eq_zero]
  simp [h4]

private theorem tie_335'_ord :
    ord (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      ((7 : ℕ) : ℕ∞) := by
  rw [show (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 2 ^ 4 :
      MvPolynomial (Fin 3) k) = X 0 ^ 3 * (X 1 ^ 4 + X 0 * X 1 * X 2 ^ 4 + X 0 * X 2 ^ 4) by ring]
  exact tie_ord_mul (ord_X_pow 0 3) tie_335'_G_ord

/-- `ord f' = 7` at `x'`. Volume 6, Example 3.3.5 of the handbook. -/
theorem example_3_3_5_ord' :
    ord (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      7 :=
  tie_335'_ord

/-- In characteristic `3`, `ι(x') = (3, 3, κ)` with `κ ≥ 2`, so `ω` stays `3`. Volume 6,
Example 3.3.5 of the handbook. -/
theorem example_3_3_5_cpIota' [CharP k 3] :
    cpIota 3 {0, 2}
      (X 0 ^ 3 * X 1 ^ 4 + X 0 ^ 4 * X 1 * X 2 ^ 4 + X 0 ^ 4 * X 2 ^ 4 : MvPolynomial (Fin 3) k) =
      toLex ((3 : ℕ∞), toLex ((3 : ℕ∞), 2)) :=
  tie_cpIota_ne (w := 3) (tie_le_ord tie_335'_ord (by norm_num)) example_3_3_5_cpOmega'
    (by norm_num)

end Example335

/-! ### Example 3.3.6 -/

section Example336

variable {k : Type*} [Field k]

private theorem tie_336_eq : (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
    monomial (single 0 2) 1 * (X 1 + X 2 ^ 2) := by
  rw [← X_pow_eq_monomial]
  ring

private theorem tie_336_G_mon : (X 1 + X 2 ^ 2 : MvPolynomial (Fin 3) k) =
    monomial (single 1 1) 1 + monomial (single 2 2) 1 := by
  simp only [← X_pow_eq_monomial, pow_one] <;> ring

private theorem tie_336_G_mem : (single 1 1 : Fin 3 →₀ ℕ) ∈
    (X 1 + X 2 ^ 2 : MvPolynomial (Fin 3) k).support := by
  rw [tie_336_G_mon, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tie_ne (a := single 2 2) (b := single 1 1) 1 (by simp)]

/-- The residual factor of `f = u_1^2 u_2 + u_1^2 u_3^2` for `E = div(u_1)` is
`G = u_2 + u_3^2`. Volume 6, Example 3.3.6 of the handbook. -/
theorem example_3_3_6_residualFactor :
    residualFactor {0} (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
      X 1 + X 2 ^ 2 := by
  rw [tie_336_eq]
  refine residualFactor_monomial_mul ?_ ?_
  · intro i hi
    fin_cases i <;> simp at hi ⊢
  · intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨_, tie_336_G_mem, by simp⟩

private theorem tie_336_B : ((2 : ℕ) : ℕ∞) ≤ ord (X 2 ^ 2 : MvPolynomial (Fin 3) k) :=
  tie_le_ord (ord_X_pow 2 2) le_rfl

private theorem tie_336_G_ord : ord (X 1 + X 2 ^ 2 : MvPolynomial (Fin 3) k) = ((1 : ℕ) : ℕ∞) :=
  tie_ord_add (n := 1) (m := 2) (tie_ord_X 1) tie_336_B (by norm_num)

private theorem tie_336_G_hc : homogeneousComponent 1 (X 1 + X 2 ^ 2 : MvPolynomial (Fin 3) k) =
    X 1 :=
  tie_hc_add (n := 1) (m := 2) (isHomogeneous_X _ 1) tie_336_B (by norm_num)

/-- `ε = 1` at `x`. Volume 6, Example 3.3.6 of the handbook. -/
theorem example_3_3_6_epsilon :
    ord (residualFactor {0} (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k)) = 1 := by
  rw [example_3_3_6_residualFactor, tie_336_G_ord, Nat.cast_one]

/-- `ω = 0` at `x`, since `in(G) = U_2` is not in the span of `U_1`. Volume 6, Example 3.3.6 of the
handbook. -/
theorem example_3_3_6_cpOmega :
    cpOmega {0} (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = 0 :=
  (tie_cpOmega_of_pderiv_ne (d := 0) (e := 1) example_3_3_6_residualFactor rfl tie_336_G_ord
    (j := 1) (by simp) (by rw [tie_336_G_hc]; simp [pderiv_X])).trans Nat.cast_zero

private theorem tie_336_ord :
    ord (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = ((3 : ℕ) : ℕ∞) :=
  tie_ord_add (n := 3) (m := 4) (tie_ord_mul (ord_X_pow 0 2) (tie_ord_X 1))
    (tie_le_ord (tie_ord_mul (ord_X_pow 0 2) (ord_X_pow 2 2)) (by norm_num)) (by norm_num)

/-- `ord f = 3` at `x`. Volume 6, Example 3.3.6 of the handbook. -/
theorem example_3_3_6_ord : ord (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = 3 :=
  tie_336_ord

/-- `ι(x) = (3, 0, 1)`. Volume 6, Example 3.3.6 of the handbook. -/
theorem example_3_3_6_cpIota :
    cpIota 3 {0} (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
      toLex ((3 : ℕ∞), toLex ((0 : ℕ∞), 1)) :=
  tie_cpIota_zero (le_of_eq tie_336_ord.symm) example_3_3_6_cpOmega

/-- The `u_3`-chart at the origin sends `f` to `u_3^3 (u_1'^2 u_2' + u_1'^2 u_3)`. Volume 6,
Example 3.3.6 of the handbook. -/
theorem example_3_3_6_chart :
    pointChart 2 (0 : Fin 3 → k) (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
      X 2 ^ 3 * (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2) := by
  have h0 : pointChart 2 (0 : Fin 3 → k) (X 0 : MvPolynomial (Fin 3) k) = X 2 * X 0 := by
    rw [pointChart_X_of_ne _ (by decide : (0 : Fin 3) ≠ 2)]
    simp
  have h1 : pointChart 2 (0 : Fin 3 → k) (X 1 : MvPolynomial (Fin 3) k) = X 2 * X 1 := by
    rw [pointChart_X_of_ne _ (by decide : (1 : Fin 3) ≠ 2)]
    simp
  simp only [map_add, map_mul, map_pow, pointChart_X_self, h0, h1]
  ring

/-- The new divisor at the origin of the `u_3`-chart is `E' = div(u_1' u_3)`. Volume 6,
Example 3.3.6 of the handbook. -/
theorem example_3_3_6_blowupDivisor [DecidableEq k] :
    blowupDivisor {0} 2 (0 : Fin 3 → k) = {0, 2} := by
  ext i
  fin_cases i <;> simp [blowupDivisor]

private theorem tie_336'_eq : (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
    monomial (single 0 2) 1 * (X 1 + X 2) := by
  rw [← X_pow_eq_monomial]
  ring

private theorem tie_336'_G_mem : (single 1 1 : Fin 3 →₀ ℕ) ∈
    (X 1 + X 2 : MvPolynomial (Fin 3) k).support := by
  rw [show (X 1 + X 2 : MvPolynomial (Fin 3) k) =
    monomial (single 1 1) 1 + monomial (single 2 1) 1 from rfl, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tie_ne (a := single 2 1) (b := single 1 1) 1 (by simp)]

/-- At `x'` the residual factor of `f' = u_1'^2 u_2' + u_1'^2 u_3` for `E' = div(u_1' u_3)` is
`G' = u_2' + u_3`. Volume 6, Example 3.3.6 of the handbook. -/
theorem example_3_3_6_residualFactor' :
    residualFactor {0, 2} (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
      X 1 + X 2 := by
  rw [tie_336'_eq]
  refine residualFactor_monomial_mul ?_ ?_
  · intro i hi
    fin_cases i <;> simp at hi ⊢
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨_, tie_336'_G_mem, by simp⟩
    · exact ⟨_, tie_336'_G_mem, by simp⟩

private theorem tie_336'_G_ord : ord (X 1 + X 2 : MvPolynomial (Fin 3) k) = ((1 : ℕ) : ℕ∞) :=
  tie_ord_eq_of_coeff (i := 1) (MvPolynomial.mem_support_iff.mp tie_336'_G_mem)
    (le_ord_add (tie_ord_X 1).ge (tie_ord_X 2).ge)

/-- `ε(x') = 1`. Volume 6, Example 3.3.6 of the handbook. -/
theorem example_3_3_6_epsilon' :
    ord (residualFactor {0, 2} (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 : MvPolynomial (Fin 3) k)) = 1 := by
  rw [example_3_3_6_residualFactor', tie_336'_G_ord, Nat.cast_one]

/-- `ω(x') = 0`, since `in(G') = U_2 + U_3` and `U_2` is not in `E'`. Volume 6, Example 3.3.6 of
the handbook. -/
theorem example_3_3_6_cpOmega' :
    cpOmega {0, 2} (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = 0 :=
  (tie_cpOmega_of_pderiv_ne (d := 0) (e := 1) example_3_3_6_residualFactor' rfl tie_336'_G_ord
    (j := 1) (by simp)
    (by
      rw [homogeneousComponent_eq_self ((isHomogeneous_X _ 1).add (isHomogeneous_X _ 2))]
      simp [pderiv_X])).trans Nat.cast_zero

private theorem tie_336'_ord :
    ord (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = ((3 : ℕ) : ℕ∞) := by
  rw [show (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = X 0 ^ 2 * (X 1 + X 2) by
    ring]
  exact tie_ord_mul (ord_X_pow 0 2) tie_336'_G_ord

/-- `ord f' = 3` at `x'`. Volume 6, Example 3.3.6 of the handbook. -/
theorem example_3_3_6_ord' : ord (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = 3 :=
  tie_336'_ord

/-- `ι(x') = (3, 0, 1) = ι(x)`. Volume 6, Example 3.3.6 of the handbook. -/
theorem example_3_3_6_cpIota' :
    cpIota 3 {0, 2} (X 0 ^ 2 * X 1 + X 0 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
      toLex ((3 : ℕ∞), toLex ((0 : ℕ∞), 1)) :=
  tie_cpIota_zero (le_of_eq tie_336'_ord.symm) example_3_3_6_cpOmega'

end Example336

section CurveBlowup

variable {R : Type*} [CommRing R]

/-- The `u_1`-chart of the blowup of `Y`: with `v = u_1 (v' + a)`, `u_1^2 v = u_1^3 (v' + a)`.
Volume 6, Example 3.3.6 of the handbook. -/
theorem example_3_3_6_curve_chart (u v a : R) : u ^ 2 * (u * (v + a)) = u ^ 3 * (v + a) := by
  ring

/-- In characteristic `3`, if `b^3 = a`, then `Z^3 + v' + a = (Z + b)^3 + v'`. Volume 6,
Example 3.3.6 of the handbook. -/
theorem example_3_3_6_translate [CharP R 3] {a b : R} (hb : b ^ 3 = a) (z v : R) :
    z ^ 3 + v + a = (z + b) ^ 3 + v := by
  linear_combination (-1 : R) * hb - (z ^ 2 * b + z * b ^ 2) * three_eq_zero_of_charP (R := R)

/-- The `v`-chart of the blowup of `Y`: with `u_1 = v u_1'` and `Z = v Z'`,
`Z^3 + u_1^2 v = v^3 (Z'^3 + u_1'^2)`. Volume 6, Example 3.3.6 of the handbook. -/
theorem example_3_3_6_v_chart (v z u : R) :
    (v * z) ^ 3 + (v * u) ^ 2 * v = v ^ 3 * (z ^ 3 + u ^ 2) := by
  ring

end CurveBlowup

end Singularity.Examples
