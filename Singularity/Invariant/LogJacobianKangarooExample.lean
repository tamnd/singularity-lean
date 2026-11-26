/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianKangarooSmall

/-!
# Example 3.11.2 of the handbook

This file checks the computation of Example 3.11.2 of Volume 7, Section 3.11 of the handbook. The
field is `ZMod 2`, so `p = 2`. The variables `x, y, z` are the indices `0, 1, 2` of `Fin 3`.

The path has three points and `ρ = 2` at each point.

* `P₀ = ({x, z}, g₀)` with `g₀ = x³z + xz³ + x⁴yz`. Here `r = (1, 0, 1)` and
  `G₀ = x² + z² + x³y`. It is of case A, `T_ρ(P₀)` is the plane `a_x = a_z`, and `τ_ρ(P₀) = 1`.
* `P₁ = ({x}, g₁)` with `g₁ = x²z³ + x⁴yz + x⁴y + x⁴z`. It comes from `P₀` by the `x`-chart
  `y ↦ x(y + 1)`, `z ↦ x(z + 1)`. The component `z = 0` leaves. The chart gives
  `x² (x²z³ + x²z² + x⁴yz + x⁴y + x⁴z + x⁴)`, and the clean part of the second factor is `g₁`.
  So `g₁ = x² G₁` with `G₁ = z³ + x²yz + x²y + x²z`. It is of case B, and `τ_ρ(P₁) = 2`.
* `P₂ = ({x, y}, g₂)` with `g₂ = x²y³z³ + x⁴y⁴z + x⁴y³ + x⁴y³z`. It comes from `P₁` by the
  `y`-chart at the origin. So `g₂ = x²y³ G₂` with `G₂ = x² + z³ + x²z + x²yz`. It is of case A,
  and `τ_ρ(P₂) = 1`.

The main result is `kangarooExample`.

## References

* Volume 7, Section 3.11 of the handbook: Example 3.11.2.
-/

open MvPolynomial Finsupp

namespace Singularity

namespace KangarooExample

instance factPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The polynomial ring `𝔽₂[x, y, z]`. -/
abbrev Poly := MvPolynomial (Fin 3) (ZMod 2)

/-- The polynomial ring `𝔽₂[x, y, z, s]`, with `s` the variable `none`. -/
abbrev Poly' := MvPolynomial (Option (Fin 3)) (ZMod 2)

/-! ### Monomials and explicit polynomials -/

/-- The exponent `(a, b, c)`. -/
noncomputable def expo (a b c : ℕ) : Fin 3 →₀ ℕ := single 0 a + single 1 b + single 2 c

@[simp] theorem expo_apply_zero (a b c : ℕ) : expo a b c 0 = a := by
  simp [expo]

@[simp] theorem expo_apply_one (a b c : ℕ) : expo a b c 1 = b := by
  simp [expo]

@[simp] theorem expo_apply_two (a b c : ℕ) : expo a b c 2 = c := by
  simp [expo]

theorem degree_eq (d : Fin 3 →₀ ℕ) : degree d = d 0 + d 1 + d 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]

theorem degree_expo (a b c : ℕ) : degree (expo a b c) = a + b + c := by
  simp [degree_eq]

theorem expo_eq_iff (a b c : ℕ) (d : Fin 3 →₀ ℕ) :
    expo a b c = d ↔ d 0 = a ∧ d 1 = b ∧ d 2 = c := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1, h2⟩
    ext i
    fin_cases i <;> simp [h0, h1, h2]

/-- The monomial `x^a y^b z^c`. -/
noncomputable def mono (a b c : ℕ) : Poly := X 0 ^ a * X 1 ^ b * X 2 ^ c

theorem mono_eq (a b c : ℕ) : mono a b c = monomial (expo a b c) 1 := by
  simp only [mono, expo, X_pow_eq_monomial, monomial_mul_monomial, mul_one]

theorem coeff_mono (a b c : ℕ) (d : Fin 3 →₀ ℕ) :
    (mono a b c).coeff d = if d 0 = a ∧ d 1 = b ∧ d 2 = c then 1 else 0 := by
  rw [mono_eq, coeff_monomial]
  by_cases h : d 0 = a ∧ d 1 = b ∧ d 2 = c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((expo_eq_iff a b c d).mpr h)),
      ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt (expo_eq_iff a b c d).mp h)),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- The sum of the monomials of a list of exponents. -/
noncomputable def poly (L : List (ℕ × ℕ × ℕ)) : Poly := (L.map fun e => mono e.1 e.2.1 e.2.2).sum

@[simp] theorem poly_nil : poly [] = 0 := by simp [poly]

@[simp] theorem poly_cons (e : ℕ × ℕ × ℕ) (L : List (ℕ × ℕ × ℕ)) :
    poly (e :: L) = mono e.1 e.2.1 e.2.2 + poly L := by
  simp [poly]

/-- A monomial of `poly L` comes from an entry of `L`. -/
theorem exists_of_coeff_ne_zero (L : List (ℕ × ℕ × ℕ)) (d : Fin 3 →₀ ℕ)
    (h : (poly L).coeff d ≠ 0) : ∃ e ∈ L, d 0 = e.1 ∧ d 1 = e.2.1 ∧ d 2 = e.2.2 := by
  induction L with
  | nil => simp at h
  | cons e L ih =>
    rw [poly_cons, coeff_add_apply] at h
    by_cases he : d 0 = e.1 ∧ d 1 = e.2.1 ∧ d 2 = e.2.2
    · exact ⟨e, List.mem_cons_self, he⟩
    · rw [coeff_mono, ite_eq_right_of_eq_false _ _ (eq_false he), zero_add] at h
      obtain ⟨e', he', h'⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

/-- The coefficient of `poly L` at `(a, b, c)` is the number of times `(a, b, c)` occurs in `L`. -/
theorem coeff_poly_expo (L : List (ℕ × ℕ × ℕ)) (a b c : ℕ) :
    (poly L).coeff (expo a b c) = ((L.countP fun e => decide (e = (a, b, c))) : ZMod 2) := by
  induction L with
  | nil => simp
  | cons e L ih =>
    obtain ⟨e1, e2, e3⟩ := e
    rw [poly_cons, coeff_add_apply, ih, coeff_mono, List.countP_cons]
    by_cases h : a = e1 ∧ b = e2 ∧ c = e3
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp [add_comm]
    · have h' : ¬ ((e1, e2, e3) = (a, b, c)) := by
        intro h''
        simp only [Prod.mk.injEq] at h''
        exact h ⟨h''.1.symm, h''.2.1.symm, h''.2.2.symm⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using h))]
      simp [h']

theorem coeff_poly_ne_zero {L : List (ℕ × ℕ × ℕ)} {a b c : ℕ}
    (h : (L.countP fun e => decide (e = (a, b, c))) % 2 = 1) :
    (poly L).coeff (expo a b c) ≠ 0 := by
  rw [coeff_poly_expo, ← ZMod.natCast_mod, h]
  simp

theorem poly_ne_zero {L : List (ℕ × ℕ × ℕ)} {a b c : ℕ}
    (h : (L.countP fun e => decide (e = (a, b, c))) % 2 = 1) : poly L ≠ 0 := by
  intro h0
  apply coeff_poly_ne_zero h
  rw [h0]
  simp

theorem le_ord_poly (L : List (ℕ × ℕ × ℕ)) (n : ℕ) (h : ∀ e ∈ L, n ≤ e.1 + e.2.1 + e.2.2) :
    (n : ℕ∞) ≤ ord (poly L) := by
  rw [le_ord_iff]
  intro d hd
  by_contra hc
  obtain ⟨e, he, h0, h1, h2⟩ := exists_of_coeff_ne_zero L d hc
  have := h e he
  rw [degree_eq] at hd
  omega

theorem ord_poly_le {L : List (ℕ × ℕ × ℕ)} {a b c : ℕ}
    (h : (L.countP fun e => decide (e = (a, b, c))) % 2 = 1) :
    ord (poly L) ≤ ((a + b + c : ℕ) : ℕ∞) := by
  have := ord_le (coeff_poly_ne_zero h)
  rwa [degree_expo] at this

theorem ord_poly_eq {L : List (ℕ × ℕ × ℕ)} (a b c : ℕ)
    (h : (L.countP fun e => decide (e = (a, b, c))) % 2 = 1)
    (h' : ∀ e ∈ L, a + b + c ≤ e.1 + e.2.1 + e.2.2) :
    ord (poly L) = ((a + b + c : ℕ) : ℕ∞) :=
  le_antisymm (ord_poly_le h) (le_ord_poly L _ h')

theorem isClean_poly (L : List (ℕ × ℕ × ℕ))
    (h : ∀ e ∈ L, ¬ (2 ∣ e.1 ∧ 2 ∣ e.2.1 ∧ 2 ∣ e.2.2)) : IsClean 2 (poly L) := by
  intro d hd hall
  obtain ⟨e, he, h0, h1, h2⟩ := exists_of_coeff_ne_zero L d (MvPolynomial.mem_support_iff.mp hd)
  exact h e he ⟨h0 ▸ hall 0, h1 ▸ hall 1, h2 ▸ hall 2⟩

theorem homogeneousComponent_mono (n a b c : ℕ) :
    homogeneousComponent n (mono a b c) = if a + b + c = n then mono a b c else 0 := by
  rw [mono_eq, homogeneousComponent_of_mem (isHomogeneous_monomial 1 (degree_expo a b c))]
  by_cases h : a + b + c = n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h.symm), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm h)),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

theorem homogeneousComponent_poly (n : ℕ) (L : List (ℕ × ℕ × ℕ)) :
    homogeneousComponent n (poly L) =
      poly (L.filter fun e => decide (e.1 + e.2.1 + e.2.2 = n)) := by
  induction L with
  | nil => simp
  | cons e L ih =>
    rw [poly_cons, map_add, ih, homogeneousComponent_mono, List.filter_cons]
    by_cases h : e.1 + e.2.1 + e.2.2 = n
    · simp [h]
    · simp [h]

/-! ### Derivatives of monomials -/

theorem pderiv_zero_mono (a b c : ℕ) :
    pderiv 0 (mono a b c) = (a : Poly) * mono (a - 1) b c := by
  simp [mono, pderiv_X]
  ring

theorem pderiv_one_mono (a b c : ℕ) :
    pderiv 1 (mono a b c) = (b : Poly) * mono a (b - 1) c := by
  simp [mono, pderiv_X]
  ring

theorem pderiv_two_mono (a b c : ℕ) :
    pderiv 2 (mono a b c) = (c : Poly) * mono a b (c - 1) := by
  simp [mono, pderiv_X]
  ring

/-! ### The divisor exponent of a product -/

theorem divisorExponent_monomial_mul' {σ k : Type*} [CommSemiring k] {Δ : Finset σ}
    {r : σ →₀ ℕ} {G : MvPolynomial σ k}
    (hr : ∀ i, i ∉ Δ → r i = 0) (hG : ∀ i ∈ Δ, ∃ d ∈ G.support, d i = 0) :
    divisorExponent Δ (monomial r 1 * G) = r := by
  classical
  have hsupp : ∀ d, d ∈ (monomial r (1 : k) * G).support ↔ r ≤ d ∧ d - r ∈ G.support := by
    intro d
    rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, coeff_monomial_mul']
    split_ifs with h
    · simp [h]
    · simp [h]
  ext i
  rw [divisorExponent_apply]
  split_ifs with hi
  · obtain ⟨d, hd, hdi⟩ := hG i hi
    have hmem : r i ∈ (fun d : σ →₀ ℕ => d i) '' ((monomial r (1 : k) * G).support : Set _) := by
      refine ⟨r + d, ?_, by simp [hdi]⟩
      rw [Finset.mem_coe, hsupp]
      simpa using hd
    refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
    rintro _ ⟨d', hd', rfl⟩
    exact ((hsupp d').mp hd').1 i
  · exact (hr i hi).symm

/-! ### The order of an ideal given by generators -/

theorem idealOrd_span_eq {S : Set Poly} {n : ℕ} (h : ∀ s ∈ S, (n : ℕ∞) ≤ ord s) {f : Poly}
    (hf : f ∈ S) (hfn : ord f = n) : idealOrd (Ideal.span S) = n := by
  refine le_antisymm (hfn ▸ idealOrd_le_ord (Ideal.subset_span hf)) ?_
  exact le_idealOrd_iff.mpr (Ideal.span_le.mpr fun s hs => le_ord_iff_mem_pow.mp (h s hs))

theorem le_ord_X_mul {n : ℕ} {f : Poly} (h : (n : ℕ∞) ≤ ord f) (a : Fin 3) :
    ((n + 1 : ℕ) : ℕ∞) ≤ ord (X a * f) := by
  rw [ord_mul, ord_X, Nat.cast_add, Nat.cast_one, add_comm]
  exact add_le_add le_rfl h

/-! ### Numerals in characteristic `2` -/

theorem num2 : (2 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 2
  simpa using this

theorem num3 : (3 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 3
  simpa using this

theorem num4 : (4 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 4
  simpa using this

theorem num5 : (5 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 5
  simpa using this

theorem num6 : (6 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 6
  simpa using this

theorem num7 : (7 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 7
  simpa using this

theorem num8 : (8 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 8
  simpa using this

theorem num9 : (9 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 9
  simpa using this

theorem num10 : (10 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 10
  simpa using this

theorem num11 : (11 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 11
  simpa using this

theorem num12 : (12 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 12
  simpa using this

theorem two_eq_zero' : (2 : Poly') = 0 := by
  have := CharP.cast_eq_mod Poly' 2 2
  simpa using this

/-- Close a polynomial identity in characteristic `2`: normalize, reduce the numerals modulo
`2`, and normalize again. -/
macro "char_two_ring" : tactic => `(tactic| (ring_nf <;>
  (try simp only [num2, num3, num4, num5, num6, num7, num8, num9, num10, num11, num12, mul_zero,
    zero_mul, add_zero, zero_add, mul_one, one_mul]) <;> (try ring_nf)))

/-! ### The polynomials of the path -/

/-- `g₀ = x³z + xz³ + x⁴yz`. -/
noncomputable def g0 : Poly := poly [(3, 0, 1), (1, 0, 3), (4, 1, 1)]
/-- The residual factor `G₀ = x² + z² + x³y` of `g₀ = xz G₀`. -/
noncomputable def G0 : Poly := poly [(2, 0, 0), (0, 0, 2), (3, 1, 0)]
/-- The quotient of the chart of `g₀` by `x²`. -/
noncomputable def h0 : Poly :=
  poly [(2, 0, 3), (2, 0, 2), (4, 1, 1), (4, 1, 0), (4, 0, 1), (4, 0, 0)]
/-- `g₁ = x²z³ + x⁴yz + x⁴y + x⁴z`, the clean part of `h0`. -/
noncomputable def g1 : Poly := poly [(2, 0, 3), (4, 1, 1), (4, 1, 0), (4, 0, 1)]
/-- The residual factor `G₁ = z³ + x²yz + x²y + x²z` of `g₁ = x² G₁`. -/
noncomputable def G1 : Poly := poly [(0, 0, 3), (2, 1, 1), (2, 1, 0), (2, 0, 1)]
/-- `g₂ = x²y³z³ + x⁴y⁴z + x⁴y³ + x⁴y³z`. -/
noncomputable def g2 : Poly := poly [(2, 3, 3), (4, 4, 1), (4, 3, 0), (4, 3, 1)]
/-- The residual factor `G₂ = x² + z³ + x²z + x²yz` of `g₂ = x²y³ G₂`. -/
noncomputable def G2 : Poly := poly [(2, 0, 0), (0, 0, 3), (2, 0, 1), (2, 1, 1)]
/-- The derivative `∂_y G₁ = x²z + x²`. -/
noncomputable def psi1 : Poly := poly [(2, 0, 1), (2, 0, 0)]
/-- The derivative `∂_z G₁ = z² + x²y + x²`. -/
noncomputable def psi2 : Poly := poly [(0, 0, 2), (2, 1, 0), (2, 0, 0)]

/-- The translation `y ↦ y + 1`, `z ↦ z + 1` of the first chart. -/
def t0 : Fin 3 → ZMod 2 := ![0, 1, 1]

/-- The first point `({x, z}, g₀)`. -/
noncomputable def P0 : Finset (Fin 3) × Poly := ({0, 2}, g0)
/-- The second point `({x}, g₁)`. -/
noncomputable def P1 : Finset (Fin 3) × Poly := ({0}, g1)
/-- The third point `({x, y}, g₂)`. -/
noncomputable def P2 : Finset (Fin 3) × Poly := ({0, 1}, g2)

/-! ### The charts -/

theorem pointChart_g0 : pointChart 0 t0 g0 = X 0 ^ 2 * h0 := by
  have hy : pointChart (0 : Fin 3) t0 (X 1) = (X 0 * (X 1 + 1) : Poly) := by
    rw [pointChart_X_of_ne t0 (by decide), show t0 1 = 1 from rfl, map_one]
  have hz : pointChart (0 : Fin 3) t0 (X 2) = (X 0 * (X 2 + 1) : Poly) := by
    rw [pointChart_X_of_ne t0 (by decide), show t0 2 = 1 from rfl, map_one]
  simp only [g0, h0, poly_cons, poly_nil, mono, map_add, map_mul, map_pow, hy, hz,
    pointChart_X_self, add_zero]
  char_two_ring

theorem pointChart_g1 : pointChart 1 0 g1 = X 1 ^ 2 * g2 := by
  have hx : pointChart (1 : Fin 3) 0 (X 0) = (X 1 * X 0 : Poly) := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  have hz : pointChart (1 : Fin 3) 0 (X 2) = (X 1 * X 2 : Poly) := by
    rw [pointChart_X_of_ne 0 (by decide)]
    simp
  simp only [g1, g2, poly_cons, poly_nil, mono, map_add, map_mul, map_pow, hx, hz,
    pointChart_X_self, add_zero]
  ring

theorem blowupDivisor_P0 : blowupDivisor ({0, 2} : Finset (Fin 3)) 0 t0 = {0} := by
  unfold blowupDivisor t0
  decide

theorem blowupDivisor_P1 :
    blowupDivisor ({0} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2) = {0, 1} := by
  unfold blowupDivisor
  decide

theorem cleanPart_h0 : cleanPart 2 h0 = g1 := by
  have h : h0 = g1 + (mono 1 0 1 + mono 2 0 0) ^ 2 ^ 1 := by
    simp only [h0, g1, poly_cons, poly_nil, mono]
    char_two_ring
  have := cleanPart_add_pow 2 1 g1 (mono 1 0 1 + mono 2 0 0)
  rw [pow_one] at this
  rw [h, pow_one, this]
  exact cleanPart_eq_self (isClean_poly _ (by decide))

theorem cleanPart_g2 : cleanPart 2 g2 = g2 :=
  cleanPart_eq_self (isClean_poly _ (by decide))

/-! ### The factorizations `g = x^r G` -/

theorem g0_eq : g0 = monomial (expo 1 0 1) 1 * G0 := by
  rw [← mono_eq]
  simp only [g0, G0, poly_cons, poly_nil, mono]
  ring

theorem g1_eq : g1 = monomial (expo 2 0 0) 1 * G1 := by
  rw [← mono_eq]
  simp only [g1, G1, poly_cons, poly_nil, mono]
  ring

theorem g2_eq : g2 = monomial (expo 2 3 0) 1 * G2 := by
  rw [← mono_eq]
  simp only [g2, G2, poly_cons, poly_nil, mono]
  ring

theorem hr0 : ∀ i, i ∉ ({0, 2} : Finset (Fin 3)) → expo 1 0 1 i = 0 := by
  intro i hi
  fin_cases i <;> simp_all

theorem hr1 : ∀ i, i ∉ ({0} : Finset (Fin 3)) → expo 2 0 0 i = 0 := by
  intro i hi
  fin_cases i <;> simp_all

theorem hr2 : ∀ i, i ∉ ({0, 1} : Finset (Fin 3)) → expo 2 3 0 i = 0 := by
  intro i hi
  fin_cases i <;> simp_all

theorem hG0 : ∀ i ∈ ({0, 2} : Finset (Fin 3)), ∃ d ∈ G0.support, d i = 0 := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨expo 0 0 2, MvPolynomial.mem_support_iff.mpr (coeff_poly_ne_zero (by decide)), by simp⟩
  · exact ⟨expo 2 0 0, MvPolynomial.mem_support_iff.mpr (coeff_poly_ne_zero (by decide)), by simp⟩

theorem hG1 : ∀ i ∈ ({0} : Finset (Fin 3)), ∃ d ∈ G1.support, d i = 0 := by
  intro i hi
  simp only [Finset.mem_singleton] at hi
  subst hi
  exact ⟨expo 0 0 3, MvPolynomial.mem_support_iff.mpr (coeff_poly_ne_zero (by decide)), by simp⟩

theorem hG2 : ∀ i ∈ ({0, 1} : Finset (Fin 3)), ∃ d ∈ G2.support, d i = 0 := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨expo 0 0 3, MvPolynomial.mem_support_iff.mpr (coeff_poly_ne_zero (by decide)), by simp⟩
  · exact ⟨expo 2 0 0, MvPolynomial.mem_support_iff.mpr (coeff_poly_ne_zero (by decide)), by simp⟩

theorem divisorExponent_g0 : divisorExponent {0, 2} g0 = expo 1 0 1 := by
  rw [g0_eq]
  exact divisorExponent_monomial_mul' hr0 hG0

theorem residualFactor_g0 : residualFactor {0, 2} g0 = G0 := by
  rw [g0_eq]
  exact residualFactor_monomial_mul hr0 hG0

theorem divisorExponent_g1 : divisorExponent {0} g1 = expo 2 0 0 := by
  rw [g1_eq]
  exact divisorExponent_monomial_mul' hr1 hG1

theorem residualFactor_g1 : residualFactor {0} g1 = G1 := by
  rw [g1_eq]
  exact residualFactor_monomial_mul hr1 hG1

theorem divisorExponent_g2 : divisorExponent {0, 1} g2 = expo 2 3 0 := by
  rw [g2_eq]
  exact divisorExponent_monomial_mul' hr2 hG2

theorem residualFactor_g2 : residualFactor {0, 1} g2 = G2 := by
  rw [g2_eq]
  exact residualFactor_monomial_mul hr2 hG2

/-! ### The generators of the ideals at `P₀` -/

theorem res0_zero : ((expo 1 0 1 0 : ℕ) : ZMod 2) • G0 + X 0 * pderiv 0 G0 =
    poly [(2, 0, 0), (0, 0, 2)] := by
  simp only [expo_apply_zero, G0, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char_two_ring

theorem res0_two : ((expo 1 0 1 2 : ℕ) : ZMod 2) • G0 + X 2 * pderiv 2 G0 = G0 := by
  simp only [expo_apply_two, G0, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char_two_ring

theorem res0_one : pderiv 1 G0 = poly [(3, 0, 0)] := by
  simp only [G0, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono]
  simp only [mono]
  char_two_ring

theorem tan0_zero : X 0 * pderiv 0 g0 = poly [(3, 0, 1), (1, 0, 3)] := by
  simp only [g0, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
  simp only [mono]
  char_two_ring

theorem tan0_two : X 2 * pderiv 2 g0 = g0 := by
  simp only [g0, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
  simp only [mono]
  char_two_ring

theorem tan0_one : pderiv 1 g0 = poly [(4, 0, 1)] := by
  simp only [g0, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono]
  simp only [mono]
  char_two_ring

/-! ### The generators of the ideals at `P₁` -/

theorem res1_zero : ((expo 2 0 0 0 : ℕ) : ZMod 2) • G1 + X 0 * pderiv 0 G1 = 0 := by
  simp only [expo_apply_zero, G1, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char_two_ring

theorem res1_one : pderiv 1 G1 = psi1 := by
  simp only [G1, psi1, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono]
  simp only [mono]
  char_two_ring

theorem res1_two : pderiv 2 G1 = psi2 := by
  simp only [G1, psi2, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
  simp only [mono]
  char_two_ring

theorem pderiv_zero_g1 : pderiv 0 g1 = 0 := by
  simp only [g1, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
  simp only [mono]
  char_two_ring

theorem tan1_one : pderiv 1 g1 = poly [(4, 0, 1), (4, 0, 0)] := by
  simp only [g1, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono]
  simp only [mono]
  char_two_ring

theorem tan1_two : pderiv 2 g1 = poly [(2, 0, 2), (4, 1, 0), (4, 0, 0)] := by
  simp only [g1, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
  simp only [mono]
  char_two_ring

theorem pderiv_one_g1 : pderiv 1 g1 = X 0 ^ 2 * psi1 := by
  rw [tan1_one]
  simp only [psi1, poly_cons, poly_nil, mono]
  ring

theorem pderiv_two_g1 : pderiv 2 g1 = X 0 ^ 2 * psi2 := by
  rw [tan1_two]
  simp only [psi2, poly_cons, poly_nil, mono]
  ring

/-! ### The generators of the ideals at `P₂` -/

theorem res2_zero : ((expo 2 3 0 0 : ℕ) : ZMod 2) • G2 + X 0 * pderiv 0 G2 = 0 := by
  simp only [expo_apply_zero, G2, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char_two_ring

theorem res2_one : ((expo 2 3 0 1 : ℕ) : ZMod 2) • G2 + X 1 * pderiv 1 G2 =
    poly [(2, 0, 0), (0, 0, 3), (2, 0, 1)] := by
  simp only [expo_apply_one, G2, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char_two_ring

theorem res2_two : pderiv 2 G2 = poly [(0, 0, 2), (2, 0, 0), (2, 1, 0)] := by
  simp only [G2, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
  simp only [mono]
  char_two_ring

theorem pderiv_zero_g2 : pderiv 0 g2 = 0 := by
  simp only [g2, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
  simp only [mono]
  char_two_ring

theorem tan2_one : X 1 * pderiv 1 g2 = poly [(2, 3, 3), (4, 3, 0), (4, 3, 1)] := by
  simp only [g2, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono]
  simp only [mono]
  char_two_ring

theorem tan2_two : pderiv 2 g2 = poly [(2, 3, 2), (4, 4, 0), (4, 3, 0)] := by
  simp only [g2, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
  simp only [mono]
  char_two_ring

/-! ### The orders `ρ` -/

theorem rho0 : logJacobianOrder ({0, 2} : Finset (Fin 3)) g0 = ((2 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, divisorExponent_g0, residualFactor_g0, residualLogJacobian]
  refine idealOrd_span_eq ?_ (Or.inl ⟨0, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · have hi' : i = 0 ∨ i = 2 := by simpa using hi
      dsimp only
      rcases hi' with rfl | rfl
      · rw [res0_zero]
        exact le_ord_poly _ _ (by decide)
      · rw [res0_two, G0]
        exact le_ord_poly _ _ (by decide)
    · have hi' : i = 1 := by
        fin_cases i <;> simp_all
      subst hi'
      dsimp only
      rw [res0_one]
      exact le_ord_poly _ _ (by decide)
  · dsimp only
    rw [res0_zero]
    exact ord_poly_eq 2 0 0 (by decide) (by decide)

theorem rho1 : logJacobianOrder ({0} : Finset (Fin 3)) g1 = ((2 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, divisorExponent_g1, residualFactor_g1, residualLogJacobian]
  refine idealOrd_span_eq ?_ (Or.inr ⟨1, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · have hi' : i = 0 := by simpa using hi
      subst hi'
      dsimp only
      rw [res1_zero, ord_zero]
      exact le_top
    · have hi' : i = 1 ∨ i = 2 := by
        fin_cases i <;> simp_all
      dsimp only
      rcases hi' with rfl | rfl
      · rw [res1_one, psi1]
        exact le_ord_poly _ _ (by decide)
      · rw [res1_two, psi2]
        exact le_ord_poly _ _ (by decide)
  · dsimp only
    rw [res1_one, psi1]
    exact ord_poly_eq 2 0 0 (by decide) (by decide)

theorem rho2 : logJacobianOrder ({0, 1} : Finset (Fin 3)) g2 = ((2 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, divisorExponent_g2, residualFactor_g2, residualLogJacobian]
  refine idealOrd_span_eq ?_ (Or.inr ⟨2, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · have hi' : i = 0 ∨ i = 1 := by simpa using hi
      dsimp only
      rcases hi' with rfl | rfl
      · rw [res2_zero, ord_zero]
        exact le_top
      · rw [res2_one]
        exact le_ord_poly _ _ (by decide)
    · have hi' : i = 2 := by
        fin_cases i <;> simp_all
      subst hi'
      dsimp only
      rw [res2_two]
      exact le_ord_poly _ _ (by decide)
  · dsimp only
    rw [res2_two]
    exact ord_poly_eq 2 0 0 (by decide) (by decide)

/-! ### The orders of `Θ₀` -/

theorem tangent0 :
    idealOrd (logJacobianTangent ({0, 2} : Finset (Fin 3)) g0) = ((4 : ℕ) : ℕ∞) := by
  rw [logJacobianTangent]
  refine idealOrd_span_eq ?_ (Or.inl ⟨2, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩)
    · have hi' : i = 0 ∨ i = 2 := by simpa using hi
      dsimp only
      rcases hi' with rfl | rfl
      · rw [tan0_zero]
        exact le_ord_poly _ _ (by decide)
      · rw [tan0_two, g0]
        exact le_ord_poly _ _ (by decide)
    · have hl' : l = 1 := by
        fin_cases l <;> simp_all
      subst hl'
      dsimp only
      rw [tan0_one]
      exact (le_ord_X_mul (n := 5) (le_ord_poly _ _ (by decide)) a).trans' (by norm_num)
  · dsimp only
    rw [tan0_two, g0]
    exact ord_poly_eq 3 0 1 (by decide) (by decide)

theorem tangent1 :
    idealOrd (logJacobianTangent ({0} : Finset (Fin 3)) g1) = ((5 : ℕ) : ℕ∞) := by
  rw [logJacobianTangent]
  refine idealOrd_span_eq ?_ (Or.inr ⟨(0, 2), by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩)
    · have hi' : i = 0 := by simpa using hi
      subst hi'
      dsimp only
      rw [pderiv_zero_g1, mul_zero, ord_zero]
      exact le_top
    · have hl' : l = 1 ∨ l = 2 := by
        fin_cases l <;> simp_all
      dsimp only
      rcases hl' with rfl | rfl
      · rw [tan1_one]
        exact le_ord_X_mul (n := 4) (le_ord_poly _ _ (by decide)) a
      · rw [tan1_two]
        exact le_ord_X_mul (n := 4) (le_ord_poly _ _ (by decide)) a
  · dsimp only
    rw [tan1_two, ord_mul, ord_X, ord_poly_eq 2 0 2 (by decide) (by decide)]
    norm_num

theorem tangent2 :
    idealOrd (logJacobianTangent ({0, 1} : Finset (Fin 3)) g2) = ((7 : ℕ) : ℕ∞) := by
  rw [logJacobianTangent]
  refine idealOrd_span_eq ?_ (Or.inl ⟨1, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩)
    · have hi' : i = 0 ∨ i = 1 := by simpa using hi
      dsimp only
      rcases hi' with rfl | rfl
      · rw [pderiv_zero_g2, mul_zero, ord_zero]
        exact le_top
      · rw [tan2_one]
        exact le_ord_poly _ _ (by decide)
    · have hl' : l = 2 := by
        fin_cases l <;> simp_all
      subst hl'
      dsimp only
      rw [tan2_two]
      exact (le_ord_X_mul (n := 7) (le_ord_poly _ _ (by decide)) a).trans' (by norm_num)
  · dsimp only
    rw [tan2_one]
    exact ord_poly_eq 4 3 0 (by decide) (by decide)

/-! ### The cases -/

theorem caseA0 : IsLogJacobianCaseA P0 := by
  show idealOrd (logJacobianTangent ({0, 2} : Finset (Fin 3)) g0) =
    ((degree (divisorExponent ({0, 2} : Finset (Fin 3)) g0) : ℕ) : ℕ∞) +
      logJacobianOrder ({0, 2} : Finset (Fin 3)) g0
  rw [tangent0, divisorExponent_g0, degree_expo, rho0]
  norm_num

theorem caseB1 : IsLogJacobianCaseB P1 := by
  show idealOrd (logJacobianTangent ({0} : Finset (Fin 3)) g1) =
    ((degree (divisorExponent ({0} : Finset (Fin 3)) g1) : ℕ) : ℕ∞) +
      logJacobianOrder ({0} : Finset (Fin 3)) g1 + 1
  rw [tangent1, divisorExponent_g1, degree_expo, rho1]
  norm_num

theorem caseA2 : IsLogJacobianCaseA P2 := by
  show idealOrd (logJacobianTangent ({0, 1} : Finset (Fin 3)) g2) =
    ((degree (divisorExponent ({0, 1} : Finset (Fin 3)) g2) : ℕ) : ℕ∞) +
      logJacobianOrder ({0, 1} : Finset (Fin 3)) g2
  rw [tangent2, divisorExponent_g2, degree_expo, rho2]
  norm_num

/-- The point `P₁` is not of case A, so its ideal is `Θ(g₁)`. -/
theorem caseIdeal1 :
    logJacobianCaseIdeal ({0} : Finset (Fin 3)) g1 = logJacobian ({0} : Finset (Fin 3)) g1 := by
  refine logJacobianCaseIdeal_of_ne ?_
  rw [tangent1, divisorExponent_g1, degree_expo, rho1]
  intro h
  rw [← Nat.cast_add] at h
  have h' := congrArg ENat.toNat h
  simp only [ENat.toNat_natCast] at h'
  omega

/-! ### The steps -/

theorem step01 : RhoStep 2 2 P0 P1 := by
  refine ⟨0, t0, h0, poly_ne_zero (a := 3) (b := 0) (c := 1) (by decide),
    isClean_poly _ (by decide), le_ord_poly _ 2 (by decide), pointChart_g0, ?_, rho0, rho1⟩
  show ((({0} : Finset (Fin 3)), g1) : Finset (Fin 3) × Poly) =
    (blowupDivisor ({0, 2} : Finset (Fin 3)) 0 t0, cleanPart 2 h0)
  rw [blowupDivisor_P0, cleanPart_h0]

theorem step12 : RhoStep 2 2 P1 P2 := by
  refine ⟨1, 0, g2, poly_ne_zero (a := 2) (b := 0) (c := 3) (by decide),
    isClean_poly _ (by decide), le_ord_poly _ 2 (by decide), pointChart_g1, ?_, rho1, rho2⟩
  show ((({0, 1} : Finset (Fin 3)), g2) : Finset (Fin 3) × Poly) =
    (blowupDivisor ({0} : Finset (Fin 3)) 1 0, cleanPart 2 g2)
  rw [blowupDivisor_P1, cleanPart_g2]

/-! ### Directrices of squares -/

theorem translate_X' (v : Fin 3 → ZMod 2) (i : Fin 3) :
    translate v (X i : Poly) = X (some i) + C (v i) * X none := by
  rw [translate, aeval_X]

theorem sq_add_sq_char_two (a b c : Poly') : (a + c) ^ 2 + (b + c) ^ 2 = a ^ 2 + b ^ 2 := by
  linear_combination (a * c + b * c + c ^ 2) * two_eq_zero'

theorem mem_directrix_add {f g : Poly} {v : Fin 3 → ZMod 2} (hf : v ∈ directrix f)
    (hg : v ∈ directrix g) : v ∈ directrix (f + g) := by
  rw [mem_directrix_iff] at hf hg ⊢
  rw [map_add, map_add, hf, hg]

/-- If `v_x = v_z`, then `v` is in the directrix of `x² + z²`. -/
theorem mem_directrix_F0 {v : Fin 3 → ZMod 2} (h : v 2 = v 0) :
    v ∈ directrix (X 0 ^ 2 + X 2 ^ 2 : Poly) := by
  rw [mem_directrix_iff]
  simp only [map_add, map_pow, translate_X', rename_X, h]
  exact sq_add_sq_char_two _ _ _

/-! ### The directrix at `P₀` -/

theorem caseAForm_g0_zero :
    caseAForm ({0, 2} : Finset (Fin 3)) g0 2 0 = X 0 ^ 2 + X 2 ^ 2 := by
  unfold caseAForm
  rw [divisorExponent_g0, residualFactor_g0, G0, homogeneousComponent_poly,
    show (List.filter (fun e : ℕ × ℕ × ℕ => decide (e.1 + e.2.1 + e.2.2 = 2))
      [(2, 0, 0), (0, 0, 2), (3, 1, 0)]) = [(2, 0, 0), (0, 0, 2)] from by decide]
  simp only [expo_apply_zero, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char_two_ring

theorem caseAForm_g0_two :
    caseAForm ({0, 2} : Finset (Fin 3)) g0 2 2 = X 0 ^ 2 + X 2 ^ 2 := by
  unfold caseAForm
  rw [divisorExponent_g0, residualFactor_g0, G0, homogeneousComponent_poly,
    show (List.filter (fun e : ℕ × ℕ × ℕ => decide (e.1 + e.2.1 + e.2.2 = 2))
      [(2, 0, 0), (0, 0, 2), (3, 1, 0)]) = [(2, 0, 0), (0, 0, 2)] from by decide]
  simp only [expo_apply_two, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char_two_ring

/-- The linear form `v ↦ v_x + v_z`. -/
noncomputable def ell0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) + LinearMap.proj 2

theorem ell0_apply (v : Fin 3 → ZMod 2) : ell0 v = v 0 + v 2 := rfl

theorem eq_of_mem_ker_ell0 {v : Fin 3 → ZMod 2} (hv : v ∈ LinearMap.ker ell0) : v 2 = v 0 := by
  rw [LinearMap.mem_ker, ell0_apply] at hv
  revert hv
  generalize v 0 = a
  generalize v 2 = c
  revert a c
  decide

theorem ker_ell0_le_T0 :
    LinearMap.ker ell0 ≤ logJacobianDirectrix ({0, 2} : Finset (Fin 3)) g0 := by
  rw [logJacobianDirectrix_eq_iInf_caseAForm rho0 caseA0]
  refine le_iInf₂ fun i hi => ?_
  have hi' : i = 0 ∨ i = 2 := by simpa using hi
  intro v hv
  rcases hi' with rfl | rfl
  · rw [caseAForm_g0_zero]
    exact mem_directrix_F0 (eq_of_mem_ker_ell0 hv)
  · rw [caseAForm_g0_two]
    exact mem_directrix_F0 (eq_of_mem_ker_ell0 hv)

theorem finrank_ker_ell0 : Module.finrank (ZMod 2) (LinearMap.ker ell0) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker ell0
  have hr : LinearMap.range ell0 = ⊤ :=
    LinearMap.range_eq_top.mpr fun c => ⟨Pi.single 0 c, by simp [ell0_apply]⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

/-- `τ_ρ(P₀) = 1`. -/
theorem codim_P0 : logJacobianDirectrixCodim P0.1 P0.2 = 1 := by
  have h1 : 1 ≤ logJacobianDirectrixCodim ({0, 2} : Finset (Fin 3)) g0 :=
    one_le_logJacobianDirectrixCodim_of_caseA rho0 two_ne_zero caseA0
  have h2 : Module.finrank (ZMod 2) (LinearMap.ker ell0) ≤
      Module.finrank (ZMod 2) (logJacobianDirectrix ({0, 2} : Finset (Fin 3)) g0) :=
    Submodule.finrank_mono ker_ell0_le_T0
  rw [finrank_ker_ell0] at h2
  have h1' : 1 ≤ Fintype.card (Fin 3) -
      Module.finrank (ZMod 2) (logJacobianDirectrix ({0, 2} : Finset (Fin 3)) g0) := h1
  show Fintype.card (Fin 3) -
      Module.finrank (ZMod 2) (logJacobianDirectrix ({0, 2} : Finset (Fin 3)) g0) = 1
  rw [Fintype.card_fin] at h1' ⊢
  omega

/-! ### The directrix at `P₂` -/

theorem caseAForm_g2_zero : caseAForm ({0, 1} : Finset (Fin 3)) g2 2 0 = 0 := by
  unfold caseAForm
  rw [divisorExponent_g2, residualFactor_g2, G2, homogeneousComponent_poly,
    show (List.filter (fun e : ℕ × ℕ × ℕ => decide (e.1 + e.2.1 + e.2.2 = 2))
      [(2, 0, 0), (0, 0, 3), (2, 0, 1), (2, 1, 1)]) = [(2, 0, 0)] from by decide]
  simp only [expo_apply_zero, poly_cons, poly_nil, add_zero, pderiv_zero_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char_two_ring

theorem caseAForm_g2_one : caseAForm ({0, 1} : Finset (Fin 3)) g2 2 1 = X 0 ^ 2 := by
  unfold caseAForm
  rw [divisorExponent_g2, residualFactor_g2, G2, homogeneousComponent_poly,
    show (List.filter (fun e : ℕ × ℕ × ℕ => decide (e.1 + e.2.1 + e.2.2 = 2))
      [(2, 0, 0), (0, 0, 3), (2, 0, 1), (2, 1, 1)]) = [(2, 0, 0)] from by decide]
  simp only [expo_apply_one, poly_cons, poly_nil, add_zero, pderiv_one_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char_two_ring

theorem ker_le_T2 : LinearMap.ker (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ≤
    logJacobianDirectrix ({0, 1} : Finset (Fin 3)) g2 := by
  rw [logJacobianDirectrix_eq_iInf_caseAForm rho2 caseA2]
  refine le_iInf₂ fun i hi => ?_
  have hi' : i = 0 ∨ i = 1 := by simpa using hi
  rcases hi' with rfl | rfl
  · rw [caseAForm_g2_zero, directrix_zero]
    exact le_top
  · rw [caseAForm_g2_one]
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.proj_apply] at hv
    exact (mem_directrix_X_pow_iff two_ne_zero).mpr hv

theorem finrank_ker : Module.finrank (ZMod 2)
    (LinearMap.ker (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
  have hr : LinearMap.range (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) = ⊤ :=
    LinearMap.range_eq_top.mpr fun c => ⟨fun _ => c, rfl⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

/-- `τ_ρ(P₂) = 1`. -/
theorem codim_P2 : logJacobianDirectrixCodim P2.1 P2.2 = 1 := by
  have h1 : 1 ≤ logJacobianDirectrixCodim ({0, 1} : Finset (Fin 3)) g2 :=
    one_le_logJacobianDirectrixCodim_of_caseA rho2 two_ne_zero caseA2
  have h2 : Module.finrank (ZMod 2)
      (LinearMap.ker (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)) ≤
      Module.finrank (ZMod 2) (logJacobianDirectrix ({0, 1} : Finset (Fin 3)) g2) :=
    Submodule.finrank_mono ker_le_T2
  rw [finrank_ker] at h2
  have h1' : 1 ≤ Fintype.card (Fin 3) -
      Module.finrank (ZMod 2) (logJacobianDirectrix ({0, 1} : Finset (Fin 3)) g2) := h1
  show Fintype.card (Fin 3) -
      Module.finrank (ZMod 2) (logJacobianDirectrix ({0, 1} : Finset (Fin 3)) g2) = 1
  rw [Fintype.card_fin] at h1' ⊢
  omega

/-! ### The directrix at `P₁` -/

theorem monoX : monomial (expo 2 0 0) (1 : ZMod 2) = (X 0 ^ 2 : Poly) := by
  rw [← mono_eq]
  simp [mono]

theorem hm1 : (logJacobianOrder ({0} : Finset (Fin 3)) g1).toNat = 2 := by
  rw [rho1]
  rfl

theorem hc_psi1 : homogeneousComponent 2 psi1 = (X 0 ^ 2 : Poly) := by
  rw [psi1, homogeneousComponent_poly,
    show (List.filter (fun e : ℕ × ℕ × ℕ => decide (e.1 + e.2.1 + e.2.2 = 2))
      [(2, 0, 1), (2, 0, 0)]) = [(2, 0, 0)] from by decide]
  simp only [poly_cons, poly_nil, mono, pow_zero, mul_one, add_zero]

theorem hc_psi2 : homogeneousComponent 2 psi2 = (X 0 ^ 2 + X 2 ^ 2 : Poly) := by
  rw [psi2, homogeneousComponent_poly,
    show (List.filter (fun e : ℕ × ℕ × ℕ => decide (e.1 + e.2.1 + e.2.2 = 2))
      [(0, 0, 2), (2, 1, 0), (2, 0, 0)]) = [(0, 0, 2), (2, 0, 0)] from by decide]
  simp only [poly_cons, poly_nil, mono, pow_zero, mul_one, one_mul, add_zero, add_comm]

theorem psi1_mem : psi1 ∈ logJacobianDirectrixSet ({0} : Finset (Fin 3)) g1 := by
  refine ⟨?_, ?_⟩
  · rw [rho1, psi1]
    exact ord_poly_eq 2 0 0 (by decide) (by decide)
  · rw [caseIdeal1, divisorExponent_g1, monoX, ← pderiv_one_g1]
    exact pderiv_mem_logJacobian (by decide) g1

theorem psi2_mem : psi2 ∈ logJacobianDirectrixSet ({0} : Finset (Fin 3)) g1 := by
  refine ⟨?_, ?_⟩
  · rw [rho1, psi2]
    exact ord_poly_eq 2 0 0 (by decide) (by decide)
  · rw [caseIdeal1, divisorExponent_g1, monoX, ← pderiv_two_g1]
    exact pderiv_mem_logJacobian (by decide) g1

/-- The ideal `Θ(g₁)` is `x² (ψ₁, ψ₂)`, with `ψ₁ = ∂_y G₁` and `ψ₂ = ∂_z G₁`. -/
theorem logJacobian_g1_le : logJacobian ({0} : Finset (Fin 3)) g1 ≤
    Ideal.span {X 0 ^ 2 * psi1, X 0 ^ 2 * psi2} := by
  rw [logJacobian, Ideal.span_le]
  rintro s (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
  · have hi' : i = 0 := by simpa using hi
    subst hi'
    dsimp only
    rw [pderiv_zero_g1, mul_zero]
    exact Ideal.zero_mem _
  · have hj' : j = 1 ∨ j = 2 := by
      fin_cases j <;> simp_all
    dsimp only
    rcases hj' with rfl | rfl
    · rw [pderiv_one_g1]
      exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [pderiv_two_g1]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem mem_span_of_mem_set {ψ : Poly}
    (hψ : ψ ∈ logJacobianDirectrixSet ({0} : Finset (Fin 3)) g1) :
    ψ ∈ Ideal.span {psi1, psi2} := by
  have h := hψ.2
  rw [caseIdeal1, divisorExponent_g1, monoX] at h
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp (logJacobian_g1_le h)
  have hX : (X 0 ^ 2 : Poly) ≠ 0 := pow_ne_zero 2 (X_ne_zero 0)
  have hψ' : ψ = c * psi1 + d * psi2 := mul_left_cancel₀ hX (by rw [← hcd]; ring)
  exact Ideal.mem_span_pair.mpr ⟨c, d, hψ'.symm⟩

/-- The vector `e_y`. -/
noncomputable def e1 : Fin 3 → ZMod 2 := Pi.single 1 1

theorem e1_ne_zero : e1 ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [e1] at this

theorem T1_le : logJacobianDirectrix ({0} : Finset (Fin 3)) g1 ≤
    Submodule.span (ZMod 2) {e1} := by
  intro v hv
  have h1 := logJacobianDirectrix_le psi1_mem hv
  have h2 := logJacobianDirectrix_le psi2_mem hv
  rw [hm1, hc_psi1] at h1
  rw [hm1, hc_psi2] at h2
  have h0 : v 0 = 0 := (mem_directrix_X_pow_iff two_ne_zero).mp h1
  have h3 : v ∈ directrix (X 2 ^ 2 : Poly) := by
    have h4 := mem_directrix_add h1 h2
    rwa [show (X 0 ^ 2 + (X 0 ^ 2 + X 2 ^ 2) : Poly) = X 2 ^ 2 by
      linear_combination (X 0 ^ 2 : Poly) * num2] at h4
  have h2' : v 2 = 0 := (mem_directrix_X_pow_iff two_ne_zero).mp h3
  rw [Submodule.mem_span_singleton]
  refine ⟨v 1, ?_⟩
  ext i
  fin_cases i <;> simp [e1, h0, h2']

theorem span_le_T1 : Submodule.span (ZMod 2) {e1} ≤
    logJacobianDirectrix ({0} : Finset (Fin 3)) g1 := by
  have he0 : e1 ∈ directrix (X 0 ^ 2 : Poly) :=
    (mem_directrix_X_pow_iff two_ne_zero).mpr (by simp [e1])
  have he2 : e1 ∈ directrix (X 2 ^ 2 : Poly) :=
    (mem_directrix_X_pow_iff two_ne_zero).mpr (by simp [e1])
  refine le_logJacobianDirectrix fun ψ hψ => ?_
  rw [hm1]
  refine le_directrix_homogeneousComponent_of_mem_span ?_ ?_ (mem_span_of_mem_set hψ)
  · intro s hs
    rcases hs with rfl | hs
    · exact le_ord_poly _ _ (by decide)
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact le_ord_poly _ _ (by decide)
  · intro s hs
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    rcases hs with rfl | hs
    · rw [hc_psi1]
      exact he0
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      rw [hc_psi2]
      exact mem_directrix_add he0 he2

/-- `τ_ρ(P₁) = 2`. -/
theorem codim_P1 : logJacobianDirectrixCodim P1.1 P1.2 = 2 := by
  have h1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {e1}) ≤
      Module.finrank (ZMod 2) (logJacobianDirectrix ({0} : Finset (Fin 3)) g1) :=
    Submodule.finrank_mono span_le_T1
  have h2 : Module.finrank (ZMod 2) (logJacobianDirectrix ({0} : Finset (Fin 3)) g1) ≤
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {e1}) :=
    Submodule.finrank_mono T1_le
  rw [finrank_span_singleton e1_ne_zero] at h1 h2
  show Fintype.card (Fin 3) -
      Module.finrank (ZMod 2) (logJacobianDirectrix ({0} : Finset (Fin 3)) g1) = 2
  rw [Fintype.card_fin]
  omega

/-! ### The example -/

/-- **Example 3.11.2 of the handbook.** The path `P₀ → P₁ → P₂` keeps `ρ = 2`. The points `P₀`
and `P₂` are of case A, and the point `P₁` is of case B. The codimension `τ_ρ` is `1` at `P₀`,
`2` at `P₁`, and `1` at `P₂`. So `τ_ρ` goes down at the last step. -/
theorem kangarooExample :
    RhoStep 2 2 P0 P1 ∧ IsLogJacobianCaseB P1 ∧ RhoStep 2 2 P1 P2 ∧
    IsLogJacobianCaseA P0 ∧ IsLogJacobianCaseA P2 ∧
    logJacobianDirectrixCodim P0.1 P0.2 = 1 ∧ logJacobianDirectrixCodim P1.1 P1.2 = 2 ∧
    logJacobianDirectrixCodim P2.1 P2.2 = 1 :=
  ⟨step01, caseB1, step12, caseA0, caseA2, codim_P0, codim_P1, codim_P2⟩

end KangarooExample

end Singularity
