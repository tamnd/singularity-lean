/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianCaseAForms

/-!
# A counterexample to the kangaroo path conjecture

This file shows that `KangarooPathConjecture` is false for `p = 2`, for three variables and for
the field `ZMod 2`. The variables `x, y, z` are the indices `0, 1, 2` of `Fin 3`.

The path has three points and `ρ = 4` at each point.

* `P₀ = ({y, z}, g₀)` with `g₀ = x²y³z + x²yz³ + x⁴yz²`. It is of case A, and `τ_ρ(P₀) = 2`.
* `P₁ = ({y}, g₁)` with `g₁ = x²y⁴z³ + x⁴y⁵ + x⁴y⁵z²`. It comes from `P₀` by the `y`-chart with
  the translation `z ↦ z + 1`, and it is of case B.
* `P₂ = ({y}, g₂)` with `g₂ = x²y⁷z³ + x⁴y⁷ + x⁴y⁹z²`. It comes from `P₁` by the `y`-chart with no
  translation, it is of case A, and `τ_ρ(P₂) = 1`.

So `τ_ρ(P₀) ≤ τ_ρ(P₂)` fails.
-/

open MvPolynomial Finsupp

namespace Singularity

namespace KangarooCounterexample

instance factPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The polynomial ring `𝔽₂[x, y, z]`. -/
abbrev Poly := MvPolynomial (Fin 3) (ZMod 2)

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

theorem num13 : (13 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 13
  simpa using this

theorem num14 : (14 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 14
  simpa using this

theorem num15 : (15 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 15
  simpa using this

theorem num16 : (16 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 16
  simpa using this

theorem num17 : (17 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 17
  simpa using this

theorem num18 : (18 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 18
  simpa using this

theorem num19 : (19 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 19
  simpa using this

theorem num20 : (20 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 20
  simpa using this

theorem num21 : (21 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 21
  simpa using this

theorem num22 : (22 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 22
  simpa using this

theorem num23 : (23 : Poly) = 1 := by
  have := CharP.cast_eq_mod Poly 2 23
  simpa using this

theorem num24 : (24 : Poly) = 0 := by
  have := CharP.cast_eq_mod Poly 2 24
  simpa using this

/-- Close a polynomial identity in characteristic `2`: normalize, reduce the numerals modulo
`2`, and normalize again. -/
macro "char2" : tactic => `(tactic| (ring_nf <;>
  (try simp only [num2, num3, num4, num5, num6, num7, num8, num9, num10, num11, num12, num13,
    num14, num15, num16, num17, num18, num19, num20, num21, num22, num23, num24, mul_zero,
    zero_mul, add_zero, zero_add, mul_one, one_mul]) <;> (try ring_nf)))

/-! ### The polynomials of the path -/

/-- `g₀ = x²y³z + x²yz³ + x⁴yz²`. -/
noncomputable def g0 : Poly := poly [(2, 3, 1), (2, 1, 3), (4, 1, 2)]
/-- The residual factor `G₀ = x²y² + x²z² + x⁴z` of `g₀ = yz G₀`. -/
noncomputable def G0 : Poly := poly [(2, 2, 0), (2, 0, 2), (4, 0, 1)]
/-- The quotient of the chart of `g₀` by `y²`. -/
noncomputable def h0 : Poly := poly [(2, 4, 3), (2, 4, 2), (4, 5, 2), (4, 5, 0)]
/-- `g₁ = x²y⁴z³ + x⁴y⁵ + x⁴y⁵z²`, the clean part of `h0`. -/
noncomputable def g1 : Poly := poly [(2, 4, 3), (4, 5, 0), (4, 5, 2)]
/-- The residual factor `G₁ = x²z³ + x⁴y + x⁴yz²` of `g₁ = y⁴ G₁`. -/
noncomputable def G1 : Poly := poly [(2, 0, 3), (4, 1, 0), (4, 1, 2)]
/-- `g₂ = x²y⁷z³ + x⁴y⁷ + x⁴y⁹z²`. -/
noncomputable def g2 : Poly := poly [(2, 7, 3), (4, 7, 0), (4, 9, 2)]
/-- The residual factor `G₂ = x²z³ + x⁴ + x⁴y²z²` of `g₂ = y⁷ G₂`. -/
noncomputable def G2 : Poly := poly [(2, 0, 3), (4, 0, 0), (4, 2, 2)]

/-- The translation `z ↦ z + 1` of the first chart. -/
def t0 : Fin 3 → ZMod 2 := ![0, 0, 1]

/-- The three points of the path. -/
noncomputable def P0 : Finset (Fin 3) × Poly := ({1, 2}, g0)
noncomputable def P1 : Finset (Fin 3) × Poly := ({1}, g1)
noncomputable def P2 : Finset (Fin 3) × Poly := ({1}, g2)

/-! ### The charts -/

theorem pointChart_g0 : pointChart 1 t0 g0 = X 1 ^ 2 * h0 := by
  have hx : pointChart (1 : Fin 3) t0 (X 0) = (X 1 * X 0 : Poly) := by
    rw [pointChart_X_of_ne t0 (by decide)]
    simp [t0]
  have hz : pointChart (1 : Fin 3) t0 (X 2) = (X 1 * (X 2 + 1) : Poly) := by
    rw [pointChart_X_of_ne t0 (by decide)]
    simp [t0]
  simp only [g0, h0, poly_cons, poly_nil, mono, map_add, map_mul, map_pow, hx, hz,
    pointChart_X_self, add_zero]
  char2

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

theorem blowupDivisor_P0 : blowupDivisor ({1, 2} : Finset (Fin 3)) 1 t0 = {1} := by
  unfold blowupDivisor t0
  decide

theorem blowupDivisor_P1 : blowupDivisor ({1} : Finset (Fin 3)) 1 (0 : Fin 3 → ZMod 2) = {1} := by
  unfold blowupDivisor
  decide

theorem cleanPart_h0 : cleanPart 2 h0 = g1 := by
  have h : h0 = g1 + mono 1 2 1 ^ 2 ^ 1 := by
    simp only [h0, g1, poly_cons, poly_nil, mono]
    ring
  have := cleanPart_add_pow 2 1 g1 (mono 1 2 1)
  rw [pow_one] at this
  rw [h, pow_one, this]
  exact cleanPart_eq_self (isClean_poly _ (by decide))

theorem cleanPart_g2 : cleanPart 2 g2 = g2 :=
  cleanPart_eq_self (isClean_poly _ (by decide))

/-! ### The factorizations `g = x^r G` -/

theorem g0_eq : g0 = monomial (expo 0 1 1) 1 * G0 := by
  rw [← mono_eq]
  simp only [g0, G0, poly_cons, poly_nil, mono]
  ring

theorem g1_eq : g1 = monomial (expo 0 4 0) 1 * G1 := by
  rw [← mono_eq]
  simp only [g1, G1, poly_cons, poly_nil, mono]
  ring

theorem g2_eq : g2 = monomial (expo 0 7 0) 1 * G2 := by
  rw [← mono_eq]
  simp only [g2, G2, poly_cons, poly_nil, mono]
  ring

theorem hr0 : ∀ i, i ∉ ({1, 2} : Finset (Fin 3)) → expo 0 1 1 i = 0 := by
  intro i hi
  fin_cases i <;> simp_all

theorem hr1 (b : ℕ) : ∀ i, i ∉ ({1} : Finset (Fin 3)) → expo 0 b 0 i = 0 := by
  intro i hi
  fin_cases i <;> simp_all

theorem hG0 : ∀ i ∈ ({1, 2} : Finset (Fin 3)), ∃ d ∈ G0.support, d i = 0 := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨expo 2 0 2, MvPolynomial.mem_support_iff.mpr (coeff_poly_ne_zero (by decide)), by simp⟩
  · exact ⟨expo 2 2 0, MvPolynomial.mem_support_iff.mpr (coeff_poly_ne_zero (by decide)), by simp⟩

theorem hG1 : ∀ i ∈ ({1} : Finset (Fin 3)), ∃ d ∈ G1.support, d i = 0 := by
  intro i hi
  simp only [Finset.mem_singleton] at hi
  subst hi
  exact ⟨expo 2 0 3, MvPolynomial.mem_support_iff.mpr (coeff_poly_ne_zero (by decide)), by simp⟩

theorem hG2 : ∀ i ∈ ({1} : Finset (Fin 3)), ∃ d ∈ G2.support, d i = 0 := by
  intro i hi
  simp only [Finset.mem_singleton] at hi
  subst hi
  exact ⟨expo 2 0 3, MvPolynomial.mem_support_iff.mpr (coeff_poly_ne_zero (by decide)), by simp⟩

theorem divisorExponent_g0 : divisorExponent {1, 2} g0 = expo 0 1 1 := by
  rw [g0_eq]
  exact divisorExponent_monomial_mul' hr0 hG0

theorem residualFactor_g0 : residualFactor {1, 2} g0 = G0 := by
  rw [g0_eq]
  exact residualFactor_monomial_mul hr0 hG0

theorem divisorExponent_g1 : divisorExponent {1} g1 = expo 0 4 0 := by
  rw [g1_eq]
  exact divisorExponent_monomial_mul' (hr1 4) hG1

theorem residualFactor_g1 : residualFactor {1} g1 = G1 := by
  rw [g1_eq]
  exact residualFactor_monomial_mul (hr1 4) hG1

theorem divisorExponent_g2 : divisorExponent {1} g2 = expo 0 7 0 := by
  rw [g2_eq]
  exact divisorExponent_monomial_mul' (hr1 7) hG2

theorem residualFactor_g2 : residualFactor {1} g2 = G2 := by
  rw [g2_eq]
  exact residualFactor_monomial_mul (hr1 7) hG2


/-! ### The generators of the ideals -/

theorem pderiv_zero_g0 : pderiv 0 g0 = 0 := by
  simp only [g0, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
  simp only [mono]
  char2

theorem pderiv_zero_G0 : pderiv 0 G0 = 0 := by
  simp only [G0, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
  simp only [mono]
  char2

theorem pderiv_zero_g1 : pderiv 0 g1 = 0 := by
  simp only [g1, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
  simp only [mono]
  char2

theorem pderiv_zero_G1 : pderiv 0 G1 = 0 := by
  simp only [G1, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
  simp only [mono]
  char2

theorem pderiv_zero_g2 : pderiv 0 g2 = 0 := by
  simp only [g2, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
  simp only [mono]
  char2

theorem pderiv_zero_G2 : pderiv 0 G2 = 0 := by
  simp only [G2, poly_cons, poly_nil, add_zero, map_add, pderiv_zero_mono]
  simp only [mono]
  char2

theorem res0_one : ((expo 0 1 1 1 : ℕ) : ZMod 2) • G0 + X 1 * pderiv 1 G0 = G0 := by
  simp only [expo_apply_one, G0, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char2

theorem res0_two : ((expo 0 1 1 2 : ℕ) : ZMod 2) • G0 + X 2 * pderiv 2 G0 =
    poly [(2, 2, 0), (2, 0, 2)] := by
  simp only [expo_apply_two, G0, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char2

theorem res1_one : ((expo 0 4 0 1 : ℕ) : ZMod 2) • G1 + X 1 * pderiv 1 G1 =
    poly [(4, 1, 0), (4, 1, 2)] := by
  simp only [expo_apply_one, G1, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char2

theorem res1_two : pderiv 2 G1 = poly [(2, 0, 2)] := by
  simp only [G1, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
  simp only [mono]
  char2

theorem res2_one : ((expo 0 7 0 1 : ℕ) : ZMod 2) • G2 + X 1 * pderiv 1 G2 = G2 := by
  simp only [expo_apply_one, G2, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char2

theorem res2_two : pderiv 2 G2 = poly [(2, 0, 2)] := by
  simp only [G2, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
  simp only [mono]
  char2

theorem tan0_one : X 1 * pderiv 1 g0 = g0 := by
  simp only [g0, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono]
  simp only [mono]
  char2

theorem tan0_two : X 2 * pderiv 2 g0 = poly [(2, 3, 1), (2, 1, 3)] := by
  simp only [g0, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
  simp only [mono]
  char2

theorem tan1_one : X 1 * pderiv 1 g1 = poly [(4, 5, 0), (4, 5, 2)] := by
  simp only [g1, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono]
  simp only [mono]
  char2

theorem tan1_two : pderiv 2 g1 = poly [(2, 4, 2)] := by
  simp only [g1, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
  simp only [mono]
  char2

theorem tan2_one : X 1 * pderiv 1 g2 = g2 := by
  simp only [g2, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono]
  simp only [mono]
  char2

theorem tan2_two : pderiv 2 g2 = poly [(2, 7, 2)] := by
  simp only [g2, poly_cons, poly_nil, add_zero, map_add, pderiv_two_mono]
  simp only [mono]
  char2

theorem le_ord_X_mul {n : ℕ} {f : Poly} (h : (n : ℕ∞) ≤ ord f) (a : Fin 3) :
    ((n + 1 : ℕ) : ℕ∞) ≤ ord (X a * f) := by
  rw [ord_mul, ord_X, Nat.cast_add, Nat.cast_one, add_comm]
  exact add_le_add le_rfl h

/-! ### The orders `ρ` -/

theorem rho0 : logJacobianOrder ({1, 2} : Finset (Fin 3)) g0 = ((4 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, divisorExponent_g0, residualFactor_g0, residualLogJacobian]
  refine idealOrd_span_eq ?_ (Or.inl ⟨1, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi
      dsimp only
      rcases hi with rfl | rfl
      · rw [res0_one, G0]
        exact le_ord_poly _ _ (by decide)
      · rw [res0_two]
        exact le_ord_poly _ _ (by decide)
    · have : i = 0 := by
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hi
        fin_cases i <;> simp_all
      subst this
      dsimp only
      rw [pderiv_zero_G0, ord_zero]
      exact le_top
  · dsimp only
    rw [res0_one, G0]
    exact ord_poly_eq 2 2 0 (by decide) (by decide)

theorem rho1 : logJacobianOrder ({1} : Finset (Fin 3)) g1 = ((4 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, divisorExponent_g1, residualFactor_g1, residualLogJacobian]
  refine idealOrd_span_eq ?_ (Or.inr ⟨2, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hi
      dsimp only
      subst hi
      rw [res1_one]
      exact le_ord_poly _ _ (by decide)
    · have : i = 0 ∨ i = 2 := by
        simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff] at hi
        fin_cases i <;> simp_all
      dsimp only
      rcases this with rfl | rfl
      · rw [pderiv_zero_G1, ord_zero]
        exact le_top
      · rw [res1_two]
        exact le_ord_poly _ _ (by decide)
  · dsimp only
    rw [res1_two]
    exact ord_poly_eq 2 0 2 (by decide) (by decide)

theorem rho2 : logJacobianOrder ({1} : Finset (Fin 3)) g2 = ((4 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, divisorExponent_g2, residualFactor_g2, residualLogJacobian]
  refine idealOrd_span_eq ?_ (Or.inr ⟨2, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hi
      dsimp only
      subst hi
      rw [res2_one, G2]
      exact le_ord_poly _ _ (by decide)
    · have : i = 0 ∨ i = 2 := by
        simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff] at hi
        fin_cases i <;> simp_all
      dsimp only
      rcases this with rfl | rfl
      · rw [pderiv_zero_G2, ord_zero]
        exact le_top
      · rw [res2_two]
        exact le_ord_poly _ _ (by decide)
  · dsimp only
    rw [res2_two]
    exact ord_poly_eq 2 0 2 (by decide) (by decide)

/-! ### The orders of `Θ₀` -/

theorem tangent0 : idealOrd (logJacobianTangent ({1, 2} : Finset (Fin 3)) g0) = ((6 : ℕ) : ℕ∞) := by
  rw [logJacobianTangent]
  refine idealOrd_span_eq ?_ (Or.inl ⟨1, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩)
    · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi
      dsimp only
      rcases hi with rfl | rfl
      · rw [tan0_one, g0]
        exact le_ord_poly _ _ (by decide)
      · rw [tan0_two]
        exact le_ord_poly _ _ (by decide)
    · have : l = 0 := by
        simp only [Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton] at hl
        fin_cases l <;> simp_all
      subst this
      dsimp only
      rw [pderiv_zero_g0, mul_zero, ord_zero]
      exact le_top
  · dsimp only
    rw [tan0_one, g0]
    exact ord_poly_eq 2 3 1 (by decide) (by decide)

theorem tangent1 : idealOrd (logJacobianTangent ({1} : Finset (Fin 3)) g1) = ((9 : ℕ) : ℕ∞) := by
  rw [logJacobianTangent]
  refine idealOrd_span_eq ?_ (Or.inl ⟨1, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩)
    · simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hi
      dsimp only
      subst hi
      rw [tan1_one]
      exact le_ord_poly _ _ (by decide)
    · have : l = 0 ∨ l = 2 := by
        simp only [Set.mem_ofPred_eq, Finset.mem_singleton] at hl
        fin_cases l <;> simp_all
      dsimp only
      rcases this with rfl | rfl
      · rw [pderiv_zero_g1, mul_zero, ord_zero]
        exact le_top
      · rw [tan1_two]
        exact le_ord_X_mul (n := 8) (le_ord_poly _ _ (by decide)) a
  · dsimp only
    rw [tan1_one]
    exact ord_poly_eq 4 5 0 (by decide) (by decide)

theorem tangent2 : idealOrd (logJacobianTangent ({1} : Finset (Fin 3)) g2) = ((11 : ℕ) : ℕ∞) := by
  rw [logJacobianTangent]
  refine idealOrd_span_eq ?_ (Or.inl ⟨1, by simp, rfl⟩) ?_
  · rintro s (⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩)
    · simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hi
      dsimp only
      subst hi
      rw [tan2_one, g2]
      exact le_ord_poly _ _ (by decide)
    · have : l = 0 ∨ l = 2 := by
        simp only [Set.mem_ofPred_eq, Finset.mem_singleton] at hl
        fin_cases l <;> simp_all
      dsimp only
      rcases this with rfl | rfl
      · rw [pderiv_zero_g2, mul_zero, ord_zero]
        exact le_top
      · rw [tan2_two]
        exact (le_ord_X_mul (n := 11) (le_ord_poly _ _ (by decide)) a).trans' (by norm_num)
  · dsimp only
    rw [tan2_one, g2]
    exact ord_poly_eq 4 7 0 (by decide) (by decide)

/-! ### The cases -/

theorem caseA0 : IsLogJacobianCaseA P0 := by
  show idealOrd (logJacobianTangent ({1, 2} : Finset (Fin 3)) g0) =
    ((degree (divisorExponent ({1, 2} : Finset (Fin 3)) g0) : ℕ) : ℕ∞) +
      logJacobianOrder ({1, 2} : Finset (Fin 3)) g0
  rw [tangent0, divisorExponent_g0, degree_expo, rho0]
  norm_num

theorem caseB1 : IsLogJacobianCaseB P1 := by
  show idealOrd (logJacobianTangent ({1} : Finset (Fin 3)) g1) =
    ((degree (divisorExponent ({1} : Finset (Fin 3)) g1) : ℕ) : ℕ∞) +
      logJacobianOrder ({1} : Finset (Fin 3)) g1 + 1
  rw [tangent1, divisorExponent_g1, degree_expo, rho1]
  norm_num

theorem caseA2 : IsLogJacobianCaseA P2 := by
  show idealOrd (logJacobianTangent ({1} : Finset (Fin 3)) g2) =
    ((degree (divisorExponent ({1} : Finset (Fin 3)) g2) : ℕ) : ℕ∞) +
      logJacobianOrder ({1} : Finset (Fin 3)) g2
  rw [tangent2, divisorExponent_g2, degree_expo, rho2]
  norm_num

/-! ### The steps -/

theorem step01 : RhoStep 2 4 P0 P1 := by
  refine ⟨1, t0, h0, poly_ne_zero (a := 2) (b := 3) (c := 1) (by decide),
    isClean_poly _ (by decide), le_ord_poly _ 2 (by decide), pointChart_g0, ?_, rho0, rho1⟩
  show ((({1} : Finset (Fin 3)), g1) : Finset (Fin 3) × Poly) =
    (blowupDivisor ({1, 2} : Finset (Fin 3)) 1 t0, cleanPart 2 h0)
  rw [blowupDivisor_P0, cleanPart_h0]

theorem step12 : RhoStep 2 4 P1 P2 := by
  refine ⟨1, 0, g2, poly_ne_zero (a := 2) (b := 4) (c := 3) (by decide),
    isClean_poly _ (by decide), le_ord_poly _ 2 (by decide), pointChart_g1, ?_, rho1, rho2⟩
  show ((({1} : Finset (Fin 3)), g2) : Finset (Fin 3) × Poly) =
    (blowupDivisor ({1} : Finset (Fin 3)) 1 0, cleanPart 2 g2)
  rw [blowupDivisor_P1, cleanPart_g2]

/-! ### The directrices -/

theorem caseAForm_g0 :
    caseAForm ({1, 2} : Finset (Fin 3)) g0 4 1 = poly [(2, 2, 0), (2, 0, 2)] := by
  unfold caseAForm
  rw [divisorExponent_g0, residualFactor_g0, G0, homogeneousComponent_poly,
    show (List.filter (fun e : ℕ × ℕ × ℕ => decide (e.1 + e.2.1 + e.2.2 = 4))
      [(2, 2, 0), (2, 0, 2), (4, 0, 1)]) = [(2, 2, 0), (2, 0, 2)] from by decide]
  simp only [expo_apply_one, poly_cons, poly_nil, add_zero, map_add, pderiv_one_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char2

theorem caseAForm_g2 : caseAForm ({1} : Finset (Fin 3)) g2 4 1 = mono 4 0 0 := by
  unfold caseAForm
  rw [divisorExponent_g2, residualFactor_g2, G2, homogeneousComponent_poly,
    show (List.filter (fun e : ℕ × ℕ × ℕ => decide (e.1 + e.2.1 + e.2.2 = 4))
      [(2, 0, 3), (4, 0, 0), (4, 2, 2)]) = [(4, 0, 0)] from by decide]
  simp only [expo_apply_one, poly_cons, poly_nil, add_zero, pderiv_one_mono,
    smul_eq_C_mul, map_natCast]
  simp only [mono]
  char2

/-- The point `(x, y, z, s)` of `𝔽₂⁴`, as a valuation of the variables of `translate`. -/
def pt (x y z s : ZMod 2) : Option (Fin 3) → ZMod 2 := fun o => Option.elim o s ![x, y, z]

theorem directrix_F0_le :
    directrix (poly [(2, 2, 0), (2, 0, 2)]) ≤ Submodule.span (ZMod 2) {![0, 1, 1]} := by
  intro v hv
  have h := mem_directrix_iff.mp hv
  simp only [poly_cons, poly_nil, mono, add_zero, map_add, map_mul, map_pow, translate, aeval_X,
    rename_X, pow_zero, mul_one] at h
  have e1 := congrArg (eval (pt 0 0 0 1)) h
  have e2 := congrArg (eval (pt 1 0 0 1)) h
  have e3 := congrArg (eval (pt 0 1 0 1)) h
  simp only [map_add, map_mul, map_pow, eval_X, eval_C, pt, Option.elim] at e1 e2 e3
  simp at e1 e2 e3
  have key : v 0 = 0 ∧ v 1 = v 2 := by
    revert e1 e2 e3
    generalize v 0 = a
    generalize v 1 = b
    generalize v 2 = c
    revert a b c
    decide
  rw [Submodule.mem_span_singleton]
  refine ⟨v 1, ?_⟩
  ext i
  fin_cases i <;> simp [key.1, key.2]

theorem finrank_T0 :
    Module.finrank (ZMod 2) (logJacobianDirectrix ({1, 2} : Finset (Fin 3)) g0) ≤ 1 := by
  rw [logJacobianDirectrix_eq_iInf_caseAForm rho0 caseA0]
  have h1 : (⨅ i ∈ ({1, 2} : Finset (Fin 3)), directrix (caseAForm {1, 2} g0 4 i)) ≤
      directrix (caseAForm {1, 2} g0 4 1) := iInf₂_le 1 (by simp)
  rw [caseAForm_g0] at h1
  refine (Submodule.finrank_mono (h1.trans directrix_F0_le)).trans ?_
  exact (finrank_span_le_card _).trans (by simp)

theorem ker_le_T2 : LinearMap.ker (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ≤
    logJacobianDirectrix ({1} : Finset (Fin 3)) g2 := by
  rw [logJacobianDirectrix_eq_iInf_caseAForm rho2 caseA2]
  refine le_iInf₂ fun i hi => ?_
  simp only [Finset.mem_singleton] at hi
  subst hi
  rw [caseAForm_g2]
  intro v hv
  rw [LinearMap.mem_ker, LinearMap.proj_apply] at hv
  rw [mem_directrix_iff]
  simp [mono, translate, hv]

theorem finrank_ker : Module.finrank (ZMod 2)
    (LinearMap.ker (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
  have hr : LinearMap.range (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) = ⊤ :=
    LinearMap.range_eq_top.mpr fun c => ⟨fun _ => c, rfl⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

theorem codim_P0 : 2 ≤ logJacobianDirectrixCodim P0.1 P0.2 := by
  show 2 ≤ Fintype.card (Fin 3) -
      Module.finrank (ZMod 2) (logJacobianDirectrix ({1, 2} : Finset (Fin 3)) g0)
  have := finrank_T0
  rw [Fintype.card_fin]
  omega

theorem codim_P2 : logJacobianDirectrixCodim P2.1 P2.2 ≤ 1 := by
  show Fintype.card (Fin 3) -
      Module.finrank (ZMod 2) (logJacobianDirectrix ({1} : Finset (Fin 3)) g2) ≤ 1
  have := Submodule.finrank_mono ker_le_T2
  rw [finrank_ker] at this
  rw [Fintype.card_fin]
  omega

/-- **The kangaroo path conjecture is false** for `p = 2`, three variables and the field
`ZMod 2`. The path `P₀ → P₁ → P₂` keeps `ρ = 4`, the points `P₀` and `P₂` are of case A, the point
`P₁` is of case B, and `τ_ρ(P₀) = 2 > 1 ≥ τ_ρ(P₂)`. -/
theorem not_kangarooPathConjecture :
    ¬ KangarooPathConjecture (σ := Fin 3) (k := ZMod 2) 2 := by
  intro h
  have := h 4 P0 P1 P2 caseA0 (Relation.TransGen.single ⟨step01, caseB1⟩) step12 caseA2
  have h0 := codim_P0
  have h2 := codim_P2
  omega

end KangarooCounterexample

end Singularity
