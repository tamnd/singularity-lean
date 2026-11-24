/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Residual

/-!
# A kangaroo point in characteristic 2

This file certifies the first example of Hauser and Perlega [HP19a, §3]. The field `K` has
characteristic 2, the variables `x, y, w` are `X 0, X 1, X 2`, and

  `f = z^4 + x^2 y^2 w^3 (w (x + y)^4 + x^13)`.

The exceptional divisor is `x y w = 0`. The residual order of `f` is `d = 5`. Blow up the origin
and look at the `x`-chart with the translation `y ↦ y + 1`. The weak transform is

  `f' = z^4 + x^8 w^3 (w y^4 + w y^6 + x^8 + x^8 y^2)`.

The monomial `x^8 y^4 w^4` is a fourth power, and cleaning it gives
`z_1^4 + x^8 w^3 (w y^6 + x^8 + x^8 y^2)`. The new exceptional divisor is `x w = 0`, so the residual
order of `f'` is `d' = 7`. The residual order goes up under a permissible blowup: the origin is a
point of order `4 = p^e` of `f`, and the new point is again a point of order 4. The point is a
kangaroo point.

The increase `7 - 5 = 2 = p^(e-1)` is the largest one allowed by Moh's bound (`moh_bound`, proved as `moh_bound_holds`), so the
bound is sharp here. The paper uses the example to show that the bound
`d' ≤ [d / p^r] p^r + p^r = 6` in Moh's proof of his stability theorem is false.

What the file certifies, in `kangaroo`: the purely inseparable equation is clean, it has order 4,
its residual order along `x y w = 0` is 5, the chart sends it to `x^4` times the stated weak
transform, the weak transform has order at least 4, the new divisor is `x w = 0`, and the residual
order of the weak transform along it is 7. All of it is checked by computation in the polynomial
ring over an arbitrary field of characteristic 2.

What the file does not certify: the value `p^r = 2` that enters the false bound 6. The file
`Singularity/Example/HauserPerlegaCycle.lean` certifies one cycle of [HP19a, §4] for one choice of
the parameters. The claim that the residual order goes to infinity along the iterated cycles is not
certified.

## References

* [HP19a] H. Hauser and S. Perlega, *Cycles of singularities appearing in the resolution problem
  in positive characteristic*, J. Algebraic Geom. 28 (2019), arXiv:1802.05010, §3.
-/

open MvPolynomial Finsupp

namespace Singularity.Examples

/-! ### Exponent vectors in three variables -/

/-- The exponent vector `(a, b, c)` of the monomial `x^a y^b w^c`. -/
noncomputable def expVec3 (a b c : ℕ) : Fin 3 →₀ ℕ := single 0 a + single 1 b + single 2 c

@[simp]
theorem expVec3_apply_zero (a b c : ℕ) : expVec3 a b c 0 = a := by simp [expVec3]

@[simp]
theorem expVec3_apply_one (a b c : ℕ) : expVec3 a b c 1 = b := by simp [expVec3]

@[simp]
theorem expVec3_apply_two (a b c : ℕ) : expVec3 a b c 2 = c := by simp [expVec3]

theorem expVec3_add (a b c a' b' c' : ℕ) :
    expVec3 a b c + expVec3 a' b' c' = expVec3 (a + a') (b + b') (c + c') := by
  simp only [expVec3, single_add]
  abel

theorem degree_expVec3 (a b c : ℕ) : Finsupp.degree (expVec3 a b c) = a + b + c := by
  simp [expVec3, map_add, Finsupp.degree_single]

theorem expVec3_ne {u v : Fin 3 →₀ ℕ} (i : Fin 3) (h : u i ≠ v i) : u ≠ v :=
  fun e => h (by rw [e])

variable {K : Type*} [Field K]

theorem monomial_expVec3 (a b c : ℕ) :
    monomial (expVec3 a b c) (1 : K) = X 0 ^ a * X 1 ^ b * X 2 ^ c := by
  rw [expVec3, monomial_add_single, monomial_add_single, ← X_pow_eq_monomial]

/-! ### Sums of three monomials -/

section Three

variable {u v w : Fin 3 →₀ ℕ}

theorem isClean_three {q : ℕ} (hu : ¬ ∀ i, q ∣ u i) (hv : ¬ ∀ i, q ∣ v i)
    (hw : ¬ ∀ i, q ∣ w i) : IsClean q (monomial u (1 : K) + monomial v 1 + monomial w 1) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · rcases Finset.mem_union.mp (MvPolynomial.support_add h) with h | h
    · rwa [Finset.mem_singleton.mp (support_monomial_subset h)]
    · rwa [Finset.mem_singleton.mp (support_monomial_subset h)]
  · rwa [Finset.mem_singleton.mp (support_monomial_subset h)]

theorem mem_support_three {d : Fin 3 →₀ ℕ} (hd : d = u ∨ d = v ∨ d = w) (huv : u ≠ v)
    (huw : u ≠ w) (hvw : v ≠ w) :
    d ∈ (monomial u (1 : K) + monomial v 1 + monomial w 1).support := by
  rw [MvPolynomial.mem_support_iff]
  rcases hd with rfl | rfl | rfl <;>
    simp [coeff_monomial, huv, huw, hvw, huv.symm, huw.symm, hvw.symm]

/-- The order of a sum of three distinct monomials whose first one has the least degree. -/
theorem ord_three {n : ℕ} (hu : Finsupp.degree u = n) (hv : n ≤ Finsupp.degree v)
    (hw : n ≤ Finsupp.degree w) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ord (monomial u (1 : K) + monomial v 1 + monomial w 1) = n := by
  refine le_antisymm ?_ ?_
  · have h := ord_le ((MvPolynomial.mem_support_iff).mp
      (mem_support_three (K := K) (Or.inl rfl) huv huw hvw))
    rwa [hu] at h
  · refine le_ord_add (le_ord_add ?_ ?_) ?_
    · rw [ord_monomial one_ne_zero, hu]
    · rw [ord_monomial one_ne_zero]
      exact_mod_cast hv
    · rw [ord_monomial one_ne_zero]
      exact_mod_cast hw

end Three

/-! ### The example -/

/-- The right side `F = x^2 y^2 w^3 (w (x + y)^4 + x^13)` of `f = z^4 + F` [HP19a, §3]. -/
noncomputable def kangarooF : MvPolynomial (Fin 3) K :=
  X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 * (X 2 * (X 0 + X 1) ^ 4 + X 0 ^ 13)

/-- The translation `y ↦ y + 1` of the `x`-chart. -/
def kangarooT : Fin 3 → K := ![0, 1, 0]

/-- The right side `F' = x^8 w^3 (w y^4 + w y^6 + x^8 + x^8 y^2)` of the weak transform
`f' = z^4 + F'` [HP19a, §3]. -/
noncomputable def kangarooF' : MvPolynomial (Fin 3) K :=
  X 0 ^ 8 * X 2 ^ 3 * (X 2 * X 1 ^ 4 + X 2 * X 1 ^ 6 + X 0 ^ 8 + X 0 ^ 8 * X 1 ^ 2)

/-- The coordinate change `z_1 = z + x^2 y w` that cleans `f'`. -/
noncomputable def kangarooH : MvPolynomial (Fin 3) K := X 0 ^ 2 * X 1 * X 2

variable [CharP K 2]

theorem two_eq_zero_mvPolynomial : (2 : MvPolynomial (Fin 3) K) = 0 := by
  rw [show (2 : MvPolynomial (Fin 3) K) = C 2 from (map_ofNat C 2).symm, CharTwo.two_eq_zero,
    map_zero]

theorem kangarooF_eq : (kangarooF : MvPolynomial (Fin 3) K) =
    monomial (expVec3 2 2 3) 1 *
      (monomial (expVec3 4 0 1) 1 + monomial (expVec3 0 4 1) 1 + monomial (expVec3 13 0 0) 1) := by
  rw [kangarooF]
  simp only [monomial_expVec3]
  linear_combination (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 4 *
    (2 * X 0 ^ 3 * X 1 + 3 * X 0 ^ 2 * X 1 ^ 2 + 2 * X 0 * X 1 ^ 3)) *
    two_eq_zero_mvPolynomial (K := K)

theorem kangarooF_eq_sum : (kangarooF : MvPolynomial (Fin 3) K) =
    monomial (expVec3 6 2 4) 1 + monomial (expVec3 2 6 4) 1 + monomial (expVec3 15 2 3) 1 := by
  rw [kangarooF_eq]
  simp only [mul_add, monomial_mul_monomial, mul_one, expVec3_add, Nat.reduceAdd]

theorem isClean_kangarooF : IsClean 4 (kangarooF : MvPolynomial (Fin 3) K) := by
  rw [kangarooF_eq_sum]
  refine isClean_three ?_ ?_ ?_ <;> intro h
  · have := h 1
    simp only [expVec3_apply_one] at this
    omega
  · have := h 0
    simp only [expVec3_apply_zero] at this
    omega
  · have := h 0
    simp only [expVec3_apply_zero] at this
    omega

theorem ord_kangarooF : ord (kangarooF : MvPolynomial (Fin 3) K) = 12 := by
  rw [kangarooF_eq_sum, ord_three (n := 12) (by simp [degree_expVec3]) (by simp [degree_expVec3])
    (by simp [degree_expVec3]) (expVec3_ne 0 (by simp)) (expVec3_ne 0 (by simp))
    (expVec3_ne 0 (by simp))]
  rfl

theorem residualOrderAlong_kangarooF :
    residualOrderAlong Finset.univ 4 (kangarooF : MvPolynomial (Fin 3) K) = 5 := by
  have hclean := isClean_kangarooF (K := K)
  rw [kangarooF_eq] at hclean ⊢
  have h1 : expVec3 4 0 1 ≠ expVec3 0 4 1 := expVec3_ne 0 (by simp)
  have h2 : expVec3 4 0 1 ≠ expVec3 13 0 0 := expVec3_ne 0 (by simp)
  have h3 : expVec3 0 4 1 ≠ expVec3 13 0 0 := expVec3_ne 0 (by simp)
  have hG : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∃ d ∈ (monomial (expVec3 4 0 1) (1 : K) +
      monomial (expVec3 0 4 1) 1 + monomial (expVec3 13 0 0) 1).support, d i = 0 := by
    intro i _
    fin_cases i
    · exact ⟨_, mem_support_three (Or.inr (Or.inl rfl)) h1 h2 h3, by simp⟩
    · exact ⟨_, mem_support_three (Or.inl rfl) h1 h2 h3, by simp⟩
    · exact ⟨_, mem_support_three (Or.inr (Or.inr rfl)) h1 h2 h3, by simp⟩
  rw [residualOrderAlong_eq hclean (fun i hi => absurd (Finset.mem_univ i) hi) hG,
    ord_three (n := 5) (by simp [degree_expVec3]) (by simp [degree_expVec3])
      (by simp [degree_expVec3]) h1 h2 h3]
  rfl

theorem pointChart_kangarooF :
    pointChart 0 kangarooT (kangarooF : MvPolynomial (Fin 3) K) = X 0 ^ 4 * kangarooF' := by
  have h1 : pointChart 0 kangarooT (X 1 : MvPolynomial (Fin 3) K) = X 0 * (X 1 + 1) := by
    rw [pointChart_X_of_ne _ (by decide)]
    simp [kangarooT]
  have h2 : pointChart 0 kangarooT (X 2 : MvPolynomial (Fin 3) K) = X 0 * X 2 := by
    rw [pointChart_X_of_ne _ (by decide)]
    simp [kangarooT]
  simp only [kangarooF, kangarooF', map_mul, map_pow, map_add, pointChart_X_self, h1, h2]
  linear_combination (8 * X 0 ^ 12 * X 2 ^ 4 + 32 * X 0 ^ 12 * X 1 * X 2 ^ 4 +
    52 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 4 + 44 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 4 +
    20 * X 0 ^ 12 * X 1 ^ 4 * X 2 ^ 4 + 5 * X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 4 +
    X 0 ^ 20 * X 1 * X 2 ^ 3) * two_eq_zero_mvPolynomial (K := K)

omit [CharP K 2] in
theorem ord_kangarooF' : 4 ≤ ord (kangarooF' : MvPolynomial (Fin 3) K) := by
  rw [kangarooF']
  refine le_trans ?_ (le_ord_mul _ _)
  rw [ord_mul, ord_X_pow, ord_X_pow]
  refine le_trans ?_ le_self_add
  exact_mod_cast (show 4 ≤ 8 + 3 by omega)

theorem kangarooF'_add_eq : (kangarooF' : MvPolynomial (Fin 3) K) + kangarooH ^ 4 =
    monomial (expVec3 8 0 3) 1 *
      (monomial (expVec3 0 6 1) 1 + monomial (expVec3 8 0 0) 1 + monomial (expVec3 8 2 0) 1) := by
  rw [kangarooF', kangarooH]
  simp only [monomial_expVec3]
  linear_combination (X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 4) * two_eq_zero_mvPolynomial (K := K)

omit [CharP K 2] in
theorem blowupDivisor_kangaroo [DecidableEq K] :
    blowupDivisor Finset.univ 0 (kangarooT : Fin 3 → K) = {0, 2} := by
  ext i
  rw [blowupDivisor, Finset.mem_insert, Finset.mem_filter]
  fin_cases i <;> simp [kangarooT]

theorem residualOrderAlong_kangarooF' :
    residualOrderAlong {0, 2} 4 (kangarooF' : MvPolynomial (Fin 3) K) = 7 := by
  have hadd := residualOrderAlong_add_pow 2 ({0, 2} : Finset (Fin 3)) 2
    (kangarooF' : MvPolynomial (Fin 3) K) kangarooH
  change residualOrderAlong {0, 2} 4 (kangarooF' + kangarooH ^ 4) =
    residualOrderAlong {0, 2} 4 kangarooF' at hadd
  rw [← hadd, kangarooF'_add_eq]
  have h1 : expVec3 0 6 1 ≠ expVec3 8 0 0 := expVec3_ne 0 (by simp)
  have h2 : expVec3 0 6 1 ≠ expVec3 8 2 0 := expVec3_ne 0 (by simp)
  have h3 : expVec3 8 0 0 ≠ expVec3 8 2 0 := expVec3_ne 1 (by simp)
  have hclean : IsClean 4 (monomial (expVec3 8 0 3) (1 : K) *
      (monomial (expVec3 0 6 1) 1 + monomial (expVec3 8 0 0) 1 + monomial (expVec3 8 2 0) 1)) := by
    simp only [mul_add, monomial_mul_monomial, mul_one, expVec3_add, Nat.reduceAdd]
    refine isClean_three ?_ ?_ ?_ <;> intro h
    · have := h 1
      simp only [expVec3_apply_one] at this
      omega
    · have := h 2
      simp only [expVec3_apply_two] at this
      omega
    · have := h 1
      simp only [expVec3_apply_one] at this
      omega
  have hr : ∀ i, i ∉ ({0, 2} : Finset (Fin 3)) → expVec3 8 0 3 i = 0 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp [expVec3, Ne.symm hi.1, Ne.symm hi.2]
  have hG : ∀ i ∈ ({0, 2} : Finset (Fin 3)), ∃ d ∈ (monomial (expVec3 0 6 1) (1 : K) +
      monomial (expVec3 8 0 0) 1 + monomial (expVec3 8 2 0) 1).support, d i = 0 := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨_, mem_support_three (Or.inl rfl) h1 h2 h3, by simp⟩
    · rw [Finset.mem_singleton.mp hi]
      exact ⟨_, mem_support_three (Or.inr (Or.inl rfl)) h1 h2 h3, by simp⟩
  rw [residualOrderAlong_eq hclean hr hG, ord_three (n := 7) (by simp [degree_expVec3])
    (by simp [degree_expVec3]) (by simp [degree_expVec3]) h1 h2 h3]
  rfl

/-- **The kangaroo point of Hauser and Perlega** [HP19a, §3]. Over a field of characteristic 2,
let `f = z^4 + F` with `F = x^2 y^2 w^3 (w (x + y)^4 + x^13)` and exceptional divisor `x y w = 0`.
Then `F` is clean and has order at least 4, so `f` has order 4 at the origin, and the residual
order of `f` is 5. In the `x`-chart of the blowup of the origin, with the translation `y ↦ y + 1`,
the transform of `f` is `x^4` times `f' = z^4 + F'`, the order of `f'` is again 4, the new divisor is
`x w = 0`, and the residual order of `f'` is 7. So the residual order goes up under a permissible
blowup. -/
theorem kangaroo [DecidableEq K] :
    IsClean 4 (kangarooF : MvPolynomial (Fin 3) K) ∧
    4 ≤ ord (kangarooF : MvPolynomial (Fin 3) K) ∧
    residualOrderAlong Finset.univ 4 (kangarooF : MvPolynomial (Fin 3) K) = 5 ∧
    pointChart 0 kangarooT (kangarooF : MvPolynomial (Fin 3) K) = X 0 ^ 4 * kangarooF' ∧
    pointChartZ 0 kangarooT (purelyInseparable 4 (kangarooF : MvPolynomial (Fin 3) K)) =
      X (Option.some 0) ^ 4 * purelyInseparable 4 kangarooF' ∧
    4 ≤ ord (kangarooF' : MvPolynomial (Fin 3) K) ∧
    blowupDivisor Finset.univ 0 (kangarooT : Fin 3 → K) = {0, 2} ∧
    residualOrderAlong (blowupDivisor Finset.univ 0 (kangarooT : Fin 3 → K)) 4
      (kangarooF' : MvPolynomial (Fin 3) K) = 7 := by
  refine ⟨isClean_kangarooF, ?_, residualOrderAlong_kangarooF, pointChart_kangarooF,
    pointChartZ_purelyInseparable pointChart_kangarooF, ord_kangarooF', blowupDivisor_kangaroo,
    ?_⟩
  · rw [ord_kangarooF]
    exact_mod_cast (show 4 ≤ 12 by omega)
  · rw [blowupDivisor_kangaroo, residualOrderAlong_kangarooF']

/-- In the kangaroo example the residual order goes up by exactly `p^(e-1) = 2`, so the bound of
Moh (`moh_bound`) holds with equality, while the bound `[d / p^r] p^r + p^r = 6` from Moh's proof
of the stability theorem, with `d = 5` and `p^r = 2` [HP19a, §3], fails. -/
theorem kangaroo_increase [DecidableEq K] :
    residualOrderAlong (blowupDivisor Finset.univ 0 (kangarooT : Fin 3 → K)) 4
        (kangarooF' : MvPolynomial (Fin 3) K) =
      residualOrderAlong Finset.univ 4 (kangarooF : MvPolynomial (Fin 3) K) + 2 ∧
    (((5 / 2) * 2 + 2 : ℕ) : ℕ∞) <
      residualOrderAlong (blowupDivisor Finset.univ 0 (kangarooT : Fin 3 → K)) 4
        (kangarooF' : MvPolynomial (Fin 3) K) := by
  rw [blowupDivisor_kangaroo, residualOrderAlong_kangarooF', residualOrderAlong_kangarooF]
  constructor
  · rfl
  · exact_mod_cast (show (5 / 2) * 2 + 2 < 7 by omega)

end Singularity.Examples
