import Singularity.Invariant.PlanarRuns

/-!
# Condition (C) for corner runs in four variables

Theorems 3.18.34 and 3.18.35 of Volume 7 of the handbook use condition (C) on a polynomial
`g ∈ K[[y, z]][x, w]`: for each `e ≥ 1` the Hasse derivatives `g^{[p^e, 0]}` and `g^{[0, p^e]}`
in the variables `(x, w)` do not depend on `x` and `w`. This file proves the algebraic part of
these theorems, the two sufficient conditions for (C) that the handbook gives.

The variables are indexed by a finite type `σ` and the coefficient ring is a commutative ring
`R`, which plays the role of `K[[y, z]]`. The Hasse derivatives are `hasse` from
`Singularity.Invariant.PlanarRuns`.

## Main results

* `CondC p g`: condition (C) for `g`.
* `condC_iff`: (C) says that each `hasse (single i (p ^ e)) g` with `e ≥ 1` is a constant.
* `condC_of_totalDegree_le`: if `deg g ≤ p`, then `g` satisfies (C).
* `condC_of_eq_sum`: if `R` has characteristic `p` and
  `g = ∑ e ∈ s, ∑ i, α_{e, i} x_i ^ (p ^ e) + h` with `deg h < p`, then `g` satisfies (C).

## Not proved

The statements on runs, that is, that a run under (C) is not planar (Theorem 3.18.34) and that
it is linear (Theorem 3.18.35), are not proved. They need the corner runs of Definition 3.17.5
and Proposition 3.17.3.
-/

namespace Singularity.PlanarRuns

open MvPolynomial Finsupp

variable {σ R : Type*} [Fintype σ] [DecidableEq σ]

section CommSemiring

variable [CommSemiring R]

/-- Condition (C) of Theorem 3.18.34 of the handbook: for each `e ≥ 1` and each variable `i`,
the Hasse derivative of order `p ^ e` in `i` has no term of positive degree. -/
def CondC (p : ℕ) (g : MvPolynomial σ R) : Prop :=
  ∀ e, 1 ≤ e → ∀ i, ∀ m : σ →₀ ℕ, m ≠ 0 → (hasse (single i (p ^ e)) g).coeff m = 0

theorem condC_iff (p : ℕ) (g : MvPolynomial σ R) :
    CondC p g ↔ ∀ e, 1 ≤ e → ∀ i,
      hasse (single i (p ^ e)) g = C ((hasse (single i (p ^ e)) g).coeff 0) := by
  refine forall_congr' fun e => forall_congr' fun _ => forall_congr' fun i => ?_
  constructor
  · intro h
    ext m
    rw [coeff_C]
    split_ifs with hm
    · subst hm
      rfl
    · exact h m (Ne.symm hm)
  · intro h m hm
    rw [h, coeff_C, ite_eq_right_iff.mpr fun h' => absurd h'.symm hm]

theorem coeff_hasse_eq_zero_of_totalDegree_lt {k m : σ →₀ ℕ} {f : MvPolynomial σ R}
    (h : f.totalDegree < degree m + degree k) : (hasse k f).coeff m = 0 := by
  rw [coeff_hasse, coeff_eq_zero_of_totalDegree_lt, smul_zero]
  rwa [← degree_apply, map_add]

/-- The first sufficient condition of Theorem 3.18.34: if `deg g ≤ p`, then `g` satisfies (C). -/
theorem condC_of_totalDegree_le {p : ℕ} {g : MvPolynomial σ R}
    (hg : g.totalDegree ≤ p) : CondC p g := by
  intro e he i m hm
  apply coeff_hasse_eq_zero_of_totalDegree_lt
  have h1 : degree m ≠ 0 := fun h => hm ((degree_eq_zero_iff m).mp h)
  have h2 : p ≤ p ^ e := Nat.le_self_pow (by omega) p
  rw [degree_single]
  omega

end CommSemiring

section CommRing

variable [CommRing R]

/-- The second sufficient condition of Theorem 3.18.34: in characteristic `p`, a sum of
multiples of `x_i ^ (p ^ e)` plus a polynomial of degree less than `p` satisfies (C). -/
theorem condC_of_eq_sum {p : ℕ} [CharP R p] (hp : p.Prime) (s : Finset ℕ) (α : ℕ → σ → R)
    {h : MvPolynomial σ R} (hh : h.totalDegree < p) :
    CondC p (∑ e ∈ s, ∑ i, C (α e i) * X i ^ (p ^ e) + h) := by
  intro e₀ he₀ i₀ m hm
  have hpe : p ≤ p ^ e₀ := Nat.le_self_pow (by omega) p
  have hpos : p ^ e₀ ≠ 0 := (pow_pos hp.pos _).ne'
  set k : σ →₀ ℕ := single i₀ (p ^ e₀) with hk
  rw [coeff_hasse, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_eq_zero_of_totalDegree_lt (f := h), add_zero, coeff_sum,
    Finset.smul_sum]
  · refine Finset.sum_eq_zero fun e _ => ?_
    rw [coeff_sum, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [X_pow_eq_monomial, C_mul_monomial, mul_one, coeff_monomial]
    split_ifs with heq
    · rw [nsmul_eq_mul]
      convert zero_mul (α e i)
      rw [CharP.cast_eq_zero_iff R p]
      have hki₀ : k i₀ = p ^ e₀ := by simp [hk]
      have hii : i = i₀ := by
        by_contra hne
        have h0 := congrArg (fun d => d i₀) heq
        simp only [single_apply, hne, ↓reduceIte, Finsupp.add_apply, hki₀] at h0
        omega
      subst hii
      have hsum : m i + p ^ e₀ = p ^ e := by
        have h0 := congrArg (fun d => d i) heq
        simp only [single_eq_same, Finsupp.add_apply, hki₀] at h0
        omega
      have hmi : m i ≠ 0 := by
        intro hmi0
        apply hm
        ext l
        by_cases hl : l = i
        · subst hl
          simpa using hmi0
        · have h0 := congrArg (fun d => d l) heq
          have hkl : k l = 0 := by simp [hk, Ne.symm hl]
          simp only [single_apply, Ne.symm hl, ↓reduceIte, Finsupp.add_apply, hkl] at h0
          simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
      refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      rw [hki₀, hsum]
      exact hp.dvd_choose_pow hpos (by omega)
    · exact smul_zero _
  · rw [← degree_apply, map_add, degree_single]
    omega

end CommRing

end Singularity.PlanarRuns
