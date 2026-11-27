import Singularity.Example.CurveNormalization
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.RingHom.Flat

/-!
# The Frobenius of the cusp is not flat

This file gives the global form of Example 6.4.9. Let `k` be a field of characteristic `p`,
and let `A = k[t^2, t^3]` be the cusp in `k[t]`. Then the Frobenius of `A` is not flat.

The proof uses the equational criterion for flatness. Over the Frobenius, the relation
`t^2 · t^(p+2) - t^3 · t^2 = 0` holds in `A`. If this relation is trivial, then `t^(3p)`
divides `t^(p+2)`. This is false, because `p + 2 < 3p`.

The result does not need `k` to be perfect. This file does not prove the local form for the
localization of `A` at the maximal ideal `(t^2, t^3)`.
-/

namespace Singularity.Algebra

open Polynomial Singularity.Example

variable {k : Type*} [Field k]

/-- Let `a` and `b` be in the cusp `k[t^2, t^3]`, with `t^2 a + t^3 b = 0`. Then `t^3` divides `a`. -/
theorem cuspFrob_X_cube_dvd {a b : k[X]} (ha : a ∈ cusp k) (hb : b ∈ cusp k)
    (h : X ^ 2 * a + X ^ 3 * b = 0) : X ^ 3 ∣ a := by
  have h2 : (X ^ 2 : k[X]) * (a + X * b) = 0 := by rw [← h]; ring
  have hab : a = -(X * b) :=
    eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 X_ne_zero))
  have ha1 : a.coeff 1 = 0 := mem_cusp_iff.mp ha
  have hb1 : b.coeff 1 = 0 := mem_cusp_iff.mp hb
  rw [X_pow_dvd_iff]
  intro d hd
  interval_cases d
  · rw [hab, coeff_neg, coeff_X_mul_zero, neg_zero]
  · exact ha1
  · rw [hab, coeff_neg, coeff_X_mul, hb1, neg_zero]

/-- Let `φ` be a ring endomorphism of the cusp `A = k[t^2, t^3]` with `φ a = a ^ p` for all `a`,
and let `2 ≤ p`. Then `φ` is not flat. The relation `t^2 · t^(p+2) - t^3 · t^2 = 0` over `φ`
is not trivial. -/
theorem cuspFrob_not_flat_of_pow {p : ℕ} (hp : 2 ≤ p) (φ : cusp k →+* cusp k)
    (hφ : ∀ a, (φ a : k[X]) = (a : k[X]) ^ p) : ¬ φ.Flat := by
  intro hflat
  let u : cusp k := ⟨X ^ 2, X_sq_mem_cusp⟩
  let v : cusp k := ⟨X ^ 3, X_cube_mem_cusp⟩
  let w : cusp k := ⟨X ^ 2 * X ^ p, X_sq_mul_mem_cusp _⟩
  let f : Fin 2 → cusp k := ![u, v]
  let x : Fin 2 → cusp k := ![w, -u]
  have hsum : ∑ i, φ (f i) * x i = 0 := by
    apply Subtype.ext
    simp only [Fin.sum_univ_two, f, x, Matrix.cons_val_zero, Matrix.cons_val_one,
      Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_zero, hφ, u, v, w]
    ring
  obtain ⟨n, a, y, hx, hrel⟩ :=
    @Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (cusp k) (cusp k) _ _ φ.toModule hflat
      (Fin 2) _ f x hsum
  have hdvd : ∀ j, (X ^ (3 * p) : k[X]) ∣ ((φ (a 0 j) : cusp k) : k[X]) := by
    intro j
    have hj := congrArg (fun z : cusp k => (z : k[X])) (hrel j)
    simp only [Fin.sum_univ_two, f, Matrix.cons_val_zero, Matrix.cons_val_one,
      Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_zero, u, v] at hj
    rw [hφ, pow_mul]
    exact pow_dvd_pow_of_dvd (cuspFrob_X_cube_dvd (a 0 j).2 (a 1 j).2 hj) p
  have h0 : w = ∑ j, φ (a 0 j) * y j := hx 0
  have h0' : (X ^ 2 * X ^ p : k[X]) = ∑ j, ((φ (a 0 j) : cusp k) : k[X]) * (y j : k[X]) := by
    have := congrArg (fun z : cusp k => (z : k[X])) h0
    simpa only [w, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul] using this
  have hd : (X ^ (3 * p) : k[X]) ∣ X ^ 2 * X ^ p := by
    rw [h0']
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (hdvd j) _
  rw [← pow_add, X_pow_dvd_iff] at hd
  have := hd (2 + p) (by omega)
  rw [coeff_X_pow_self] at this
  exact one_ne_zero this

/-- Example 6.4.9, global form. Let `k` be a field of characteristic `p`. Then the Frobenius of
the cusp `k[t^2, t^3]` is not flat. -/
theorem cuspFrob_not_flat (p : ℕ) [Fact p.Prime] [CharP k p] :
    letI : CharP (cusp k) p := charP_of_injective_algebraMap (algebraMap k (cusp k)).injective p
    ¬ (frobenius (cusp k) p).Flat := by
  let _ : CharP (cusp k) p := charP_of_injective_algebraMap (algebraMap k (cusp k)).injective p
  exact cuspFrob_not_flat_of_pow (Fact.out : p.Prime).two_le _ fun a => by
    rw [frobenius_def]; rfl

end Singularity.Algebra
