/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.CharacteristicPolyhedron
import Singularity.Invariant.Residual
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.Algebra.CharP.Algebra

/-!
# The characteristic polyhedron of a purely inseparable equation

Let `k` be a commutative ring of exponential characteristic `p`, let `q = p ^ e`, and let `F` be a
power series in `x = (x_i)_{i ∈ σ}`. This file computes the characteristic polyhedron of Hironaka
for the polynomial `f = z^q + F(x)` in `z`, when `F` is clean: no monomial of `F` is a `q`-th
power, that is, no exponent of `F` lies in `q ℕ^σ`.

The reason is short. A change of coordinate `z ↦ z + φ(x)` with `φ(0) = 0` sends `f` to
`z^q + (φ^q + F)`, because the binomial coefficients of `(z + φ)^q` in the middle vanish in
exponential characteristic `p`. Every exponent of `φ^q` lies in `q ℕ^σ`, so the change does not
touch the monomials of a clean `F`. The projected polyhedron can only grow, and the coordinate
`z` already attains the characteristic polyhedron.

## Main results

* `coeff_pow_expChar_pow_eq_zero`: the exponents of `φ^(p^e)` lie in `p^e ℕ^σ`.
* `taylor_X_pow_add_C`: `(z + φ)^q + F = z^q + (φ^q + F)`.
* `projPoints_X_pow_add_C`: the points of `z^n + G` are the exponents of `G` divided by `n`.
* `charPolyhedron_X_pow_add_C_of_clean`: for clean `F`, `Δ(f; x) = Δ(f; x; z)`. This is the
  converse direction of the vertex criterion in this special case.
* `projPolyhedron_X_pow_add_C_coe`: for a polynomial `F`, `Δ(z^n + F; x; z) = (1/n) N(F)`.
* `charPolyhedron_X_pow_add_C_eq_smul_newtonPolyhedron`: for a clean polynomial `F`, the
  characteristic polyhedron of `z^q + F` is `(1/q) N(F)`.
* `not_isSolvableVertex_of_clean`: no vertex `v ≠ 0` of `Δ(z^q + F; x; z)` is solvable.

## References

* [Hir67] H. Hironaka, *Characteristic polyhedra of singularities*, J. Math. Kyoto Univ. 7
  (1967), 251-293.
-/

open Polynomial Pointwise

namespace Singularity

variable {σ k : Type*}

section Orthant

/-- A positive multiple of the orthant is the orthant. -/
theorem smul_orthant {c : ℝ} (hc : 0 < c) : c • orthant σ = orthant σ := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    simpa only [Pi.smul_apply, smul_eq_mul] using mul_nonneg hc.le (hw i)
  · intro hv
    refine ⟨c⁻¹ • v, fun i => ?_, smul_inv_smul₀ hc.ne' v⟩
    simpa only [Pi.smul_apply, smul_eq_mul] using mul_nonneg (inv_nonneg.2 hc.le) (hv i)

end Orthant

section Semiring

variable [CommSemiring k]

/-- The points of `z^n + G` with `n ≥ 1` are the exponents of `G` divided by `n`. Only the
coefficient of `z^0` is nonzero below the top degree. -/
theorem projPoints_X_pow_add_C [Nontrivial k] {n : ℕ} (hn : 1 ≤ n) (G : MvPowerSeries σ k) :
    projPoints (X ^ n + C G) =
      {u | ∃ α, MvPowerSeries.coeff α G ≠ 0 ∧ u = (n : ℝ)⁻¹ • expToReal α} := by
  ext u
  simp only [projPoints, natDegree_X_pow_add_C, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi1, hin, α, hα, rfl⟩
    have hi : i = n := by
      by_contra hne
      apply hα
      have h1 : n - i ≠ n := by omega
      have h2 : n - i ≠ 0 := by omega
      simp [coeff_X_pow, coeff_C, h1, h2]
    subst hi
    refine ⟨α, ?_, rfl⟩
    have h1 : (0 : ℕ) ≠ i := by omega
    simpa [coeff_X_pow, h1] using hα
  · rintro ⟨α, hα, rfl⟩
    refine ⟨n, hn, le_rfl, α, ?_, rfl⟩
    have h1 : (0 : ℕ) ≠ n := by omega
    simpa [coeff_X_pow, h1] using hα

/-- For a polynomial `F` and `n ≥ 1`, the projected polyhedron of `z^n + F` is `(1/n) N(F)`,
where `N(F)` is the Newton polyhedron of `F`. -/
theorem projPolyhedron_X_pow_add_C_coe [Nontrivial k] {n : ℕ} (hn : 1 ≤ n)
    (F : MvPolynomial σ k) :
    projPolyhedron (X ^ n + C (F : MvPowerSeries σ k)) = (n : ℝ)⁻¹ • newtonPolyhedron F := by
  have hpos : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hn)
  have hpts : projPoints (X ^ n + C (F : MvPowerSeries σ k)) =
      (n : ℝ)⁻¹ • (expToReal '' (F.support : Set (σ →₀ ℕ))) := by
    rw [projPoints_X_pow_add_C hn]
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_smul_set, Set.mem_image, Finset.mem_coe,
      MvPolynomial.mem_support_iff, MvPolynomial.coeff_coe]
    constructor
    · rintro ⟨α, hα, rfl⟩
      exact ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
      exact ⟨α, hα, rfl⟩
  rw [projPolyhedron, hpts, newtonPolyhedron, smul_add, convexHull_smul, smul_orthant hpos]

end Semiring

section ExpChar

variable [CommRing k] (p : ℕ) [ExpChar k p]

/-- In exponential characteristic `p`, every exponent of the power series `φ^(p^e)` lies in
`p^e ℕ^σ`: the coefficient of `x^d` vanishes when some `d_i` is not divisible by `p^e`. -/
theorem coeff_pow_expChar_pow_eq_zero (e : ℕ) (φ : MvPowerSeries σ k) {d : σ →₀ ℕ}
    (hd : ¬ ∀ i, p ^ e ∣ d i) : MvPowerSeries.coeff d (φ ^ p ^ e) = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hd
  have hp : p ≠ 0 := expChar_ne_zero k p
  rw [← MvPowerSeries.map_iterateFrobenius_expand p hp φ e, MvPowerSeries.coeff_map,
    MvPowerSeries.coeff_expand_of_not_dvd (p ^ e) (pow_ne_zero e hp) φ hi, map_zero]

/-- In exponential characteristic `p`, the change of coordinate `z ↦ z + φ` sends `z^q + F` to
`z^q + (φ^q + F)`, where `q = p^e`. -/
theorem taylor_X_pow_add_C (e : ℕ) (φ F : MvPowerSeries σ k) :
    taylor φ (X ^ p ^ e + C F) = X ^ p ^ e + C (φ ^ p ^ e + F) := by
  have : ExpChar (MvPowerSeries σ k)[X] p :=
    expChar_of_injective_ringHom
      (f := (Polynomial.C).comp (MvPowerSeries.C : k →+* MvPowerSeries σ k))
      (Polynomial.C_injective.comp MvPowerSeries.C_injective) p
  rw [taylor_apply, add_comp, X_pow_comp, C_comp, add_pow_expChar_pow, C_add, C_pow, add_assoc]

variable [Nontrivial k]

/-- Let `q = p^e` and let `F` be clean: no exponent of `F` lies in `q ℕ^σ`. Then no change of
coordinate `z ↦ z + φ` makes the projected polyhedron of `z^q + F` smaller. -/
theorem projPolyhedron_subset_taylor_of_clean (e : ℕ) {F : MvPowerSeries σ k}
    (hF : ∀ α, MvPowerSeries.coeff α F ≠ 0 → ¬ ∀ i, p ^ e ∣ α i) (φ : MvPowerSeries σ k) :
    projPolyhedron (X ^ p ^ e + C F) ⊆ projPolyhedron (taylor φ (X ^ p ^ e + C F)) := by
  have hq : 1 ≤ p ^ e := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (expChar_ne_zero k p))
  rw [taylor_X_pow_add_C, projPolyhedron, projPolyhedron, projPoints_X_pow_add_C hq,
    projPoints_X_pow_add_C hq]
  refine Set.add_subset_add (convexHull_mono ?_) subset_rfl
  rintro _ ⟨α, hα, rfl⟩
  refine ⟨α, ?_, rfl⟩
  rwa [map_add, coeff_pow_expChar_pow_eq_zero p e φ (hF α hα), zero_add]

/-- The converse direction of the vertex criterion of Hironaka [Hir67] for the equation
`f = z^q + F` with `q = p^e`, over a nontrivial commutative ring of exponential characteristic
`p`. If `F` is clean, that is no exponent of `F` lies in `q ℕ^σ`, then the coordinate `z`
attains the characteristic polyhedron: `Δ(f; x) = Δ(f; x; z)`. -/
theorem charPolyhedron_X_pow_add_C_of_clean (e : ℕ) {F : MvPowerSeries σ k}
    (hF : ∀ α, MvPowerSeries.coeff α F ≠ 0 → ¬ ∀ i, p ^ e ∣ α i) :
    charPolyhedron (X ^ p ^ e + C F) = projPolyhedron (X ^ p ^ e + C F) :=
  subset_antisymm (charPolyhedron_subset_projPolyhedron _)
    (Set.subset_iInter₂ fun φ _ => projPolyhedron_subset_taylor_of_clean p e hF φ)

/-- The characteristic polyhedron of `z^q + F` with `q = p^e`, over a nontrivial commutative ring
of exponential characteristic `p`, for a clean polynomial `F` (`IsClean q F`: no monomial of `F`
is a `q`-th power). It is `(1/q) N(F)`, where `N(F)` is the Newton polyhedron of `F`. -/
theorem charPolyhedron_X_pow_add_C_eq_smul_newtonPolyhedron (e : ℕ) {F : MvPolynomial σ k}
    (hF : IsClean (p ^ e) F) :
    charPolyhedron (X ^ p ^ e + C (F : MvPowerSeries σ k)) =
      ((p ^ e : ℕ) : ℝ)⁻¹ • newtonPolyhedron F := by
  have hq : 1 ≤ p ^ e := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (expChar_ne_zero k p))
  rw [charPolyhedron_X_pow_add_C_of_clean p e (F := (F : MvPowerSeries σ k)) fun α hα =>
    hF α (by rwa [MvPolynomial.mem_support_iff, ← MvPolynomial.coeff_coe]),
    projPolyhedron_X_pow_add_C_coe hq]

/-- For `f = z^q + F` with `q = p^e` and `F` clean, no vertex `v ≠ 0` of `Δ(f; x; z)` is solvable.
The ring is nontrivial, commutative and of exponential characteristic `p`. -/
theorem not_isSolvableVertex_of_clean (e : ℕ) {F : MvPowerSeries σ k}
    (hF : ∀ α, MvPowerSeries.coeff α F ≠ 0 → ¬ ∀ i, p ^ e ∣ α i) {v : σ →₀ ℕ} (hv0 : v ≠ 0)
    (hv : expToReal v ∈ (projPolyhedron (X ^ p ^ e + C F)).extremePoints ℝ) (c : k) :
    ¬ IsSolvableVertex (X ^ p ^ e + C F) v c :=
  not_isSolvableVertex_of_charPolyhedron_eq (charPolyhedron_X_pow_add_C_of_clean p e hF) hv0 hv c

end ExpChar

end Singularity
