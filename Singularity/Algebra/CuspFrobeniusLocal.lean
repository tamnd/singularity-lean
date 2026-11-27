import Singularity.Algebra.CuspFrobenius
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The Frobenius of the local ring of the cusp is not flat

This file gives the local form of Volume 1, Example 6.4.9 of the handbook. Let `k` be a field of characteristic `p`, let `A = k[t^2, t^3]` be the cusp in `k[t]`, and let `R` be the localization of `A` at the maximal ideal `(t^2, t^3)`. Then the Frobenius of `R` is not flat.

The maximal ideal `(t^2, t^3)` is the kernel of the evaluation at `0` (`cuspMaxIdeal`). The proof uses the map `cuspLocToPowerSeries` from `R` to `k[[t]]`. This map exists because an element of `A` with a nonzero constant term is a unit in `k[[t]]`.

The proof is the proof of the global form. Over the Frobenius, the relation `t^2 · t^(p+2) - t^3 · t^2 = 0` holds in `R`. Let `t^2 a + t^3 b = 0` in `R`. Then `t^3` divides the image of `a` in `k[[t]]` (`cuspLoc_X_cube_dvd`). If the relation is trivial, then `t^(3p)` divides `t^(p+2)` in `k[[t]]`. This is false, because `p + 2 < 3p`.

The result does not need `k` to be perfect.
-/

namespace Singularity.Algebra

open Polynomial Singularity.Example

variable {k : Type*} [Field k]

/-- The evaluation at `0` on the cusp `k[t^2, t^3]`. -/
noncomputable def cuspEvalZero : cusp k →+* k :=
  (Polynomial.evalRingHom 0).comp (algebraMap (cusp k) k[X])

/-- The maximal ideal `(t^2, t^3)` of the cusp, as the kernel of the evaluation at `0`. -/
noncomputable def cuspMaxIdeal : Ideal (cusp k) := RingHom.ker (cuspEvalZero (k := k))

instance cuspMaxIdeal_isPrime : (cuspMaxIdeal (k := k)).IsPrime :=
  RingHom.ker_isPrime _

/-- The local ring of the cusp at the maximal ideal `(t^2, t^3)`. -/
def CuspLoc (k : Type*) [Field k] : Type _ := Localization.AtPrime (cuspMaxIdeal (k := k))

noncomputable instance : CommRing (CuspLoc k) :=
  inferInstanceAs (CommRing (Localization.AtPrime (cuspMaxIdeal (k := k))))

noncomputable instance : Algebra (cusp k) (CuspLoc k) :=
  inferInstanceAs (Algebra (cusp k) (Localization.AtPrime (cuspMaxIdeal (k := k))))

instance : IsLocalization.AtPrime (CuspLoc k) (cuspMaxIdeal (k := k)) :=
  inferInstanceAs (IsLocalization.AtPrime (Localization.AtPrime (cuspMaxIdeal (k := k))) _)

instance : IsLocalRing (CuspLoc k) :=
  inferInstanceAs (IsLocalRing (Localization.AtPrime (cuspMaxIdeal (k := k))))

/-- The map from the cusp to `k[[t]]`. -/
noncomputable def cuspToPowerSeries : cusp k →+* PowerSeries k :=
  (Polynomial.coeToPowerSeries.ringHom).comp (algebraMap (cusp k) k[X])

theorem cuspToPowerSeries_apply (a : cusp k) : cuspToPowerSeries a = ((a : k[X]) : PowerSeries k) :=
  rfl

theorem isUnit_cuspToPowerSeries (s : (cuspMaxIdeal (k := k)).primeCompl) :
    IsUnit (cuspToPowerSeries (s : cusp k)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, cuspToPowerSeries_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, isUnit_iff_ne_zero]
  have hs := s.2
  simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
    SetLike.mem_coe, cuspMaxIdeal, RingHom.mem_ker, cuspEvalZero, RingHom.comp_apply,
    Polynomial.coe_evalRingHom] at hs
  rwa [Polynomial.coeff_zero_eq_eval_zero]

/-- The map from the local ring of the cusp to `k[[t]]`. -/
noncomputable def cuspLocToPowerSeries : CuspLoc k →+* PowerSeries k :=
  IsLocalization.lift (M := (cuspMaxIdeal (k := k)).primeCompl) isUnit_cuspToPowerSeries

theorem cuspLocToPowerSeries_algebraMap (a : cusp k) :
    cuspLocToPowerSeries (algebraMap (cusp k) (CuspLoc k) a) = ((a : k[X]) : PowerSeries k) :=
  IsLocalization.lift_eq _ _

/-- Let `a` and `b` be in the local ring of the cusp, with `t^2 a + t^3 b = 0`. Then `t^3` divides the image of `a` in `k[[t]]`. -/
theorem cuspLoc_X_cube_dvd {a b : CuspLoc k}
    (h : algebraMap (cusp k) (CuspLoc k) ⟨X ^ 2, X_sq_mem_cusp⟩ * a +
      algebraMap (cusp k) (CuspLoc k) ⟨X ^ 3, X_cube_mem_cusp⟩ * b = 0) :
    (PowerSeries.X : PowerSeries k) ^ 3 ∣ cuspLocToPowerSeries a := by
  obtain ⟨⟨a', s₁⟩, rfl⟩ := IsLocalization.mk'_surjective (cuspMaxIdeal (k := k)).primeCompl a
  obtain ⟨⟨b', s₂⟩, rfl⟩ := IsLocalization.mk'_surjective (cuspMaxIdeal (k := k)).primeCompl b
  dsimp only at h
  have ha : cuspLocToPowerSeries (IsLocalization.mk' (CuspLoc k) a' s₁) * cuspToPowerSeries s₁ =
      cuspToPowerSeries a' := by
    rw [cuspToPowerSeries_apply, cuspToPowerSeries_apply,
      ← cuspLocToPowerSeries_algebraMap (s₁ : cusp k), ← cuspLocToPowerSeries_algebraMap a',
      ← map_mul, IsLocalization.mk'_spec]
  have hb : cuspLocToPowerSeries (IsLocalization.mk' (CuspLoc k) b' s₂) * cuspToPowerSeries s₂ =
      cuspToPowerSeries b' := by
    rw [cuspToPowerSeries_apply, cuspToPowerSeries_apply,
      ← cuspLocToPowerSeries_algebraMap (s₂ : cusp k), ← cuspLocToPowerSeries_algebraMap b',
      ← map_mul, IsLocalization.mk'_spec]
  set α := cuspLocToPowerSeries (IsLocalization.mk' (CuspLoc k) a' s₁)
  set β := cuspLocToPowerSeries (IsLocalization.mk' (CuspLoc k) b' s₂)
  have h' := congrArg cuspLocToPowerSeries h
  rw [map_add, map_mul, map_mul, cuspLocToPowerSeries_algebraMap,
    cuspLocToPowerSeries_algebraMap, map_zero] at h'
  have hpoly : ((X ^ 2 * ((a' : k[X]) * ((s₂ : cusp k) : k[X])) + X ^ 3 * ((b' : k[X]) * ((s₁ : cusp k) : k[X])) :
      k[X]) : PowerSeries k) = 0 := by
    have e : ((X ^ 2 * ((a' : k[X]) * ((s₂ : cusp k) : k[X])) + X ^ 3 * ((b' : k[X]) * ((s₁ : cusp k) : k[X])) :
        k[X]) : PowerSeries k) = (cuspToPowerSeries s₁ * cuspToPowerSeries s₂) *
          (((X ^ 2 : k[X]) : PowerSeries k) * α + ((X ^ 3 : k[X]) : PowerSeries k) * β) := by
      rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_mul,
        Polynomial.coe_mul, ← cuspToPowerSeries_apply a', ← cuspToPowerSeries_apply b',
        ← cuspToPowerSeries_apply (s₁ : cusp k), ← cuspToPowerSeries_apply (s₂ : cusp k), ← ha,
        ← hb]
      ring
    rw [e, show ((X ^ 2 : k[X]) : PowerSeries k) * α + ((X ^ 3 : k[X]) : PowerSeries k) * β = 0
      from h', mul_zero]
  rw [Polynomial.coe_eq_zero_iff] at hpoly
  have hdvd := cuspFrob_X_cube_dvd (Subalgebra.mul_mem _ a'.2 s₂.1.2)
    (Subalgebra.mul_mem _ b'.2 s₁.1.2) hpoly
  have hdvd' : (PowerSeries.X : PowerSeries k) ^ 3 ∣ α * (cuspToPowerSeries s₁ * cuspToPowerSeries s₂) := by
    have := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := k)) hdvd
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow, Polynomial.coe_X,
      Polynomial.coe_mul] at this
    convert this using 1
    rw [← mul_assoc, ha]; rfl
  exact ((isUnit_cuspToPowerSeries s₁).mul (isUnit_cuspToPowerSeries s₂)).dvd_mul_right.mp hdvd'

/-- Let `φ` be a ring endomorphism of the local ring `R` of the cusp at `(t^2, t^3)` with `φ r = r ^ p` for all `r`, and let `2 ≤ p`. Then `φ` is not flat. The relation `t^2 · t^(p+2) - t^3 · t^2 = 0` over `φ` is not trivial. -/
theorem cuspLocFrob_not_flat_of_pow {p : ℕ} (hp : 2 ≤ p) (φ : CuspLoc k →+* CuspLoc k)
    (hφ : ∀ r, φ r = r ^ p) : ¬ φ.Flat := by
  intro hflat
  let ι := algebraMap (cusp k) (CuspLoc k)
  let u0 : cusp k := ⟨X ^ 2, X_sq_mem_cusp⟩
  let v0 : cusp k := ⟨X ^ 3, X_cube_mem_cusp⟩
  let w0 : cusp k := ⟨X ^ 2 * X ^ p, X_sq_mul_mem_cusp _⟩
  let f : Fin 2 → CuspLoc k := ![ι u0, ι v0]
  let x : Fin 2 → CuspLoc k := ![ι w0, -ι u0]
  have h0 : u0 ^ p * w0 - v0 ^ p * u0 = 0 := by
    apply Subtype.ext
    simp only [u0, v0, w0, Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_pow,
      Subalgebra.coe_zero]
    ring
  have hsum : ∑ i, φ (f i) * x i = 0 := by
    simp only [Fin.sum_univ_two, f, x, Matrix.cons_val_zero, Matrix.cons_val_one, hφ]
    rw [← map_pow, ← map_pow, mul_neg, ← map_mul, ← map_mul, ← sub_eq_add_neg, ← map_sub, h0,
      map_zero]
  obtain ⟨n, a, y, hx, hrel⟩ :=
    @Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (CuspLoc k) (CuspLoc k) _ _ φ.toModule
      hflat (Fin 2) _ f x hsum
  have hdvd : ∀ j, (PowerSeries.X : PowerSeries k) ^ (3 * p) ∣ cuspLocToPowerSeries (φ (a 0 j)) := by
    intro j
    have hj := hrel j
    simp only [Fin.sum_univ_two, f, Matrix.cons_val_zero, Matrix.cons_val_one] at hj
    rw [hφ, map_pow, pow_mul]
    exact pow_dvd_pow_of_dvd (cuspLoc_X_cube_dvd hj) p
  have hw : ι w0 = ∑ j, φ (a 0 j) * y j := hx 0
  have hw' : ((X ^ 2 * X ^ p : k[X]) : PowerSeries k) =
      ∑ j, cuspLocToPowerSeries (φ (a 0 j)) * cuspLocToPowerSeries (y j) := by
    have := congrArg cuspLocToPowerSeries hw
    rw [cuspLocToPowerSeries_algebraMap, map_sum] at this
    simpa only [map_mul] using this
  have hd : (PowerSeries.X : PowerSeries k) ^ (3 * p) ∣ PowerSeries.X ^ (2 + p) := by
    have e : (PowerSeries.X : PowerSeries k) ^ (2 + p) = ((X ^ 2 * X ^ p : k[X]) : PowerSeries k) := by
      simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, pow_add]
    rw [e, hw']
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (hdvd j) _
  rw [PowerSeries.X_pow_dvd_iff] at hd
  have := hd (2 + p) (by omega)
  rw [PowerSeries.coeff_X_pow_self] at this
  exact one_ne_zero this

/-- Example 6.4.9, local form. Let `k` be a field of characteristic `p`, and let `R` be the local ring of the cusp `k[t^2, t^3]` at the maximal ideal `(t^2, t^3)`. Then the Frobenius of `R` is not flat. -/
theorem cuspLocFrob_not_flat (p : ℕ) [Fact p.Prime] [CharP k p] :
    letI : CharP (CuspLoc k) p := charP_of_injective_ringHom
      ((algebraMap (cusp k) (CuspLoc k)).comp (algebraMap k (cusp k))).injective p
    ¬ (frobenius (CuspLoc k) p).Flat := by
  let _ : CharP (CuspLoc k) p := charP_of_injective_ringHom
      ((algebraMap (cusp k) (CuspLoc k)).comp (algebraMap k (cusp k))).injective p
  exact cuspLocFrob_not_flat_of_pow (Fact.out : p.Prime).two_le _ fun r => by
    rw [frobenius_def]

end Singularity.Algebra
