import Singularity.Algebra.NormalizationCharP
import Singularity.Algebra.Regular

/-!
# The normal locus of a domain with a finite normalization

Let `A` be a domain with field of fractions `K`, and assume that the integral closure `Ã` of `A` in `K` is a finite `A`-module. This file proves that the normal locus of `Spec A` is open. More precisely, let `p` be a prime ideal of `A` such that `A_p` is integrally closed. Then there is an element `s ∉ p` such that `s Ã ⊆ A`, and for each such `s` the localization `A_s` is integrally closed.

This is the algebra that Section 2.5 of Volume 1 of the handbook uses for the resolution of curves. The proof is [Mat, Section 23] in a simple case: the conductor of `A` in `Ã` is not contained in `p`.

## Main results

* `finite_integralClosure_of_isFractionRing`: the theorem of E. Noether for each model of the field of fractions.
* `exists_smul_mem_of_isIntegrallyClosed_localization`: the element `s`.
* `isIntegrallyClosed_of_isLocalization_away`: the localization `A_s` is integrally closed.
-/

universe u v

namespace Singularity.Algebra

open Polynomial

/-- The theorem of E. Noether for a field of fractions `B` of `A` that is not `FractionRing A`. -/
theorem finite_integralClosure_of_isFractionRing (k A : Type u) (B : Type v) [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [CommRing B] [Algebra A B]
    [IsFractionRing A B] : Module.Finite A (integralClosure A B) := by
  have := finite_integralClosure k A
  let e : FractionRing A ≃ₐ[A] B := IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) B
  exact Module.Finite.equiv e.mapIntegralClosure.toLinearEquiv

variable {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]

omit [IsDomain A] [IsFractionRing A K] in
/-- Let `A` be a domain with field of fractions `K` and a finite normalization. Let `p` be a prime ideal of `A`, and assume that a localization `S` of `A` at `p` is integrally closed. Then there is an element `s ∉ p` such that `s b ∈ A` for each element `b` of `K` that is integral over `A`. -/
theorem exists_smul_mem_of_isIntegrallyClosed_localization
    [Module.Finite A (integralClosure A K)] (p : Ideal A) [p.IsPrime]
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S p] [Algebra S K]
    [IsScalarTower A S K] [IsFractionRing S K] [IsIntegrallyClosed S] :
    ∃ s ∉ p, ∀ b : K, IsIntegral A b → ∃ a : A, algebraMap A K a = s • b := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := A) (M := integralClosure A K)
  have key : ∀ g : integralClosure A K, ∃ u ∈ p.primeCompl, ∃ a : A,
      algebraMap A K a = u • (g : K) := by
    intro g
    have hg : IsIntegral S (g : K) := (g.2 : IsIntegral A (g : K)).tower_top
    obtain ⟨t, ht⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := K)).mp hg
    obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl t
    refine ⟨u, u.2, a, ?_⟩
    simp only [Algebra.smul_def, ← ht, IsScalarTower.algebraMap_apply A S K, ← map_mul,
      IsLocalization.mk'_spec']
  choose u hu a ha using key
  have H : ∀ x ∈ Submodule.span A (G : Set (integralClosure A K)),
      ∃ c : A, algebraMap A K c = (∏ g ∈ G, u g) • (x : K) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      refine ⟨(∏ h ∈ G.erase g, u h) * a g, ?_⟩
      rw [map_mul, ha, ← Finset.prod_erase_mul G _ hg]
      simp only [Algebra.smul_def, map_mul, mul_assoc]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨cx, hx⟩ := hx
      obtain ⟨cy, hy⟩ := hy
      exact ⟨cx + cy, by rw [map_add, hx, hy, Subalgebra.coe_add, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨cx, hx⟩ := hx
      refine ⟨r * cx, ?_⟩
      show _ = _ • (r • (x : K))
      rw [map_mul, hx, smul_comm, Algebra.smul_def r]
  refine ⟨∏ g ∈ G, u g, ?_, fun b hb => H ⟨b, hb⟩ (by rw [hG]; trivial)⟩
  show _ ∈ p.primeCompl
  exact Submonoid.prod_mem _ fun g _ => hu g

omit [IsDomain A] in
/-- Let `A` be a domain with field of fractions `K`, and let `s ∈ A` be an element with `s b ∈ A` for each element `b` of `K` that is integral over `A`. Then the localization `A_s` is integrally closed. -/
theorem isIntegrallyClosed_of_isLocalization_away (s : A)
    (hs : ∀ b : K, IsIntegral A b → ∃ a : A, algebraMap A K a = s • b)
    (R : Type*) [CommRing R] [IsDomain R] [Algebra A R] [IsLocalization.Away s R] [Algebra R K]
    [IsScalarTower A R K] [IsFractionRing R K] : IsIntegrallyClosed R := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : Subsingleton R := IsLocalization.subsingleton (M := Submonoid.powers (0 : A))
      (Submonoid.mem_powers 0)
    exact not_subsingleton R this
  have hsK : algebraMap A K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hs0
  refine (isIntegrallyClosed_iff K).mpr fun {x} hx => ?_
  obtain ⟨⟨m, n, rfl⟩, hm⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers s) (Rₘ := R) x hx
  obtain ⟨a, ha⟩ := hs _ hm
  let t : Submonoid.powers s := ⟨s ^ (n + 1), n + 1, rfl⟩
  refine ⟨IsLocalization.mk' R a t, ?_⟩
  have hsn : algebraMap A K (s ^ (n + 1)) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hsK
  have hspec : IsLocalization.mk' R a t * algebraMap A R (s ^ (n + 1)) = algebraMap A R a :=
    IsLocalization.mk'_spec R a t
  apply mul_right_cancel₀ hsn
  rw [IsScalarTower.algebraMap_apply A R K (s ^ (n + 1)), ← map_mul, hspec,
    ← IsScalarTower.algebraMap_apply, ha]
  simp only [Submonoid.smul_def, Algebra.smul_def, map_pow, ← IsScalarTower.algebraMap_apply]
  ring

end Singularity.Algebra
