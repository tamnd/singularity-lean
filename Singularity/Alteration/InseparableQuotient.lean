/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The quotient of a Galois alteration

This file proves the algebraic steps of parts 1, 2 and 3 of Volume 8, Proposition 3.1.4 of the handbook. Let `A` be a normal domain with field of fractions `K`.

* Let `L'/K` be an extension. Each `K`-automorphism of `L'` maps an element that is integral over `A` to an element that is integral over `A` (`isIntegral_algEquiv_apply`). So the group acts on the integral closure `B` of `A` in `L'`.
* For a subgroup `H` of the `K`-automorphisms of `L'`, an element of `L'` is in `B` and fixed by `H` if and only if it is in the fixed field `L'^H` and integral over `A` (`mem_integralClosure_and_fixed_iff`). So `B^H` is the integral closure of `A` in `L'^H`.
* Let `M/K` be purely inseparable, of exponential characteristic `q`. If `b ∈ M` is integral over `A`, then `b^(q^n) ∈ A` for some `n` (`exists_algebraMap_eq_pow_of_isPurelyInseparable`).
* Let `R → S` be a ring map such that each element of `S` has a power with a positive exponent in the image of `R`. Then two primes of `S` with the same inverse image in `R` are equal (`eq_of_comap_eq_of_forall_exists_pow`).
* So, for the integral closure `A_M` of `A` in `M`, the map `Spec A_M → Spec A` is injective (`eq_of_comap_eq_integralClosure`).

The surjectivity of `Spec A_M → Spec A`, the claim on the residue fields, the claim that the map is a universal homeomorphism, and the gluing to schemes are not proved.
-/

open IntermediateField

namespace Singularity

/-- Volume 8, Proposition 3.1.4, part 1 of the handbook: a `K`-automorphism of `L'` maps an element that is integral over `A` to an element that is integral over `A`. -/
theorem isIntegral_algEquiv_apply {A K L : Type*} [CommRing A] [Field K] [Field L] [Algebra A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] (σ : L ≃ₐ[K] L) {x : L}
    (hx : IsIntegral A x) : IsIntegral A (σ x) :=
  hx.map (σ.restrictScalars A)

/-- Volume 8, Proposition 3.1.4, part 2 of the handbook: the elements of the integral closure of `A` in `L'` that are fixed by `H` are the elements of the fixed field `L'^H` that are integral over `A`. -/
theorem mem_integralClosure_and_fixed_iff {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A L] [Algebra K L] (H : Subgroup Gal(L/K)) (x : L) :
    (x ∈ integralClosure A L ∧ ∀ σ ∈ H, σ x = x) ↔
      (x ∈ fixedField H ∧ IsIntegral A x) := by
  rw [mem_fixedField_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Volume 8, Proposition 3.1.4, part 3 of the handbook: let `M/K` be purely inseparable of exponential characteristic `q`, and let `b ∈ M` be integral over the normal domain `A`. Then `b^(q^n) ∈ A` for some `n`. -/
theorem exists_algebraMap_eq_pow_of_isPurelyInseparable {A K M : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field K] [Field M] [Algebra A K] [IsFractionRing A K] [Algebra K M]
    [Algebra A M] [IsScalarTower A K M] [IsPurelyInseparable K M] (q : ℕ) [ExpChar K q] {b : M}
    (hb : IsIntegral A b) : ∃ n : ℕ, ∃ a : A, algebraMap A M a = b ^ q ^ n := by
  obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem (F := K) (q := q) b
  have hc' : IsIntegral A (IsScalarTower.toAlgHom A K M c) := by
    rw [IsScalarTower.toAlgHom_apply, hc]
    exact hb.pow _
  have hci : IsIntegral A c :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K M)
      (fun x y hxy => (algebraMap K M).injective hxy)).mp hc'
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hci
  exact ⟨n, a, by rw [IsScalarTower.algebraMap_apply A K M, ha, hc]⟩

/-- Let `R → S` be a ring map such that each element of `S` has a power with a positive exponent in the image of `R`. Then two primes of `S` with the same inverse image in `R` are equal. -/
theorem eq_of_comap_eq_of_forall_exists_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ s : S, ∃ n : ℕ, 0 < n ∧ ∃ r : R, algebraMap R S r = s ^ n) {P Q : Ideal S}
    (hP : P.IsPrime) (hQ : Q.IsPrime) (hPQ : P.comap (algebraMap R S) = Q.comap (algebraMap R S)) :
    P = Q := by
  have key : ∀ P Q : Ideal S, Q.IsPrime →
      P.comap (algebraMap R S) = Q.comap (algebraMap R S) → P ≤ Q := by
    intro P Q hQ hPQ s hs
    obtain ⟨n, hn, r, hr⟩ := h s
    have h1 : algebraMap R S r ∈ P := hr ▸ P.pow_mem_of_mem hs n hn
    have h2 : r ∈ Q.comap (algebraMap R S) := hPQ ▸ (Ideal.mem_comap.mpr h1)
    have h3 : s ^ n ∈ Q := hr ▸ Ideal.mem_comap.mp h2
    exact hQ.mem_of_pow_mem n h3
  exact le_antisymm (key P Q hQ hPQ) (key Q P hP hPQ.symm)

/-- Volume 8, Proposition 3.1.4, part 3 of the handbook: let `M/K` be purely inseparable, and let `A_M` be the integral closure of the normal domain `A` in `M`. Then two primes of `A_M` over the same prime of `A` are equal, so `Spec A_M → Spec A` is injective. -/
theorem eq_of_comap_eq_integralClosure {A K M : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field K] [Field M] [Algebra A K] [IsFractionRing A K] [Algebra K M]
    [Algebra A M] [IsScalarTower A K M] [IsPurelyInseparable K M] (q : ℕ) [hq : ExpChar K q]
    {P Q : Ideal (integralClosure A M)} (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hPQ : P.comap (algebraMap A (integralClosure A M)) =
      Q.comap (algebraMap A (integralClosure A M))) :
    P = Q := by
  have hq0 : 0 < q := by
    rcases hq with _ | ⟨hp⟩
    · exact Nat.one_pos
    · exact hp.pos
  refine eq_of_comap_eq_of_forall_exists_pow (fun s => ?_) hP hQ hPQ
  obtain ⟨n, a, ha⟩ := exists_algebraMap_eq_pow_of_isPurelyInseparable (K := K) q
    (show IsIntegral A (s : M) from s.2)
  refine ⟨q ^ n, pow_pos hq0 n, a, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow]
  exact ha

end Singularity
