/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.Frobenius
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat local homomorphisms and descent of flatness

This file proves two results of Volume 1, Section 6.4 of the handbook.

* `Singularity.Algebra.faithfullyFlat_and_injective_of_flat_of_isLocalHom`: a flat local homomorphism `A → B` of local rings is faithfully flat and injective (Volume 1, Proposition 6.4.1 of the handbook). Both facts are in Mathlib.
* `Singularity.Algebra.isReduced_of_flat_frobenius`: a ring of characteristic `p` with a flat Frobenius is reduced (the last claim of Volume 1, Proposition 6.4.1 of the handbook).
* `Singularity.Algebra.flat_of_faithfullyFlat_of_flat`: let `A → B → C` be ring homomorphisms. If `C` is faithfully flat over `B` and flat over `A`, then `B` is flat over `A` (Volume 1, Lemma 6.4.6 of the handbook).

The handbook proves the claim on the Frobenius with the localizations of `R`, and it assumes that `R` is Noetherian. The proof here uses the equational criterion of flatness, and it does not need this hypothesis. Let `F(x) = 0`. The relation `x · 1 = 0` in the `R`-module `F_* R` is trivial, so `1 = ∑ F(a_j) y_j` with `x a_j = 0`. Thus `x = ∑ x a_j^p y_j = 0`, so `F` is injective, and `R` is reduced by Proposition 6.1.3.
-/

open TensorProduct

namespace Singularity.Algebra

/-- A flat local homomorphism of local rings is faithfully flat and injective (Volume 1, Proposition 6.4.1 of the handbook). -/
theorem faithfullyFlat_and_injective_of_flat_of_isLocalHom (A B : Type*) [CommRing A]
    [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B] [Module.Flat A B]
    [IsLocalHom (algebraMap A B)] :
    Module.FaithfullyFlat A B ∧ Function.Injective (algebraMap A B) := by
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨this, FaithfulSMul.algebraMap_injective A B⟩

/-- Let `f : R → S` be a flat ring homomorphism and let `x ∈ R` with `f(x) = 0`. Then `1 = ∑ f(a_j) y_j` for some `a_j ∈ R` with `x a_j = 0` and some `y_j ∈ S`. This is the equational criterion of flatness for one relation. -/
theorem exists_sum_eq_one_of_flat {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.Flat) {x : R} (hx : f x = 0) :
    ∃ (k : ℕ) (a : Fin k → R) (y : Fin k → S), (1 : S) = ∑ j, f (a j) * y j ∧
      ∀ j, x * a j = 0 := by
  letI := f.toAlgebra
  haveI : Module.Flat R S := hf
  have h : ∑ i : Unit, (fun _ : Unit => x) i • (fun _ : Unit => (1 : S)) i = 0 := by
    rw [Fintype.sum_unique, Algebra.smul_def, mul_one]
    exact hx
  obtain ⟨k, a, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h
  refine ⟨k, fun j => a () j, y, ?_, fun j => ?_⟩
  · have e := h1 ()
    simp only [Algebra.smul_def] at e
    exact e
  · simpa using h2 j

/-- Let `R` be a ring of prime characteristic `p`. If the Frobenius of `R` is flat, then it is injective. -/
theorem injective_frobenius_of_flat (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hF : (frobenius R p).Flat) : Function.Injective (frobenius R p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨k, a, y, h1, h2⟩ := exists_sum_eq_one_of_flat (frobenius R p) hF hx
  have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel (Fact.out : p.Prime).one_le).symm
  calc x = x * 1 := (mul_one x).symm
    _ = ∑ j, x * (frobenius R p (a j) * y j) := by rw [h1, Finset.mul_sum]
    _ = 0 := Finset.sum_eq_zero fun j _ => by
        rw [frobenius_def, hp1, pow_succ]
        linear_combination (a j ^ (p - 1) * y j) * h2 j

/-- Let `R` be a ring of prime characteristic `p`. If the Frobenius of `R` is flat, then `R` is reduced (the last claim of Volume 1, Proposition 6.4.1 of the handbook). The handbook assumes that `R` is Noetherian. This hypothesis is not necessary. -/
theorem isReduced_of_flat_frobenius (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hF : (frobenius R p).Flat) : IsReduced R :=
  (injective_frobenius_iff_isReduced R p).mp (injective_frobenius_of_flat R p hF)

/-- Descent of flatness (Volume 1, Lemma 6.4.6 of the handbook). Let `A → B → C` be ring homomorphisms. If `C` is faithfully flat over `B` and flat over `A`, then `B` is flat over `A`. -/
theorem flat_of_faithfullyFlat_of_flat (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.FaithfullyFlat B C] [Module.Flat A C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have h1 : Function.Injective (f.lTensor C) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have h3 : Function.Injective
      ((AlgebraTensorModule.cancelBaseChange A B B C N').toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor B C (AlgebraTensorModule.lTensor B B f)) := by
    rw [← AlgebraTensorModule.lTensor_comp_cancelBaseChange]
    exact h1.comp (AlgebraTensorModule.cancelBaseChange A B B C N).injective
  have h4 : Function.Injective
      (AlgebraTensorModule.lTensor B C (AlgebraTensorModule.lTensor B B f)) :=
    Function.Injective.of_comp h3
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective (R := B) (M := C)
    (f := AlgebraTensorModule.lTensor B B f)).mp h4

end Singularity.Algebra
