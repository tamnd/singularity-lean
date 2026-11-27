/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.MixedCharZero
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Local rings that contain a field

This file proves Volume 1, Lemma 4.4.2 of the handbook. A local ring `(R, m, κ)` contains a field if and only if it is equicharacteristic, that is, `char R = char κ`. In Lean, "R contains a field" means that a subring of `R` is a field.

* `Singularity.Algebra.isField_range`: the image of a field in a nontrivial ring is a field.
* `Singularity.Algebra.exists_isField_subring_iff_ringChar_eq`: Lemma 4.4.2 of the handbook.

If `char κ = p` is a prime, the field is the image of `ZMod p`. If `char κ = 0`, the field is the image of `ℚ`, from `EqualCharZero.nonempty_algebraRat_iff` of Mathlib.
-/

open IsLocalRing

namespace Singularity.Algebra

/-- The image of a field `F` in a nontrivial ring `R` is a subring of `R` that is a field. -/
theorem isField_range {F R : Type*} [Field F] [CommRing R] [Nontrivial R] (f : F →+* R) :
    IsField f.range := by
  have hinj : Function.Injective f.rangeRestrict := fun x y h =>
    f.injective (congrArg Subtype.val h)
  exact MulEquiv.isField (Field.toIsField F)
    (RingEquiv.ofBijective f.rangeRestrict ⟨hinj, f.rangeRestrict_surjective⟩).symm.toMulEquiv

/-- A local ring contains a field if and only if it is equicharacteristic (Volume 1, Lemma 4.4.2 of the handbook). Let `(R, m, κ)` be a local ring. Then a subring of `R` is a field if and only if `char R = char κ`. -/
theorem exists_isField_subring_iff_ringChar_eq {R : Type*} [CommRing R] [IsLocalRing R] :
    (∃ K : Subring R, IsField K) ↔ ringChar R = ringChar (ResidueField R) := by
  constructor
  · rintro ⟨K, hK⟩
    letI : Field K := hK.toField
    have hinj : Function.Injective ((residue R).comp K.subtype) := RingHom.injective _
    haveI : CharP R (ringChar K) :=
      charP_of_injective_ringHom (f := K.subtype) Subtype.val_injective (ringChar K)
    haveI : CharP (ResidueField R) (ringChar K) :=
      charP_of_injective_ringHom hinj (ringChar K)
    rw [ringChar.eq R (ringChar K), ringChar.eq (ResidueField R) (ringChar K)]
  · intro h
    rcases CharP.char_is_prime_or_zero (ResidueField R) (ringChar (ResidueField R)) with hp | h0
    · haveI : Fact (ringChar (ResidueField R)).Prime := ⟨hp⟩
      haveI : CharP R (ringChar (ResidueField R)) := ringChar.of_eq h
      exact ⟨(ZMod.castHom (dvd_refl _) R).range, isField_range _⟩
    · haveI : CharZero (ResidueField R) :=
        (CharP.ringChar_zero_iff_CharZero (R := ResidueField R)).mp h0
      have hq : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
        intro I hI
        have hle : I ≤ maximalIdeal R := le_maximalIdeal hI
        let φ : R ⧸ I →+* ResidueField R := Ideal.Quotient.lift I (residue R)
          fun x hx => (residue_eq_zero_iff x).mpr (hle hx)
        refine ⟨fun a b hab => ?_⟩
        have h1 := congrArg φ hab
        rw [map_natCast, map_natCast] at h1
        exact Nat.cast_injective h1
      obtain ⟨_⟩ := (EqualCharZero.nonempty_algebraRat_iff R).mpr hq
      exact ⟨(algebraMap ℚ R).range, isField_range _⟩

end Singularity.Algebra
