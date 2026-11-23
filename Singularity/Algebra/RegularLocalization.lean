/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.SerreConverse
import Singularity.Algebra.GlobalDimension
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The localization of a regular local ring is regular

Let `R` be a regular local ring and let `𝔭` be a prime ideal of `R`. This file proves that
`R_𝔭` is a regular local ring ([Ser55], [Mat89, Theorem 19.3]). The result is the
characterization of Serre in both directions, applied to the module `R/𝔭`.

## Main results

* `isRegularLocalRing_iff_exists_hasProjectiveDimensionLT`: a Noetherian local ring is regular
  if and only if its residue field has finite projective dimension.
* `isRegularLocalRing_localization`: if `R` is regular, then `R_𝔭` is regular.

## The proof

Let `d = dim R`. Then `pd_R (R/𝔭) ≤ d`, because each finite module over `R` has projective
dimension at most `d`. Localization does not increase the projective dimension, thus
`pd (R/𝔭)_𝔭 ≤ d` over `R_𝔭`. The module `(R/𝔭)_𝔭` is the residue field `κ(𝔭)` of `R_𝔭`.
By the converse of the theorem of Serre, `R_𝔭` is regular.

## References

* [Ser55] J.-P. Serre, *Sur la dimension homologique des anneaux et des modules noethériens*,
  1956.
* [Mat89] H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1989.
-/

universe u

open CategoryTheory IsLocalRing

namespace Singularity.Algebra

/-- A Noetherian local ring is regular if and only if its residue field has finite projective
dimension ([Ser55], [Mat89, Theorem 19.2]). -/
theorem isRegularLocalRing_iff_exists_hasProjectiveDimensionLT (R : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔
      ∃ n : ℕ, HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) n := by
  refine ⟨fun h => ?_, fun ⟨n, h⟩ => isRegularLocalRing_of_hasProjectiveDimensionLT R n h⟩
  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast R
  exact ⟨d + 1, hasProjectiveDimensionLT_of_isRegularLocalRing d R hd (ResidueField R)⟩

variable {R : Type u} [CommRing R]

/-- The image of `R \ 𝔭` in `R/𝔭` is the set of nonzerodivisors of `R/𝔭`. -/
theorem algebraMapSubmonoid_primeCompl_eq (p : Ideal R) [p.IsPrime] :
    Algebra.algebraMapSubmonoid (R ⧸ p) p.primeCompl = nonZeroDivisors (R ⧸ p) := by
  ext y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · rintro ⟨b, hb, hba⟩ ha
    apply hb
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hba.trans (Ideal.Quotient.eq_zero_iff_mem.mpr ha))
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- The residue field `κ(𝔭)` is the localization of `R/𝔭` at `R \ 𝔭`. -/
instance isLocalization_residueField (p : Ideal R) [p.IsPrime] :
    IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ p) p.primeCompl) p.ResidueField := by
  rw [algebraMapSubmonoid_primeCompl_eq]
  infer_instance

/-- The localization of a regular local ring at a prime ideal is a regular local ring
([Ser55], [Mat89, Theorem 19.3]). -/
theorem isRegularLocalRing_localization [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast R
  have h1 : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ p)) d :=
    hasProjectiveDimensionLT_of_isRegularLocalRing d R hd (R ⧸ p)
  have h2 : HasProjectiveDimensionLE
      ((ModuleCat.of R (R ⧸ p)).localizedModule p.primeCompl) d :=
    ModuleCat.localizedModule_hasProjectiveDimensionLE d p.primeCompl _
  let f := (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap
  let e₀ : LocalizedModule p.primeCompl (R ⧸ p) ≃ₗ[R] p.ResidueField :=
    IsLocalizedModule.iso p.primeCompl f
  let e₁ : LocalizedModule p.primeCompl (R ⧸ p) ≃ₗ[Localization.AtPrime p] p.ResidueField :=
    e₀.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
  let e : (ModuleCat.of R (R ⧸ p)).localizedModule p.primeCompl ≅
      ModuleCat.of (Localization.AtPrime p) (ResidueField (Localization.AtPrime p)) :=
    ((Shrink.linearEquiv (Localization.AtPrime p) _).trans e₁).toModuleIso
  have h3 : HasProjectiveDimensionLT
      (ModuleCat.of (Localization.AtPrime p) (ResidueField (Localization.AtPrime p))) (d + 1) :=
    hasProjectiveDimensionLT_of_iso e (d + 1)
  exact isRegularLocalRing_of_hasProjectiveDimensionLT _ (d + 1) h3

end Singularity.Algebra
