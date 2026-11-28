/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Surface.IdealChart
import Singularity.Surface.LipmanCores
import Singularity.Surface.LipmanResolution
import Singularity.Algebra.RegularLocus
import Singularity.Valuation.LocalUniformizationCurves
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Category.Ring.Limits

/-!
# One round of the process of Lipman, and rational singularities

This file proves algebraic cores of Corollary 1.2.5 and Remark 2.2.3 of Volume 4 of the
handbook. It also gives Definition 2.1.3 of Volume 4 in Lean. The main declarations are as
follows.

Corollary 1.2.5 (one round of the process), the affine steps.

* `Singularity.bot_mem_regularLocus`: for a domain `R`, the generic point `(0)` of `Spec R` is
  regular.
* `Singularity.regularLocus_compl_ne_univ`: so the singular locus of a domain is not all of
  `Spec R`. This is the step "`S ≠ X`".
* `Singularity.idealChart_top_eq_top`: the chart `R[I/f]` of the blowup of the unit ideal is
  all of `R_f`. So the blowup is an isomorphism where the center is empty. This is the chart
  step of "the blowup is an isomorphism over `X \ S`".
* `Singularity.exists_algebraMap_eq_of_isIntegral_localization`: let `R` be a domain with
  fraction field `K`, and let `R_M` be a localization that is integrally closed. Then each
  element of `K` that is integral over `R` lies in `R_M`. So the normalization does not change
  the open set where `X` is normal.
* `Singularity.ringKrullDim_integralClosure_le`: the integral closure of a domain `B` in its
  fraction field has dimension at most `dim B`. This is the step "`dim X_1 ≤ 2`" from
  `dim Bl_S X ≤ 2`.

Definition 2.1.3 (rational singularities).

* `Singularity.hasExtSheafAb`: abelian sheaves on a scheme have `Ext` groups in universe `u`.
* `Singularity.structureSheafAb`: the structure sheaf of a scheme as a sheaf of abelian groups.
* `Singularity.cohomOne`: the group `H^1(W, O_Y)` for an open `W` of `Y`, as the sheaf
  cohomology of Mathlib (an `Ext` group in the category of abelian sheaves).
* `Singularity.cohomOneRes`: the restriction map `H^1(W, O_Y) → H^1(W', O_Y)` for `W' ≤ W`.
* `Singularity.R1PushforwardVanishes`: the condition `R^1 f_* O_Y = 0`. The sheaf `R^1 f_* O_Y`
  is the sheaf associated with `V ↦ H^1(f⁻¹ V, O_Y)`. It is `0` if and only if each class in
  `H^1(f⁻¹ V, O_Y)` is locally `0` on `V`. We take this as the definition.
* `Singularity.HasRationalSingularities`: `R^1 f_* O_Y = 0` for each normal modification `f`.
* `Singularity.IsRationalSingularity`: a ring `A` has a rational singularity if `Spec A` has
  rational singularities.
* `Singularity.r1PushforwardVanishes_of_subsingleton`: if all the groups `H^1(f⁻¹ V, O_Y)` are
  `0`, then `R^1 f_* O_Y = 0`.

Remark 2.2.3 (a ring with an infinite normalization has no resolution), the affine step.

* `Singularity.not_moduleFinite_of_not_moduleFinite_integralClosure`: let `R` be Noetherian
  with an infinite normalization in `K`. Then no subalgebra of `K` that is integrally closed in
  `K` is a finite `R`-module. With Proposition 2.2.2 this is the claim of the remark.

Not proved. In Corollary 1.2.5: the finiteness of the normalization of `Bl_S X` (this needs
that an excellent ring is a Nagata ring), the excellence of `Bl_S X` and of `X_1`, the dimension
inequality that gives `dim Bl_S X ≤ 2`, the properness of `X_1 → X`, and the gluing of the
charts into a statement on schemes. Theorem 1.2.4, which gives that `S` is finite, is proved
in `Singularity.Surface.IsolatedSingular` for affine schemes. In Definition 2.1.3: the
hypotheses that `A` is excellent, normal, local and of dimension `2` are not part of the Lean
definition, since excellence is not in Mathlib. We do not prove that our condition agrees with
`R^1 f_* O_Y = 0` for the derived functor `R^1 f_*`, and we do not prove any vanishing of `H^1`.
In Remark 2.2.3: the example of Nagata of a Noetherian local domain with an infinite
normalization, and the scheme part of Proposition 2.2.2, are not proved. Remark 2.1.4 and
Theorem 2.1.6 are not treated.
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Singularity

/-! ### Corollary 1.2.5, the affine steps -/

section Round

variable {R : Type u} [CommRing R]

/-- Corollary 1.2.5, the step `S ≠ X`. For a domain `R`, the local ring at the generic point
`(0)` is a field, so it is regular. -/
theorem bot_mem_regularLocus [IsDomain R] :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Algebra.regularLocus R := by
  rw [Algebra.mem_regularLocus]
  have hdim : ringKrullDim (Localization.AtPrime (⊥ : Ideal R)) = 0 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (⊥ : Ideal R)
      (Localization.AtPrime (⊥ : Ideal R)), Ideal.height_bot]
    rfl
  have : Ring.KrullDimLE 0 (Localization.AtPrime (⊥ : Ideal R)) :=
    Ring.krullDimLE_iff.mpr (by rw [hdim]; simp)
  have hf : IsField (Localization.AtPrime (⊥ : Ideal R)) :=
    Ring.KrullDimLE.isField_of_isDomain
  let := hf.toField
  infer_instance

/-- Corollary 1.2.5, the step `S ≠ X`. The singular locus of a domain is not all of
`Spec R`. -/
theorem regularLocus_compl_ne_univ [IsDomain R] :
    (Algebra.regularLocus R)ᶜ ≠ Set.univ := fun h => by
  have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ (Algebra.regularLocus R)ᶜ :=
    h ▸ Set.mem_univ _
  exact hmem bot_mem_regularLocus

/-- Corollary 1.2.5, the chart step over `X \ S`. The chart `R[⊤/f]` of the blowup of the unit
ideal is all of `R_f`. -/
theorem idealChart_top_eq_top (f : R) : idealChart (⊤ : Ideal R) f = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) x
  have hinv : IsLocalization.Away.invSelf f ∈ idealChart (⊤ : Ideal R) f := by
    simpa using div_mem_idealChart (I := (⊤ : Ideal R)) (f := f) (a := 1) Submodule.mem_top
  have : IsLocalization.mk' (Localization.Away f) a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) =
      algebraMap R (Localization.Away f) a * IsLocalization.Away.invSelf f ^ n := by
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    show algebraMap R _ a = _ * algebraMap R _ (f ^ n)
    rw [map_pow, mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf f),
      IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  show IsLocalization.mk' (Localization.Away f) a (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) ∈ _
  rw [this]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (Subalgebra.pow_mem _ hinv n)

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Corollary 1.2.5, the normalization step over `X \ S`. Let `R` be a domain with fraction
field `K`, and let `R_M` be a localization of `R` that is integrally closed. Then each element
of `K` that is integral over `R` lies in `R_M`. So the normalization of `R`, localized at `M`,
is `R_M`. -/
theorem exists_algebraMap_eq_of_isIntegral_localization [IsDomain R] (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
    [Algebra S K] [IsScalarTower R S K] [IsIntegrallyClosed S] {x : K} (hx : IsIntegral R x) :
    ∃ s : S, algebraMap S K s = x := by
  have : IsFractionRing S K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S K
  exact IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := S))

/-- Corollary 1.2.5, the step `dim X_1 ≤ 2`. The integral closure of `B` in `K` has dimension
at most `dim B`. -/
theorem ringKrullDim_integralClosure_le (B L : Type*) [CommRing B] [Field L] [Algebra B L] :
    ringKrullDim (integralClosure B L) ≤ ringKrullDim B :=
  ringKrullDim_le_of_isIntegral B (integralClosure B L)

end Round

/-! ### Definition 2.1.3, rational singularities -/

section Rational

/-- The category of abelian sheaves on a scheme has `Ext` groups in universe `u`, since it is a
Grothendieck abelian category. -/
noncomputable instance hasExtSheafAb (Y : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) :=
  IsGrothendieckAbelian.hasExt _

/-- The structure sheaf of a scheme `Y` as a sheaf of abelian groups. -/
noncomputable def structureSheafAb (Y : Scheme.{u}) : TopCat.Sheaf AddCommGrpCat.{u} Y :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u} ⋙
    forget₂ RingCat.{u} AddCommGrpCat.{u})).obj Y.sheaf

/-- The group `H^1(W, O_Y)` for an open set `W` of a scheme `Y`. -/
noncomputable abbrev cohomOne (Y : Scheme.{u}) (W : Y.Opens) : AddCommGrpCat.{u} :=
  Sheaf.H' (structureSheafAb Y) 1 W

/-- The restriction map `H^1(W, O_Y) → H^1(W', O_Y)` for opens `W' ≤ W`. -/
noncomputable def cohomOneRes (Y : Scheme.{u}) {W W' : Y.Opens} (h : W' ≤ W) :
    cohomOne Y W ⟶ cohomOne Y W' :=
  ((structureSheafAb Y).cohomologyPresheaf 1).map (homOfLE h).op

/-- The condition `R^1 f_* O_Y = 0`. The sheaf `R^1 f_* O_Y` is associated with the presheaf
`V ↦ H^1(f⁻¹ V, O_Y)`. It is `0` if and only if each class of `H^1(f⁻¹ V, O_Y)` is `0` near
each point of `V`. -/
def R1PushforwardVanishes {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∀ (V : X.Opens) (c : cohomOne Y (f ⁻¹ᵁ V)) (x : X), x ∈ V →
    ∃ (W : X.Opens) (h : W ≤ V), x ∈ W ∧ cohomOneRes Y (f.preimage_mono h) c = 0

/-- Definition 2.1.3. A scheme `X` has rational singularities if `R^1 f_* O_Y = 0` for each
normal modification `f : Y → X`. -/
def HasRationalSingularities (X : Scheme.{u}) : Prop :=
  ∀ (Y : Scheme.{u}) (f : Y ⟶ X), IsNormalModification f → R1PushforwardVanishes f

/-- Definition 2.1.3. A ring `A` has a rational singularity if `Spec A` has rational
singularities. The handbook asks this for an excellent normal local domain of dimension `2`. -/
def IsRationalSingularity (A : Type u) [CommRing A] : Prop :=
  HasRationalSingularities (Spec (CommRingCat.of A))

/-- If each group `H^1(f⁻¹ V, O_Y)` is `0`, then `R^1 f_* O_Y = 0`. -/
theorem r1PushforwardVanishes_of_subsingleton {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : ∀ V : X.Opens, Subsingleton (cohomOne Y (f ⁻¹ᵁ V))) : R1PushforwardVanishes f :=
  fun V c x hx => ⟨V, le_rfl, hx, by
    rw [Subsingleton.elim c 0, map_zero]⟩

end Rational

/-! ### Remark 2.2.3, the affine step -/

section Nagata

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

/-- Remark 2.2.3, the affine step. Let `R` be Noetherian, and assume that the integral closure
of `R` in `K` is not a finite `R`-module. Then no subalgebra `B` of `K` that is integrally
closed in `K` is a finite `R`-module. So the proof of Proposition 2.2.2 shows that `R` has no
resolution. -/
theorem not_moduleFinite_of_not_moduleFinite_integralClosure [IsNoetherianRing R]
    (h : ¬ Module.Finite R (integralClosure R K)) (B : Subalgebra R K)
    (hB : ∀ x : K, IsIntegral B x → x ∈ B) : ¬ Module.Finite R B := fun _ =>
  h (Lipman.moduleFinite_integralClosure_of_subalgebra B hB)

end Nagata

end Singularity
