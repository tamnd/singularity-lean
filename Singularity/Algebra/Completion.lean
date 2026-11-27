/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Singularity.Algebra.FlatLocal

/-!
# The Rees algebra and the completion of a Noetherian ring

This file states seven results of Volume 1, Sections 4.1 to 4.3 of the handbook in the form of the handbook. Mathlib proves most of them, and the results here are short consequences.

* `Singularity.Algebra.isNoetherianRing_reesAlgebra`: the Rees algebra of an ideal of a Noetherian ring is Noetherian (Volume 1, Lemma 4.1.3 of the handbook).
* `Singularity.Algebra.fg_filtration_submodule_iff_stable`: over a Noetherian ring, an `I`-filtration of a finitely generated module is stable if and only if the module `M^*` over the Rees algebra is finitely generated (Volume 1, Lemma 4.1.4 of the handbook).
* `Singularity.Algebra.adicCompletion_shortExact`: over a Noetherian ring, `I`-adic completion is exact on short exact sequences of finitely generated modules (Volume 1, Proposition 4.2.5 of the handbook).
* `Singularity.Algebra.exists_tensorProduct_equiv_adicCompletion`: over a Noetherian ring, `R̂ ⊗_R M → M̂` is an isomorphism of `R̂`-modules for each finitely generated `M` (Volume 1, Theorem 4.2.6 of the handbook).
* `Singularity.Algebra.flat_adicCompletion`: the `I`-adic completion of a Noetherian ring is flat (Volume 1, Theorem 4.2.7 of the handbook).
* `Singularity.Algebra.adicCompletion_isLocalRing`: the completion of a Noetherian local ring is local with maximal ideal `m R̂` and the same residue field, and `R → R̂` is injective (Volume 1, Proposition 4.3.1, parts 1 and 2 of the handbook, without the claim that `R̂` is Noetherian).
* `Singularity.Algebra.faithfullyFlat_adicCompletion`: the completion of a Noetherian local ring is faithfully flat, so `R̂ ⊗_R P = 0` implies `P = 0` (Volume 1, Proposition 4.3.2 of the handbook, without the claim on exact sequences).

In Lean, the Rees algebra is the subalgebra `reesAlgebra I` of `R[X]` of the polynomials whose coefficient of `X^n` is in `I^n`, and `M̂` is `AdicCompletion I M`.
-/

universe u

open IsLocalRing TensorProduct

namespace Singularity.Algebra

/-- The Rees algebra of a Noetherian ring is Noetherian (Volume 1, Lemma 4.1.3 of the handbook). Let `R` be a Noetherian ring and let `I` be an ideal. Then the Rees algebra `R^* = ⊕ I^n t^n ⊆ R[t]` is a Noetherian ring. This is an instance of Mathlib. -/
theorem isNoetherianRing_reesAlgebra {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (reesAlgebra I) :=
  inferInstance

/-- Stable filtrations and the Rees algebra (Volume 1, Lemma 4.1.4 of the handbook). Let `R` be a Noetherian ring, let `M` be a finitely generated `R`-module and let `F` be an `I`-filtration of `M`. Then `M^* = ⊕ M_n t^n` is a finitely generated module over `R^*` if and only if `F` is stable. In Lean, `M^*` is `F.submodule`, the `R^*`-submodule of `M[t]` of the polynomials whose coefficient of `t^n` is in `M_n`. Each `M_n` is finitely generated since `M` is a Noetherian module, so Mathlib's `Ideal.Filtration.submodule_fg_iff_stable` applies. -/
theorem fg_filtration_submodule_iff_stable {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] {I : Ideal R} (F : I.Filtration M) :
    F.submodule.FG ↔ F.Stable :=
  F.submodule_fg_iff_stable fun _ => IsNoetherian.noetherian _

/-- Completion is exact (Volume 1, Proposition 4.2.5 of the handbook). Let `R` be a Noetherian ring, let `I` be an ideal and let `0 → N → M → P → 0` be an exact sequence of finitely generated `R`-modules. Then `0 → N̂ → M̂ → P̂ → 0` is exact. Only `M` needs to be finitely generated. -/
theorem adicCompletion_shortExact {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {N M P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] [Module.Finite R M] {f : N →ₗ[R] M} {g : M →ₗ[R] P}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective (AdicCompletion.map I f) ∧
      Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
      Function.Surjective (AdicCompletion.map I g) :=
  ⟨AdicCompletion.map_injective I hf, AdicCompletion.map_exact hf hfg hg,
    AdicCompletion.map_surjective I hg⟩

/-- Completion as a tensor product (Volume 1, Theorem 4.2.6 of the handbook). Let `R` be a Noetherian ring, let `I` be an ideal and let `M` be a finitely generated `R`-module. Then the natural map `R̂ ⊗_R M → M̂`, which sends `a ⊗ x` to `a x̂`, is an isomorphism of `R̂`-modules. This is `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` of Mathlib. -/
theorem exists_tensorProduct_equiv_adicCompletion {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ e : AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M,
      ∀ (a : AdicCompletion I R) (x : M), e (a ⊗ₜ x) = a • AdicCompletion.of I M x :=
  ⟨AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M, fun a x => by simp⟩

/-- The completion is flat (Volume 1, Theorem 4.2.7 of the handbook). Let `R` be a Noetherian ring and let `I` be an ideal. Then the `I`-adic completion `R̂` is a flat `R`-module. This is an instance of Mathlib. -/
theorem flat_adicCompletion {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Module.Flat R (AdicCompletion I R) :=
  inferInstance

/-- The completion of a local ring (Volume 1, Proposition 4.3.1, parts 1 and 2 of the handbook). Let `(R, m, κ)` be a Noetherian local ring. Then `R̂` is a local ring with maximal ideal `m R̂`, the map `R → R̂` gives a bijection of the residue fields, and the map `R → R̂` is injective. The claim that `R̂` is Noetherian and part 3 are not proved here. -/
theorem adicCompletion_isLocalRing (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] :
    IsLocalRing (AdicCompletion (maximalIdeal R) R) ∧
      maximalIdeal (AdicCompletion (maximalIdeal R) R) =
        (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ∧
      Function.Bijective
        (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) ∧
      Function.Injective (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  ⟨inferInstance, AdicCompletion.maximalIdeal_eq_map, AdicCompletion.residueField_map_bijective R,
    (faithfullyFlat_and_injective_of_flat_of_isLocalHom R
      (AdicCompletion (maximalIdeal R) R)).2⟩

/-- The completion of a local ring is faithfully flat (Volume 1, Proposition 4.3.2 of the handbook). Let `(R, m)` be a Noetherian local ring. Then `R̂` is a faithfully flat `R`-module, and for each `R`-module `P`, `R̂ ⊗_R P = 0` implies `P = 0`. The claim that a sequence is exact if it is exact after the tensor product with `R̂` is not stated here. -/
theorem faithfullyFlat_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) ∧
      ∀ (P : Type*) [AddCommGroup P] [Module R P],
        Subsingleton (AdicCompletion (maximalIdeal R) R ⊗[R] P) → Subsingleton P := by
  have hff : Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) :=
    (faithfullyFlat_and_injective_of_flat_of_isLocalHom R
      (AdicCompletion (maximalIdeal R) R)).1
  refine ⟨hff, fun P _ _ hP => ?_⟩
  exact Module.FaithfullyFlat.lTensor_reflects_triviality R
    (AdicCompletion (maximalIdeal R) R) P

end Singularity.Algebra
