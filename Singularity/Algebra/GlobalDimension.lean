/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.RegularSequence
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Finite modules over a regular local ring have finite projective dimension

Let `R` be a regular local ring of dimension `d`. This file proves that each finite `R`-module
has projective dimension at most `d` ([Mat89, Theorem 19.2], the second half of the first
direction of the theorem of Serre). With `projectiveDimension_residueField`, the bound is sharp.

## Main results

* `hasProjectiveDimensionLT_of_quotient`: let `x` be a nonzerodivisor of `R` and let `N` be a
  finite `R ⧸ (x)`-module. If `pd N < n` over `R ⧸ (x)`, then `pd N < n + 1` over `R`.
* `hasProjectiveDimensionLT_of_isRegularLocalRing`: over a regular local ring of dimension `d`,
  each finite module `M` has `pd M < d + 1`.
* `projectiveDimension_le_ringKrullDim`: the same result for `projectiveDimension`.

## The proof

The proof is by induction on `d`. If `d = 0`, then `R` is a field and each module is free.
If `d > 0`, take `x ∈ 𝔪 \ 𝔪²`. Then `R ⧸ (x)` is regular of dimension `d - 1`. Let
`0 → K → F → M → 0` be a presentation with `F` finite and free. The element `x` is a
nonzerodivisor on `K`, because `R` is a domain and `K ⊆ F`. By induction, `K ⧸ xK` has projective
dimension at most `d - 1` over `R ⧸ (x)`, so at most `d` over `R`. By the theorem of Mathlib on
the quotient by a regular element, `pd K + 1 = pd (K ⧸ xK) ≤ d`. Thus `pd M ≤ pd K + 1 ≤ d`.

The change of rings uses the resolution `0 → Rᵐ → Rᵐ → (R ⧸ (x))ᵐ → 0` of a free module over
`R ⧸ (x)`, and induction on the projective dimension.

## References

* [Mat89] H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1989.
-/

universe u

open CategoryTheory Abelian IsLocalRing Ideal Module TensorProduct

namespace Singularity.Algebra

section ChangeOfRings

variable {R : Type u} [CommRing R] {x : R}

/-- If `x` is a nonzerodivisor, then `(R ⧸ (x))ᵐ` has projective dimension at most `1` over `R`. -/
theorem hasProjectiveDimensionLT_pi_quotient (hx : IsSMulRegular R x) (m : ℕ) :
    HasProjectiveDimensionLT (ModuleCat.of R (Fin m → R ⧸ span {x})) 2 := by
  have hreg : IsSMulRegular (ModuleCat.of R (Fin m → R)) x := fun a b hab =>
    funext fun i => hx (congrFun hab i)
  have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R (Fin m → R)) hreg
  have h₃ : HasProjectiveDimensionLT
      (ModuleCat.smulShortComplex (ModuleCat.of R (Fin m → R)) x).X₃ 2 :=
    hS.hasProjectiveDimensionLT_X₃ 1
      (inferInstanceAs (HasProjectiveDimensionLT (ModuleCat.of R (Fin m → R)) 1))
      (inferInstanceAs (HasProjectiveDimensionLT (ModuleCat.of R (Fin m → R)) 2))
  let e : QuotSMulTop x (Fin m → R) ≃ₗ[R] (Fin m → R ⧸ span {x}) :=
    QuotSMulTop.equivQuotTensor x (Fin m → R) ≪≫ₗ
      (Algebra.TensorProduct.piScalarRight R R (R ⧸ span {x}) (Fin m)).toLinearEquiv
  have h₃' : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x (Fin m → R))) 2 := h₃
  exact hasProjectiveDimensionLT_of_iso e.toModuleIso 2

variable [IsNoetherianRing R]

/-- Let `x` be a nonzerodivisor of `R` and let `N` be a finite `R ⧸ (x)`-module. If `N` has
projective dimension less than `n` over `R ⧸ (x)`, then it has projective dimension less than
`n + 1` over `R`. -/
theorem hasProjectiveDimensionLT_of_quotient (hx : IsSMulRegular R x) (n : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module (R ⧸ span {x}) N] [Module R N]
      [IsScalarTower R (R ⧸ span {x}) N] [Module.Finite (R ⧸ span {x}) N],
      HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) N) n →
        HasProjectiveDimensionLT (ModuleCat.of R N) (n + 1) := by
  induction n with
  | zero =>
    intro N _ _ _ _ _ h
    have hz := isZero_of_hasProjectiveDimensionLT_zero (ModuleCat.of (R ⧸ span {x}) N)
    have : Subsingleton N := (ModuleCat.isZero_iff_subsingleton.mp hz)
    have hz' : Limits.IsZero (ModuleCat.of R N) := ModuleCat.isZero_of_subsingleton _
    have := hz'.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 1 (Nat.zero_le 1)
  | succ n ih =>
    intro N _ _ _ _ _ h
    obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (R ⧸ span {x}) N
    have := hasProjectiveDimensionLT_pi_quotient hx m
    cases n with
    | zero =>
      have hproj : Module.Projective (R ⧸ span {x}) N :=
        (IsProjective.iff_projective (R := R ⧸ span {x}) N).mpr
          (projective_iff_hasProjectiveDimensionLT_one.mpr h)
      obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
      let r : Retract (ModuleCat.of R N) (ModuleCat.of R (Fin m → R ⧸ span {x})) :=
        { i := ModuleCat.ofHom (s.restrictScalars R)
          r := ModuleCat.ofHom (f.restrictScalars R)
          retract := by
            ext y
            exact LinearMap.congr_fun hs y }
      exact r.hasProjectiveDimensionLT 2
    | succ n =>
      let Sq := f.shortComplexKer
      have hSq : Sq.ShortExact := LinearMap.shortExact_shortComplexKer hf
      have hK : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (LinearMap.ker f))
          (n + 1) :=
        (hSq.hasProjectiveDimensionLT_X₃_iff n
          (inferInstanceAs (Projective (ModuleCat.of _ (Fin m → R ⧸ span {x}))))).mp h
      have hKR := ih (LinearMap.ker f) hK
      let S : ShortComplex (ModuleCat.{u} R) :=
        { X₁ := ModuleCat.of R (LinearMap.ker f)
          X₂ := ModuleCat.of R (Fin m → R ⧸ span {x})
          X₃ := ModuleCat.of R N
          f := ModuleCat.ofHom ((LinearMap.ker f).subtype.restrictScalars R)
          g := ModuleCat.ofHom (f.restrictScalars R)
          zero := by ext y; exact y.2 }
      have hS : S.ShortExact :=
        { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
            fun y => by
              constructor
              · intro hy
                exact ⟨⟨y, hy⟩, rfl⟩
              · rintro ⟨z, rfl⟩
                exact z.2
          mono_f := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
          epi_g := (ModuleCat.epi_iff_surjective _).mpr hf }
      exact hS.hasProjectiveDimensionLT_X₃ (n + 2) hKR
        (hasProjectiveDimensionLT_of_ge _ 2 (n + 3) (by omega))

end ChangeOfRings

/-- Over a regular local ring of dimension `d`, each finite module has projective dimension
less than `d + 1` ([Mat89, Theorem 19.2]). -/
theorem hasProjectiveDimensionLT_of_isRegularLocalRing (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], ringKrullDim R = d →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
        HasProjectiveDimensionLT (ModuleCat.of R M) (d + 1) := by
  induction d with
  | zero =>
    intro R _ _ h M _ _ _
    have h0 : (maximalIdeal R).spanFinrank = 0 := by
      have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
      rw [h] at this
      exact_mod_cast this
    have hbot : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp h0
    let := (isField_iff_maximalIdeal_eq.mpr hbot).toField
    have : Module.Projective R M := Module.Projective.of_free
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
    exact (IsProjective.iff_projective (R := R) M).mp this
  | succ d ih =>
    intro R _ _ h M _ _ _
    have hpos : 0 < ringKrullDim R := by
      rw [h]; exact_mod_cast Nat.succ_pos d
    obtain ⟨x, mem, nmem, -⟩ :=
      exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes hpos
    obtain ⟨hQ, hdim⟩ := quotient_span_singleton mem nmem
    have := hQ
    have hQd : ringKrullDim (R ⧸ span {x}) = d := by
      obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast (R ⧸ span {x})
      rw [hm, h] at hdim
      have : m + 1 = d + 1 := by exact_mod_cast hdim
      rw [hm, Nat.succ_inj.mp this]
    have hdom := isDomain_of_isRegularLocalRing R
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact nmem (zero_mem _)
    have hxR : IsSMulRegular R x := IsSMulRegular.of_ne_zero hx0
    obtain ⟨P, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
    let K := LinearMap.ker f
    have hxK : IsSMulRegular K x := IsSMulRegular.of_ne_zero hx0
    -- The module `K ⧸ xK` over `R ⧸ (x)`.
    have hN := ih (R ⧸ span {x}) hQd ((R ⧸ span {x}) ⊗[R] K)
    have hNR := hasProjectiveDimensionLT_of_quotient hxR (d + 1) ((R ⧸ span {x}) ⊗[R] K) hN
    have hQK : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x K)) (d + 2) :=
      hasProjectiveDimensionLT_of_iso (QuotSMulTop.equivQuotTensor x K).toModuleIso.symm _
    -- The projective dimension of `K`.
    have hpd := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (ModuleCat.of R K) x hxK mem
    have hle : projectiveDimension (ModuleCat.of R (QuotSMulTop x K)) ≤ (d + 1 : ℕ) :=
      (projectiveDimension_le_iff _ _).mpr hQK
    have hKle : projectiveDimension (ModuleCat.of R K) ≤ d := by
      rw [hpd] at hle
      have : ((d + 1 : ℕ) : WithBot ℕ∞) = (d : WithBot ℕ∞) + 1 := by push_cast; rfl
      rw [this] at hle
      exact (ENat.WithBot.add_le_add_one_right_iff).mp (by exact_mod_cast hle)
    have hK : HasProjectiveDimensionLT (ModuleCat.of R K) (d + 1) :=
      (projectiveDimension_le_iff _ _).mp hKle
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    exact (hS.hasProjectiveDimensionLT_X₃_iff d
      (inferInstanceAs (Projective (ModuleCat.of R P)))).mpr hK

/-- Over a regular local ring, each finite module has projective dimension at most the
dimension of the ring ([Mat89, Theorem 19.2]). -/
theorem projectiveDimension_le_ringKrullDim (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    projectiveDimension (ModuleCat.of R M) ≤ ringKrullDim R := by
  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast R
  rw [hd, projectiveDimension_le_iff]
  exact hasProjectiveDimensionLT_of_isRegularLocalRing d R hd M

end Singularity.Algebra
