/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.ExtCriterion
import Singularity.Algebra.Regular
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# The converse of the theorem of Serre

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and residue field `k`. The theorem of
Serre states that `R` is regular if and only if `pd k < ∞` ([Ser55], [Mat89, Theorem 19.2]).
The file `GlobalDimension` proves that a regular local ring has `pd k < ∞`. This file proves the
converse.

## Main results

* `hasProjectiveDimensionLT_baseChange_quotient`: let `x` be a nonzerodivisor on `R` and on a
  finite module `M`. Then `pd_{R/(x)} (R/(x) ⊗ M) ≤ pd_R M`.
* `free_of_hasProjectiveDimensionLT_of_socle`: if some `s ≠ 0` has `𝔪 s = 0`, then each finite
  module of finite projective dimension is free.
* `maximalIdeal_eq_bot_of_socle`: if some `s ≠ 0` has `𝔪 s = 0` and `pd k < ∞`, then `𝔪 = 0`.
* `exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors`: if `𝔪 ≠ 0` and no `s ≠ 0` has
  `𝔪 s = 0`, then some `x ∈ 𝔪 \ 𝔪²` is a nonzerodivisor.
* `hasProjectiveDimensionLT_residueField_quotient`: for such an `x`, the residue field of
  `R/(x)` has finite projective dimension over `R/(x)`.
* `isRegularLocalRing_of_hasProjectiveDimensionLT`: if `pd k < ∞`, then `R` is regular.

## The proof

The proof is by induction on the number of generators of `𝔪`.

1. If `s ≠ 0` and `𝔪 s = 0`, then `a ↦ a s` is an injective map `j : k → R`. Let
   `0 → K → F → M → 0` be exact with `K` and `F` free. The maps `j ⊗ K` and `j ⊗ F` are
   injective, because `K` and `F` are flat. Thus `k ⊗ K → k ⊗ F` is injective, and the
   criterion of Mathlib shows that `M` is free. Induction on the projective dimension shows
   that `k` is free, thus `𝔪 = 0`. This argument replaces the minimal resolution in the proof of
   [Mat89, Theorem 19.2].
2. Otherwise `𝔪` is not an associated prime of `R`. Prime avoidance gives a nonzerodivisor
   `x ∈ 𝔪 \ 𝔪²`. The sequence `0 → 𝔪 → R → k → 0` gives `pd 𝔪 < ∞`.
3. If `x` is a nonzerodivisor on `M`, then `R/(x) ⊗ -` keeps a free resolution of `M` exact.
   Thus `pd_{R/(x)} (𝔪/x𝔪) < ∞`.
4. A linear form on `𝔪/𝔪²` with value `1` at `x` shows that the residue field of `R/(x)` is a
   direct summand of `𝔪/x𝔪`. Thus it has finite projective dimension over `R/(x)`.
5. The maximal ideal of `R/(x)` has one generator fewer than `𝔪`. By induction `R/(x)` is
   regular, and thus `R` is regular.

## References

* [Ser55] J.-P. Serre, *Sur la dimension homologique des anneaux et des modules noethériens*,
  1956.
* [Mat89] H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1989.
-/

universe u

open CategoryTheory Abelian IsLocalRing Module TensorProduct Ideal

namespace Singularity.Algebra

section BaseChange

variable {R : Type u} [CommRing R] {x : R}

/-- Let `R → R → Q → 0` be exact, with first map `x`, and let `x` be a nonzerodivisor on `M`.
Then `Q ⊗ K → Q ⊗ P` is injective for each injective map `K → P` with cokernel `M`. -/
theorem lTensor_injective_of_isSMulRegular {K P M Q : Type u} [AddCommGroup K]
    [Module R K] [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup Q]
    [Module R Q] (q : R →ₗ[R] Q) (hq : Function.Surjective q)
    (hxq : Function.Exact (x • LinearMap.id : R →ₗ[R] R) q)
    (i : K →ₗ[R] P) (f : P →ₗ[R] M) (hi : Function.Injective i) (hif : Function.Exact i f)
    (hf : Function.Surjective f) (hx : IsSMulRegular M x) :
    Function.Injective (i.lTensor Q) := by
  refine lTensor_injective_of_exact_of_exact_of_rTensor_injective hxq hq hif hf ?_
    (Module.Flat.lTensor_preserves_injective_linearMap i hi)
  rw [LinearMap.rTensor_smul, LinearMap.rTensor_id]
  intro a b hab
  apply (TensorProduct.lid R M).injective
  apply hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hab
  change x • TensorProduct.lid R M a = x • TensorProduct.lid R M b
  rw [← map_smul, ← map_smul, hab]

/-- The sequence `R → R → R/(x) → 0` is exact, with first map `x`. -/
theorem exact_smul_algebraMap_quotient (x : R) :
    Function.Exact (x • LinearMap.id : R →ₗ[R] R) (Algebra.linearMap R (R ⧸ span {x})) := by
  intro a
  rw [Algebra.linearMap_apply, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
    mem_span_singleton']
  simp only [Set.mem_range, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, by rw [← hb, mul_comm]⟩, fun ⟨b, hb⟩ => ⟨b, by rw [← hb, mul_comm]⟩⟩

/-- Let `x` be a nonzerodivisor on `R` and on `M`. If `pd_R M < n + 1`, then
`pd_{R/(x)} (R/(x) ⊗ M) < n + 1`. -/
theorem hasProjectiveDimensionLT_baseChange_quotient [IsNoetherianRing R]
    (hx : IsSMulRegular R x) (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M], IsSMulRegular M x →
      HasProjectiveDimensionLT (ModuleCat.of R M) (n + 1) →
        HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) ((R ⧸ span {x}) ⊗[R] M))
          (n + 1) := by
  induction n with
  | zero =>
    intro M _ _ _ _ h
    have : Module.Projective R M :=
      (IsProjective.iff_projective (R := R) (ModuleCat.of R M)).mpr
        (projective_iff_hasProjectiveDimensionLT_one.mpr h)
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
    exact (IsProjective.iff_projective (R := R ⧸ span {x}) _).mp inferInstance
  | succ n ih =>
    intro M _ _ _ hxM h
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hK : HasProjectiveDimensionLT S.X₁ (n + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff n
        (inferInstanceAs (Projective (ModuleCat.of R P)))).mp h
    have hxP : IsSMulRegular P x := by
      let b := Module.Free.chooseBasis R P
      intro a c hac
      apply b.repr.injective
      ext i
      have := congrArg (fun v => b.repr v i) hac
      exact hx (by simpa using this)
    have hxK : IsSMulRegular (LinearMap.ker f) x := fun a b hab =>
      Subtype.ext (hxP (congrArg Subtype.val hab))
    have hKq := ih (LinearMap.ker f) hxK hK
    let A := R ⧸ span {x}
    have hzero : f ∘ₗ (LinearMap.ker f).subtype = 0 := by ext z; exact z.2
    let T : ShortComplex (ModuleCat.{u} A) :=
      { X₁ := ModuleCat.of A (A ⊗[R] LinearMap.ker f)
        X₂ := ModuleCat.of A (A ⊗[R] P)
        X₃ := ModuleCat.of A (A ⊗[R] M)
        f := ModuleCat.ofHom ((LinearMap.ker f).subtype.baseChange A)
        g := ModuleCat.ofHom (f.baseChange A)
        zero := by
          rw [← ModuleCat.ofHom_comp, ← LinearMap.baseChange_comp, hzero,
            LinearMap.baseChange_zero]
          rfl }
    have hT : T.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (by
          change Function.Exact ((LinearMap.ker f).subtype.baseChange A) (f.baseChange A)
          rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
          exact lTensor_exact (f := (LinearMap.ker f).subtype) (g := f) A f.exact_subtype_ker_map hf)
        mono_f := (ModuleCat.mono_iff_injective _).mpr (by
          change Function.Injective ((LinearMap.ker f).subtype.baseChange A)
          rw [LinearMap.baseChange_eq_lTensor]
          exact lTensor_injective_of_isSMulRegular (Algebra.linearMap R A)
            Ideal.Quotient.mk_surjective (exact_smul_algebraMap_quotient x)
            (LinearMap.ker f).subtype f Subtype.val_injective f.exact_subtype_ker_map hf hxM)
        epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
          change Function.Surjective (f.baseChange A)
          rw [LinearMap.baseChange_eq_lTensor]
          exact LinearMap.lTensor_surjective A hf) }
    have hP : Projective T.X₂ :=
      (IsProjective.iff_projective (R := A) _).mp inferInstance
    exact hT.hasProjectiveDimensionLT_X₃ (n + 1) hKq
      (hasProjectiveDimensionLT_of_ge _ 1 (n + 2) (by omega))

end BaseChange

section Local

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Let `j : k → R` be injective and let `φ : K → F` be an injective map of flat modules. Then
`k ⊗ φ` is injective. -/
theorem lTensor_residueField_injective_of_socle {K F : Type u} [AddCommGroup K] [Module R K]
    [AddCommGroup F] [Module R F] [Module.Flat R K] [Module.Flat R F] (φ : K →ₗ[R] F)
    (hφ : Function.Injective φ) (j : ResidueField R →ₗ[R] R) (hj : Function.Injective j) :
    Function.Injective (φ.lTensor (ResidueField R)) := by
  have hcomm : (φ.lTensor R).comp (j.rTensor K) = (j.rTensor F).comp (φ.lTensor _) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have h1 : Function.Injective ((φ.lTensor R).comp (j.rTensor K)) :=
    (Module.Flat.lTensor_preserves_injective_linearMap φ hφ).comp
      (Module.Flat.rTensor_preserves_injective_linearMap j hj)
  rw [hcomm, LinearMap.coe_comp] at h1
  exact h1.of_comp

/-- If `s ≠ 0` and `𝔪 s = 0`, then `a ↦ a s` is an injective map from the residue field
to `R`. -/
theorem exists_injective_residueField_of_socle {s : R} (hs : s ≠ 0)
    (hm : ∀ a ∈ maximalIdeal R, a * s = 0) :
    ∃ j : ResidueField R →ₗ[R] R, Function.Injective j := by
  have hker : maximalIdeal R = LinearMap.ker (LinearMap.mulRight R s) := by
    ext a
    rw [LinearMap.mem_ker, LinearMap.mulRight_apply]
    refine ⟨hm a, fun h => ?_⟩
    by_contra ha
    exact hs ((IsLocalRing.notMem_maximalIdeal.mp ha).mul_left_cancel (by rw [h, mul_zero]))
  refine ⟨Submodule.liftQ (maximalIdeal R) (LinearMap.mulRight R s) hker.le, ?_⟩
  exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ hker.le hker.ge)

/-- Let `x ∈ 𝔪 \ 𝔪²`. Then there is an `R`-linear map `g : 𝔪 → k` with `g x = 1`. -/
theorem exists_linearMap_maximalIdeal_eq_one {x : R} (hx : x ∈ maximalIdeal R)
    (nx : x ∉ maximalIdeal R ^ 2) :
    ∃ g : maximalIdeal R →ₗ[R] ResidueField R, g ⟨x, hx⟩ = 1 := by
  have hv : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rwa [Ne, Ideal.toCotangent_eq_zero]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ResidueField R) (CotangentSpace R),
      φ ((maximalIdeal R).toCotangent ⟨x, hx⟩) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff _ _).mp hc)
  refine ⟨(((φ ((maximalIdeal R).toCotangent ⟨x, hx⟩))⁻¹ • φ).restrictScalars R) ∘ₗ
    (maximalIdeal R).toCotangent, ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearMap.smul_apply, smul_eq_mul]
  exact inv_mul_cancel₀ hφ

/-- Let `x ∈ 𝔪 \ 𝔪²` be a nonzerodivisor, and let `pd k < n`. Then the residue field of
`R/(x)` has projective dimension less than `n + 1` over `R/(x)`. The proof uses that the
residue field of `R/(x)` is a direct summand of `𝔪/x𝔪`. -/
theorem hasProjectiveDimensionLT_residueField_quotient [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (nx : x ∉ maximalIdeal R ^ 2) (reg : x ∈ nonZeroDivisors R)
    [IsLocalRing (R ⧸ span {x})] (n : ℕ)
    (h : HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) n) :
    HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (ResidueField (R ⧸ span {x})))
      (n + 1) := by
  let A := R ⧸ span {x}
  let N := maximalIdeal R
  have hxR : IsSMulRegular R x := fun a b hab => sub_eq_zero.mp
    ((mem_nonZeroDivisors_iff.mp reg).1 _ (by rw [mul_sub]; exact sub_eq_zero.mpr hab))
  have hxN : IsSMulRegular N x := fun a b hab => Subtype.ext (hxR (congrArg Subtype.val hab))
  -- The sequence `0 → 𝔪 → R → k → 0` gives `pd 𝔪 < n + 1`.
  let S : ShortComplex (ModuleCat.{u} R) :=
    { X₁ := ModuleCat.of R N
      X₂ := ModuleCat.of R R
      X₃ := ModuleCat.of R (ResidueField R)
      f := ModuleCat.ofHom N.subtype
      g := ModuleCat.ofHom (Algebra.linearMap R (ResidueField R))
      zero := by
        ext y
        exact (residue_eq_zero_iff _).mpr y.2 }
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr fun y => by
        constructor
        · intro hy
          exact ⟨⟨y, (residue_eq_zero_iff y).mp hy⟩, rfl⟩
        · rintro ⟨z, rfl⟩
          exact (residue_eq_zero_iff _).mpr z.2
      mono_f := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
      epi_g := (ModuleCat.epi_iff_surjective _).mpr residue_surjective }
  have hR : HasProjectiveDimensionLT S.X₂ (n + 1) := by
    have : Projective S.X₂ := (IsProjective.iff_projective (R := R) _).mp inferInstance
    exact hasProjectiveDimensionLT_of_ge _ 1 (n + 1) (by omega)
  have hN : HasProjectiveDimensionLT (ModuleCat.of R N) (n + 1) :=
    hS.hasProjectiveDimensionLT_X₁ (n + 1) hR
      (hasProjectiveDimensionLT_of_ge _ n (n + 2) (by omega))
  have hNq : HasProjectiveDimensionLT (ModuleCat.of A (A ⊗[R] N)) (n + 1) :=
    hasProjectiveDimensionLT_baseChange_quotient hxR n N hxN hN
  -- The residue field of `A` is a retract of `A ⊗ 𝔪`.
  have : IsLocalHom (algebraMap R A) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨g₀, hg₀⟩ := exists_linearMap_maximalIdeal_eq_one hx nx
  let ι : ResidueField R →ₗ[R] ResidueField A :=
    (Algebra.linearMap (ResidueField R) (ResidueField A)).restrictScalars R
  let r : A ⊗[R] N →ₗ[A] ResidueField A := (ι ∘ₗ g₀).liftBaseChange A
  have hle : maximalIdeal A ≤
      LinearMap.ker (LinearMap.toSpanSingleton A (A ⊗[R] N) ((1 : A) ⊗ₜ[R] ⟨x, hx⟩)) := by
    intro b hb
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    rw [maximalIdeal_quotient_eq_map] at hb
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hb
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h1 : (Ideal.Quotient.mk (span {x}) a : A) = a • (1 : A) :=
      Algebra.algebraMap_eq_smul_one a
    have h2 : (a • (⟨x, hx⟩ : N)) = x • (⟨a, ha⟩ : N) :=
      Subtype.ext (by simp [mul_comm])
    rw [h1, TensorProduct.smul_tmul, h2, ← TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self x), TensorProduct.zero_tmul]
  let i : ResidueField A →ₗ[A] A ⊗[R] N :=
    Submodule.liftQ (maximalIdeal A) (LinearMap.toSpanSingleton A _ ((1 : A) ⊗ₜ[R] ⟨x, hx⟩)) hle
  have hri : ∀ z, r (i z) = z := by
    intro z
    obtain ⟨a, rfl⟩ := residue_surjective z
    have hi : i (residue A a) = a • ((1 : A) ⊗ₜ[R] (⟨x, hx⟩ : N)) := rfl
    rw [hi, map_smul, LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, hg₀, one_smul]
    simp only [ι, LinearMap.coe_restrictScalars, Algebra.linearMap_apply, map_one]
    rw [Algebra.smul_def, mul_one, ResidueField.algebraMap_eq]
  let ret : Retract (ModuleCat.of A (ResidueField A)) (ModuleCat.of A (A ⊗[R] N)) :=
    { i := ModuleCat.ofHom i
      r := ModuleCat.ofHom r
      retract := by
        ext z
        exact hri z }
  exact ret.hasProjectiveDimensionLT (n + 1)

variable [IsNoetherianRing R]

/-- If some `s ≠ 0` has `𝔪 s = 0`, then each finite module of finite projective dimension
is free. -/
theorem free_of_hasProjectiveDimensionLT_of_socle {s : R} (hs : s ≠ 0)
    (hm : ∀ a ∈ maximalIdeal R, a * s = 0) (n : ℕ) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLT M n →
      Module.Free R M := by
  obtain ⟨j, hj⟩ := exists_injective_residueField_of_socle hs hm
  induction n with
  | zero =>
    intro M _ h
    have hz := isZero_of_hasProjectiveDimensionLT_zero M
    have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Module.Free.of_subsingleton R M
  | succ n ih =>
    intro M _ h
    obtain ⟨P, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    cases n with
    | zero =>
      have : Module.Projective R M :=
        (IsProjective.iff_projective (R := R) M).mpr
          (projective_iff_hasProjectiveDimensionLT_one.mpr h)
      exact Module.free_of_flat_of_isLocalRing
    | succ n =>
      have hK : HasProjectiveDimensionLT S.X₁ (n + 1) :=
        (hS.hasProjectiveDimensionLT_X₃_iff n
          (inferInstanceAs (Projective (ModuleCat.of R P)))).mp h
      have : Module.Free R (LinearMap.ker f) := ih S.X₁ hK
      exact Module.free_of_lTensor_residueField_injective (LinearMap.ker f).subtype f surjf
        f.exact_subtype_ker_map
        (lTensor_residueField_injective_of_socle _ Subtype.val_injective j hj)

/-- If some `s ≠ 0` has `𝔪 s = 0` and the residue field has finite projective dimension, then
`𝔪 = 0`. -/
theorem maximalIdeal_eq_bot_of_socle {s : R} (hs : s ≠ 0)
    (hm : ∀ a ∈ maximalIdeal R, a * s = 0) (n : ℕ)
    (h : HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) n) :
    maximalIdeal R = ⊥ := by
  have := free_of_hasProjectiveDimensionLT_of_socle hs hm n _ h
  let b := Module.Free.chooseBasis R (ResidueField R)
  obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex R (ResidueField R)) := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    have : Subsingleton (ResidueField R) := b.repr.toEquiv.subsingleton
    exact zero_ne_one (Subsingleton.elim (0 : ResidueField R) 1)
  rw [eq_bot_iff]
  intro a ha
  have h0 : a • b i = 0 := by
    rw [Algebra.smul_def, ResidueField.algebraMap_eq, (residue_eq_zero_iff a).mpr ha, zero_mul]
  have := congrArg (fun v => b.repr v i) h0
  simpa using this

/-- Let `𝔪 ≠ 0`, and assume that no `s ≠ 0` has `𝔪 s = 0`. Then some `x ∈ 𝔪 \ 𝔪²` is a
nonzerodivisor. -/
theorem exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors (hne : maximalIdeal R ≠ ⊥)
    (hsoc : ∀ s : R, s ≠ 0 → ∃ a ∈ maximalIdeal R, a * s ≠ 0) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ x ∈ nonZeroDivisors R := by
  classical
  have hfin : (associatedPrimes R R).Finite := associatedPrimes.finite R R
  set S : Finset (Ideal R) := insert (maximalIdeal R ^ 2) hfin.toFinset with hS
  have hprime : ∀ i ∈ S, i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → i.IsPrime := by
    intro i hi hne _
    rcases Finset.mem_insert.mp hi with h' | h'
    · exact absurd h' hne
    · exact (hfin.mem_toFinset.mp h').isPrime
  have hsq : maximalIdeal R ^ 2 < maximalIdeal R := by
    refine lt_of_le_of_ne (Ideal.pow_le_self two_ne_zero) fun heq => hne ?_
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
      (IsNoetherian.noetherian _) ?_ (maximalIdeal_le_jacobson _)
    rw [Ideal.smul_eq_mul, ← pow_two, heq]
  have hnot : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ i ∈ (S : Set (Ideal R)), (i : Set R)) := by
    rw [Ideal.subset_union_prime (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) hprime]
    rintro ⟨i, hi, hle⟩
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact lt_irrefl _ (hsq.trans_le hle)
    · obtain ⟨hip, s, hs⟩ := isAssociatedPrime_iff.mp (hfin.mem_toFinset.mp hi')
      have heq : i = maximalIdeal R := le_antisymm (le_maximalIdeal hip.ne_top) hle
      have hs0 : s ≠ 0 := by
        rintro rfl
        apply hip.ne_top
        rw [hs, eq_top_iff]
        intro a _
        rw [Submodule.mem_colon_singleton, smul_zero]
        exact Submodule.zero_mem _
      obtain ⟨a, ha, has⟩ := hsoc s hs0
      apply has
      have hai : a ∈ i := heq ▸ ha
      rw [hs, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at hai
      exact hai
  rw [Set.not_subset] at hnot
  obtain ⟨x, hx, hxU⟩ := hnot
  refine ⟨x, hx, fun hx2 => hxU ?_, ?_⟩
  · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hx2
  · by_contra hnz
    have hc : x ∈ (nonZeroDivisors R : Set R)ᶜ := hnz
    rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors, Set.mem_iUnion₂] at hc
    obtain ⟨p, hp, hxp⟩ := hc
    exact hxU (Set.mem_biUnion
      (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hp))) hxp)

end Local

/-- Let `R` be a Noetherian local ring such that `𝔪` has at most `e` generators. If the residue
field has finite projective dimension, then `R` is regular. -/
theorem isRegularLocalRing_of_spanFinrank_le (e : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (maximalIdeal R).spanFinrank ≤ e → ∀ n : ℕ,
        HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) n → IsRegularLocalRing R := by
  have base : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (maximalIdeal R).spanFinrank = 0 → IsRegularLocalRing R := by
    intro R _ _ _ h0
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := R) ?_
    rw [h0, Nat.cast_zero]
    exact ringKrullDim_nonneg_of_nontrivial
  induction e with
  | zero =>
    intro R _ _ _ he n h
    exact base R (Nat.le_zero.mp he)
  | succ e ih =>
    intro R _ _ _ he n h
    by_cases hm : maximalIdeal R = ⊥
    · exact base R (by rw [hm, Submodule.spanFinrank_bot])
    by_cases hsoc : ∃ s : R, s ≠ 0 ∧ ∀ a ∈ maximalIdeal R, a * s = 0
    · obtain ⟨s, hs, hms⟩ := hsoc
      exact absurd (maximalIdeal_eq_bot_of_socle hs hms n h) hm
    push Not at hsoc
    obtain ⟨x, hx, nx, reg⟩ := exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors hm hsoc
    have : IsLocalRing (R ⧸ span {x}) :=
      isLocalRing_quotient_of_le_maximalIdeal ((span_singleton_le_iff_mem _).mpr hx)
    have hsf := spanFinrank_maximalIdeal_quotient_add_one_le hx nx
    have hq := hasProjectiveDimensionLT_residueField_quotient hx nx reg n h
    have hreg := ih (R ⧸ span {x}) (by omega) (n + 1) hq
    exact (of_quotient_span_singleton hx reg hreg).1

/-- The converse of the theorem of Serre. Let `R` be a Noetherian local ring. If the residue
field has finite projective dimension, then `R` is regular ([Ser55], [Mat89, Theorem 19.2]). -/
theorem isRegularLocalRing_of_hasProjectiveDimensionLT (R : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (h : HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) n) : IsRegularLocalRing R :=
  isRegularLocalRing_of_spanFinrank_le _ R le_rfl n h

end Singularity.Algebra
