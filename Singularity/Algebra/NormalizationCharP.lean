/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.Normalization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.MvPolynomial.Expand
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableDegree

/-!
# Finiteness of the normalization in each characteristic

Let `A` be a domain that is a finitely generated algebra over a field `k`. This file proves that the integral closure of `A` in its field of fractions is a finite `A`-module (`finite_integralClosure`). The file `Singularity/Algebra/Normalization.lean` proves the theorem when the extension of fraction fields is separable. This file removes that condition.

Let `P = k[X₁, ..., Xₛ]` and `K = Frac P`. The proof has two steps.

1. The purely inseparable case. Let `M` be a finite purely inseparable extension of `K`, of exponent `e`, and let `q = p ^ e`. Then `x ^ q` is in `K` for each `x` in `M`. Let `k'` be the finite extension of `k` that contains a `q`-th root of each coefficient of a finite set of polynomials, and let `T = k'[Y₁, ..., Yₛ]` with the map `Xᵢ ↦ Yᵢ ^ q`. Then `T` is a finite `P`-algebra, `T` is a normal domain, and `M` has a `K`-algebra map to `Frac T`. Thus the integral closure of `P` in `M` is a `P`-submodule of `T`, so it is finite.
2. The reduction to step 1. Let `L` be a finite extension of `K`, and let `L'` be its normal closure. The fixed field `M` of the automorphism group of `L'` is purely inseparable over `K`, and `L'` is Galois over `M`. Step 1 gives that the integral closure `R` of `P` in `M` is finite over `P`. The ring `R` is Noetherian and normal, with field of fractions `M`, so the separable case gives that the integral closure of `R` in `L'` is finite over `R`. This ring contains the integral closure of `P` in `L`.

The proof follows [Eisenbud, Commutative Algebra, Corollary 13.13] and [Zariski and Samuel, Commutative Algebra I, Chapter V, Section 4].
-/

open Module Polynomial
open scoped nonZeroDivisors

universe u v

namespace Singularity.Algebra

attribute [local instance] FractionRing.liftAlgebra

/-- Let `L` be a normal extension of `K`. Then the field of the elements of `L` that each `K`-automorphism of `L` fixes is purely inseparable over `K`. -/
theorem isPurelyInseparable_fixedField_top (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Normal K L] :
    IsPurelyInseparable K (IntermediateField.fixedField (⊤ : Subgroup Gal(L/K))) := by
  classical
  rw [isPurelyInseparable_iff_natSepDegree_eq_one]
  intro x
  have hx : IsIntegral K (x : L) := Algebra.IsIntegral.isIntegral (x : L)
  rw [IntermediateField.minpoly_eq x, natSepDegree_eq_of_splits _ (Normal.splits' (x : L)),
    Finset.card_eq_one]
  refine ⟨(x : L), ?_⟩
  ext y
  simp only [Finset.mem_singleton, Multiset.mem_toFinset]
  constructor
  · intro hy
    rw [mem_aroots] at hy
    have hmy : minpoly K (x : L) = minpoly K y :=
      minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) hy.2 (minpoly.monic hx)
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (E := L)).mp hmy.symm
    have hfix := (IntermediateField.mem_fixedField_iff _ _).mp x.2 σ (Subgroup.mem_top _)
    rw [← hσ]
    exact hfix
  · rintro rfl
    exact mem_aroots.mpr ⟨minpoly.ne_zero hx, minpoly.aeval K _⟩

/-- Let `P` be a Noetherian domain with field of fractions `K`, and let `K ⊆ M ⊆ L` be finite extensions with `L` separable over `M`. If the integral closure of `P` in `M` is a finite `P`-module, then the integral closure of `P` in `L` is a finite `P`-module. -/
theorem finite_integralClosure_of_tower (P K M L : Type*) [CommRing P] [IsDomain P]
    [IsNoetherianRing P] [Field K] [Field M] [Field L] [Algebra P K] [IsFractionRing P K]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]
    [Algebra P M] [Algebra P L] [IsScalarTower P K M] [IsScalarTower P K L] [IsScalarTower P M L]
    [FiniteDimensional K L] [Algebra.IsSeparable M L]
    (hM : Module.Finite P (integralClosure P M)) :
    Module.Finite P (integralClosure P L) := by
  have : IsNoetherianRing (integralClosure P M) := IsNoetherianRing.of_finite P _
  have : FiniteDimensional K M := FiniteDimensional.left K M L
  have : IsFractionRing (integralClosure P M) M :=
    integralClosure.isFractionRing_of_finite_extension K M
  have : IsIntegrallyClosed (integralClosure P M) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : IsScalarTower P (integralClosure P M) L := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply P M L]; rfl)
  have : FiniteDimensional M L := FiniteDimensional.right K M L
  have hC : Module.Finite (integralClosure P M) (integralClosure (integralClosure P M) L) :=
    IsIntegralClosure.finite (integralClosure P M) M L _
  have hfg : ((Subalgebra.toSubmodule (integralClosure (integralClosure P M) L)).restrictScalars
      P).FG := Submodule.FG.restrictScalars (Module.Finite.iff_fg.mp hC)
  have hN : IsNoetherian P ((Subalgebra.toSubmodule
      (integralClosure (integralClosure P M) L)).restrictScalars P) :=
    isNoetherian_of_fg_of_noetherian _ hfg
  have hle : Subalgebra.toSubmodule (integralClosure P L) ≤
      (Subalgebra.toSubmodule (integralClosure (integralClosure P M) L)).restrictScalars P :=
    fun x hx => IsIntegral.tower_top (A := integralClosure P M) hx
  exact (isNoetherian_of_le hle).finite


/-- Let `P` be a Noetherian domain with field of fractions `K`. Suppose that for each finite purely inseparable extension `M` of `K`, the integral closure of `P` in `M` is a finite `P`-module. Then this is also true for each finite extension `L` of `K`. The proof uses the normal closure of `L` and the fixed field of its automorphism group. -/
theorem finite_integralClosure_of_isPurelyInseparable (P K : Type*) [CommRing P] [IsDomain P]
    [IsNoetherianRing P] [Field K] [Algebra P K] [IsFractionRing P K] (L : Type u) [Field L]
    [Algebra K L] [Algebra P L] [IsScalarTower P K L] [FiniteDimensional K L]
    (h : ∀ (M : Type u) [Field M] [Algebra K M] [Algebra P M] [IsScalarTower P K M]
      [FiniteDimensional K M] [IsPurelyInseparable K M], Module.Finite P (integralClosure P M)) :
    Module.Finite P (integralClosure P L) := by
  let L' := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let M := IntermediateField.fixedField (⊤ : Subgroup Gal(L'/K))
  have : Algebra.IsSeparable M L' := by
    have := IsGalois.of_fixed_field L' (⊤ : Subgroup Gal(L'/K))
    exact this.to_isSeparable
  have : IsPurelyInseparable K M := isPurelyInseparable_fixedField_top K L'
  have : IsScalarTower P M L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hL' : Module.Finite P (integralClosure P L') :=
    finite_integralClosure_of_tower P K M L' (h M)
  have : IsNoetherian P (integralClosure P L') := isNoetherian_of_isNoetherianRing_of_finite _ _
  let f : L →ₐ[P] L' := (IsScalarTower.toAlgHom K L L').restrictScalars P
  refine Module.Finite.of_injective (f.mapIntegralClosure).toLinearMap (fun x y hxy => ?_)
  exact Subtype.ext (f.injective (congrArg Subtype.val hxy))

/-- Let `T` be a normal Noetherian domain that is a finite `P`-algebra, with `P` Noetherian, and let `K'` be the field of fractions of `T`. If a field `M` has a `P`-algebra map to `K'`, then the integral closure of `P` in `M` is a finite `P`-module. -/
theorem finite_integralClosure_of_algHom (P T K' M : Type*) [CommRing P] [IsNoetherianRing P]
    [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [Algebra P T] [Module.Finite P T]
    [Field K'] [Algebra T K'] [IsFractionRing T K'] [Algebra P K'] [IsScalarTower P T K']
    [Field M] [Algebra P M] (ι : M →ₐ[P] K') :
    Module.Finite P (integralClosure P M) := by
  let N := LinearMap.range ((Algebra.linearMap T K').restrictScalars P)
  have hfg : N.FG := by
    change (LinearMap.range _).FG
    rw [LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map _
  have : IsNoetherian P N := isNoetherian_of_fg_of_noetherian N hfg
  have hmem : ∀ x : integralClosure P M, ι x ∈ N := by
    intro x
    have h1 : IsIntegral T (ι x) := (x.2.map ι).tower_top
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
    exact ⟨t, ht⟩
  let g : integralClosure P M →ₗ[P] N :=
    LinearMap.codRestrict N (ι.toLinearMap ∘ₗ (integralClosure P M).val.toLinearMap) hmem
  refine Module.Finite.of_injective g (fun x y hxy => ?_)
  have : ι x = ι y := congrArg Subtype.val hxy
  exact Subtype.ext (ι.injective this)


/-- Let `k'` be an extension of `k` of characteristic `p`, and let `q = p ^ e`. If each coefficient of `f` has a `q`-th root in `k'`, then the polynomial `f(X₁ ^ q, ..., Xₛ ^ q)` over `k'` is the `q`-th power of a polynomial over `k'`. -/
theorem expand_map_eq_pow {σ k k' : Type*} [Field k] [Field k'] [Algebra k k'] (p e : ℕ)
    [ExpChar k' p] (root : k → k') (f : MvPolynomial σ k)
    (hroot : ∀ c ∈ f.coeffs, root c ^ p ^ e = algebraMap k k' c) :
    MvPolynomial.expand (p ^ e) (MvPolynomial.map (algebraMap k k') f) =
      (∑ α ∈ f.support, MvPolynomial.monomial α (root (f.coeff α))) ^ p ^ e := by
  rw [← MvPolynomial.map_iterateFrobenius_expand, MvPolynomial.map_expand]
  congr 1
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff f]
  simp only [map_sum, MvPolynomial.map_monomial, iterateFrobenius_def]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  rw [hroot _ (MvPolynomial.coeff_mem_coeffs α (MvPolynomial.mem_support_iff.mp hα))]


/-- The map `k[X₁, ..., Xₛ] → k'[X₁, ..., Xₛ]` that sends `Xᵢ` to `Xᵢ ^ q`. -/
noncomputable def expandMap (σ k k' : Type*) [Field k] [Field k'] [Algebra k k'] (q : ℕ) :
    MvPolynomial σ k →+* MvPolynomial σ k' :=
  (MvPolynomial.expand q).toRingHom.comp (MvPolynomial.map (algebraMap k k'))

theorem expandMap_C {σ k k' : Type*} [Field k] [Field k'] [Algebra k k'] (q : ℕ) (c : k) :
    expandMap σ k k' q (MvPolynomial.C c) = MvPolynomial.C (algebraMap k k' c) := by
  simp [expandMap]

theorem expandMap_X {σ k k' : Type*} [Field k] [Field k'] [Algebra k k'] (q : ℕ) (i : σ) :
    expandMap σ k k' q (MvPolynomial.X i) = MvPolynomial.X i ^ q := by
  simp [expandMap]

/-- If `k'` is finite over `k` and `q > 0`, then `k'[X₁, ..., Xₛ]` is finite over `k[X₁, ..., Xₛ]` by the map `Xᵢ ↦ Xᵢ ^ q`. -/
theorem expandMap_finite (σ k k' : Type*) [Finite σ] [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] {q : ℕ} (hq : 0 < q) : (expandMap σ k k' q).Finite := by
  let : Algebra (MvPolynomial σ k) (MvPolynomial σ k') := (expandMap σ k k' q).toAlgebra
  have : IsScalarTower k (MvPolynomial σ k) (MvPolynomial σ k') :=
    IsScalarTower.of_algebraMap_eq (fun c => by
      rw [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq, expandMap_C]; rfl)
  have : Algebra.FiniteType k (MvPolynomial σ k') := Algebra.FiniteType.trans (S := k')
    inferInstance inferInstance
  have : Algebra.FiniteType (MvPolynomial σ k) (MvPolynomial σ k') :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  have : Algebra.IsIntegral (MvPolynomial σ k) (MvPolynomial σ k') := by
    constructor
    intro f
    induction f using MvPolynomial.induction_on with
    | C a =>
      have h : IsIntegral k (MvPolynomial.C a : MvPolynomial σ k') :=
        (Algebra.IsIntegral.isIntegral (R := k) a).map (IsScalarTower.toAlgHom k k' _)
      exact h.tower_top
    | add f g hf hg => exact hf.add hg
    | mul_X f i hf =>
      refine hf.mul ⟨X ^ q - C (MvPolynomial.X i), monic_X_pow_sub_C _ hq.ne', ?_⟩
      simp [RingHom.algebraMap_toAlgebra, expandMap_X]
  exact Algebra.IsIntegral.finite

theorem expandMap_injective (σ k k' : Type*) [Field k] [Field k'] [Algebra k k'] (p e : ℕ)
    [ExpChar k' p] : Function.Injective (expandMap σ k k' (p ^ e)) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h := MvPolynomial.map_iterateFrobenius_expand p (MvPolynomial.map (algebraMap k k') f) e
  rw [show MvPolynomial.expand (p ^ e) (MvPolynomial.map (algebraMap k k') f) = 0 from hf,
    map_zero] at h
  have h2 : MvPolynomial.map (algebraMap k k') f = 0 :=
    (pow_eq_zero_iff (pow_pos (expChar_pos k' p) e).ne').mp h.symm
  exact MvPolynomial.map_injective _ (algebraMap k k').injective (h2.trans (map_zero _).symm)



/-- Let `k` be a field of characteristic `p > 0`, let `P = k[X₁, ..., Xₛ]`, and let `M` be a finite purely inseparable extension of `Frac P`. Then the integral closure of `P` in `M` is a finite `P`-module. -/
theorem finite_integralClosure_mvPolynomial_of_isPurelyInseparable (k : Type u) [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (s : ℕ) (M : Type v) [Field M]
    [Algebra (FractionRing (MvPolynomial (Fin s) k)) M] [Algebra (MvPolynomial (Fin s) k) M]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) M]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) M]
    [IsPurelyInseparable (FractionRing (MvPolynomial (Fin s) k)) M] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) M) := by
  classical
  set P := MvPolynomial (Fin s) k
  set K := FractionRing P
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  set e := IsPurelyInseparable.exponent K M
  set q := p ^ e
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos e
  let b := Module.finBasis K M
  have ha : ∀ j, ∃ a : K, algebraMap K M a = b j ^ q := fun j =>
    IsPurelyInseparable.exponent_def' K p (b j)
  choose a ha using ha
  have hfg : ∀ j, ∃ x : P × P⁰, IsLocalization.mk' K x.1 x.2 = a j := fun j =>
    IsLocalization.mk'_surjective P⁰ (a j)
  choose fg hfg using hfg
  let S : Finset k := Finset.univ.biUnion (fun j => (fg j).1.coeffs ∪ ((fg j).2 : P).coeffs)
  let Ω := AlgebraicClosure k
  have hrt : ∀ c : k, ∃ r : Ω, r ^ q = algebraMap k Ω c := fun c =>
    IsAlgClosed.exists_pow_nat_eq _ hq
  choose rt hrt using hrt
  let k' := IntermediateField.adjoin k (↑(S.image rt) : Set Ω)
  have : FiniteDimensional k k' :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  let root : k → k' := fun c => if hc : c ∈ S then
    ⟨rt c, IntermediateField.subset_adjoin k _ (by simpa using Finset.mem_image_of_mem rt hc)⟩
    else 0
  have hroot : ∀ c ∈ S, root c ^ q = algebraMap k k' c := by
    intro c hc
    apply (algebraMap k' Ω).injective
    rw [map_pow, ← IsScalarTower.algebraMap_apply, ← hrt c]
    simp only [root, hc, ↓reduceDIte]
    rfl
  let T := MvPolynomial (Fin s) k'
  let φ := expandMap (Fin s) k k' q
  let : Algebra P T := φ.toAlgebra
  have : Module.Finite P T := expandMap_finite (Fin s) k k' hq
  let K' := FractionRing T
  have hinj : Function.Injective (algebraMap P K') := by
    rw [IsScalarTower.algebraMap_eq P T K']
    exact (IsFractionRing.injective T K').comp (expandMap_injective (Fin s) k k' p e)
  let : Algebra K K' := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower P K K' := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsFractionRing.lift_algebraMap hinj x).symm)
  have : CharP K' p := charP_of_injective_algebraMap (algebraMap K K').injective p
  have hpow : ∀ x : P, x.coeffs ⊆ S → ∃ z : T, φ x = z ^ q := fun x hx =>
    ⟨_, expand_map_eq_pow p e root x (fun c hc => hroot c (hx hc))⟩
  have hsplit : ∀ j, ((minpoly K (b j)).map (algebraMap K K')).Splits := by
    intro j
    obtain ⟨z1, hz1⟩ := hpow (fg j).1 (fun c hc => Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_union_left _ hc⟩)
    obtain ⟨z2, hz2⟩ := hpow ((fg j).2 : P) (fun c hc => Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_union_right _ hc⟩)
    have hz : algebraMap K K' (a j) =
        (algebraMap T K' z1 / algebraMap T K' z2) ^ q := by
      rw [← hfg j, RingHom.algebraMap_toAlgebra, IsFractionRing.lift_mk', div_pow,
        ← map_pow, ← map_pow, ← hz1, ← hz2]
      rfl
    have hdvd : minpoly K (b j) ∣ X ^ q - C (a j) :=
      minpoly.dvd K (b j) (by simp [ha j])
    have hne : (X ^ q - C (algebraMap K K' (a j)) : K'[X]) ≠ 0 :=
      (monic_X_pow_sub_C _ hq.ne').ne_zero
    refine Splits.of_dvd (g := X ^ q - C (algebraMap K K' (a j))) ?_ hne ?_
    · rw [hz, C_pow, ← sub_pow_char_pow]
      exact (Splits.X_sub_C _).pow _
    · simpa using Polynomial.map_dvd (algebraMap K K') hdvd
  have hadj : IntermediateField.adjoin K (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← b.sum_repr x]
    exact sum_mem (fun j _ => IntermediateField.smul_mem _
      (IntermediateField.subset_adjoin K (Set.range b) (Set.mem_range_self j)))
  obtain ⟨ι⟩ := IntermediateField.nonempty_algHom_of_adjoin_splits (fun x hx => by
    obtain ⟨j, rfl⟩ := hx
    exact ⟨Algebra.IsIntegral.isIntegral _, hsplit j⟩) hadj
  have : IsIntegrallyClosed T := UniqueFactorizationMonoid.instIsIntegrallyClosed
  exact finite_integralClosure_of_algHom P T K' M (ι.restrictScalars P)

/-- Let `k` be a field and let `L` be a finite extension of the field of fractions of `P = k[X₁, ..., Xₛ]`. Then the integral closure of `P` in `L` is a finite `P`-module. -/
theorem finite_integralClosure_mvPolynomial (k : Type u) [Field k] (s : ℕ) (L : Type u) [Field L]
    [Algebra (FractionRing (MvPolynomial (Fin s) k)) L] [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    refine finite_integralClosure_of_isPurelyInseparable (MvPolynomial (Fin s) k)
      (FractionRing (MvPolynomial (Fin s) k)) L ?_
    intro M _ _ _ _ _ _
    exact finite_integralClosure_mvPolynomial_of_isPurelyInseparable k p s M
  · have : CharZero k := CharP.charP_to_charZero k
    have : CharZero (FractionRing (MvPolynomial (Fin s) k)) :=
      charZero_of_injective_algebraMap (algebraMap k _).injective
    have : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin s) k)) L :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsIntegralClosure.finite _ (FractionRing (MvPolynomial (Fin s) k)) L _

/-- **Finiteness of the normalization** (E. Noether). Let `A` be a domain that is a finitely generated algebra over a field `k`. Then the integral closure of `A` in `Frac A` is a finite `A`-module. -/
theorem finite_integralClosure (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] : Module.Finite A (integralClosure A (FractionRing A)) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  have : IsTorsionFree (MvPolynomial (Fin s) k) A :=
    Module.IsTorsionFree.trans_faithfulSMul (R := MvPolynomial (Fin s) k) (A := A) (M := A)
  exact finite_integralClosure_of_finite_of_finite (MvPolynomial (Fin s) k) A
    (finite_integralClosure_mvPolynomial k s (FractionRing A))

end Singularity.Algebra
