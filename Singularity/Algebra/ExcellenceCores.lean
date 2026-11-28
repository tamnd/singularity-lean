/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Scheme.RegularLocusJ2
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# G-rings, catenary rings and excellent rings

This file proves parts of Volume 1, Chapter 5 of the handbook.

## Main definitions

* `IsGeometricallyRegular k B`: `B ⊗_k k'` is a regular ring for each finite field extension `k'`
  of `k` (Definition 5.1.1).
* `IsRegularAlgebra A B`: `B` is flat over `A` and each fibre `κ(p) ⊗_A B` is geometrically
  regular over `κ(p)` (Definition 5.1.4).
* `IsGRing A`: for each prime `p`, the map `A_p → (A_p)^` is regular (Definition 5.1.5).
* `IsCatenary A`, `IsUniversallyCatenary A`: Definition 5.2.4. A chain of primes is maximal if each
  step is a covering relation.
* `IsQuasiExcellent A`, `IsExcellent A`: Definition 5.2.7.

## Main results

* `IsGeometricallyRegular.isRegularRing`: a geometrically regular ring is regular. This is one
  implication of Proposition 5.1.2.
* `isGeometricallyRegular_of_charZero`: a field `L` over a field `K` of characteristic `0` is
  geometrically regular. This is the other implication of Proposition 5.1.2 when `B` is a field.
  It is also the last step of the proof of Proposition 5.1.6.
* `isRegularAlgebra_adicCompletion`: if `A` is `I`-adically complete, then `A → Â` is regular.
  For a complete local ring this says that the formal fibres of `A` itself are geometrically
  regular. This is the easy part of Theorem 5.1.7, part 4, as the handbook explains after it.
* `isRegularAlgebra_adicCompletion_bot`: for a domain `A`, the map `A_0 → (A_0)^` is regular. This
  is the step of the proof of Proposition 5.1.6 at the prime `0`.
* `isGRing_of_field`: a field is a G-ring (the remark after Definition 5.1.5).
* `isCatenary_of_krullDimLE_one`: a ring of dimension at most `1` is catenary. So a field and a
  Dedekind domain are catenary (`isCatenary_of_isDedekindDomain`). This is a special case of
  Theorem 5.2.5, without the word universally.
* `IsUniversallyCatenary.of_finiteType`, `IsUniversallyCatenary.of_surjective`: a finitely
  generated algebra and a quotient of a universally catenary ring are universally catenary. The
  second is the last step of the proof of Proposition 5.2.6.
* `isQuasiExcellent_of_field`: a field is quasi-excellent (Theorem 5.2.8, part 1, for a field,
  without the universally catenary property).
* `IsQuasiExcellent.isJ2_of_finiteType`, `IsExcellent.isJ2_of_finiteType`,
  `IsExcellent.isUniversallyCatenary_of_finiteType`: Theorem 5.2.8, part 2, for the J-2 and the
  universally catenary property and for finitely generated algebras.
* `isJ2_of_finiteType_field`: a ring of finite type over a field is Noetherian and J-2. This is the
  part of Corollary 5.2.9 that the handbook proves.
* `tmul_sub_tmul_pow_eq_zero`, `tmul_eq_tmul_of_isReduced`: Step 3 of the proof of Proposition
  5.3.8. In characteristic `p`, if `a ^ p = b ^ p = c` with `c ∈ R`, then `a ⊗ 1 - 1 ⊗ b` is
  nilpotent, so it is `0` in a reduced ring.
* `not_finite_of_not_finite_of_finite`: the last step of Example 5.3.9. If `R'` is not finite
  over `R` and `D` is finite over `R`, then `R'` is not finite over `D`.

## What is not proved

Proposition 5.1.2 is proved in one direction, and in the other direction only when `B` is a field.
Proposition 5.1.6 is not proved: the completion of a discrete valuation ring and its generic formal
fibre are not studied here. Theorem 5.1.7 is not proved, except the triviality of the formal fibres
of a complete ring. Theorem 5.2.5 is proved only for rings of dimension at most `1`, and only for
the catenary property. Proposition 5.2.6 is proved only in its last step. Theorem 5.2.8 is not
proved for complete local rings, for Dedekind domains or for localizations, the universally
catenary property of a field is not proved, and the G-ring property of a finitely generated algebra
is not proved. Corollary 5.2.9 is proved only for the J-2 property. Theorem 5.3.6 is not proved
here; its J-2 part is `Singularity.isJ2_of_resolution` (Corollary 5.3.5). Proposition 5.3.8 and
Example 5.3.9 are proved only in the steps listed above, and the ring of Nagata is not built.
-/

open IsLocalRing TensorProduct

universe u v w

namespace Singularity

namespace Algebra

/-! ### Geometric regularity -/

/-- A ring that is Artinian and reduced is regular: each local ring is a field. -/
theorem isRegularRing_of_isArtinianRing_of_isReduced (R : Type*) [CommRing R]
    [IsArtinianRing R] [IsReduced R] : IsRegularRing R := by
  rw [isRegularRing_iff]
  intro p _
  have hf : IsField (Localization.AtPrime p) :=
    IsArtinianRing.isField_of_isReduced_of_isLocalRing _
  let _ : Field (Localization.AtPrime p) := hf.toField
  infer_instance

/-- Let `k` be a field. A `k`-algebra `B` is geometrically regular over `k` if `B ⊗_k k'` is a
regular ring for each finite field extension `k'` of `k` (Definition 5.1.1). The fields `k'` are
taken in the universe of `k`. -/
def IsGeometricallyRegular (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B] :
    Prop :=
  ∀ (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k'], IsRegularRing (B ⊗[k] k')

/-- A geometrically regular ring is regular: take `k' = k`. This is one implication of
Proposition 5.1.2. -/
theorem IsGeometricallyRegular.isRegularRing {k : Type u} {B : Type v} [Field k] [CommRing B]
    [Algebra k B] (h : IsGeometricallyRegular k B) : IsRegularRing B := by
  have := h k
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.rid k k B).toRingEquiv

/-- Geometric regularity passes along an isomorphism of `k`-algebras. -/
theorem IsGeometricallyRegular.of_algEquiv {k : Type u} {B : Type v} {C : Type w} [Field k]
    [CommRing B] [CommRing C] [Algebra k B] [Algebra k C] (e : B ≃ₐ[k] C)
    (h : IsGeometricallyRegular k B) :
    IsGeometricallyRegular k C := by
  intro k' _ _ _
  have := h k'
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : k' ≃ₐ[k] k')).toRingEquiv

/-- A field is geometrically regular over itself, since `k ⊗_k k' = k'` is a field. -/
theorem isGeometricallyRegular_self (k : Type u) [Field k] : IsGeometricallyRegular k k := by
  intro k' _ _ _
  have : IsRegularRing k' := isRegularRing_of_isArtinianRing_of_isReduced k'
  exact IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.comm k k k').trans (Algebra.TensorProduct.rid k k k')).toRingEquiv.symm

/-- Let `K` be a field of characteristic `0` and let `L` be a field extension of `K`. Then `L` is
geometrically regular over `K`. This is Proposition 5.1.2 in the direction "regular implies
geometrically regular" when `B` is a field. For a finite extension `k'` of `K`, the ring
`L ⊗_K k'` is finite over `L`, so it is Artinian. It is unramified over `L`, because `k'` is
separable over `K`, so it is reduced. An Artinian reduced ring is regular. -/
theorem isGeometricallyRegular_of_charZero (K : Type u) (L : Type v) [Field K] [CharZero K]
    [Field L] [Algebra K L] : IsGeometricallyRegular K L := by
  intro k' _ _ _
  have : Algebra.FormallyUnramified K k' := .of_isSeparable K k'
  have : IsReduced (L ⊗[K] k') := Algebra.FormallyUnramified.isReduced_of_field L _
  have : IsArtinianRing (L ⊗[K] k') := IsArtinianRing.of_finite L _
  exact isRegularRing_of_isArtinianRing_of_isReduced _

/-! ### Regular homomorphisms and G-rings -/

/-- An `A`-algebra `B` is regular if it is flat and, for each prime `p` of `A`, the fibre
`κ(p) ⊗_A B` is geometrically regular over `κ(p)` (Definition 5.1.4). -/
def IsRegularAlgebra (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  Module.Flat A B ∧ ∀ (p : Ideal A) [p.IsPrime],
    IsGeometricallyRegular p.ResidueField (p.ResidueField ⊗[A] B)

/-- If `A → B` is an isomorphism of `A`-algebras, then `B` is a regular `A`-algebra. Each fibre
`κ(p) ⊗_A B` is `κ(p)`. -/
theorem isRegularAlgebra_of_algEquiv {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (e : A ≃ₐ[A] B) : IsRegularAlgebra A B := by
  refine ⟨Module.Flat.of_linearEquiv e.symm.toLinearEquiv, fun p _ => ?_⟩
  exact (isGeometricallyRegular_self p.ResidueField).of_algEquiv
    ((Algebra.TensorProduct.rid A p.ResidueField p.ResidueField).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] _) e))

/-- If `A` is `I`-adically complete, then `A → Â` is regular. For a complete local ring this says
that the formal fibres of `A` are geometrically regular. This is the easy part of Theorem 5.1.7,
part 4: the hard part is about the localizations of `A`. -/
theorem isRegularAlgebra_adicCompletion {A : Type u} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] : IsRegularAlgebra A (AdicCompletion I A) :=
  isRegularAlgebra_of_algEquiv (AdicCompletion.ofAlgEquiv I)

/-- A ring `A` is a G-ring if, for each prime `p` of `A`, the map `A_p → (A_p)^` from `A_p` to its
completion at the maximal ideal is regular (Definition 5.1.5). The definition does not ask that
`A` is Noetherian. -/
def IsGRing (A : Type u) [CommRing A] : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], IsRegularAlgebra (Localization.AtPrime p)
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))

/-- Let `A` be a domain. Then `A_0 → (A_0)^` is regular. The ring `A_0` is the field of fractions
of `A`, its maximal ideal is `0`, and it is complete. This is the step of the proof of
Proposition 5.1.6 at the prime `0`. -/
theorem isRegularAlgebra_adicCompletion_bot (A : Type u) [CommRing A] [IsDomain A] :
    IsRegularAlgebra (Localization.AtPrime (⊥ : Ideal A))
      (AdicCompletion (maximalIdeal (Localization.AtPrime (⊥ : Ideal A)))
        (Localization.AtPrime (⊥ : Ideal A))) := by
  have hm : maximalIdeal (Localization.AtPrime (⊥ : Ideal A)) = ⊥ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]
  rw [hm]
  exact isRegularAlgebra_adicCompletion ⊥

/-- A field is a G-ring. Its only prime is `0`, and its local ring there is complete. -/
theorem isGRing_of_field (K : Type u) [Field K] : IsGRing K := by
  intro p hp
  obtain rfl : p = ⊥ := Ideal.eq_bot_of_prime p
  exact isRegularAlgebra_adicCompletion_bot K

/-! ### Catenary rings -/

/-- A ring `A` is catenary if any two maximal chains of primes with the same first and last prime
have the same length (Definition 5.2.4). A chain is maximal if each step is a covering relation.
The definition does not ask that `A` is Noetherian. -/
def IsCatenary (A : Type u) [CommRing A] : Prop :=
  ∀ s t : LTSeries (PrimeSpectrum A),
    (∀ i : Fin s.length, s.toFun i.castSucc ⋖ s.toFun i.succ) →
    (∀ i : Fin t.length, t.toFun i.castSucc ⋖ t.toFun i.succ) →
    s.head = t.head → s.last = t.last → s.length = t.length

/-- A ring `A` is universally catenary if each finitely generated `A`-algebra is catenary
(Definition 5.2.4). The algebras are taken in the universe of `A`. -/
def IsUniversallyCatenary (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B], IsCatenary B

/-- A universally catenary ring is catenary. -/
theorem IsUniversallyCatenary.isCatenary {A : Type u} [CommRing A] (h : IsUniversallyCatenary A) :
    IsCatenary A :=
  h A

/-- A finitely generated algebra over a universally catenary ring is universally catenary. -/
theorem IsUniversallyCatenary.of_finiteType {A : Type u} [CommRing A] (h : IsUniversallyCatenary A)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B] : IsUniversallyCatenary B := by
  intro C _ _ _
  let _ : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType A C := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  exact h C

/-- A quotient of a universally catenary ring is universally catenary. This is the last step of
the proof of Proposition 5.2.6. -/
theorem IsUniversallyCatenary.of_surjective {A B : Type u} [CommRing A] [CommRing B]
    (h : IsUniversallyCatenary A) (f : A →+* B) (hf : Function.Surjective f) :
    IsUniversallyCatenary B := by
  let _ : Algebra A B := f.toAlgebra
  have : Algebra.FiniteType A B := RingHom.FiniteType.of_surjective f hf
  exact h.of_finiteType B

/-- In a ring of dimension at most `1`, a chain of primes has length at most `1`. -/
theorem LTSeries.length_le_one_of_krullDimLE_one {A : Type u} [CommRing A] [Ring.KrullDimLE 1 A]
    (s : LTSeries (PrimeSpectrum A)) : s.length ≤ 1 := by
  have h1 := Order.LTSeries.length_le_krullDim s
  have h2 : Order.krullDim (PrimeSpectrum A) ≤ (1 : ℕ) := Order.KrullDimLE.krullDim_le
  have h3 : (s.length : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := h1.trans h2
  exact_mod_cast h3

/-- A chain of primes of positive length has its first prime strictly below its last prime. -/
theorem LTSeries.head_lt_last_of_length_ne_zero {α : Type*} [Preorder α] (s : LTSeries α)
    (h : s.length ≠ 0) : s.head < s.last :=
  s.strictMono (Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero h))

/-- A ring of dimension at most `1` is catenary. Two chains with the same ends have length `0` if
the ends are equal, and length `1` if not. This is a special case of Theorem 5.2.5. -/
theorem isCatenary_of_krullDimLE_one (A : Type u) [CommRing A] [Ring.KrullDimLE 1 A] :
    IsCatenary A := by
  intro s t _ _ hh hl
  have hs := LTSeries.length_le_one_of_krullDimLE_one s
  have ht := LTSeries.length_le_one_of_krullDimLE_one t
  by_cases h0 : s.length = 0
  · by_contra hne
    have hlt := LTSeries.head_lt_last_of_length_ne_zero t (by omega)
    have heq : s.head = s.last := by
      simp only [RelSeries.head, RelSeries.last]
      congr 1
      ext
      simp [h0]
    rw [← hh, ← hl, heq] at hlt
    exact lt_irrefl _ hlt
  · by_contra hne
    have ht0 : t.length = 0 := by omega
    have hlt := LTSeries.head_lt_last_of_length_ne_zero s h0
    have heq : t.head = t.last := by
      simp only [RelSeries.head, RelSeries.last]
      congr 1
      ext
      simp [ht0]
    rw [hh, hl, heq] at hlt
    exact lt_irrefl _ hlt

/-- A Dedekind domain is catenary, since its dimension is at most `1`. This contains the case of a
field. -/
theorem isCatenary_of_isDedekindDomain (A : Type u) [CommRing A] [IsDedekindDomain A] :
    IsCatenary A :=
  isCatenary_of_krullDimLE_one A

/-! ### Excellent rings -/

/-- A ring is quasi-excellent if it is Noetherian, a G-ring and J-2 (Definition 5.2.7). -/
structure IsQuasiExcellent (A : Type u) [CommRing A] : Prop where
  isNoetherianRing : IsNoetherianRing A
  isGRing : IsGRing A
  isJ2 : IsJ2 A

/-- A ring is excellent if it is quasi-excellent and universally catenary (Definition 5.2.7). -/
structure IsExcellent (A : Type u) [CommRing A] : Prop where
  isQuasiExcellent : IsQuasiExcellent A
  isUniversallyCatenary : IsUniversallyCatenary A

/-- A quasi-excellent ring is J-1: its regular locus is open. -/
theorem IsQuasiExcellent.isJ1 {A : Type u} [CommRing A] (h : IsQuasiExcellent A) : IsJ1 A :=
  h.isJ2.isJ1

/-- A field is quasi-excellent. This is Theorem 5.2.8, part 1, for a field, without the
universally catenary property. -/
theorem isQuasiExcellent_of_field (K : Type u) [Field K] : IsQuasiExcellent K :=
  ⟨inferInstance, isGRing_of_field K, isJ2_of_field K⟩

/-- A finitely generated algebra over a quasi-excellent ring is Noetherian and J-2. This is
Theorem 5.2.8, part 2, for the J-2 property. -/
theorem IsQuasiExcellent.isJ2_of_finiteType {A : Type u} [CommRing A] (h : IsQuasiExcellent A)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B] :
    IsNoetherianRing B ∧ IsJ2 B := by
  have := h.isNoetherianRing
  exact ⟨Algebra.FiniteType.isNoetherianRing A B, h.isJ2.of_finiteType B⟩

/-- A finitely generated algebra over an excellent ring is Noetherian and J-2. -/
theorem IsExcellent.isJ2_of_finiteType {A : Type u} [CommRing A] (h : IsExcellent A)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B] :
    IsNoetherianRing B ∧ IsJ2 B :=
  h.isQuasiExcellent.isJ2_of_finiteType B

/-- A finitely generated algebra over an excellent ring is universally catenary. This is
Theorem 5.2.8, part 2, for the universally catenary property. -/
theorem IsExcellent.isUniversallyCatenary_of_finiteType {A : Type u} [CommRing A]
    (h : IsExcellent A) (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B] :
    IsUniversallyCatenary B :=
  h.isUniversallyCatenary.of_finiteType B

/-- A ring of finite type over a field is Noetherian and J-2. This is the part of
Corollary 5.2.9 that the handbook proves. -/
theorem isJ2_of_finiteType_field (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] : IsNoetherianRing A ∧ IsJ2 A :=
  (isQuasiExcellent_of_field k).isJ2_of_finiteType A

/-! ### The example of Nagata -/

/-- Step 3 of the proof of Proposition 5.3.8. Let `R` have characteristic `p` and let `A` and `B`
be `R`-algebras. If `a ^ p` and `b ^ p` are the images of the same `c ∈ R`, then
`(a ⊗ 1 - 1 ⊗ b) ^ p = 0` in `A ⊗_R B`. -/
theorem tmul_sub_tmul_pow_eq_zero {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (p : ℕ) [hp : Fact p.Prime] [CharP R p] (a : A) (b : B) (c : R)
    (ha : a ^ p = algebraMap R A c) (hb : b ^ p = algebraMap R B c) :
    (a ⊗ₜ[R] (1 : B) - (1 : A) ⊗ₜ[R] b) ^ p = 0 := by
  cases subsingleton_or_nontrivial (A ⊗[R] B) with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    have : CharP (A ⊗[R] B) p := by
      rw [CharP.charP_iff_prime_eq_zero hp.out]
      rw [← map_natCast (algebraMap R (A ⊗[R] B)), CharP.cast_eq_zero, map_zero]
    rw [sub_pow_char, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow,
      one_pow, ha, hb, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, sub_self]

/-- Step 3 of the proof of Proposition 5.3.8, with the conclusion. If moreover `A ⊗_R B` is
reduced, then `a ⊗ 1 = 1 ⊗ b`. In the handbook `A ⊗_R B` is a domain by Step 2, and
`a ⊗ 1 ≠ 1 ⊗ b`, which gives the contradiction. -/
theorem tmul_eq_tmul_of_isReduced {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsReduced (A ⊗[R] B)] (p : ℕ) [Fact p.Prime] [CharP R p]
    (a : A) (b : B) (c : R) (ha : a ^ p = algebraMap R A c) (hb : b ^ p = algebraMap R B c) :
    a ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] b :=
  sub_eq_zero.mp (IsNilpotent.eq_zero ⟨p, tmul_sub_tmul_pow_eq_zero p a b c ha hb⟩)

/-- The last step of Example 5.3.9. Let `R → D → R'` be a tower with `D` finite over `R`. If `R'`
is not finite over `R`, then `R'` is not finite over `D`. -/
theorem not_finite_of_not_finite_of_finite (R D R' : Type*) [CommRing R] [CommRing D]
    [CommRing R'] [Algebra R D] [Algebra D R'] [Algebra R R'] [IsScalarTower R D R']
    [Module.Finite R D] (h : ¬ Module.Finite R R') : ¬ Module.Finite D R' := fun _ =>
  h (Module.Finite.trans D R')

end Algebra

end Singularity
