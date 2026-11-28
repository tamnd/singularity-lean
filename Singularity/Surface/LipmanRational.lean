/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Rational singularities: the algebraic steps

This file proves the commutative algebra steps of four results of Volume 4, Section 2.1 of
the handbook (Lipman's proof, rational singularities). The scheme theory around these steps is
not formalised here.

* `Singularity.Lipman.subalgebra_eq_bot_of_finite`: Lemma 2.1.2, part 1, affine step. Let `R` be
  an integrally closed domain with field of fractions `K`. A subalgebra of `K` that is a finite
  `R`-module is equal to `R`.
* `Singularity.Lipman.subsingleton_of_length_le`: Proposition 2.1.7, length step. In a short
  exact sequence `0 → M → M' → Q → 0` with `M` of finite length and `ℓ(M') ≤ ℓ(M)`, the module
  `Q` is zero.
* `Singularity.Lipman.length_le_of_surjective'`: Proposition 2.1.9, part 2, length step. A
  quotient module has at most the length of the module.
* `Singularity.Lipman.diagQuotInf`, `Singularity.Lipman.diffQuotSup` and
  `Singularity.Lipman.exact_diagQuotInf_diffQuotSup`: Corollary 2.1.10, part 2. For ideals
  `I, J` of a ring `R`, the sequence `0 → R/(I ∩ J) → R/I × R/J → R/(I + J) → 0` is exact.
* `Singularity.Lipman.length_quot_sup_le_one`: Corollary 2.1.10, part 2, length count. Let `R`
  be an `A`-algebra and let `R/I` and `R/J` have `A`-length 1. Then `R/(I + J)` has `A`-length
  at most 1.

Not proved: the statements about schemes, normal modifications, cohomology, direct images and
the Leray spectral sequence. In particular the passage from the exact sequence of rings to the
exact sequence of sheaves and to `H^0` in Corollary 2.1.10 is not proved. Theorem 2.1.6 (the
bound of Lipman) is not proved.
-/

namespace Singularity

namespace Lipman

section Integral

variable {R K : Type*} [CommRing R] [IsIntegrallyClosed R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Lemma 2.1.2, part 1, affine step. A subalgebra of the field of fractions of an integrally
closed domain `R` that is a finite `R`-module is equal to `R`. -/
theorem subalgebra_eq_bot_of_finite (S : Subalgebra R K) [Module.Finite R S] : S = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have h : IsIntegral R (⟨x, hx⟩ : S) := Algebra.IsIntegral.isIntegral _
  have h' : IsIntegral R x := by simpa using h.map S.val
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact Algebra.mem_bot.mpr ⟨y, rfl⟩

end Integral

section Length

variable {A M M' Q : Type*} [Ring A] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup Q]
  [Module A M] [Module A M'] [Module A Q]

/-- Proposition 2.1.7, length step. Let `0 → M → M' → Q → 0` be exact, let `M` have finite
length, and let `ℓ(M') ≤ ℓ(M)`. Then `Q` is zero. -/
theorem subsingleton_of_length_le (f : M →ₗ[A] M') (g : M' →ₗ[A] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    (hM : Module.length A M ≠ ⊤) (hle : Module.length A M' ≤ Module.length A M) :
    Subsingleton Q := by
  rw [← Module.length_eq_zero_iff (R := A)]
  rw [Module.length_eq_add_of_exact f g hf hg H] at hle
  lift Module.length A M to ℕ using hM with m
  generalize Module.length A Q = q at hle ⊢
  induction q using ENat.recTopCoe with
  | top =>
    rw [add_top, top_le_iff] at hle
    exact absurd hle (ENat.natCast_ne_top m)
  | coe n =>
    norm_cast at hle ⊢
    omega

/-- Proposition 2.1.9, part 2, length step. A quotient module has at most the length of the
module. -/
theorem length_le_of_surjective' (g : M' →ₗ[A] Q) (hg : Function.Surjective g) :
    Module.length A Q ≤ Module.length A M' :=
  Module.length_le_of_surjective g hg

end Length

section Ideals

variable {R : Type*} [CommRing R] (I J : Ideal R)

/-- The diagonal map `R/(I ∩ J) → R/I × R/J`. -/
noncomputable def diagQuotInf : (R ⧸ (I ⊓ J)) →ₗ[R] (R ⧸ I) × (R ⧸ J) :=
  LinearMap.prod (Submodule.factor inf_le_left) (Submodule.factor inf_le_right)

/-- The difference map `R/I × R/J → R/(I + J)`, given by `(a, b) ↦ a - b`. -/
noncomputable def diffQuotSup : (R ⧸ I) × (R ⧸ J) →ₗ[R] R ⧸ (I ⊔ J) :=
  LinearMap.coprod (Submodule.factor le_sup_left) (-Submodule.factor le_sup_right)

theorem diagQuotInf_mk (r : R) :
    diagQuotInf I J (Submodule.Quotient.mk r) =
      (Submodule.Quotient.mk r, Submodule.Quotient.mk r) := rfl

theorem diffQuotSup_mk (a b : R) :
    diffQuotSup I J (Submodule.Quotient.mk a, Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (a - b) := by
  change (Submodule.Quotient.mk a : R ⧸ (I ⊔ J)) + -Submodule.Quotient.mk b =
    Submodule.Quotient.mk (a - b)
  rw [Submodule.Quotient.mk_sub, sub_eq_add_neg]

theorem diagQuotInf_injective : Function.Injective (diagQuotInf I J) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, diagQuotInf_mk, Prod.mk_eq_zero] at hx
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  exact ⟨(Submodule.Quotient.mk_eq_zero _).mp hx.1, (Submodule.Quotient.mk_eq_zero _).mp hx.2⟩

theorem diffQuotSup_surjective : Function.Surjective (diffQuotSup I J) := by
  intro x
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨(Submodule.Quotient.mk r, 0), by
    simpa using diffQuotSup_mk I J r 0⟩

/-- Corollary 2.1.10, part 2. The sequence `0 → R/(I ∩ J) → R/I × R/J → R/(I + J) → 0` is
exact in the middle. -/
theorem exact_diagQuotInf_diffQuotSup : Function.Exact (diagQuotInf I J) (diffQuotSup I J) := by
  intro y
  obtain ⟨a', b'⟩ := y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a'
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b'
  rw [diffQuotSup_mk, Submodule.Quotient.mk_eq_zero, Set.mem_range]
  constructor
  · intro h
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h
    refine ⟨Submodule.Quotient.mk (a - i), ?_⟩
    rw [diagQuotInf_mk, Prod.mk.injEq, Submodule.Quotient.eq, Submodule.Quotient.eq]
    refine ⟨by simpa using I.neg_mem hi, ?_⟩
    rw [sub_right_comm, ← eq_sub_of_add_eq' hij]
    exact hj
  · rintro ⟨x, hx⟩
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [diagQuotInf_mk, Prod.mk.injEq, Submodule.Quotient.eq, Submodule.Quotient.eq] at hx
    rw [← sub_sub_sub_cancel_left b a r]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right hx.2) (Submodule.mem_sup_left hx.1)

variable {A : Type*} [CommRing A] [Algebra A R]

/-- Corollary 2.1.10, part 2, length count. Let `R` be an `A`-algebra and let `R/I` and `R/J`
have `A`-length 1. Then `R/(I + J)` has `A`-length at most 1. -/
theorem length_quot_sup_le_one (hI : Module.length A (R ⧸ I) = 1)
    (hJ : Module.length A (R ⧸ J) = 1) : Module.length A (R ⧸ (I ⊔ J)) ≤ 1 := by
  have hex := Module.length_eq_add_of_exact ((diagQuotInf I J).restrictScalars A)
    ((diffQuotSup I J).restrictScalars A) (diagQuotInf_injective I J)
    (diffQuotSup_surjective I J) (exact_diagQuotInf_diffQuotSup I J)
  rw [Module.length_prod, hI, hJ] at hex
  have hnt : Nontrivial (R ⧸ (I ⊓ J)) := by
    have : Nontrivial (R ⧸ I) := by
      rw [← Module.length_pos_iff (R := A), hI]
      exact zero_lt_one
    rw [Submodule.Quotient.nontrivial_iff] at this ⊢
    exact ne_top_of_le_ne_top this inf_le_left
  have hpos : 1 ≤ Module.length A (R ⧸ (I ⊓ J)) :=
    Order.one_le_iff_pos.mpr (Module.length_pos_iff.mpr hnt)
  set a := Module.length A (R ⧸ (I ⊓ J))
  set b := Module.length A (R ⧸ (I ⊔ J))
  have h2 : (1 : ℕ∞) + 1 = 2 := one_add_one_eq_two
  rw [h2] at hex
  have hb : b ≠ ⊤ := by
    intro h
    rw [h, add_top] at hex
    exact ENat.natCast_ne_top 2 hex
  have ha : a ≠ ⊤ := by
    intro h
    rw [h, top_add] at hex
    exact ENat.natCast_ne_top 2 hex
  lift a to ℕ using ha with m
  lift b to ℕ using hb with n
  norm_cast at hex hpos ⊢
  omega

end Ideals

end Lipman

end Singularity
