/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# The theorem of Lipman: the algebraic steps

This file proves the algebraic and numerical steps of two results of Volume 4, Section 2.2 of
the handbook (the theorem of Lipman). The scheme theory around these steps is not formalised.

Proposition 2.2.2 (a resolution forces a finite normalization), the affine step. Let `R` be a
Noetherian ring and let `K` be an `R`-algebra that is a field.

* `Singularity.Lipman.mem_iInf_of_isIntegral`: an intersection of subalgebras of `K` that are
  integrally closed in `K` is integrally closed in `K`. This is the step "`B` is the
  intersection of the local rings `O_{Y,y}`, so `B` is integrally closed in `K`".
* `Singularity.Lipman.integralClosure_le_of_isIntegral`: if a subalgebra `B` of `K` is
  integrally closed in `K`, then the integral closure of `R` in `K` lies in `B`.
* `Singularity.Lipman.moduleFinite_integralClosure_of_subalgebra`: if moreover `B` is a finite
  `R`-module, then the integral closure of `R` in `K` is a finite `R`-module.

Proposition 2.2.6, parts 2 and 3, the numerical steps.

* `Singularity.Lipman.monotone_of_eq_add`: a sequence with `h (i + 1) = h i + r i` in `ℕ` does
  not go down.
* `Singularity.Lipman.exists_forall_eq_zero_of_le`: if moreover `h i ≤ N` for each `i`, then
  there is `i₀` with `r i = 0` for each `i ≥ i₀`.
* `Singularity.Lipman.length_monotone_of_exact`: part 2 for modules. Let
  `0 → H i → H (i + 1) → Q i → 0` be exact for each `i`. Then `ℓ(H i)` does not go down.
* `Singularity.Lipman.exists_forall_subsingleton_of_length_le`: part 3 for modules. If moreover
  `ℓ(H i) ≤ N` for each `i`, then there is `i₀` with `Q i = 0` for each `i ≥ i₀`.

Not proved. In Proposition 2.2.2: that `Y` is integral and normal with function field `K`, the
finiteness of `Γ(π⁻¹(Spec R), O_Y)` for proper `π`, and the description of this ring as an
intersection of local rings. In Proposition 2.2.6: part 1, the identification of the modules
with `H^1(X_i, O_{X_i})` and `H^0(X_i, R^1 g_{i*} O_{X_{i+1}})`, the exact sequence from the
Leray spectral sequence, the bound of Theorem 2.1.6 (here it is a hypothesis), and the passage
from `H^0 = 0` to the vanishing of the sheaf. Theorem 2.2.1, Lemma 2.2.5 and Example 2.2.4 are
not treated here.
-/

namespace Singularity

namespace Lipman

section Normalization

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

/-- Proposition 2.2.2, intersection step. An intersection of subalgebras of `K` that are
integrally closed in `K` is integrally closed in `K`. -/
theorem mem_iInf_of_isIntegral {ι : Sort*} (S : ι → Subalgebra R K)
    (hS : ∀ i (x : K), IsIntegral (S i) x → x ∈ S i) (x : K)
    (hx : IsIntegral (⨅ i, S i : Subalgebra R K) x) : x ∈ ⨅ i, S i := by
  rw [Algebra.mem_iInf]
  intro i
  apply hS i
  have hle : (⨅ j, S j : Subalgebra R K) ≤ S i := iInf_le S i
  exact IsIntegral.map_of_comp_eq (Subalgebra.inclusion hle).toRingHom (RingHom.id K) rfl hx

/-- Proposition 2.2.2, comparison step. If a subalgebra `B` of `K` is integrally closed in `K`,
then the integral closure of `R` in `K` lies in `B`. -/
theorem integralClosure_le_of_isIntegral (B : Subalgebra R K)
    (hB : ∀ x : K, IsIntegral B x → x ∈ B) : integralClosure R K ≤ B :=
  fun x hx => hB x (IsIntegral.tower_top hx)

/-- Proposition 2.2.2, affine step. Let `R` be Noetherian, and let `B` be a subalgebra of `K`
that is integrally closed in `K` and a finite `R`-module. Then the integral closure of `R` in
`K` is a finite `R`-module. -/
theorem moduleFinite_integralClosure_of_subalgebra [IsNoetherianRing R] (B : Subalgebra R K)
    [Module.Finite R B] (hB : ∀ x : K, IsIntegral B x → x ∈ B) :
    Module.Finite R (integralClosure R K) := by
  have hle := integralClosure_le_of_isIntegral B hB
  exact Module.Finite.of_injective (Subalgebra.inclusion hle).toLinearMap
    (Subalgebra.inclusion_injective hle)

end Normalization

section Sequence

/-- Proposition 2.2.6, part 2, numerical step. A sequence with `h (i + 1) = h i + r i` in `ℕ`
does not go down. -/
theorem monotone_of_eq_add {h r : ℕ → ℕ} (hstep : ∀ i, h (i + 1) = h i + r i) :
    Monotone h :=
  monotone_nat_of_le_succ fun i => by rw [hstep i]; exact Nat.le_add_right _ _

/-- Proposition 2.2.6, part 3, numerical step. Let `h (i + 1) = h i + r i` in `ℕ`, and let
`h i ≤ N` for each `i`. Then `r i = 0` for each `i` from some index on. -/
theorem exists_forall_eq_zero_of_le {h r : ℕ → ℕ} (hstep : ∀ i, h (i + 1) = h i + r i)
    (N : ℕ) (hN : ∀ i, h i ≤ N) : ∃ i₀, ∀ i ≥ i₀, r i = 0 := by
  by_contra hne
  push Not at hne
  have hmono := monotone_of_eq_add hstep
  have key : ∀ n : ℕ, ∃ i, n ≤ h i := by
    intro n
    induction n with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, hj, hrj⟩ := hne i
      refine ⟨j + 1, ?_⟩
      rw [hstep j]
      have := hmono hj
      omega
  obtain ⟨i, hi⟩ := key (N + 1)
  have := hN i
  omega

end Sequence

section Length

variable {A : Type*} [Ring A] {H Q : ℕ → Type*} [∀ i, AddCommGroup (H i)]
  [∀ i, Module A (H i)] [∀ i, AddCommGroup (Q i)] [∀ i, Module A (Q i)]

/-- Proposition 2.2.6, part 2, for modules. Let `0 → H i → H (i + 1) → Q i → 0` be exact for
each `i`. Then the length of `H i` does not go down. -/
theorem length_monotone_of_exact (f : ∀ i, H i →ₗ[A] H (i + 1))
    (g : ∀ i, H (i + 1) →ₗ[A] Q i)
    (hf : ∀ i, Function.Injective (f i)) (hg : ∀ i, Function.Surjective (g i))
    (hfg : ∀ i, Function.Exact (f i) (g i)) :
    Monotone fun i => Module.length A (H i) :=
  monotone_nat_of_le_succ fun i => by
    rw [Module.length_eq_add_of_exact (f i) (g i) (hf i) (hg i) (hfg i)]
    exact le_self_add

/-- Proposition 2.2.6, part 3, for modules. Let `0 → H i → H (i + 1) → Q i → 0` be exact for
each `i`, and let the length of `H i` be at most `N` for each `i`. Then `Q i = 0` for each `i`
from some index on. -/
theorem exists_forall_subsingleton_of_length_le (f : ∀ i, H i →ₗ[A] H (i + 1))
    (g : ∀ i, H (i + 1) →ₗ[A] Q i) (hf : ∀ i, Function.Injective (f i))
    (hg : ∀ i, Function.Surjective (g i)) (hfg : ∀ i, Function.Exact (f i) (g i)) (N : ℕ)
    (hN : ∀ i, Module.length A (H i) ≤ N) : ∃ i₀, ∀ i ≥ i₀, Subsingleton (Q i) := by
  have hadd : ∀ i, Module.length A (H (i + 1)) = Module.length A (H i) + Module.length A (Q i) :=
    fun i => Module.length_eq_add_of_exact (f i) (g i) (hf i) (hg i) (hfg i)
  have hH : ∀ i, Module.length A (H i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (ENat.natCast_ne_top N) (hN i)
  have hQ : ∀ i, Module.length A (Q i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hH (i + 1)) (by rw [hadd i]; exact le_add_self)
  have hstep : ∀ i, (Module.length A (H (i + 1))).toNat =
      (Module.length A (H i)).toNat + (Module.length A (Q i)).toNat := fun i => by
    rw [hadd i, ENat.toNat_add (hH i) (hQ i)]
  have hNat : ∀ i, (Module.length A (H i)).toNat ≤ N := fun i => by
    have := ENat.toNat_le_toNat (hN i) (ENat.natCast_ne_top N)
    simpa using this
  obtain ⟨i₀, hi₀⟩ := exists_forall_eq_zero_of_le hstep N hNat
  refine ⟨i₀, fun i hi => ?_⟩
  rw [← Module.length_eq_zero_iff (R := A)]
  have h0 := hi₀ i hi
  rw [ENat.toNat_eq_zero] at h0
  exact h0.resolve_right (hQ i)

end Length

end Lipman

end Singularity
