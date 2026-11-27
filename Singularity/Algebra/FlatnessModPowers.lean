/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Flatness modulo the powers of an ideal

This file proves Volume 1, Lemma 6.4.3 of the handbook. Let `A → B` be a map of Noetherian rings and let `I` be an ideal of `A` such that `IB` is in the Jacobson radical of `B`. If `(A ⧸ I ^ n) ⊗[A] B` is flat over `A ⧸ I ^ n` for each `n`, then `B` is flat over `A`.

The handbook states the hypothesis with `B ⧸ I ^ n B`. The Lean statement uses `(A ⧸ I ^ n) ⊗[A] B`, which is isomorphic to `B ⧸ I ^ n B`. The file does not prove this isomorphism.

The proof follows the handbook, with the ideal criterion of flatness in place of all inclusions of finitely generated modules. Let `J` be an ideal of `A` and let `z` be in the kernel of `B ⊗[A] J → B`. For each `n`, the image `Q` of `J` in `A' = A ⧸ I ^ n` is an ideal of `A'`, and `B ⊗[A] Q → B ⊗[A] A'` is injective because `A' ⊗[A] B` is flat over `A'` (`lTensor_subtype_injective_of_flat_baseChange`). So `z` comes from `B ⊗[A] (J ∩ I ^ n)`, by the right exactness of the tensor product. The lemma of Artin and Rees gives `J ∩ I ^ n ⊆ I ^ (n - k) J`, so `z ∈ I ^ (n - k) (B ⊗[A] J)` for each `n ≥ k`. The intersection theorem of Krull for the finite `B`-module `B ⊗[A] J` then gives `z = 0`.

* `Singularity.Algebra.lTensor_subtype_injective_of_flat_baseChange`: the step `Q ⊗_A B = Q ⊗_{A'} (A' ⊗_A B)`.
* `Singularity.Algebra.mem_smul_top_of_coe_mem_smul`: an element of `J` in `I • J` is in `I • ⊤` as an element of `J`.
* `Singularity.Algebra.lTensor_mem_smul_top`: the image of `B ⊗[A] P` in `B ⊗[A] N` is in `I • ⊤` when `P ≤ I • ⊤`.
* `Singularity.Algebra.flat_of_flat_quotient_pow`: Lemma 6.4.3.

Corollary 6.4.4 in general, for each extension of fields `L ⊆ K`, needs the isomorphism `(A ⧸ I ^ n) ⊗[A] B = K ⊗_L (A ⧸ I ^ n)` for `A = L[[y]]` and `B = K[[y]]`. That step is not in Lean.
-/

namespace Singularity.Algebra

open TensorProduct LinearMap

section FlatnessModPowers

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Let `A' = A ⧸ I ^ n` and let `Q` be an ideal of `A'`. If `A' ⊗[A] B` is flat over `A'`, then the map `B ⊗[A] Q → B ⊗[A] A'` is injective. This is the identity `Q ⊗_A B = Q ⊗_{A'} (A' ⊗_A B)` of the proof of Lemma 6.4.3. -/
theorem lTensor_subtype_injective_of_flat_baseChange {A' : Type*} [CommRing A'] [Algebra A A']
    [Module.Flat A' (A' ⊗[A] B)] (Q : Ideal A') :
    Function.Injective (lTensor B (Q.subtype.restrictScalars A)) := by
  have hR := Module.Flat.iff_rTensor_injective'.mp ‹Module.Flat A' (A' ⊗[A] B)› Q
  let E1 : Q ⊗[A'] (A' ⊗[A] B) ≃ B ⊗[A] Q :=
    (AlgebraTensorModule.cancelBaseChange A A' A' Q B).toEquiv.trans
      (TensorProduct.comm A Q B).toEquiv
  let E2 : A' ⊗[A'] (A' ⊗[A] B) ≃ B ⊗[A] A' :=
    (AlgebraTensorModule.cancelBaseChange A A' A' A' B).toEquiv.trans
      (TensorProduct.comm A A' B).toEquiv
  have hE1 : ∀ x y, E1 (x + y) = E1 x + E1 y := fun x y => by simp [E1]
  have hE2 : ∀ x y, E2 (x + y) = E2 x + E2 y := fun x y => by simp [E2]
  have key : ∀ x, lTensor B (Q.subtype.restrictScalars A) (E1 x) =
      E2 (rTensor (A' ⊗[A] B) Q.subtype x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul q t =>
      induction t using TensorProduct.inductionOn with
      | tmul a b => simp [E1, E2]
      | add t₁ t₂ h₁ h₂ => rw [tmul_add, hE1, map_add, h₁, h₂, map_add, hE2]
    | add x y hx hy => rw [hE1, map_add, hx, hy, map_add, hE2]
  intro u v huv
  obtain ⟨x, rfl⟩ := E1.surjective u
  obtain ⟨y, rfl⟩ := E1.surjective v
  rw [key, key] at huv
  rw [hR (E2.injective huv)]

/-- If `y` is an element of `J` such that `(y : M) ∈ I • J`, then `y ∈ I • ⊤` in `J`. -/
theorem mem_smul_top_of_coe_mem_smul {M : Type*} [AddCommGroup M] [Module A M]
    (I : Ideal A) (J : Submodule A M) (y : J) (hy : (y : M) ∈ I • J) :
    y ∈ I • (⊤ : Submodule A J) := by
  have : (y : M) ∈ (I • (⊤ : Submodule A J)).map J.subtype := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
    exact hy
  obtain ⟨z, hz, hzy⟩ := this
  rwa [Subtype.ext hzy] at hz

/-- The image of `B ⊗[A] (I • ⊤)` in `B ⊗[A] N` is in `I • ⊤`. -/
theorem lTensor_mem_smul_top {N : Type*} [AddCommGroup N] [Module A N] (I : Ideal A)
    (P : Submodule A N) (hP : P ≤ I • ⊤) (w : B ⊗[A] P) :
    lTensor B P.subtype w ∈ I • (⊤ : Submodule A (B ⊗[A] N)) := by
  induction w using TensorProduct.inductionOn with
  | tmul b y =>
    simp only [lTensor_tmul, Submodule.subtype_apply]
    have hy : (y : N) ∈ I • (⊤ : Submodule A N) := hP y.2
    refine Submodule.smul_induction_on
      (p := fun x => b ⊗ₜ[A] x ∈ I • (⊤ : Submodule A (B ⊗[A] N))) hy ?_ ?_
    · intro a ha t _
      rw [tmul_smul]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · intro t₁ t₂ h₁ h₂
      rw [tmul_add]
      exact Submodule.add_mem _ h₁ h₂
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- **Volume 1, Lemma 6.4.3.** Let `A → B` be a map of Noetherian rings and let `I` be an ideal of `A` such that `IB` is in the Jacobson radical of `B`. If `(A ⧸ I ^ n) ⊗[A] B = B ⧸ I ^ n B` is flat over `A ⧸ I ^ n` for each `n`, then `B` is flat over `A`. -/
theorem flat_of_flat_quotient_pow [IsNoetherianRing A] [IsNoetherianRing B] (I : Ideal A)
    (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : ∀ n : ℕ, Module.Flat (A ⧸ I ^ n) ((A ⧸ I ^ n) ⊗[A] B)) : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (M := A) J
  have hzm : ∀ m : ℕ,
      z ∈ ((I.map (algebraMap A B)) ^ m • (⊤ : Submodule B (B ⊗[A] J))) := by
    intro m
    obtain ⟨n, hn⟩ : ∃ n, n = m + k := ⟨_, rfl⟩
    let Q : Ideal (A ⧸ I ^ n) := J.map (Ideal.Quotient.mk (I ^ n))
    let πJ : J →ₗ[A] Q :=
      { toFun := fun x => ⟨Ideal.Quotient.mk (I ^ n) x, Ideal.mem_map_of_mem _ x.2⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun a x => by
          ext
          simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] }
    have hcomm : (Q.subtype.restrictScalars A) ∘ₗ πJ =
        (Ideal.Quotient.mkₐ A (I ^ n)).toLinearMap ∘ₗ J.subtype := by
      ext x
      rfl
    have hsurj : Function.Surjective πJ := by
      rintro ⟨q, hq⟩
      obtain ⟨x, hx, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hq
      exact ⟨⟨x, hx⟩, rfl⟩
    let K : Submodule A J := Submodule.comap J.subtype (I ^ n)
    have hexact : Function.Exact K.subtype πJ := by
      rw [LinearMap.exact_iff]
      ext x
      simp [K, πJ, Subtype.ext_iff, Ideal.Quotient.eq_zero_iff_mem]
    have := h n
    have h1 : lTensor B πJ z = 0 := by
      apply lTensor_subtype_injective_of_flat_baseChange (A' := A ⧸ I ^ n) Q
      rw [map_zero, ← lTensor_comp_apply, hcomm, lTensor_comp_apply, hz, map_zero]
    obtain ⟨w, rfl⟩ := ((lTensor_exact B hexact hsurj) z).mp h1
    have hK : K ≤ I ^ m • (⊤ : Submodule A J) := by
      intro y hy
      apply mem_smul_top_of_coe_mem_smul
      have h2 : (y : A) ∈ I ^ n • (⊤ : Submodule A A) ⊓ J := by
        refine ⟨?_, y.2⟩
        rw [smul_eq_mul, Ideal.mul_top]
        exact Submodule.mem_comap.mp hy
      rw [hk n (by omega)] at h2
      have h3 : n - k = m := by omega
      rw [h3] at h2
      exact Submodule.smul_mono le_rfl inf_le_right h2
    have h4 := lTensor_mem_smul_top (B := B) (I ^ m) K hK w
    have h5 : I ^ m • (⊤ : Submodule A (B ⊗[A] J)) ≤
        ((I.map (algebraMap A B)) ^ m • (⊤ : Submodule B (B ⊗[A] J))).restrictScalars A := by
      rw [Submodule.smul_le]
      intro a ha t _
      rw [Submodule.restrictScalars_mem, ← algebraMap_smul B a t]
      have ha' : algebraMap A B a ∈ (I.map (algebraMap A B)) ^ m := by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ ha
      exact Submodule.smul_mem_smul ha' (Submodule.mem_top (x := t))
    exact h5 h4
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (I.map (algebraMap A B))
    (M := B ⊗[A] J) hI
  have : z ∈ (⨅ i : ℕ, (I.map (algebraMap A B)) ^ i • ⊤ : Submodule B (B ⊗[A] J)) :=
    Submodule.mem_iInf _ |>.mpr hzm
  rw [hbot] at this
  exact (Submodule.mem_bot B).mp this

end FlatnessModPowers

end Singularity.Algebra
