/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Ideal.Maps

/-!
# The Reynolds operator

Let `B` be a commutative ring, let `G` be a finite group that acts on `B` by ring automorphisms, and let `A = B^G` be the ring of invariants. If `|G|` is a unit of `B`, the map `ρ(b) = |G|⁻¹ ∑_{g ∈ G} g • b` sends `B` to `A`, it is `A`-linear, and `ρ(a) = a` for `a ∈ A`. So `A` is a direct summand of `B` as an `A`-module, and `I B ∩ A = I` for each ideal `I` of `A`. This is Volume 8, Lemma 3.1.8 of the handbook.

The action does not need to be faithful, and `B` does not need to be a domain.

## Main results

* `Singularity.invariantSubring`: the ring of invariants `B^G`.
* `Singularity.reynolds`: the operator `ρ`.
* `Singularity.reynolds_mem`: `ρ(b) ∈ B^G`.
* `Singularity.reynolds_add`, `Singularity.reynolds_mul_of_mem`: `ρ` is `B^G`-linear.
* `Singularity.reynolds_of_mem`: `ρ(a) = a` for `a ∈ B^G`.
* `Singularity.comap_map_invariantSubring`: `I B ∩ A = I`.
-/

namespace Singularity

variable (G B : Type*) [Group G] [Fintype G] [CommRing B] [MulSemiringAction G B]

/-- The ring of invariants `B^G` of a group `G` that acts on a ring `B`. -/
def invariantSubring : Subring B where
  carrier := {b | ∀ g : G, g • b = b}
  mul_mem' := by
    intro a b ha hb g
    rw [smul_mul', ha g, hb g]
  one_mem' := by
    intro g
    exact smul_one g
  add_mem' := by
    intro a b ha hb g
    rw [smul_add, ha g, hb g]
  zero_mem' := by
    intro g
    exact smul_zero g
  neg_mem' := by
    intro a ha g
    rw [smul_neg, ha g]

variable {G B}

theorem mem_invariantSubring {b : B} : b ∈ invariantSubring G B ↔ ∀ g : G, g • b = b :=
  Iff.rfl

/-- The Reynolds operator `ρ(b) = |G|⁻¹ ∑_{g ∈ G} g • b`, for `|G|` a unit of `B`. -/
noncomputable def reynolds (hG : IsUnit (Fintype.card G : B)) (b : B) : B :=
  (↑hG.unit⁻¹ : B) * ∑ g : G, g • b

theorem reynolds_smul_natCast (g : G) (n : ℕ) : g • (n : B) = n :=
  map_natCast (MulSemiringAction.toRingHom G B g) n

theorem reynolds_smul_inv_card (hG : IsUnit (Fintype.card G : B)) (g : G) :
    g • (↑hG.unit⁻¹ : B) = ↑hG.unit⁻¹ := by
  have h1 : (Fintype.card G : B) * ↑hG.unit⁻¹ = 1 := hG.mul_val_inv
  have h2 : g • (Fintype.card G : B) * g • (↑hG.unit⁻¹ : B) = 1 := by
    rw [← smul_mul', h1, smul_one]
  rw [reynolds_smul_natCast] at h2
  calc g • (↑hG.unit⁻¹ : B) = (↑hG.unit⁻¹ * (Fintype.card G : B)) * g • (↑hG.unit⁻¹ : B) := by
        rw [mul_comm _ (Fintype.card G : B), h1, one_mul]
    _ = ↑hG.unit⁻¹ := by rw [mul_assoc, h2, mul_one]

theorem reynolds_smul_sum (g : G) (b : B) : g • ∑ h : G, h • b = ∑ h : G, h • b := by
  rw [Finset.smul_sum]
  simp_rw [← mul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => rfl)

/-- Volume 8, Lemma 3.1.8 of the handbook: the Reynolds operator sends `B` into `B^G`. -/
theorem reynolds_mem (hG : IsUnit (Fintype.card G : B)) (b : B) :
    reynolds hG b ∈ invariantSubring G B := by
  intro g
  rw [reynolds, smul_mul', reynolds_smul_inv_card, reynolds_smul_sum]

/-- The Reynolds operator is additive. -/
theorem reynolds_add (hG : IsUnit (Fintype.card G : B)) (x y : B) :
    reynolds hG (x + y) = reynolds hG x + reynolds hG y := by
  simp only [reynolds, smul_add, Finset.sum_add_distrib, mul_add]

/-- Volume 8, Lemma 3.1.8 of the handbook: the Reynolds operator is `B^G`-linear. -/
theorem reynolds_mul_of_mem (hG : IsUnit (Fintype.card G : B)) {a : B}
    (ha : a ∈ invariantSubring G B) (b : B) : reynolds hG (a * b) = a * reynolds hG b := by
  have h : ∑ g : G, g • (a * b) = a * ∑ g : G, g • b := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_mul', ha g]
  rw [reynolds, reynolds, h, mul_left_comm]

/-- Volume 8, Lemma 3.1.8 of the handbook: `ρ(a) = a` for `a ∈ B^G`. -/
theorem reynolds_of_mem (hG : IsUnit (Fintype.card G : B)) {a : B}
    (ha : a ∈ invariantSubring G B) : reynolds hG a = a := by
  have h : ∑ g : G, g • a = (Fintype.card G : B) * a := by
    rw [Finset.sum_congr rfl fun g _ => ha g, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [reynolds, h, ← mul_assoc, hG.val_inv_mul, one_mul]

/-- For an ideal `I` of `B^G`, the ideal of the `y ∈ B` with `ρ(b y) ∈ I` for each `b ∈ B`. It contains `I B`. -/
noncomputable def reynoldsIdeal (hG : IsUnit (Fintype.card G : B))
    (I : Ideal (invariantSubring G B)) : Ideal B where
  carrier := {y | ∀ b : B, (⟨reynolds hG (b * y), reynolds_mem hG _⟩ :
      invariantSubring G B) ∈ I}
  add_mem' := by
    intro x y hx hy b
    have h := I.add_mem (hx b) (hy b)
    convert h using 1
    ext
    show reynolds hG (b * (x + y)) = reynolds hG (b * x) + reynolds hG (b * y)
    rw [mul_add, reynolds_add]
  zero_mem' := by
    intro b
    convert I.zero_mem using 1
    ext
    show reynolds hG (b * 0) = 0
    simp [reynolds]
  smul_mem' := by
    intro c y hy b
    have h := hy (b * c)
    convert h using 1
    ext
    show reynolds hG (b * (c • y)) = reynolds hG (b * c * y)
    rw [smul_eq_mul, mul_assoc]

theorem mem_reynoldsIdeal (hG : IsUnit (Fintype.card G : B)) (I : Ideal (invariantSubring G B))
    {y : B} : y ∈ reynoldsIdeal hG I ↔
      ∀ b : B, (⟨reynolds hG (b * y), reynolds_mem hG _⟩ : invariantSubring G B) ∈ I :=
  Iff.rfl

/-- Volume 8, Lemma 3.1.8 of the handbook: if `|G|` is a unit of `B`, then `I B ∩ B^G = I` for each ideal `I` of `B^G`. -/
theorem comap_map_invariantSubring (hG : IsUnit (Fintype.card G : B))
    (I : Ideal (invariantSubring G B)) :
    (I.map (invariantSubring G B).subtype).comap (invariantSubring G B).subtype = I := by
  refine le_antisymm ?_ Ideal.le_comap_map
  have hIJ : I.map (invariantSubring G B).subtype ≤ reynoldsIdeal hG I := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_reynoldsIdeal]
    intro b
    have h := I.mul_mem_left ⟨reynolds hG b, reynolds_mem hG b⟩ ha
    convert h using 1
    ext
    show reynolds hG (b * a) = reynolds hG b * a
    rw [mul_comm b, reynolds_mul_of_mem hG a.2, mul_comm]
  intro x hx
  have h := (mem_reynoldsIdeal hG I).mp (hIJ (Ideal.mem_comap.mp hx)) 1
  convert h using 1
  ext
  show (x : B) = reynolds hG (1 * x)
  rw [one_mul, reynolds_of_mem hG x.2]

end Singularity
