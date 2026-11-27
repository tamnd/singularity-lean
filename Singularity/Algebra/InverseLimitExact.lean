/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Function

/-!
# Limits of short exact sequences of inverse systems

This file proves Volume 1, Lemma 4.2.3 of the handbook. Let `0 → (A_n) → (B_n) → (C_n) → 0` be maps of inverse systems such that each sequence `0 → A_n → B_n → C_n → 0` is exact. Assume that each map `A_{n+1} → A_n` is surjective. Then the sequence `0 → lim A_n → lim B_n → lim C_n → 0` is exact.

In Lean an inverse system is a family of additive groups `A n` with maps `t n : A (n + 1) →+ A n`. The limit is the set `Singularity.Algebra.invLim t` of the families `x` with `t n (x (n + 1)) = x n` for each `n`.

* `Singularity.Algebra.invLim`: the limit of an inverse system.
* `Singularity.Algebra.invLimMap`: the map of limits that a map of inverse systems gives.
* `Singularity.Algebra.injOn_invLimMap`: exactness at `lim A_n`.
* `Singularity.Algebra.exists_invLim_of_invLimMap_eq_zero`: exactness at `lim B_n`.
* `Singularity.Algebra.surjOn_invLimMap`: exactness at `lim C_n`.

The proof is the proof of the handbook. For the surjectivity, we choose the elements `b_n` by induction on `n`.
-/

namespace Singularity.Algebra

variable {A B C : ℕ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
  [∀ n, AddCommGroup (C n)]

/-- The limit of the inverse system `(A n, t n)`, as the set of the compatible families. -/
def invLim (t : ∀ n, A (n + 1) →+ A n) : Set (∀ n, A n) :=
  {x | ∀ n, t n (x (n + 1)) = x n}

/-- The map of the products that the maps `f n : A n →+ B n` give. -/
def invLimMap (f : ∀ n, A n →+ B n) (x : ∀ n, A n) : ∀ n, B n :=
  fun n => f n (x n)

variable {tA : ∀ n, A (n + 1) →+ A n} {tB : ∀ n, B (n + 1) →+ B n}
  {tC : ∀ n, C (n + 1) →+ C n}

/-- A map of inverse systems sends the limit into the limit. -/
theorem invLimMap_mem {f : ∀ n, A n →+ B n} (hf : ∀ n a, tB n (f (n + 1) a) = f n (tA n a))
    {x : ∀ n, A n} (hx : x ∈ invLim tA) : invLimMap f x ∈ invLim tB := by
  intro n
  simp only [invLimMap, hf, hx n]

/-- If each map `f n` is injective, then the map of limits is injective. -/
theorem injOn_invLimMap {f : ∀ n, A n →+ B n} (hinj : ∀ n, Function.Injective (f n)) :
    Set.InjOn (invLimMap f) (invLim tA) := by
  intro x _ y _ h
  funext n
  exact hinj n (congrFun h n)

/-- Exactness at `lim B_n`. If `x` is in the limit of the `B n` and each `g n (x n)` is `0`, then `x` is the image of an element of the limit of the `A n`. -/
theorem exists_invLim_of_invLimMap_eq_zero {f : ∀ n, A n →+ B n} {g : ∀ n, B n →+ C n}
    (hf : ∀ n a, tB n (f (n + 1) a) = f n (tA n a)) (hinj : ∀ n, Function.Injective (f n))
    (hexact : ∀ n b, g n b = 0 ↔ ∃ a, f n a = b) {x : ∀ n, B n} (hx : x ∈ invLim tB)
    (hgx : ∀ n, g n (x n) = 0) : ∃ y ∈ invLim tA, invLimMap f y = x := by
  choose y hy using fun n => (hexact n (x n)).1 (hgx n)
  refine ⟨y, fun n => hinj n ?_, funext hy⟩
  rw [← hf, hy, hy, hx n]

/-- The step of the induction in the proof of `surjOn_invLimMap`. -/
theorem exists_lift_succ {f : ∀ n, A n →+ B n} {g : ∀ n, B n →+ C n}
    (hf : ∀ n a, tB n (f (n + 1) a) = f n (tA n a))
    (hg : ∀ n b, tC n (g (n + 1) b) = g n (tB n b))
    (hexact : ∀ n b, g n b = 0 ↔ ∃ a, f n a = b) (hsurj : ∀ n, Function.Surjective (g n))
    (hA : ∀ n, Function.Surjective (tA n)) {c : ∀ n, C n} (hc : c ∈ invLim tC) (n : ℕ)
    (b : B n) (hb : g n b = c n) :
    ∃ b' : B (n + 1), g (n + 1) b' = c (n + 1) ∧ tB n b' = b := by
  obtain ⟨b₁, hb₁⟩ := hsurj (n + 1) (c (n + 1))
  have h0 : g n (tB n b₁ - b) = 0 := by
    rw [map_sub, ← hg, hb₁, hc n, hb, sub_self]
  obtain ⟨a, ha⟩ := (hexact n _).1 h0
  obtain ⟨a', rfl⟩ := hA n a
  have hgf : g (n + 1) (f (n + 1) a') = 0 := (hexact (n + 1) _).2 ⟨a', rfl⟩
  refine ⟨b₁ - f (n + 1) a', ?_, ?_⟩
  · rw [map_sub, hgf, sub_zero, hb₁]
  · rw [map_sub, hf, ha, sub_sub_cancel]

/-- Exactness at `lim C_n`. If each map `tA n : A (n + 1) → A n` is surjective, then the map of limits `lim B_n → lim C_n` is surjective. -/
theorem surjOn_invLimMap {f : ∀ n, A n →+ B n} {g : ∀ n, B n →+ C n}
    (hf : ∀ n a, tB n (f (n + 1) a) = f n (tA n a))
    (hg : ∀ n b, tC n (g (n + 1) b) = g n (tB n b))
    (hexact : ∀ n b, g n b = 0 ↔ ∃ a, f n a = b) (hsurj : ∀ n, Function.Surjective (g n))
    (hA : ∀ n, Function.Surjective (tA n)) :
    Set.SurjOn (invLimMap g) (invLim tB) (invLim tC) := by
  intro c hc
  choose s hs₁ hs₂ using exists_lift_succ hf hg hexact hsurj hA hc
  let b : ∀ n, {b : B n // g n b = c n} := fun n =>
    Nat.rec ⟨(hsurj 0 (c 0)).choose, (hsurj 0 (c 0)).choose_spec⟩
      (fun n b => ⟨s n b.1 b.2, hs₁ n b.1 b.2⟩) n
  refine ⟨fun n => (b n).1, fun n => hs₂ n (b n).1 (b n).2, funext fun n => (b n).2⟩

end Singularity.Algebra
