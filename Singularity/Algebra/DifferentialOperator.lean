/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Differential operators of Grothendieck

This file proves Volume 1, Lemma 6.3.4 of the handbook. Let `k` be a ring and let `A` be a `k`-algebra. A `k`-linear map `D : A → A` is a differential operator of order at most `0` if it is `A`-linear. It is a differential operator of order at most `n + 1` if, for each `a ∈ A`, the commutator `[D, a] = D ∘ a - a ∘ D` is a differential operator of order at most `n` (Definition 6.3.3 of the handbook).

* `Singularity.Algebra.IsDiffOp`: the predicate "`D` is a differential operator of order at most `n`".
* `Singularity.Algebra.IsDiffOp.mono`: an operator of order at most `m` has order at most `n` for each `n ≥ m`.
* `Singularity.Algebra.IsDiffOp.add`, `Singularity.Algebra.IsDiffOp.mulLeft_mul` and `Singularity.Algebra.IsDiffOp.mul`: the sum, the product with an element of `A` and the composite (Lemma 6.3.4 of the handbook).
* `Singularity.Algebra.IsDiffOp.of_hasseSchmidt`: the term `D n` of a Hasse-Schmidt derivation has order at most `n` (Lemma 6.3.4 of the handbook).
* `Singularity.Algebra.IsDiffOp.map_mul_of_mem_adjoin`: in characteristic `p`, an operator of order less than `q = p ^ e` is linear over the subring `k[A^q]` (Lemma 6.3.5 of the handbook).
-/

open Finset

namespace Singularity.Algebra

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The commutator `[D, a] = D ∘ a - a ∘ D` of a `k`-linear map `D : A → A` with the multiplication by `a`. -/
def diffComm (D : Module.End k A) (a : A) : Module.End k A :=
  D * LinearMap.mulLeft k a - LinearMap.mulLeft k a * D

/-- `IsDiffOp n D` says that `D` is a differential operator of order at most `n` (Definition 6.3.3 of the handbook). -/
def IsDiffOp : ℕ → Module.End k A → Prop
  | 0, D => ∀ a b : A, D (a * b) = a * D b
  | n + 1, D => ∀ a : A, IsDiffOp n (diffComm D a)

theorem isDiffOp_zero_iff {D : Module.End k A} :
    IsDiffOp 0 D ↔ ∀ a b : A, D (a * b) = a * D b := Iff.rfl

theorem isDiffOp_succ_iff {n : ℕ} {D : Module.End k A} :
    IsDiffOp (n + 1) D ↔ ∀ a : A, IsDiffOp n (diffComm D a) := Iff.rfl

theorem diffComm_add (D E : Module.End k A) (a : A) :
    diffComm (D + E) a = diffComm D a + diffComm E a := by
  unfold diffComm
  noncomm_ring

theorem diffComm_mul (D E : Module.End k A) (a : A) :
    diffComm (D * E) a = diffComm D a * E + D * diffComm E a := by
  simp only [diffComm, sub_mul, mul_sub, mul_assoc]
  abel

/-- The commutator of an `A`-linear map with a multiplication is zero. -/
theorem diffComm_eq_zero {D : Module.End k A} (hD : IsDiffOp 0 D) (a : A) :
    diffComm D a = 0 := by
  ext b
  simp only [diffComm, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    LinearMap.zero_apply]
  rw [hD a b, sub_self]

/-- The multiplication by an element of `A` has order at most `0`. -/
theorem isDiffOp_mulLeft (c : A) : IsDiffOp 0 (LinearMap.mulLeft k c) := fun a b => by
  simp only [LinearMap.mulLeft_apply]
  exact mul_left_comm c a b

theorem isDiffOp_one : IsDiffOp 0 (1 : Module.End k A) := fun a b => rfl

/-- An operator of order at most `n` has order at most `n + 1`. -/
theorem IsDiffOp.succ : ∀ {n : ℕ} {D : Module.End k A}, IsDiffOp n D → IsDiffOp (n + 1) D
  | 0, D, hD => fun a => by
      rw [diffComm_eq_zero hD a]
      intro x y
      simp
  | n + 1, D, hD => fun a => IsDiffOp.succ (hD a)

/-- An operator of order at most `m` has order at most `n` for each `n ≥ m`. -/
theorem IsDiffOp.mono {m n : ℕ} {D : Module.End k A} (hD : IsDiffOp m D) (h : m ≤ n) :
    IsDiffOp n D := by
  induction n, h using Nat.le_induction with
  | base => exact hD
  | succ n _ ih => exact ih.succ

/-- The sum of two operators of order at most `n` has order at most `n`. -/
theorem IsDiffOp.add : ∀ {n : ℕ} {D E : Module.End k A}, IsDiffOp n D → IsDiffOp n E →
    IsDiffOp n (D + E)
  | 0, D, E, hD, hE => fun a b => by
      simp only [LinearMap.add_apply]
      rw [hD a b, hE a b, mul_add]
  | n + 1, D, E, hD, hE => fun a => by
      rw [diffComm_add]
      exact IsDiffOp.add (hD a) (hE a)

/-- A sum of an operator of order at most `m` and an operator of order at most `n` has order at most `max m n` (Lemma 6.3.4 of the handbook). -/
theorem IsDiffOp.add_max {m n : ℕ} {D E : Module.End k A} (hD : IsDiffOp m D)
    (hE : IsDiffOp n E) : IsDiffOp (max m n) (D + E) :=
  (hD.mono (le_max_left m n)).add (hE.mono (le_max_right m n))

theorem isDiffOp_zero_map (n : ℕ) : IsDiffOp n (0 : Module.End k A) :=
  IsDiffOp.mono (m := 0) (fun a b => by simp) (Nat.zero_le n)

theorem IsDiffOp.sum {ι : Type*} (s : Finset ι) {n : ℕ} {D : ι → Module.End k A}
    (hD : ∀ i ∈ s, IsDiffOp n (D i)) : IsDiffOp n (∑ i ∈ s, D i) :=
  Finset.sum_induction D (IsDiffOp n) (fun _ _ h₁ h₂ => h₁.add h₂) (isDiffOp_zero_map n) hD

/-- The composite of an operator of order at most `m` and an operator of order at most `n` has order at most `m + n` (Lemma 6.3.4 of the handbook). -/
theorem IsDiffOp.mul : ∀ {m n : ℕ} {D E : Module.End k A}, IsDiffOp m D → IsDiffOp n E →
    IsDiffOp (m + n) (D * E)
  | 0, 0, D, E, hD, hE => fun a b => by
      simp only [Module.End.mul_apply]
      rw [hE a b, hD a]
  | m + 1, 0, D, E, hD, hE => fun a => by
      rw [diffComm_mul, diffComm_eq_zero hE a, mul_zero, add_zero]
      exact IsDiffOp.mul (m := m) (n := 0) (hD a) hE
  | 0, n + 1, D, E, hD, hE => fun a => by
      rw [diffComm_mul, diffComm_eq_zero hD a, zero_mul, zero_add]
      exact IsDiffOp.mul (m := 0) (n := n) hD (hE a)
  | m + 1, n + 1, D, E, hD, hE => by
      have h : m + 1 + (n + 1) = (m + n + 1) + 1 := by omega
      rw [h]
      intro a
      rw [diffComm_mul]
      exact (IsDiffOp.mul (hD a) hE).add ((IsDiffOp.mul hD (hE a)).mono (by omega))
termination_by m n => m + n

/-- The product of an operator of order at most `m` with an element `c` of `A` has order at most `m` (Lemma 6.3.4 of the handbook). -/
theorem IsDiffOp.mulLeft_mul {m : ℕ} {D : Module.End k A} (hD : IsDiffOp m D) (c : A) :
    IsDiffOp m (LinearMap.mulLeft k c * D) := by
  simpa using (isDiffOp_mulLeft (k := k) c).mul hD

/-- The term `D n` of a Hasse-Schmidt derivation `D` of `A` over `k` is a differential operator of order at most `n` (Lemma 6.3.4 of the handbook). The hypotheses say that `D 0` is the identity and that `D n (a * b) = ∑ i ≤ n, D i a * D (n - i) b`. -/
theorem IsDiffOp.of_hasseSchmidt (D : ℕ → Module.End k A) (h0 : D 0 = 1)
    (hmul : ∀ (n : ℕ) (a b : A), D n (a * b) = ∑ i ∈ range (n + 1), D i a * D (n - i) b)
    (n : ℕ) : IsDiffOp n (D n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [h0]
      exact isDiffOp_one
    · intro a
      have hc : diffComm (D (n + 1)) a =
          ∑ i ∈ range (n + 1), LinearMap.mulLeft k (D (i + 1) a) * D (n - i) := by
        ext b
        rw [LinearMap.sum_apply]
        simp only [diffComm, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply]
        rw [hmul, Finset.sum_range_succ', h0]
        simp [Nat.add_sub_add_right]
      rw [hc]
      refine IsDiffOp.sum _ fun i hi => ?_
      have hi' : n - i < n + 1 := by omega
      exact ((ih (n - i) hi').mulLeft_mul _).mono (Nat.sub_le n i)

/-- The commutator of the zero map is zero. -/
theorem diffComm_zero (a : A) : diffComm (0 : Module.End k A) a = 0 := by
  simp [diffComm]

/-- For an operator `D` of order at most `n`, the commutator with `a` taken `n + 1` times is zero. -/
theorem IsDiffOp.iterate_diffComm : ∀ {n : ℕ} {D : Module.End k A}, IsDiffOp n D → ∀ a : A,
    (fun F => diffComm F a)^[n + 1] D = 0
  | 0, D, hD, a => diffComm_eq_zero hD a
  | n + 1, D, hD, a => by
      rw [Function.iterate_succ_apply]
      exact IsDiffOp.iterate_diffComm (hD a) a

theorem IsDiffOp.iterate_diffComm_of_lt {n m : ℕ} {D : Module.End k A} (hD : IsDiffOp n D)
    (a : A) (h : n < m) : (fun F => diffComm F a)^[m] D = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + (n + 1) := ⟨m - (n + 1), by omega⟩
  rw [Function.iterate_add_apply, hD.iterate_diffComm a]
  exact Function.iterate_fixed (diffComm_zero a) j

/-- If `A` has characteristic `p`, then the ring of `k`-linear maps of `Module.End k A` also has characteristic `p`. -/
theorem charP_end_end (p : ℕ) [CharP A p] : CharP (Module.End k (Module.End k A)) p := by
  refine ⟨fun n => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h1 := congrArg (fun T : Module.End k (Module.End k A) => T 1 1) h
    simp only [Module.End.natCast_apply, LinearMap.smul_apply, Module.End.one_apply,
      LinearMap.zero_apply, nsmul_eq_mul, mul_one] at h1
    exact (CharP.cast_eq_zero_iff A p n).mp h1
  · refine LinearMap.ext fun F => LinearMap.ext fun b => ?_
    rw [Module.End.natCast_apply, LinearMap.smul_apply, LinearMap.zero_apply, LinearMap.zero_apply,
      nsmul_eq_mul, (CharP.cast_eq_zero_iff A p n).mpr h, zero_mul]

/-- Let `A` have characteristic `p`, let `q = p ^ e` and let `D` have order at most `n` with `n < q`. Then `D (a ^ q * b) = a ^ q * D b` for all `a` and `b` (Volume 1, Lemma 6.3.5 of the handbook). -/
theorem IsDiffOp.map_pow_mul {p : ℕ} [Fact p.Prime] [CharP A p] {e n : ℕ} {D : Module.End k A}
    (hD : IsDiffOp n D) (hn : n < p ^ e) (a b : A) : D (a ^ p ^ e * b) = a ^ p ^ e * D b := by
  haveI := charP_end_end (k := k) (A := A) p
  set l : Module.End k A := LinearMap.mulLeft k a
  let ad : Module.End k (Module.End k A) := LinearMap.mulRight k l - LinearMap.mulLeft k l
  have had : ⇑ad = fun F => diffComm F a := by
    funext F
    simp [ad, diffComm, l]
  have hpow : (ad ^ p ^ e) D = diffComm D (a ^ p ^ e) := by
    rw [sub_pow_char_pow_of_commute p e (LinearMap.commute_mulLeft_right l l).symm,
      LinearMap.pow_mulRight, LinearMap.pow_mulLeft, LinearMap.pow_mulLeft]
    simp [diffComm, l]
  have h0 : diffComm D (a ^ p ^ e) = 0 := by
    rw [← hpow, Module.End.pow_apply, had]
    exact hD.iterate_diffComm_of_lt a hn
  have h1 := congrArg (fun F : Module.End k A => F b) h0
  simp only [diffComm, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    LinearMap.zero_apply, sub_eq_zero] at h1
  exact h1

/-- Let `A` have characteristic `p`, let `q = p ^ e` and let `D` have order at most `n` with `n < q`. Then `D` is linear over the subring `k[A^q]` of `A` that `k` and the `q`-th powers generate (Volume 1, Lemma 6.3.5 of the handbook). -/
theorem IsDiffOp.map_mul_of_mem_adjoin {p : ℕ} [Fact p.Prime] [CharP A p] {e n : ℕ}
    {D : Module.End k A} (hD : IsDiffOp n D) (hn : n < p ^ e) {s : A}
    (hs : s ∈ Algebra.adjoin k (Set.range fun a : A => a ^ p ^ e)) (b : A) :
    D (s * b) = s * D b := by
  revert b
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hD.map_pow_mul hn a
  | algebraMap r =>
      intro b
      rw [← Algebra.smul_def, ← Algebra.smul_def, LinearMap.map_smul]
  | add x y _ _ hx hy =>
      intro b
      rw [add_mul, map_add, hx, hy, add_mul]
  | mul x y _ _ hx hy =>
      intro b
      rw [mul_assoc, hx, hy, mul_assoc]

end Singularity.Algebra
