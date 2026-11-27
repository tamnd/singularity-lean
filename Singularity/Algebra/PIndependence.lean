/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.PBasis
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Algebra.CharP.Lemmas

/-!
# p-independent sets

This file proves Volume 1, Lemma 6.2.2 of the handbook for finite sets. Let `k ⊆ K` be fields of
characteristic `p`, with `p` prime. Let `L = k K^p`. A finite set `B ⊆ K` is `p`-independent if
the `p`-monomials in `B` are linearly independent over `L` (Definition 6.2.1).

* `Singularity.Algebra.isField_pSubring`: the ring `L` is a field.
* `Singularity.Algebra.IsPIndependent`: a finite set `B` is `p`-independent over `k`.
* `Singularity.Algebra.span_pMonomial_eq`: the `p`-monomials in `S` span `L[S]`.
* `Singularity.Algebra.adjoin_toSubalgebra_pSubring`: `L[S] = L(S)`.
* `Singularity.Algebra.isPIndependent_iff_finrank`: `B` is `p`-independent if and only if
  `[L(B) : L] = p^|B|`.
* `Singularity.Algebra.finrank_adjoin_insert`: if `b ∉ L(S)`, then
  `[L(S ∪ {b}) : L] = p [L(S) : L]`.
* `Singularity.Algebra.isPIndependent_iff`: part (1) of Lemma 6.2.2. The set `B` is
  `p`-independent if and only if `b ∉ L(B ∖ {b})` for each `b ∈ B`.
* `Singularity.Algebra.IsPIndependent.exists_isPBasis_superset`: part (2) of Lemma 6.2.2 when
  `[K : L]` is finite. Each finite `p`-independent set is contained in a finite `p`-basis.
* `Singularity.Algebra.exists_isPBasis`: when `[K : L]` is finite, `K` has a finite `p`-basis
  over `k`.

All sets in this file are finite. Part (2) for an infinite extension `K / L` needs `p`-independence
for infinite sets and Zorn's lemma. This file does not prove that case.
-/

namespace Singularity.Algebra

open Polynomial Module

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {p : ℕ}

local notation "Lp" => pSubring (K := K) k p

/-- Each `p`-th power `a ^ p` is in `L = k K^p`. -/
theorem pow_mem_pSubring (a : K) : a ^ p ∈ pSubring (K := K) k p :=
  Subring.subset_closure (Or.inr ⟨a, rfl⟩)

/-- For `p ≠ 0`, the ring `L = k K^p` is a field. The inverse of `x ≠ 0` is `x^(p-1) (x⁻¹)^p`. -/
theorem isField_pSubring (hp : p ≠ 0) : IsField (pSubring (K := K) k p) where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
  mul_comm a b := mul_comm a b
  mul_inv_cancel {a} ha := by
    have ha' : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
    refine ⟨⟨(a : K) ^ (p - 1) * ((a : K)⁻¹) ^ p,
      Subring.mul_mem _ (Subring.pow_mem _ a.2 _) (pow_mem_pSubring _)⟩, Subtype.ext ?_⟩
    show (a : K) * ((a : K) ^ (p - 1) * ((a : K)⁻¹) ^ p) = 1
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp), ← mul_pow,
      mul_inv_cancel₀ ha', one_pow]

/-- The field structure on `L = k K^p` for a prime `p`. -/
noncomputable instance instFieldPSubring [hp : Fact p.Prime] : Field (pSubring (K := K) k p) :=
  (isField_pSubring hp.out.ne_zero).toField

/-- A finite set `B` is `p`-independent over `k` if the `p`-monomials in `B` are linearly
independent over `L = k K^p` (Definition 6.2.1 of the handbook). -/
def IsPIndependent (k : Type*) [Field k] [Algebra k K] (p : ℕ) (B : Finset K) : Prop :=
  LinearIndependent (pSubring (K := K) k p) (pMonomial (p := p) B)

/-- Each `p`-monomial in `S` is in the algebra that `S` generates. -/
theorem pMonomial_mem_adjoin (S : Finset K) (α : S → Fin p) :
    pMonomial S α ∈ Algebra.adjoin (pSubring (K := K) k p) (S : Set K) :=
  prod_mem fun b _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin b.2) _

private theorem pMonomial_update [DecidableEq K] (S : Finset K) (α : S → Fin p) (b : S)
    (i : Fin p) : pMonomial S (Function.update α b i) =
      (b : K) ^ (i : ℕ) * ∏ c ∈ Finset.univ.erase b, (c : K) ^ (α c : ℕ) := by
  rw [pMonomial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ b), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun c hc => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hc)]

/-- The algebra `L[S]` is in the span of the `p`-monomials in `S`, because `b ^ p ∈ L`. -/
theorem adjoin_le_span_pMonomial [Fact p.Prime] (S : Finset K) :
    Subalgebra.toSubmodule (Algebra.adjoin (pSubring (K := K) k p) (S : Set K)) ≤
      Submodule.span (pSubring (K := K) k p) (Set.range (pMonomial (p := p) S)) := by
  classical
  have hp : p.Prime := Fact.out
  set M := Submodule.span (pSubring (K := K) k p) (Set.range (pMonomial (p := p) S))
  have h1 : (1 : K) ∈ M := by
    have : pMonomial S (fun _ => (⟨0, hp.pos⟩ : Fin p)) = 1 := by simp [pMonomial]
    exact this ▸ Submodule.subset_span ⟨_, rfl⟩
  have hmono : ∀ b ∈ S, ∀ α : S → Fin p, b * pMonomial S α ∈ M := by
    intro b hb α
    set b' : S := ⟨b, hb⟩
    have hα : pMonomial S α = b ^ (α b' : ℕ) * ∏ c ∈ Finset.univ.erase b', (c : K) ^ (α c : ℕ) := by
      rw [← pMonomial_update S α b' (α b'), Function.update_eq_self]
    by_cases hlt : (α b' : ℕ) + 1 < p
    · have := pMonomial_update S α b' ⟨(α b' : ℕ) + 1, hlt⟩
      rw [hα, ← mul_assoc, ← pow_succ']
      rw [← this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have heq : (α b' : ℕ) + 1 = p := by have := (α b').2; omega
      have := pMonomial_update S α b' ⟨0, hp.pos⟩
      rw [pow_zero, one_mul] at this
      rw [hα, ← mul_assoc, ← pow_succ', heq, ← this]
      exact M.smul_mem (⟨b ^ p, pow_mem_pSubring b⟩ : pSubring (K := K) k p)
        (Submodule.subset_span ⟨_, rfl⟩)
  have hmul : ∀ b ∈ S, ∀ z ∈ M, b * z ∈ M := by
    intro b hb z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨α, rfl⟩ := hz; exact hmono b hb α
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact M.smul_mem r hx
  have key : ∀ x ∈ Algebra.adjoin (pSubring (K := K) k p) (S : Set K), ∀ z ∈ M, x * z ∈ M := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hmul x hx
    | algebraMap r =>
      intro z hz
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact M.smul_mem r hz
    | add x y _ _ hx hy => intro z hz; rw [add_mul]; exact add_mem (hx z hz) (hy z hz)
    | mul x y _ _ hx hy => intro z hz; rw [mul_assoc]; exact hx _ (hy z hz)
  intro x hx
  have := key x hx 1 h1
  rwa [mul_one] at this

/-- The span of the `p`-monomials in `S` over `L` is the algebra `L[S]`. -/
theorem span_pMonomial_eq [Fact p.Prime] (S : Finset K) :
    Submodule.span (pSubring (K := K) k p) (Set.range (pMonomial (p := p) S)) =
      Subalgebra.toSubmodule (Algebra.adjoin (pSubring (K := K) k p) (S : Set K)) :=
  le_antisymm (Submodule.span_le.mpr (by rintro _ ⟨α, rfl⟩; exact pMonomial_mem_adjoin S α))
    (adjoin_le_span_pMonomial S)

/-- Each element of `K` is integral over `L = k K^p`. It is a root of `X^p - x^p`. -/
theorem isIntegral_pSubring [hp : Fact p.Prime] (x : K) :
    IsIntegral (pSubring (K := K) k p) x := by
  refine ⟨X ^ p - C ⟨x ^ p, pow_mem_pSubring x⟩, monic_X_pow_sub_C _ hp.out.ne_zero, ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_C]
  exact sub_eq_zero.mpr rfl

/-- The field `L(S)` is equal to the algebra `L[S]`. -/
theorem adjoin_toSubalgebra_pSubring [Fact p.Prime] (S : Set K) :
    (IntermediateField.adjoin (pSubring (K := K) k p) S).toSubalgebra =
      Algebra.adjoin (pSubring (K := K) k p) S :=
  IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun x _ => (isIntegral_pSubring x).isAlgebraic

/-- The degree `[L(S) : L]` is the dimension of the span of the `p`-monomials in `S`. -/
theorem finrank_adjoin_eq [Fact p.Prime] (S : Finset K) :
    finrank (pSubring (K := K) k p) (IntermediateField.adjoin (pSubring (K := K) k p) (S : Set K)) =
      (Set.range (pMonomial (p := p) S)).finrank (pSubring (K := K) k p) := by
  rw [Set.finrank, span_pMonomial_eq, ← adjoin_toSubalgebra_pSubring, Subalgebra.finrank_toSubmodule,
    IntermediateField.finrank_eq_finrank_subalgebra]

/-- A finite set `B` is `p`-independent if and only if `[L(B) : L] = p^|B|`. -/
theorem isPIndependent_iff_finrank [Fact p.Prime] (B : Finset K) :
    IsPIndependent k p B ↔
      finrank (pSubring (K := K) k p) (IntermediateField.adjoin (pSubring (K := K) k p) (B : Set K)) =
        p ^ B.card := by
  classical
  rw [IsPIndependent, linearIndependent_iff_card_eq_finrank_span, finrank_adjoin_eq]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  exact eq_comm

/-- The degree `[L(S) : L]` is at most `p^|S|`. -/
theorem finrank_adjoin_le [Fact p.Prime] (S : Finset K) :
    finrank (pSubring (K := K) k p) (IntermediateField.adjoin (pSubring (K := K) k p) (S : Set K)) ≤
      p ^ S.card := by
  classical
  rw [finrank_adjoin_eq]
  have := finrank_range_le_card (R := pSubring (K := K) k p) (pMonomial (p := p) S)
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using this

/-- If `b ∉ L(S)`, then `[L(S ∪ {b}) : L] = p [L(S) : L]`. The minimal polynomial of `b` over
`L(S)` is `X^p - b^p`. -/
theorem finrank_adjoin_insert [hp : Fact p.Prime] [CharP K p] [DecidableEq K] {S : Finset K} {b : K}
    (hb : b ∉ IntermediateField.adjoin (pSubring (K := K) k p) (S : Set K)) :
    finrank (pSubring (K := K) k p)
        (IntermediateField.adjoin (pSubring (K := K) k p) ((insert b S : Finset K) : Set K)) =
      p * finrank (pSubring (K := K) k p)
        (IntermediateField.adjoin (pSubring (K := K) k p) (S : Set K)) := by
  set E := IntermediateField.adjoin (pSubring (K := K) k p) (S : Set K) with hE
  have hle : E ≤ IntermediateField.adjoin (pSubring (K := K) k p) ((insert b S : Finset K) : Set K) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
  rw [← IntermediateField.relfinrank_bot_left, ← IntermediateField.relfinrank_bot_left,
    ← IntermediateField.relfinrank_mul_relfinrank bot_le hle, mul_comm]
  congr 1
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  have heq : IntermediateField.extendScalars hle = IntermediateField.adjoin E {b} := by
    apply IntermediateField.restrictScalars_injective (pSubring (K := K) k p)
    rw [IntermediateField.extendScalars_restrictScalars, hE, IntermediateField.adjoin_adjoin_left,
      Finset.coe_insert, Set.union_singleton]
  rw [heq]
  have hbp : b ^ p ∈ E := E.algebraMap_mem (⟨b ^ p, pow_mem_pSubring b⟩ : pSubring (K := K) k p)
  have hirr : Irreducible (X ^ p - C (⟨b ^ p, hbp⟩ : E)) := by
    refine X_pow_sub_C_irreducible_of_prime hp.out fun c hc => hb ?_
    have h1 : (c : K) ^ p = b ^ p := by simpa using congrArg Subtype.val hc
    have h2 : ((c : K) - b) ^ p = 0 := by rw [sub_pow_char, h1, sub_self]
    have h3 : (c : K) = b := sub_eq_zero.mp ((pow_eq_zero_iff hp.out.ne_zero).mp h2)
    exact h3 ▸ c.2
  have hmin : X ^ p - C (⟨b ^ p, hbp⟩ : E) = minpoly E b :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [IntermediateField.algebraMap_apply])
      (monic_X_pow_sub_C _ hp.out.ne_zero)
  rw [IntermediateField.adjoin.finrank ((isIntegral_pSubring (k := k) (p := p) b).tower_top (A := E)), ← hmin,
    natDegree_X_pow_sub_C]

/-- Volume 1, Lemma 6.2.2 (1) of the handbook, for a finite set `B`. The set `B` is
`p`-independent over `k` if and only if `b ∉ L(B ∖ {b})` for each `b ∈ B`. -/
theorem isPIndependent_iff [hp : Fact p.Prime] [CharP K p] [DecidableEq K] (B : Finset K) :
    IsPIndependent k p B ↔
      ∀ b ∈ B, b ∉ IntermediateField.adjoin (pSubring (K := K) k p) ((B.erase b : Finset K) : Set K) := by
  rw [isPIndependent_iff_finrank]
  constructor
  · intro hB b hb hmem
    have heq : IntermediateField.adjoin (pSubring (K := K) k p) (B : Set K) =
        IntermediateField.adjoin (pSubring (K := K) k p) ((B.erase b : Finset K) : Set K) := by
      refine le_antisymm (IntermediateField.adjoin_le_iff.mpr fun c hc => ?_)
        (IntermediateField.adjoin.mono _ _ _ (Finset.coe_subset.mpr (Finset.erase_subset b B)))
      by_cases hcb : c = b
      · exact hcb ▸ hmem
      · exact IntermediateField.subset_adjoin _ _
          (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hcb, Finset.mem_coe.mp hc⟩))
    have hle := finrank_adjoin_le (k := k) (p := p) (B.erase b)
    rw [← heq, hB, Finset.card_erase_of_mem hb] at hle
    have hcard : 0 < B.card := Finset.card_pos.mpr ⟨b, hb⟩
    exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right hp.out.one_lt (Nat.sub_lt hcard one_pos)))
  · intro h
    suffices H : ∀ S : Finset K, (∀ b ∈ S, b ∉ IntermediateField.adjoin (pSubring (K := K) k p)
        ((S.erase b : Finset K) : Set K)) →
        finrank (pSubring (K := K) k p)
          (IntermediateField.adjoin (pSubring (K := K) k p) (S : Set K)) = p ^ S.card from H B h
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      simp [IntermediateField.adjoin_empty]
    | insert a T haT ih =>
      intro hS
      have hT : ∀ b ∈ T, b ∉ IntermediateField.adjoin (pSubring (K := K) k p)
          ((T.erase b : Finset K) : Set K) := fun b hb hmem =>
        hS b (Finset.mem_insert_of_mem hb)
          (IntermediateField.adjoin.mono _ _ _ (Finset.coe_subset.mpr
            (Finset.erase_subset_erase b (Finset.subset_insert a T))) hmem)
      have ha : a ∉ IntermediateField.adjoin (pSubring (K := K) k p) (T : Set K) := by
        have := hS a (Finset.mem_insert_self a T)
        rwa [Finset.erase_insert haT] at this
      rw [finrank_adjoin_insert ha, ih hT, Finset.card_insert_of_notMem haT, pow_succ']

/-- If `K` is finite dimensional over `L`, then `[L(S) : L] ≤ [K : L]`. -/
theorem finrank_adjoin_le_finrank [Fact p.Prime] [FiniteDimensional (pSubring (K := K) k p) K]
    (S : Finset K) :
    finrank (pSubring (K := K) k p) (IntermediateField.adjoin (pSubring (K := K) k p) (S : Set K)) ≤
      finrank (pSubring (K := K) k p) K := by
  rw [finrank_adjoin_eq]
  exact Submodule.finrank_le _

/-- Volume 1, Lemma 6.2.2 (2) of the handbook, for `K` finite dimensional over `L = k K^p`.
Each finite `p`-independent set is contained in a finite `p`-basis. -/
theorem IsPIndependent.exists_isPBasis_superset [hp : Fact p.Prime] [CharP K p]
    [FiniteDimensional (pSubring (K := K) k p) K] {B : Finset K} (hB : IsPIndependent k p B) :
    ∃ B' : Finset K, B ⊆ B' ∧ IsPBasis k p B' := by
  classical
  suffices H : ∀ n, ∀ B : Finset K, finrank (pSubring (K := K) k p) K -
      finrank (pSubring (K := K) k p) (IntermediateField.adjoin (pSubring (K := K) k p) (B : Set K)) = n →
      IsPIndependent k p B → ∃ B' : Finset K, B ⊆ B' ∧ IsPBasis k p B' from H _ B rfl hB
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hn hB
  by_cases htop : ∀ x : K, x ∈ IntermediateField.adjoin (pSubring (K := K) k p) (B : Set K)
  · refine ⟨B, subset_rfl, hB, ?_⟩
    rw [span_pMonomial_eq, ← adjoin_toSubalgebra_pSubring]
    intro x _
    exact htop x
  · push Not at htop
    obtain ⟨x, hx⟩ := htop
    have hxB : x ∉ B := fun h => hx (IntermediateField.subset_adjoin _ _ (Finset.mem_coe.mpr h))
    have hB1 : IsPIndependent k p (insert x B) := by
      rw [isPIndependent_iff_finrank] at hB ⊢
      rw [finrank_adjoin_insert hx, hB, Finset.card_insert_of_notMem hxB, pow_succ']
    have hlt : finrank (pSubring (K := K) k p) K - finrank (pSubring (K := K) k p)
        (IntermediateField.adjoin (pSubring (K := K) k p) ((insert x B : Finset K) : Set K)) < n := by
      have h1 := finrank_adjoin_le_finrank (k := k) (p := p) (insert x B)
      rw [finrank_adjoin_insert hx] at h1 ⊢
      have h0 : 0 < finrank (pSubring (K := K) k p)
          (IntermediateField.adjoin (pSubring (K := K) k p) (B : Set K)) := by
        rw [(isPIndependent_iff_finrank B).mp hB]; exact pow_pos hp.out.pos _
      have h2 : finrank (pSubring (K := K) k p)
          (IntermediateField.adjoin (pSubring (K := K) k p) (B : Set K)) <
          p * finrank (pSubring (K := K) k p)
            (IntermediateField.adjoin (pSubring (K := K) k p) (B : Set K)) := by
        have := hp.out.two_le; nlinarith
      rw [← hn]
      generalize p * finrank (pSubring (K := K) k p)
        (IntermediateField.adjoin (pSubring (K := K) k p) (B : Set K)) = m at *
      omega
    obtain ⟨B', hB', h'⟩ := ih _ hlt (insert x B) rfl hB1
    exact ⟨B', (Finset.subset_insert x B).trans hB', h'⟩

/-- Volume 1, Lemma 6.2.2 (2) of the handbook, last claim, for `K` finite dimensional over
`L = k K^p`. The field `K` has a finite `p`-basis over `k`. -/
theorem exists_isPBasis [Fact p.Prime] [CharP K p] [FiniteDimensional (pSubring (K := K) k p) K] :
    ∃ B : Finset K, IsPBasis k p B := by
  have h0 : IsPIndependent k p (∅ : Finset K) := by
    rw [isPIndependent_iff_finrank]
    simp [IntermediateField.adjoin_empty]
  obtain ⟨B, -, hB⟩ := h0.exists_isPBasis_superset
  exact ⟨B, hB⟩

end Singularity.Algebra
