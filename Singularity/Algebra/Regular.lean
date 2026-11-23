/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.

Sections 1 to 4 of this file are adapted from `Hironaka/Algebra/Local/Regular.lean` of
resolutionorg/hironaka at commit 044d89c9455859446fc5e986667319f910e15f4b, by Chris Elliott
(Resolution), released under the Apache 2.0 licence. The changes are the namespace, the names
and the comments.
-/
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Regular local rings

Mathlib has the class `IsRegularLocalRing` (Stacks tag 00KU): a Noetherian local ring `R` with
maximal ideal `𝔪` is regular when `𝔪` has a set of `dim R` generators. This file adds the
first facts about this class that the project uses.

* `quotient_span_singleton`: if `x ∈ 𝔪 \ 𝔪²`, then `R / (x)` is regular and its dimension is
  `dim R - 1` (Stacks tag 00NQ).
* `isDomain_of_isRegularLocalRing`: a regular local ring is a domain (Stacks tag 00NP,
  [Mat89, Theorem 14.3]).
* `of_quotient_span_singleton`: if `x ∈ 𝔪` is a nonzerodivisor and `R / (x)` is regular, then
  `R` is regular (Stacks tag 00NU).
* `isRegularLocalRing_iff_isDiscreteValuationRing` and
  `isRegularLocalRing_iff_isIntegrallyClosed`: a Noetherian local domain of dimension 1 is
  regular if and only if it is a discrete valuation ring, if and only if it is integrally closed
  ([AM69, Proposition 9.2], [Mat89, Theorem 11.2]).

The last two facts are the local form of the resolution of curves: a normal curve is regular.

The proof that a regular local ring is a domain is by induction on the dimension. If the
dimension is 0, then `𝔪 = 0`, so `R` is a field. If the dimension is `m + 1`, choose
`x ∈ 𝔪 \ 𝔪²` that is in no minimal prime (prime avoidance). Then `R / (x)` is regular of
dimension `m`, so `(x)` is prime by induction. Let `P ⊆ (x)` be a minimal prime. Each `y ∈ P`
is `z x` with `z ∈ P`, thus `P = x P`, and Nakayama's lemma gives `P = 0`.

Mathlib does not have the theorem that a localization of a regular local ring at a prime is
regular (Serre). This file does not prove it.

## References

* [AM69] M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*, 1969.
* [Mat89] H. Matsumura, *Commutative ring theory*, 1989.
* [Sta] The Stacks project authors, *The Stacks project*.
-/

open IsLocalRing Ideal

universe u

namespace Singularity.Algebra

variable {R : Type u} [CommRing R]

/-! ### 1. Dimension and quotients -/

/-- A ring of finite Krull dimension has a natural number as its dimension. -/
theorem exists_ringKrullDim_eq_natCast (R : Type u) [CommRing R] [FiniteRingKrullDim R] :
    ∃ n : ℕ, ringKrullDim R = n := by
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
  have ha' : a ≠ ⊤ := by
    rintro rfl
    exact ringKrullDim_ne_top (R := R) ha.symm
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ha'
  exact ⟨n, by rw [← ha, ← hn]; rfl⟩

section Quotient

variable [IsLocalRing R]

/-- The quotient of a local ring by a proper ideal is local. -/
theorem isLocalRing_quotient_of_le_maximalIdeal {I : Ideal R} (hI : I ≤ maximalIdeal R) :
    IsLocalRing (R ⧸ I) := by
  have : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- The maximal ideal of a local quotient is the image of `𝔪`. -/
theorem maximalIdeal_quotient_eq_map (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    maximalIdeal (R ⧸ I) = (maximalIdeal R).map (Ideal.Quotient.mk I) :=
  (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm

variable [IsNoetherianRing R]

/-- The exchange step. Let `x ∈ 𝔪 \ 𝔪²`. Then `x` replaces one element of a minimal set of
generators of `𝔪`: `𝔪 = (x) + (t)` with `t.card + 1 = spanFinrank 𝔪`. -/
theorem exists_span_insert_eq_maximalIdeal {x : R} (mem : x ∈ maximalIdeal R)
    (nmem : x ∉ maximalIdeal R ^ 2) :
    ∃ t : Finset R, (t : Set R) ⊆ maximalIdeal R ∧ t.card + 1 = (maximalIdeal R).spanFinrank ∧
      maximalIdeal R = span (insert x (t : Set R)) := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal R).fg_of_isNoetherianRing
  have hspan : span (s : Set R) = maximalIdeal R := hspan
  have hs : (s : Set R) ⊆ maximalIdeal R := hspan ▸ Ideal.subset_span
  obtain ⟨f, -, hf⟩ :=
    Submodule.mem_span_finset.mp (show x ∈ span (s : Set R) from hspan ▸ mem)
  simp only [smul_eq_mul] at hf
  have : ∃ i ∈ s, f i ∉ maximalIdeal R := by
    by_contra hall
    push Not at hall
    apply nmem
    rw [← hf, pow_two]
    exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_mul (hall i hi) (hs hi)
  obtain ⟨i₀, hi₀, hu⟩ := this
  rw [IsLocalRing.notMem_maximalIdeal] at hu
  refine ⟨s.erase i₀, fun y hy => hs (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hy)),
    (Finset.card_erase_add_one hi₀).trans hcard, le_antisymm ?_ ?_⟩
  · rw [← hspan, Ideal.span_le]
    intro i hi
    by_cases h : i = i₀
    · subst h
      have hsum : f i * i + ∑ j ∈ s.erase i, f j * j = x := by
        rw [← hf]; exact Finset.add_sum_erase s (fun j => f j * j) hi
      have hx' : x ∈ span (insert x ((s.erase i : Finset R) : Set R)) :=
        Ideal.subset_span (Set.mem_insert _ _)
      have hsum' : ∑ j ∈ s.erase i, f j * j ∈ span (insert x ((s.erase i : Finset R) : Set R)) :=
        Ideal.sum_mem _ fun j hj =>
          Ideal.mul_mem_left _ _
            (Ideal.subset_span (Set.mem_insert_of_mem _ (Finset.mem_coe.mpr hj)))
      have hfi : f i * i = x - ∑ j ∈ s.erase i, f j * j := eq_sub_of_add_eq hsum
      have : f i * i ∈ span (insert x ((s.erase i : Finset R) : Set R)) := by
        rw [hfi]; exact Ideal.sub_mem _ hx' hsum'
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp this
    · exact Ideal.subset_span
        (Set.mem_insert_of_mem _ (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨h, hi⟩)))
  · rw [Ideal.span_le]
    rintro y (rfl | hy)
    · exact mem
    · exact hs (Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hy)))

/-- For `x ∈ 𝔪 \ 𝔪²` the maximal ideal of `R / (x)` needs one generator fewer than `𝔪`. -/
theorem spanFinrank_maximalIdeal_quotient_add_one_le {x : R} (mem : x ∈ maximalIdeal R)
    (nmem : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  obtain ⟨t, -, hcard, hspan⟩ := exists_span_insert_eq_maximalIdeal mem nmem
  rw [← hcard, maximalIdeal_quotient_eq_map, hspan, Ideal.map_span, Set.image_insert_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x), Ideal.span_insert_zero]
  refine Nat.add_le_add_right ?_ 1
  calc (span ((Ideal.Quotient.mk (span {x})) '' (t : Set R))).spanFinrank
      ≤ ((Ideal.Quotient.mk (span {x})) '' (t : Set R)).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite (t.finite_toSet.image _)
    _ ≤ (t : Set R).ncard := Set.ncard_image_le t.finite_toSet
    _ = t.card := Set.ncard_coe_finset t

/-- For `x ∈ 𝔪`, the lifts of a set of generators of the maximal ideal of `R / (x)`, together
with `x`, generate `𝔪`. -/
theorem spanFinrank_maximalIdeal_le_spanFinrank_maximalIdeal_quotient_add_one {x : R}
    (hx : x ∈ maximalIdeal R) [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 := by
  classical
  obtain ⟨t, htcard, htspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (maximalIdeal (R ⧸ span {x})).fg_of_isNoetherianRing
  have htspan : span (t : Set (R ⧸ span {x})) = maximalIdeal (R ⧸ span {x}) := htspan
  set mk := Ideal.Quotient.mk (span {x}) with hmk
  set t' : Set R := Function.surjInv Ideal.Quotient.mk_surjective '' (t : Set (R ⧸ span {x}))
    with ht'
  have himg : mk '' t' = t := by
    rw [ht', ← Set.image_comp, Function.comp_surjInv, Set.image_id]
  have ht'fin : t'.Finite := t.finite_toSet.image _
  have hspan : maximalIdeal R = span (insert x t') := by
    apply le_antisymm
    · intro y hy
      have hy' : mk y ∈ span (mk '' t') := by
        rw [himg, htspan, maximalIdeal_quotient_eq_map]
        exact Ideal.mem_map_of_mem _ hy
      rw [← Ideal.map_span, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hy'
      obtain ⟨y', hy'mem, hyy'⟩ := hy'
      have hsub : y - y' ∈ span {x} := Ideal.Quotient.eq.mp hyy'.symm
      rw [Ideal.span_insert, show y = (y - y') + y' by ring]
      exact Submodule.add_mem_sup hsub hy'mem
    · rw [Ideal.span_le]
      rintro y (rfl | hy)
      · exact hx
      · obtain ⟨q, hq, rfl⟩ := hy
        have hmkq : mk (Function.surjInv Ideal.Quotient.mk_surjective q) = q :=
          Function.surjInv_eq _ _
        by_contra hnot
        have hu : IsUnit (Function.surjInv Ideal.Quotient.mk_surjective q) :=
          IsLocalRing.notMem_maximalIdeal.mp hnot
        have hqm : q ∈ maximalIdeal (R ⧸ span {x}) := htspan ▸ Ideal.subset_span hq
        exact IsLocalRing.notMem_maximalIdeal.mpr (hmkq ▸ hu.map mk) hqm
  rw [hspan]
  calc (span (insert x t')).spanFinrank
      ≤ (insert x t').ncard := Submodule.spanFinrank_span_le_ncard_of_finite (ht'fin.insert x)
    _ ≤ t'.ncard + 1 := Set.ncard_insert_le x t'
    _ ≤ (t : Set (R ⧸ span {x})).ncard + 1 :=
        Nat.add_le_add_right (Set.ncard_image_le t.finite_toSet) 1
    _ = t.card + 1 := by rw [Set.ncard_coe_finset]
    _ = (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 := by rw [htcard]

end Quotient

/-! ### 2. Prime avoidance -/

/-- In a Noetherian local ring of positive dimension there is `x ∈ 𝔪 \ 𝔪²` that is in no
minimal prime. The reason is that `𝔪` is not a subset of `𝔪² ∪ P₁ ∪ ... ∪ P_k`, where the
`Pᵢ` are the finitely many minimal primes (prime avoidance, with `𝔪²` in one of the two places
for an ideal that is not prime). -/
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes [IsLocalRing R]
    [IsNoetherianRing R] (h : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing (R := R)
  set S : Finset (Ideal R) := insert (maximalIdeal R ^ 2) hfin.toFinset with hS
  have hprime : ∀ i ∈ S, i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → i.IsPrime := by
    intro i hi hne _
    rcases Finset.mem_insert.mp hi with h' | h'
    · exact absurd h' hne
    · exact IsMinimalPrime.isPrime (hfin.mem_toFinset.mp h')
  have hnot : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ i ∈ (S : Set (Ideal R)), (i : Set R)) := by
    rw [Ideal.subset_union_prime (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) hprime]
    rintro ⟨i, hi, hle⟩
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact lt_irrefl _
        ((IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero h.ne').trans_le hle)
    · have hmin : i ∈ minimalPrimes R := hfin.mem_toFinset.mp hi'
      have hip : i.IsPrime := IsMinimalPrime.isPrime hmin
      have heq : i = maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hip.ne_top) hle
      rw [heq] at hmin
      have h0 : (maximalIdeal R).height = 0 := Ideal.height_eq_zero_iff.mpr hmin
      have : ringKrullDim R = 0 := by
        rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h0]; rfl
      exact h.ne' this
  rw [Set.not_subset] at hnot
  obtain ⟨x, hx, hxU⟩ := hnot
  refine ⟨x, hx, fun hx2 => hxU ?_, fun p hp hxp => hxU ?_⟩
  · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hx2
  · exact Set.mem_biUnion
      (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hp))) hxp

/-! ### 3. The quotient by a parameter, and the converse -/

/-- Let `R` be a regular local ring and let `x ∈ 𝔪 \ 𝔪²`. Then `R / (x)` is a regular local ring
and `dim R / (x) + 1 = dim R` (Stacks tag 00NQ). -/
theorem quotient_span_singleton [IsRegularLocalRing R] {x : R}
    (mem : x ∈ maximalIdeal R) (nmem : x ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ span {x}) ∧ ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have : IsLocalRing (R ⧸ span {x}) :=
    isLocalRing_quotient_of_le_maximalIdeal ((span_singleton_le_iff_mem _).mpr mem)
  have hsf := spanFinrank_maximalIdeal_quotient_add_one_le mem nmem
  have hreg : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have hle : ringKrullDim R ≤ ringKrullDim (R ⧸ span {x}) + 1 := by
    refine (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (span {x}) ?_).trans
      (add_le_add le_rfl ?_)
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal R]
      exact (span_singleton_le_iff_mem _).mpr mem
    · have h1 : (span {x}).spanFinrank ≤ 1 :=
        (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)).trans_eq
          (Set.ncard_singleton x)
      exact_mod_cast h1
  have hQle : ringKrullDim (R ⧸ span {x}) ≤
      ((maximalIdeal (R ⧸ span {x})).spanFinrank : WithBot ℕ∞) :=
    ringKrullDim_le_spanFinrank_maximalIdeal _
  obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast (R ⧸ span {x})
  rw [hm] at hle hQle
  rw [← hreg] at hle
  have h1 : (maximalIdeal R).spanFinrank ≤ m + 1 := by exact_mod_cast hle
  have h2 : m ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank := by exact_mod_cast hQle
  have h3 : (maximalIdeal (R ⧸ span {x})).spanFinrank = m := by omega
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_, ?_⟩
  · rw [hm, h3]
  · rw [hm, ← hreg]
    have : m + 1 = (maximalIdeal R).spanFinrank := by omega
    exact_mod_cast this

/-- Let `R` be a Noetherian local ring, let `x ∈ 𝔪` be a nonzerodivisor, and assume that
`R / (x)` is a regular local ring. Then `R` is a regular local ring and
`dim R / (x) + 1 = dim R` (Stacks tag 00NU). -/
theorem of_quotient_span_singleton [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (reg : x ∈ nonZeroDivisors R)
    (hq : IsRegularLocalRing (R ⧸ span {x})) :
    IsRegularLocalRing R ∧ ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have hdim :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors reg hx
  refine ⟨?_, hdim⟩
  have := hq
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h1 := spanFinrank_maximalIdeal_le_spanFinrank_maximalIdeal_quotient_add_one hx
  have h2 : ((maximalIdeal (R ⧸ span {x})).spanFinrank : WithBot ℕ∞) =
      ringKrullDim (R ⧸ span {x}) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ span {x})
  calc ((maximalIdeal R).spanFinrank : WithBot ℕ∞)
      ≤ (((maximalIdeal (R ⧸ span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h1
    _ = ringKrullDim (R ⧸ span {x}) + 1 := by push_cast; rw [h2]
    _ = ringKrullDim R := hdim

/-! ### 4. A regular local ring is a domain -/

/-- A regular local ring of dimension `n` is a domain. The proof is by induction on `n`, as in
[Mat89, Theorem 14.3]. -/
theorem isDomain_of_isRegularLocalRing_of_ringKrullDim_eq (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], ringKrullDim R = n → IsDomain R := by
  induction n with
  | zero =>
    intro R _ _ h
    have h0 : (maximalIdeal R).spanFinrank = 0 := by
      have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
      rw [h] at this
      exact_mod_cast this
    have hbot : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp h0
    have : (⊥ : Ideal R).IsPrime := hbot ▸ (maximalIdeal.isMaximal R).isPrime
    exact IsDomain.of_bot_isPrime R
  | succ n ih =>
    intro R _ _ h
    have hpos : 0 < ringKrullDim R := by
      rw [h]; exact_mod_cast Nat.succ_pos n
    obtain ⟨x, mem, nmem, hmin⟩ :=
      exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes hpos
    obtain ⟨hQ, hdim⟩ := quotient_span_singleton mem nmem
    have := hQ
    have hQn : ringKrullDim (R ⧸ span {x}) = n := by
      obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast (R ⧸ span {x})
      rw [hm, h] at hdim
      have : m + 1 = n + 1 := by exact_mod_cast hdim
      rw [hm, Nat.succ_inj.mp this]
    have hdom : IsDomain (R ⧸ span {x}) := ih _ hQn
    have hprime : (span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := span {x}) bot_le
    have hPprime : P.IsPrime := IsMinimalPrime.isPrime hP
    have hxP : x ∉ P := hmin P hP
    have hle : P ≤ span {x} • P := by
      intro y hy
      obtain ⟨z, rfl⟩ := mem_span_singleton'.mp (hPle hy)
      have hz : z ∈ P := (hPprime.mem_or_mem hy).resolve_right hxP
      rw [mul_comm]
      exact Submodule.smul_mem_smul (mem_span_singleton_self x) hz
    have hjac : span {x} ≤ Ideal.jacobson ⊥ :=
      ((span_singleton_le_iff_mem _).mpr mem).trans (maximalIdeal_le_jacobson _)
    have hPbot : P = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (span {x}) P P.fg_of_isNoetherianRing hle hjac
    have : (⊥ : Ideal R).IsPrime := hPbot ▸ hPprime
    exact IsDomain.of_bot_isPrime R

/-- A regular local ring is a domain (Stacks tag 00NP, [Mat89, Theorem 14.3]). -/
theorem isDomain_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := by
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast R
  exact isDomain_of_isRegularLocalRing_of_ringKrullDim_eq n R hn

/-! ### 5. Dimension 1 -/

section DimOne

variable [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]

omit [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] in
/-- A ring of dimension 1 is not a field. -/
theorem not_isField_of_ringKrullDim_eq_one (h : ringKrullDim R = 1) : ¬ IsField R := by
  intro hF
  rw [ringKrullDim_eq_zero_of_isField hF] at h
  exact zero_ne_one h

/-- In a local domain of dimension 1, the maximal ideal is the only nonzero prime. -/
theorem eq_maximalIdeal_of_isPrime_of_ne_bot (h : ringKrullDim R = 1) {P : Ideal R}
    [hP : P.IsPrime] (hne : P ≠ ⊥) : P = maximalIdeal R := by
  by_contra hPm
  have hlt : P < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal hP.ne_top) hPm
  have hm : (maximalIdeal R).height = 1 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [h] at this
    exact_mod_cast this
  have hPh : P.height < 1 := by
    have := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    rwa [hm] at this
  have h0 : P.height = 0 := Order.lt_one_iff.mp hPh
  exact hne (Ideal.height_eq_zero_iff_eq_bot.mp h0)

/-- A Noetherian local domain of dimension 1 is regular if and only if it is a discrete
valuation ring ([AM69, Proposition 9.2]). -/
theorem isRegularLocalRing_iff_isDiscreteValuationRing (h : ringKrullDim R = 1) :
    IsRegularLocalRing R ↔ IsDiscreteValuationRing R := by
  have hF := not_isField_of_ringKrullDim_eq_one h
  have e := (IsDiscreteValuationRing.TFAE R hF).out 1 6
  rw [e, IsRegularLocalRing.iff_finrank_cotangentSpace R, h]
  constructor
  · intro e; exact_mod_cast e
  · intro e; exact_mod_cast e

/-- A Noetherian local domain of dimension 1 is regular if and only if it is integrally closed
([AM69, Proposition 9.2], [Mat89, Theorem 11.2]). -/
theorem isRegularLocalRing_iff_isIntegrallyClosed (h : ringKrullDim R = 1) :
    IsRegularLocalRing R ↔ IsIntegrallyClosed R := by
  have hF := not_isField_of_ringKrullDim_eq_one h
  have e := (IsDiscreteValuationRing.TFAE R hF).out 1 4
  rw [isRegularLocalRing_iff_isDiscreteValuationRing h, e]
  refine ⟨And.left, fun hic => ⟨hic, ⟨maximalIdeal R, ⟨?_, inferInstance⟩, ?_⟩⟩⟩
  · intro hm
    exact hF ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hm)
  · rintro P ⟨hne, hP⟩
    exact eq_maximalIdeal_of_isPrime_of_ne_bot h hne

end DimOne

end Singularity.Algebra
