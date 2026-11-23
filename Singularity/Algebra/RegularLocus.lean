/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.RegularLocalization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The regular locus of a Noetherian ring

Let `A` be a Noetherian ring. The regular locus `Reg(A)` is the set of the primes `p` such that
`A_p` is a regular local ring. This file proves the criterion of Nagata for the openness of
`Reg(A)` ([Mat89, Theorem 24.4]).

## Main results

* `regularLocus_stableUnderGeneralization`: if `q ⊆ p` and `A_p` is regular, then `A_q` is
  regular. This is the localization theorem of Serre.
* `exists_notMem_isRegularLocalRing_of_quotient`: let `A_p` be regular. Then there is `f ∉ p`
  such that for each prime `q ⊇ p` with `f ∉ q`, if `A_q / p A_q` is regular, then `A_q` is
  regular.
* `isOpen_of_stableUnderGeneralization`: a set `U` of primes is open if it is closed under
  generization and each `p ∈ U` has a basic open `D(f) ∋ p` with `D(f) ∩ V(p) ⊆ U`.
* `isOpen_regularLocus`: the criterion of Nagata. If for each `p ∈ Reg(A)` the ring `A_q / p A_q`
  is regular for all `q` in a set `D(g) ∩ V(p)` with `g ∉ p`, then `Reg(A)` is open.
* `localizationQuotientEquiv`: for primes `p ⊆ q`, the ring `(A / p)_(q / p)` is isomorphic to
  `A_q / p A_q`.
* `isOpen_regularLocus_of_exists_isOpen`: the criterion of Nagata in the form of the textbook.
  If for each `p ∈ Reg(A)` the set `Reg(A / p)` contains a nonempty open set, then `Reg(A)` is
  open.

## The proof

The second result is an induction on `dim A_p / I A_p` for an ideal `I ⊆ p`. If the dimension
is `0`, then `p A_p = I A_p`, and this equality spreads to an open set `D(f)`. In the other case,
take `x ∈ p` whose image is in `m \ m²` of `A_p / I A_p`. The image of `x` is a nonzerodivisor
in `A_q / I A_q` for `q` in an open set `D(g)`, and the induction hypothesis for the ideal
`I + (x)` with Proposition 1.2.8 of the handbook completes the step.

The topological result uses the finitely many minimal primes of the closure of the complement.

## References

* [Mat89] H. Matsumura, *Commutative Ring Theory*, Cambridge University Press, 1989.
-/

universe u

open IsLocalRing Ideal

namespace Singularity.Algebra

variable {A : Type u} [CommRing A]

/-- The regular locus of a ring: the primes `p` such that `A_p` is a regular local ring. -/
def regularLocus (A : Type u) [CommRing A] : Set (PrimeSpectrum A) :=
  {p | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

theorem mem_regularLocus {p : PrimeSpectrum A} :
    p ∈ regularLocus A ↔ IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
  Iff.rfl

/-- The regular locus of a Noetherian ring is closed under generization. -/
theorem regularLocus_stableUnderGeneralization [IsNoetherianRing A] :
    StableUnderGeneralization (regularLocus A) := by
  intro p q hqp hp
  obtain ⟨q, hq⟩ := q
  have hle : q ≤ p.asIdeal := (PrimeSpectrum.le_iff_specializes ⟨q, hq⟩ p).mpr hqp
  have : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hp
  have hd : Disjoint (p.asIdeal.primeCompl : Set A) q :=
    Set.disjoint_left.mpr fun _ hx hxq => hx (hle hxq)
  obtain ⟨Q, hQ, hQq⟩ : ∃ Q : Ideal (Localization.AtPrime p.asIdeal), Q.IsPrime ∧
      Q.comap (algebraMap A (Localization.AtPrime p.asIdeal)) = q :=
    ⟨q.map _, IsLocalization.isPrime_of_isPrime_disjoint p.asIdeal.primeCompl _ q hq hd,
      IsLocalization.under_map_of_isPrime_disjoint p.asIdeal.primeCompl _ hq hd⟩
  subst hQq
  have := isRegularLocalRing_localization Q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization p.asIdeal.primeCompl
      Q).symm.toRingEquiv

/-- Let `p` be a prime of a Noetherian ring and let `J` be an ideal. If each `y ∈ J` has some
`s ∉ p` with `s y ∈ I`, then one `g ∉ p` has `g y ∈ I` for all `y ∈ J`. -/
theorem exists_notMem_forall_mul_mem [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    (I J : Ideal A) (h : ∀ y ∈ J, ∃ s ∉ p, s * y ∈ I) : ∃ g ∉ p, ∀ y ∈ J, g * y ∈ I := by
  suffices key : ∀ (N : Submodule A A) (_ : N.FG), (∀ y ∈ N, ∃ s ∉ p, s * y ∈ I) →
      ∃ g ∉ p, ∀ y ∈ N, g * y ∈ I from key J (IsNoetherian.noetherian J) h
  intro N hN
  induction N, hN using Submodule.fg_induction with
  | singleton x =>
    intro h
    obtain ⟨s, hs, hsx⟩ := h x (Submodule.mem_span_singleton_self x)
    refine ⟨s, hs, fun y hy => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [smul_eq_mul, mul_left_comm]
    exact I.mul_mem_left c hsx
  | sup N₁ N₂ _ _ ih₁ ih₂ =>
    intro h
    obtain ⟨g₁, hg₁, h₁⟩ := ih₁ fun y hy => h y (Submodule.mem_sup_left hy)
    obtain ⟨g₂, hg₂, h₂⟩ := ih₂ fun y hy => h y (Submodule.mem_sup_right hy)
    refine ⟨g₁ * g₂, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hg₁ hg₂, fun y hy => ?_⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [mul_add]
    refine I.add_mem ?_ ?_
    · rw [mul_right_comm]
      exact I.mul_mem_right _ (h₁ y₁ hy₁)
    · rw [mul_assoc]
      exact I.mul_mem_left _ (h₂ y₂ hy₂)

/-- The quotient of `S / I S` by the image of `a` is `S / (I + (a)) S`. -/
noncomputable def quotQuotSpanEquiv {S : Type u} [CommRing S] (φ : A →+* S) (I : Ideal A)
    (a : A) : (S ⧸ I.map φ) ⧸ span {Ideal.Quotient.mk (I.map φ) (φ a)} ≃+*
      S ⧸ (I ⊔ span {a}).map φ :=
  (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
    ((DoubleQuot.quotQuotEquivQuotSup (I.map φ) (span {φ a})).trans
      (Ideal.quotEquivOfEq (by rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton])))

/-- Let `q` be a prime and let `y ∈ A`. If `g ∉ q` and `g y ∈ I`, then the image of `y` in
`A_q` is in `I A_q`. -/
theorem algebraMap_mem_map_of_mul_mem (q : Ideal A) [q.IsPrime] (I : Ideal A) {g y : A}
    (hg : g ∉ q) (hgy : g * y ∈ I) :
    algebraMap A (Localization.AtPrime q) y ∈ I.map (algebraMap A (Localization.AtPrime q)) := by
  have hu : IsUnit (algebraMap A (Localization.AtPrime q) g) :=
    IsLocalization.map_units (Localization.AtPrime q) (⟨g, hg⟩ : q.primeCompl)
  refine (Ideal.unit_mul_mem_iff_mem _ hu).mp ?_
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ hgy

/-- The quotient `A_q / I A_q` is a local ring when `I ⊆ q`. -/
theorem isLocalRing_localization_quotient (q : Ideal A) [q.IsPrime] {I : Ideal A}
    (hI : I ≤ q) : IsLocalRing (Localization.AtPrime q ⧸ I.map (algebraMap A (Localization.AtPrime q))) := by
  refine isLocalRing_quotient_of_le_maximalIdeal (Ideal.map_le_iff_le_comap.mpr fun y hy => ?_)
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q y).mpr (hI hy)

/-- The induction step of the spreading lemma, for an ideal `I ⊆ p` with
`dim A_p / I A_p = r`. -/
theorem exists_notMem_isRegularLocalRing_quotient [IsNoetherianRing A] (p : Ideal A)
    [p.IsPrime] (r : ℕ) :
    ∀ I : Ideal A, I ≤ p →
      IsRegularLocalRing (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) →
      ringKrullDim (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) = r →
      ∃ f ∉ p, ∀ (q : Ideal A) [q.IsPrime], p ≤ q → f ∉ q →
        IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) →
        IsRegularLocalRing (Localization.AtPrime q ⧸ I.map (algebraMap A (Localization.AtPrime q))) := by
  induction r with
  | zero =>
    intro I hI hreg hdim
    set B := Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))
    have h0 : (maximalIdeal B).spanFinrank = 0 := by
      have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := B)
      rw [hdim] at this
      exact_mod_cast this
    have hbot : maximalIdeal B = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal B).fg_of_isNoetherianRing).mp h0
    have hsp : ∀ y ∈ p, ∃ s ∉ p, s * y ∈ I := by
      intro y hy
      have hy' : algebraMap A (Localization.AtPrime p) y ∈ maximalIdeal _ :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p y).mpr hy
      have hmk : Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p)))
          (algebraMap A (Localization.AtPrime p) y) ∈ maximalIdeal B := by
        rw [maximalIdeal_quotient_eq_map]
        exact Ideal.mem_map_of_mem _ hy'
      rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmk
      obtain ⟨s, hs, hsy⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl _ I y).mp hmk
      exact ⟨s, hs, hsy⟩
    obtain ⟨g, hg, hgp⟩ := exists_notMem_forall_mul_mem p I p hsp
    refine ⟨g, hg, fun q _ hpq hgq hq => ?_⟩
    have heq : p.map (algebraMap A (Localization.AtPrime q)) =
        I.map (algebraMap A (Localization.AtPrime q)) :=
      le_antisymm (Ideal.map_le_iff_le_comap.mpr fun y hy =>
        algebraMap_mem_map_of_mul_mem q I hgq (hgp y hy)) (Ideal.map_mono hI)
    exact IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq heq)
  | succ r ih =>
    intro I hI hreg hdim
    set B := Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))
    have hpos : 0 < ringKrullDim B := by
      rw [hdim]
      exact_mod_cast Nat.succ_pos r
    obtain ⟨z, hzm, hzm2, -⟩ := exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes hpos
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, hw0⟩ := IsLocalization.mk'_surjective p.primeCompl w
    dsimp only at hw0
    subst hw0
    have hw : IsLocalization.mk' (Localization.AtPrime p) a s ∈ maximalIdeal _ :=
      (mem_maximalIdeal _).mpr fun hu =>
        (mem_maximalIdeal _).mp hzm (hu.map (Ideal.Quotient.mk _))
    have ha : a ∈ p :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime p) p a s).mp hw
    -- the image `x` of `a` in `B` is the unit multiple `z * s` of `z`
    have hus : IsUnit (Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p)))
        (algebraMap A (Localization.AtPrime p) s)) :=
      (IsLocalization.map_units (Localization.AtPrime p) s).map _
    have hx : Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p)))
        (algebraMap A (Localization.AtPrime p) a) =
        Ideal.Quotient.mk _ (IsLocalization.mk' (Localization.AtPrime p) a s) *
          Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime p) s) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    have hxm : Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p)))
        (algebraMap A (Localization.AtPrime p) a) ∈ maximalIdeal B := by
      rw [hx]
      exact Ideal.mul_mem_right _ _ hzm
    have hxm2 : Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p)))
        (algebraMap A (Localization.AtPrime p) a) ∉ maximalIdeal B ^ 2 := by
      rw [hx, Ideal.mul_unit_mem_iff_mem _ hus]
      exact hzm2
    -- the ideal `I + (a)` satisfies the induction hypothesis
    obtain ⟨hreg', hdim'⟩ := quotient_span_singleton hxm hxm2
    set xB : B := Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p)))
      (algebraMap A (Localization.AtPrime p) a) with hxB
    have e := quotQuotSpanEquiv (algebraMap A (Localization.AtPrime p)) I a
    have hI' : I ⊔ span {a} ≤ p := sup_le hI ((span_singleton_le_iff_mem _).mpr ha)
    have hreg'' : IsRegularLocalRing
        (Localization.AtPrime p ⧸ (I ⊔ span {a}).map (algebraMap A (Localization.AtPrime p))) :=
      IsRegularLocalRing.of_ringEquiv e
    have hdim'' : ringKrullDim
        (Localization.AtPrime p ⧸ (I ⊔ span {a}).map (algebraMap A (Localization.AtPrime p))) = r := by
      rw [← ringKrullDim_eq_of_ringEquiv e]
      obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast (B ⧸ span {xB})
      rw [hn] at hdim' ⊢
      rw [hdim] at hdim'
      have : n + 1 = r + 1 := by exact_mod_cast hdim'
      rw [show n = r by omega]
    obtain ⟨f, hf, hfq⟩ := ih (I ⊔ span {a}) hI' hreg'' hdim''
    -- the image of `a` is a nonzerodivisor near `p`
    have hdom : IsDomain B := isDomain_of_isRegularLocalRing B
    have hx0 : xB ≠ 0 := by
      intro h0
      apply hxm2
      rw [h0]
      exact Ideal.zero_mem _
    have hcol : ∀ y ∈ Submodule.colon I {a}, ∃ s ∉ p, s * y ∈ I := by
      intro y hy
      have hya : y * a ∈ I := Submodule.mem_colon_singleton.mp hy
      have h1 : Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p)))
          (algebraMap A (Localization.AtPrime p) y) *
          Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p)))
            (algebraMap A (Localization.AtPrime p) a) = 0 := by
        rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ hya
      have h2 := (mul_eq_zero.mp h1).resolve_right hx0
      rw [Ideal.Quotient.eq_zero_iff_mem] at h2
      obtain ⟨s, hs, hsy⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl _ I y).mp h2
      exact ⟨s, hs, hsy⟩
    obtain ⟨g, hg, hgc⟩ := exists_notMem_forall_mul_mem p I (Submodule.colon I {a}) hcol
    refine ⟨f * g, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hf hg,
      fun q _ hpq hfgq hq => ?_⟩
    have hfq' : f ∉ q := fun h => hfgq (q.mul_mem_right g h)
    have hgq : g ∉ q := fun h => hfgq (q.mul_mem_left f h)
    have hq' := hfq q hpq hfq' hq
    have := isLocalRing_localization_quotient q (hI.trans hpq)
    set C := Localization.AtPrime q ⧸ I.map (algebraMap A (Localization.AtPrime q))
    have hxq : Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime q)))
        (algebraMap A (Localization.AtPrime q) a) ∈ maximalIdeal C := by
      rw [maximalIdeal_quotient_eq_map]
      exact Ideal.mem_map_of_mem _
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q a).mpr
          (hpq ha))
    have hnzd : Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime q)))
        (algebraMap A (Localization.AtPrime q) a) ∈ nonZeroDivisors C := by
      refine mem_nonZeroDivisors_iff_right.mpr fun c hc => ?_
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨⟨b, t⟩, hw0⟩ := IsLocalization.mk'_surjective q.primeCompl w
      dsimp only at hw0
      subst hw0
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hc
      have hut : IsUnit (algebraMap A (Localization.AtPrime q) t) :=
        IsLocalization.map_units (Localization.AtPrime q) t
      have hba : algebraMap A (Localization.AtPrime q) (b * a) ∈
          I.map (algebraMap A (Localization.AtPrime q)) := by
        have := Ideal.mul_mem_right (algebraMap A (Localization.AtPrime q) t) _ hc
        rwa [mul_right_comm, IsLocalization.mk'_spec, ← map_mul] at this
      obtain ⟨u, hu, hub⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl _ I _).mp hba
      have hcol' : u * b ∈ Submodule.colon I {a} := by
        rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc]
        exact hub
      have hb : algebraMap A (Localization.AtPrime q) b ∈
          I.map (algebraMap A (Localization.AtPrime q)) := by
        refine algebraMap_mem_map_of_mul_mem q I (g := g * u)
          (fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hgq hu) ?_
        rw [mul_assoc]
        exact hgc _ hcol'
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rw [← IsLocalization.mk'_spec (Localization.AtPrime q) b t] at hb
      exact (Ideal.mul_unit_mem_iff_mem _ hut).mp hb
    set xq : C := Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime q)))
      (algebraMap A (Localization.AtPrime q) a)
    have hreg_q : IsRegularLocalRing (C ⧸ span {xq}) :=
      IsRegularLocalRing.of_ringEquiv
        (quotQuotSpanEquiv (algebraMap A (Localization.AtPrime q)) I a).symm
    exact (of_quotient_span_singleton hxq hnzd hreg_q).1

/-- Let `p` be a prime of a Noetherian ring `A` such that `A_p` is regular. Then there is
`f ∉ p` such that for each prime `q ⊇ p` with `f ∉ q`, if `A_q / p A_q` is regular, then `A_q`
is regular. -/
theorem exists_notMem_isRegularLocalRing_of_quotient [IsNoetherianRing A] (p : Ideal A)
    [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)] :
    ∃ f ∉ p, ∀ (q : Ideal A) [q.IsPrime], p ≤ q → f ∉ q →
      IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) →
      IsRegularLocalRing (Localization.AtPrime q) := by
  have e₀ : ∀ (S : Type u) [CommRing S] [Algebra A S],
      S ⧸ (⊥ : Ideal A).map (algebraMap A S) ≃+* S := fun S _ _ =>
    (Ideal.quotEquivOfEq (Ideal.map_bot)).trans (RingEquiv.quotientBot S)
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast (Localization.AtPrime p)
  have hreg : IsRegularLocalRing (Localization.AtPrime p ⧸ (⊥ : Ideal A).map (algebraMap A (Localization.AtPrime p))) :=
    IsRegularLocalRing.of_ringEquiv (e₀ _).symm
  have hdim : ringKrullDim (Localization.AtPrime p ⧸ (⊥ : Ideal A).map (algebraMap A (Localization.AtPrime p))) = n := by
    rw [ringKrullDim_eq_of_ringEquiv (e₀ _), hn]
  obtain ⟨f, hf, h⟩ := exists_notMem_isRegularLocalRing_quotient p n ⊥ bot_le hreg hdim
  refine ⟨f, hf, fun q _ hpq hfq hq => ?_⟩
  have := h q hpq hfq hq
  exact IsRegularLocalRing.of_ringEquiv (e₀ _)

/-- A set `U` of primes of a Noetherian ring is open if it is closed under generization and
each `p ∈ U` has `f ∉ p` such that each prime `q ⊇ p` with `f ∉ q` is in `U`
([Mat89, Lemma 24.2]). -/
theorem isOpen_of_stableUnderGeneralization [IsNoetherianRing A] (U : Set (PrimeSpectrum A))
    (hU : StableUnderGeneralization U)
    (h : ∀ p ∈ U, ∃ f : A, f ∉ p.asIdeal ∧
      ∀ q : PrimeSpectrum A, p ≤ q → f ∉ q.asIdeal → q ∈ U) :
    IsOpen U := by
  rw [← isClosed_compl_iff, ← closure_subset_iff_isClosed]
  set J := PrimeSpectrum.vanishingIdeal Uᶜ
  have hcl : closure Uᶜ = PrimeSpectrum.zeroLocus (J : Set A) :=
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).symm
  -- each minimal prime over `J` is in the complement of `U`
  have hmin : ∀ P ∈ J.minimalPrimes, ∀ hP : P.IsPrime, (⟨P, hP⟩ : PrimeSpectrum A) ∈ Uᶜ := by
    intro P hPmin hP hPU
    obtain ⟨f, hf, hfU⟩ := h ⟨P, hP⟩ hPU
    have hfin : (J.minimalPrimes \ {P}).Finite :=
      (Ideal.finite_minimalPrimes_of_isNoetherianRing A J).sdiff
    let O : Set (PrimeSpectrum A) := (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) ∩
      ⋂ Q ∈ J.minimalPrimes \ {P}, (PrimeSpectrum.zeroLocus (Q : Set A))ᶜ
    have hO : IsOpen O := (PrimeSpectrum.basicOpen f).isOpen.inter
      (hfin.isOpen_biInter fun Q _ => (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl)
    have hPO : (⟨P, hP⟩ : PrimeSpectrum A) ∈ O := by
      refine ⟨hf, Set.mem_iInter₂.mpr fun Q hQ hPQ => ?_⟩
      have hQP : Q ≤ P := (PrimeSpectrum.mem_zeroLocus _ _).mp hPQ
      exact hQ.2 (Set.mem_singleton_iff.mpr
        (le_antisymm hQP (hPmin.2 hQ.1.1 hQP)))
    have hPcl : (⟨P, hP⟩ : PrimeSpectrum A) ∈ closure Uᶜ := by
      rw [hcl]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr hPmin.1.2
    obtain ⟨q, hqO, hqU⟩ := mem_closure_iff.mp hPcl O hO hPO
    have hJq : J ≤ q.asIdeal :=
      (PrimeSpectrum.mem_zeroLocus _ _).mp (hcl ▸ subset_closure hqU)
    obtain ⟨Q, hQ, hQq⟩ := Ideal.exists_minimalPrimes_le hJq
    by_cases hQP : Q = P
    · subst hQP
      exact hqU (hfU q hQq hqO.1)
    · exact Set.mem_iInter₂.mp hqO.2 Q ⟨hQ, hQP⟩
        ((PrimeSpectrum.mem_zeroLocus _ _).mpr hQq)
  intro z hz
  rw [hcl] at hz
  have hJz : J ≤ z.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp hz
  obtain ⟨P, hP, hPz⟩ := Ideal.exists_minimalPrimes_le hJz
  intro hzU
  exact hmin P hP hP.1.1 (hU ((PrimeSpectrum.le_iff_specializes ⟨P, hP.1.1⟩ z).mp hPz) hzU)

/-- The criterion of Nagata ([Mat89, Theorem 24.4]). Let `A` be a Noetherian ring. Assume that
each `p ∈ Reg(A)` has `g ∉ p` such that `A_q / p A_q` is regular for each prime `q ⊇ p` with
`g ∉ q`. Then the regular locus of `A` is open. -/
theorem isOpen_regularLocus [IsNoetherianRing A]
    (h : ∀ p ∈ regularLocus A, ∃ g ∉ p.asIdeal, ∀ q : PrimeSpectrum A, p ≤ q → g ∉ q.asIdeal →
      IsRegularLocalRing (Localization.AtPrime q.asIdeal ⧸
        p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) :
    IsOpen (regularLocus A) := by
  refine isOpen_of_stableUnderGeneralization _ regularLocus_stableUnderGeneralization
    fun p hp => ?_
  have : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hp
  obtain ⟨f, hf, hfq⟩ := exists_notMem_isRegularLocalRing_of_quotient p.asIdeal
  obtain ⟨g, hg, hgq⟩ := h p hp
  refine ⟨f * g, fun hm => (Ideal.IsPrime.mem_or_mem p.2 hm).elim hf hg, fun q hpq hq => ?_⟩
  have hfq' : f ∉ q.asIdeal := fun h' => hq (q.asIdeal.mul_mem_right g h')
  have hgq' : g ∉ q.asIdeal := fun h' => hq (q.asIdeal.mul_mem_left f h')
  exact hfq q.asIdeal hpq hfq' (hgq q hpq hgq')

/-- Let `p ⊆ q` be ideals with `q` prime. Then `q / p` is a prime of `A / p`. -/
theorem isPrime_map_quotient (p q : Ideal A) [q.IsPrime] (hpq : p ≤ q) :
    (q.map (Ideal.Quotient.mk p)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

/-- Let `p ⊆ q` be ideals with `q` prime. Then `A_q / p A_q` is the localization of `A / p` at
the prime `q / p`. -/
theorem isLocalization_localization_quotient (p q : Ideal A) [q.IsPrime] (hpq : p ≤ q)
    [(q.map (Ideal.Quotient.mk p)).IsPrime] :
    IsLocalization (q.map (Ideal.Quotient.mk p)).primeCompl
      (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) := by
  have hmem : ∀ y : A, Ideal.Quotient.mk p y ∈ q.map (Ideal.Quotient.mk p) ↔ y ∈ q :=
    fun y => Ideal.mem_quotient_iff_mem hpq
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hyq : y ∉ q := fun h => hy ((hmem y).mpr h)
    exact (IsLocalization.map_units (Localization.AtPrime q) (⟨y, hyq⟩ : q.primeCompl)).map
      (Ideal.Quotient.mk _)
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, hw⟩ := IsLocalization.mk'_surjective q.primeCompl w
    dsimp only at hw
    subst hw
    refine ⟨⟨Ideal.Quotient.mk p a, ⟨Ideal.Quotient.mk p s, fun h => s.2 ((hmem s).mp h)⟩⟩, ?_⟩
    show Ideal.Quotient.mk _ (IsLocalization.mk' (Localization.AtPrime q) a s) *
        Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime q) (s : A)) =
      Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime q) a)
    rw [← map_mul, IsLocalization.mk'_spec]
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime q) x) =
      Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime q) y) at hxy
    rw [Ideal.Quotient.eq, ← map_sub] at hxy
    obtain ⟨u, hu, hux⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl _ p _).mp hxy
    refine ⟨⟨Ideal.Quotient.mk p u, fun h => hu ((hmem u).mp h)⟩, ?_⟩
    show Ideal.Quotient.mk p u * Ideal.Quotient.mk p x = Ideal.Quotient.mk p u * Ideal.Quotient.mk p y
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
    exact hux

/-- Let `p ⊆ q` be ideals with `q` prime. Then `(A / p)_(q / p)` is isomorphic to `A_q / p A_q`. -/
noncomputable def localizationQuotientEquiv (p q : Ideal A) [q.IsPrime] (hpq : p ≤ q)
    [(q.map (Ideal.Quotient.mk p)).IsPrime] :
    Localization.AtPrime (q.map (Ideal.Quotient.mk p)) ≃+*
      Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q)) :=
  haveI := isLocalization_localization_quotient p q hpq
  (IsLocalization.algEquiv (q.map (Ideal.Quotient.mk p)).primeCompl _ _).toRingEquiv

/-- The criterion of Nagata in the form of [Mat89, Theorem 24.4]. Let `A` be a Noetherian ring.
Assume that for each `p ∈ Reg(A)` the regular locus of `A / p` contains a nonempty open set.
Then the regular locus of `A` is open. -/
theorem isOpen_regularLocus_of_exists_isOpen [IsNoetherianRing A]
    (h : ∀ p ∈ regularLocus A, ∃ U : Set (PrimeSpectrum (A ⧸ p.asIdeal)),
      IsOpen U ∧ U.Nonempty ∧ U ⊆ regularLocus (A ⧸ p.asIdeal)) :
    IsOpen (regularLocus A) := by
  refine isOpen_regularLocus fun p hp => ?_
  obtain ⟨U, hU, ⟨u, hu⟩, hUreg⟩ := h p hp
  -- the generic point of `Spec (A / p)` is in `U`
  have h0 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (A ⧸ p.asIdeal)) ∈ U :=
    hU.stableUnderGeneralization ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le) hu
  obtain ⟨_, ⟨g, rfl⟩, hg0, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h0 hU
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
  have hg0' := (PrimeSpectrum.mem_basicOpen _ _).mp hg0
  have hgp : g ∉ p.asIdeal := fun h' =>
    hg0' ((Ideal.mem_bot).mpr (Ideal.Quotient.eq_zero_iff_mem.mpr h'))
  refine ⟨g, hgp, fun q hpq hgq => ?_⟩
  have := isPrime_map_quotient p.asIdeal q.asIdeal hpq
  have hmem : (⟨q.asIdeal.map (Ideal.Quotient.mk p.asIdeal), this⟩ :
      PrimeSpectrum (A ⧸ p.asIdeal)) ∈ U :=
    hgU ((PrimeSpectrum.mem_basicOpen _ _).mpr fun h' =>
      hgq ((Ideal.mem_quotient_iff_mem hpq).mp h'))
  have : IsRegularLocalRing (Localization.AtPrime (q.asIdeal.map
      (Ideal.Quotient.mk p.asIdeal))) := hUreg hmem
  exact IsRegularLocalRing.of_ringEquiv (localizationQuotientEquiv p.asIdeal q.asIdeal hpq)

end Singularity.Algebra
