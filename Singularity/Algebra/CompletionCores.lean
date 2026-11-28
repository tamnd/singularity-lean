/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib
import Singularity.Algebra.HilbertSerre

/-!
# Dimension, completion, coefficient fields and Cohen rings

This file proves results of Volume 1, Chapters 1, 3, 4 and 6 of the handbook.

## Theorem 1.1.2 (the dimension theorem), in full

* `dimension_theorem`: for a Noetherian local ring `R`, `dim R` is finite, there is an
  `m`-primary ideal with `dim R` generators, and each `m`-primary ideal needs at least `dim R`
  generators. An ideal is `m`-primary here when its radical is `m`.

The proof uses the height theorem of Krull and its converse from Mathlib.

## Remark 3.1.7, one part

* `exists_primary_isEventuallyPolynomial_hilbertSamuel`: there is an `m`-primary ideal `q` with
  `dim R` generators such that the Hilbert-Samuel function of each finitely generated module with
  respect to `q` is eventually a polynomial of degree at most `dim R`.

The bound for every `m`-primary ideal, the equality of the degree with `dim R` for `M = R` and the
theorem of Nagata are not proved.

## Theorem 4.2.9, in full

* `exists_surjective_mvPowerSeries_adicCompletion`: if `a_1, ..., a_r` generate `I`, then the
  `I`-adic completion of `R` is a quotient of `R[[X_1, ..., X_r]]`. This needs no Noetherian
  hypothesis.
* `isNoetherianRing_adicCompletion`: the `I`-adic completion of a Noetherian ring is Noetherian.

## Theorem 4.3.3, in full

* `ringKrullDim_adicCompletion`: `dim R̂ = dim R` for a Noetherian local ring `R`.
* `spanFinrank_maximalIdeal_adicCompletion`: `edim R̂ = edim R`, from Mathlib.
* `isRegularLocalRing_adicCompletion_iff`: `R̂` is regular if and only if `R` is regular.

The proof of the dimension differs from the handbook. It uses that `R̂` is flat over `R`, the
dimension formula for a flat local map from Mathlib, and `m R̂ = m̂`.

## Theorem 4.4.4, the uniqueness only

* `IsCoefficientField`: Definition 4.4.1 of the handbook.
* `IsCoefficientField.eq`: a Noetherian local ring of characteristic `p` with a perfect residue
  field has at most one coefficient field. The ring need not be complete.

The existence of a coefficient field is not proved.

## Theorem 4.4.9, the case `κ = 𝔽_p` of parts 1 and 2

* `padicInt_isCohenRing`: `ℤ_p` is a complete discrete valuation ring with maximal ideal `(p)`
  and residue field `𝔽_p`, so it is a Cohen ring for `𝔽_p`.
* `exists_isLocalHom_padicInt`: each complete local ring whose residue field has characteristic
  `p` receives a local homomorphism from `ℤ_p`. The map of residue fields is the unique map from
  `𝔽_p` (`ringHom_residueField_padicInt_subsingleton`).

Cohen rings for other fields, the uniqueness of the Cohen ring, the quotient of a power series
ring in part 2 and part 3 are not proved.

## Remark 6.4.8, the step on the coefficients

* `mvPowerSeriesBasis`: a basis of `K` over `L` is a basis of `K[[X]]` over `L[[X]]`.
* `free_mvPowerSeries_and_finrank`: if `K` is free of finite rank over `L`, then `K[[X]]` is free
  over `L[[X]]` of the same rank. With `L = κ^p` and `K = κ` this is the claim that `κ[[y]]` is
  free of rank `p^r` over `κ^p[[y]]`.

The rank `p^(d + r)` of `F_* R̂` is not proved, because Mathlib does not have the Cohen structure
theorem `R̂ ≅ κ[[x]]`.

## Remark 3.3.14

Nothing is proved for Remark 3.3.14. The theorem of Nagata and the computation `e(R) = 1` for the
ring `k[x, y]_{(x, y)}/(x^2, xy)` are not in this file.
-/

namespace Singularity

namespace Algebra

open IsLocalRing

section DimensionTheorem

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] in
theorem maximalIdeal_mem_minimalPrimes_of_radical_eq {q : Ideal R}
    (hq : q.radical = maximalIdeal R) : maximalIdeal R ∈ q.minimalPrimes := by
  refine ⟨⟨inferInstance, hq ▸ Ideal.le_radical⟩, fun p hp _ => ?_⟩
  have := hp.1
  rw [← hq]
  exact (Ideal.IsPrime.radical_le_iff hp.1).2 hp.2

omit [IsNoetherianRing R] in
theorem radical_eq_maximalIdeal_of_mem_minimalPrimes {q : Ideal R}
    (hq : maximalIdeal R ∈ q.minimalPrimes) : q.radical = maximalIdeal R := by
  refine le_antisymm ((Ideal.IsPrime.radical_le_iff inferInstance).2 hq.1.2) ?_
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J hJ => ?_
  have := hJ.2
  exact hq.2 ⟨hJ.2, hJ.1⟩ (le_maximalIdeal hJ.2.ne_top)

theorem ringKrullDim_le_card_of_radical_span_eq {s : Finset R}
    (hs : (Ideal.span (s : Set R)).radical = maximalIdeal R) :
    ringKrullDim R ≤ s.card := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_le_coe.2 (Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (maximalIdeal_mem_minimalPrimes_of_radical_eq hs))

theorem exists_card_eq_ringKrullDim :
    ∃ s : Finset R, (Ideal.span (s : Set R)).radical = maximalIdeal R ∧
      (s.card : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨s, hs, hcard⟩ := (maximalIdeal R).exists_finset_card_eq_height_of_isNoetherianRing
  refine ⟨s, radical_eq_maximalIdeal_of_mem_minimalPrimes hs, ?_⟩
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hcard]
  rfl

/-- Volume 1, Theorem 1.1.2 of the handbook (the dimension theorem): `dim R` is finite, some
`m`-primary ideal has `dim R` generators, and no `m`-primary ideal has fewer generators. -/
theorem dimension_theorem :
    ringKrullDim R < ⊤ ∧
    (∃ s : Finset R, (Ideal.span (s : Set R)).radical = maximalIdeal R ∧
      (s.card : WithBot ℕ∞) = ringKrullDim R) ∧
    ∀ s : Finset R, (Ideal.span (s : Set R)).radical = maximalIdeal R →
      ringKrullDim R ≤ s.card := by
  refine ⟨?_, exists_card_eq_ringKrullDim,
    fun s hs => ringKrullDim_le_card_of_radical_span_eq hs⟩
  obtain ⟨s, -, hs⟩ := exists_card_eq_ringKrullDim (R := R)
  rw [← hs]
  exact WithBot.coe_lt_coe.2 (ENat.natCast_lt_top _)

end DimensionTheorem

section CompletionNoetherian

variable {R : Type*} [CommRing R] (I : Ideal R) {r : ℕ} (a : Fin r → R)

/-- The ideal `(X_1, ..., X_r)` of `R[X_1, ..., X_r]` maps into `I` under `X_i ↦ a_i`. -/
theorem map_idealOfVars_le (ha : ∀ i, a i ∈ I) :
    (MvPolynomial.idealOfVars (Fin r) R).map (MvPolynomial.aeval a) ≤ I := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  simpa using ha i

theorem map_idealOfVars_eq (ha : Ideal.span (Set.range a) = I) :
    (MvPolynomial.idealOfVars (Fin r) R).map (MvPolynomial.aeval a) = I := by
  rw [Ideal.map_span, ← ha, ← Set.range_comp]
  congr 1
  ext x
  simp

/-- The map `R[X]/(X)^n → R/I^n` with `X_i ↦ a_i`. -/
noncomputable def polyQuotPowMap (ha : ∀ i, a i ∈ I) (n : ℕ) :
    MvPolynomial (Fin r) R ⧸ MvPolynomial.idealOfVars (Fin r) R ^ n →+* R ⧸ I ^ n :=
  Ideal.quotientMap (I ^ n) (MvPolynomial.aeval a).toRingHom (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (map_idealOfVars_le I a ha) n)

/-- The ring map `(R[X])^ → R̂` from the `(X)`-adic completion of `R[X_1, ..., X_r]` to the
`I`-adic completion of `R`, given by `X_i ↦ a_i`. -/
noncomputable def adicCompletionPolyMap (ha : ∀ i, a i ∈ I) :
    AdicCompletion (MvPolynomial.idealOfVars (Fin r) R) (MvPolynomial (Fin r) R) →+*
      AdicCompletion I R :=
  AdicCompletion.liftRingHom I
    (fun n => (polyQuotPowMap I a ha n).comp
      (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin r) R) n).toRingHom)
    (fun {m n} hle => by
      ext x
      obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective _ _ x
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AdicCompletion.evalₐ_mk]
      rw [← AdicCompletion.Ideal.mk_eq_mk _ hle s]
      rfl)

theorem evalₐ_adicCompletionPolyMap (ha : ∀ i, a i ∈ I) (n : ℕ)
    (s : AdicCompletion.AdicCauchySequence (MvPolynomial.idealOfVars (Fin r) R)
      (MvPolynomial (Fin r) R)) :
    AdicCompletion.evalₐ I n (adicCompletionPolyMap I a ha (AdicCompletion.mk _ _ s)) =
      Ideal.Quotient.mk (I ^ n) (MvPolynomial.aeval a (s.val n)) := by
  simp only [adicCompletionPolyMap, AlgHom.toRingHom_eq_coe]
  rfl

theorem adicCompletionPolyMap_surjective (ha : Ideal.span (Set.range a) = I) :
    Function.Surjective (adicCompletionPolyMap I a
      (fun i => ha ▸ Ideal.subset_span ⟨i, rfl⟩)) := by
  intro x
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I R x
  set J := MvPolynomial.idealOfVars (Fin r) R
  set ψ := MvPolynomial.aeval (R := R) a
  have hψ : Function.Surjective ψ := fun y => ⟨MvPolynomial.C y, by simp [ψ]⟩
  have hdiff : ∀ n, ∃ t, t ∈ J ^ n ∧ ψ t = c.val (n + 1) - c.val n := by
    intro n
    have key : ∀ y ∈ I ^ n, ∃ t, t ∈ J ^ n ∧ ψ t = y := by
      intro y hy
      rw [← map_idealOfVars_eq I a ha, ← Ideal.map_pow] at hy
      exact (Ideal.mem_map_iff_of_surjective ψ hψ).1 hy
    apply key
    have := AdicCompletion.Ideal.mk_eq_mk I (Nat.le_succ n) c
    rw [Ideal.Quotient.eq] at this
    exact this
  choose d hdJ hdψ using hdiff
  let s : ℕ → MvPolynomial (Fin r) R :=
    fun n => MvPolynomial.C (c.val 0) + ∑ i ∈ Finset.range n, d i
  have hs : ∀ n, ψ (s n) = c.val n := by
    intro n
    have hC : ψ (MvPolynomial.C (c.val 0)) = c.val 0 := MvPolynomial.aeval_C a _
    simp only [s, map_add, map_sum, hdψ, Finset.sum_range_sub (fun i => c.val i), hC]
    ring
  let t : AdicCompletion.AdicCauchySequence J (MvPolynomial (Fin r) R) :=
    AdicCompletion.AdicCauchySequence.mk J _ s (fun n => by
      rw [SModEq.sub_mem]
      have : s n - s (n + 1) = -d n := by simp [s, Finset.sum_range_succ]
      rw [this, neg_mem_iff, smul_eq_mul, Ideal.mul_top]
      exact hdJ n)
  refine ⟨AdicCompletion.mk _ _ t, AdicCompletion.ext_evalₐ fun n => ?_⟩
  rw [evalₐ_adicCompletionPolyMap, AdicCompletion.evalₐ_mk]
  exact congrArg _ (hs n)

/-- Volume 1, Theorem 4.2.9 of the handbook, the second claim: if `a_1, ..., a_r` generate `I`,
then the `I`-adic completion of `R` is a quotient of `R[[X_1, ..., X_r]]`. -/
theorem exists_surjective_mvPowerSeries_adicCompletion (ha : Ideal.span (Set.range a) = I) :
    ∃ φ : MvPowerSeries (Fin r) R →+* AdicCompletion I R, Function.Surjective φ :=
  ⟨(adicCompletionPolyMap I a (fun i => ha ▸ Ideal.subset_span ⟨i, rfl⟩)).comp
      (MvPowerSeries.toAdicCompletionAlgEquiv (Fin r) R).toRingEquiv.toRingHom,
    (adicCompletionPolyMap_surjective I a ha).comp
      (MvPowerSeries.toAdicCompletionAlgEquiv (Fin r) R).surjective⟩

/-- Volume 1, Theorem 4.2.9 of the handbook: the `I`-adic completion of a Noetherian ring is
Noetherian. -/
theorem isNoetherianRing_adicCompletion [IsNoetherianRing R] :
    IsNoetherianRing (AdicCompletion I R) := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  let a : Fin s.card → R := fun i => (s.equivFin.symm i : R)
  have ha : Ideal.span (Set.range a) = I := by
    rw [← hs]
    congr 1
    ext x
    simp only [Set.mem_range, Finset.mem_coe, a]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (s.equivFin.symm i).2,
      fun hx => ⟨s.equivFin ⟨x, hx⟩, by simp⟩⟩
  obtain ⟨φ, hφ⟩ := exists_surjective_mvPowerSeries_adicCompletion I a ha
  exact isNoetherianRing_of_surjective _ _ φ hφ

end CompletionNoetherian

section LocalCompletion

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

instance isNoetherianRing_adicCompletion_maximalIdeal :
    IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
  isNoetherianRing_adicCompletion _

/-- Volume 1, Theorem 4.3.3 of the handbook, the dimension: `dim R̂ = dim R`. -/
theorem ringKrullDim_adicCompletion :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  set S := AdicCompletion (maximalIdeal R) R
  have hcomap : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    IsLocalRing.maximalIdeal_comap _
  have : (maximalIdeal S).LiesOver (maximalIdeal R) := ⟨hcomap.symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R)
    (maximalIdeal S)
  have hmap : (maximalIdeal S).map
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S))) = ⊥ := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.map_quotient_self _
  have h0 : ((maximalIdeal S).map
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)))).height = 0 := by
    rw [hmap]
    have : ((maximalIdeal R).map (algebraMap R S)).IsMaximal := by
      rw [← AdicCompletion.maximalIdeal_eq_map]
      infer_instance
    exact Ideal.height_eq_zero_iff_eq_bot.2 rfl
  rw [h0, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]

/-- Volume 1, Theorem 4.3.3 of the handbook, the embedding dimension: `edim R̂ = edim R`. This is
`AdicCompletion.spanFinrank_maximalIdeal_eq` of Mathlib. -/
theorem spanFinrank_maximalIdeal_adicCompletion :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank =
      (maximalIdeal R).spanFinrank :=
  AdicCompletion.spanFinrank_maximalIdeal_eq

/-- Volume 1, Theorem 4.3.3 of the handbook, the last claim: `R` is regular if and only if `R̂`
is regular. -/
theorem isRegularLocalRing_adicCompletion_iff :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) ↔ IsRegularLocalRing R := by
  rw [isRegularLocalRing_iff, isRegularLocalRing_iff R, spanFinrank_maximalIdeal_adicCompletion,
    ringKrullDim_adicCompletion]

end LocalCompletion

section CoefficientField

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Volume 1, Definition 4.4.1 of the handbook: a subring `K` of a local ring `R` is a
coefficient field if it is a field and the map `K → κ` to the residue field is surjective. -/
def IsCoefficientField (K : Subring R) : Prop :=
  IsField K ∧ Function.Surjective ((residue R).comp K.subtype)

theorem IsCoefficientField.injective {K : Subring R} (hK : IsCoefficientField K) :
    Function.Injective ((residue R).comp K.subtype) := by
  let := hK.1.toField
  exact RingHom.injective _

variable (p : ℕ) [Fact p.Prime] [CharP R p] [CharP (ResidueField R) p]
  [PerfectRing (ResidueField R) p]

omit [CharP R p] in
theorem IsCoefficientField.exists_pow_eq {K : Subring R} (hK : IsCoefficientField K)
    (x : K) (n : ℕ) : ∃ u : K, u ^ p ^ n = x := by
  obtain ⟨ρ, hρ⟩ := (bijective_iterateFrobenius (ResidueField R) p n).2 (residue R x)
  obtain ⟨u, hu⟩ := hK.2 ρ
  refine ⟨u, hK.injective ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply, Subring.coe_subtype] at hu ⊢
  rw [Subring.coe_pow, map_pow, hu, ← hρ, iterateFrobenius_def]

omit [CharP R p] in
theorem residue_eq_of_pow_eq {a b : R} (n : ℕ)
    (h : residue R (a ^ p ^ n) = residue R (b ^ p ^ n)) : residue R a = residue R b := by
  have := (bijective_iterateFrobenius (ResidueField R) p n).1
  apply this
  simpa [iterateFrobenius_def] using h

include p in
/-- The core of the uniqueness in Volume 1, Theorem 4.4.4 of the handbook: in a Noetherian local
ring of characteristic `p` with a perfect residue field, two elements of two coefficient fields
with the same residue are equal. -/
theorem IsCoefficientField.eq_of_residue_eq [IsNoetherianRing R] {K K' : Subring R}
    (hK : IsCoefficientField K) (hK' : IsCoefficientField K') {x x' : R} (hx : x ∈ K)
    (hx' : x' ∈ K') (h : residue R x = residue R x') : x = x' := by
  rw [← sub_eq_zero]
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R)
    (Ideal.IsPrime.ne_top inferInstance)
  rw [← Ideal.mem_bot, ← hbot, Ideal.mem_iInf]
  intro n
  obtain ⟨u, hu⟩ := hK.exists_pow_eq p ⟨x, hx⟩ n
  obtain ⟨u', hu'⟩ := hK'.exists_pow_eq p ⟨x', hx'⟩ n
  have hu1 : (u : R) ^ p ^ n = x := by rw [← Subring.coe_pow, hu]
  have hu2 : (u' : R) ^ p ^ n = x' := by rw [← Subring.coe_pow, hu']
  have hres : residue R (u : R) = residue R (u' : R) :=
    residue_eq_of_pow_eq p n (by rw [hu1, hu2, h])
  have hm : (u : R) - u' ∈ maximalIdeal R := by
    exact Ideal.Quotient.eq.1 hres
  rw [← hu1, ← hu2, ← sub_pow_char_pow]
  exact Ideal.pow_le_pow_right (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    (Ideal.pow_mem_pow hm _)

include p in
/-- Volume 1, Theorem 4.4.4 of the handbook, the uniqueness: if `R` is a Noetherian local ring of
characteristic `p` whose residue field is perfect, then `R` has at most one coefficient field.
The proof does not need that `R` is complete. -/
theorem IsCoefficientField.eq [IsNoetherianRing R] {K K' : Subring R}
    (hK : IsCoefficientField K) (hK' : IsCoefficientField K') : K = K' := by
  have key : ∀ {K K' : Subring R}, IsCoefficientField K → IsCoefficientField K' →
      K ≤ K' := by
    intro K K' hK hK' x hx
    obtain ⟨x', hx'⟩ := hK'.2 (residue R x)
    have := hK.eq_of_residue_eq p hK' hx x'.2 hx'.symm
    exact this ▸ x'.2
  exact le_antisymm (key hK hK') (key hK' hK)

end CoefficientField

section CohenRing

variable (p : ℕ) [Fact p.Prime]

/-- Volume 1, Theorem 4.4.9 of the handbook, part 1 for `κ = 𝔽_p`, the existence: `ℤ_p` is a
Cohen ring for `𝔽_p`. It is a complete discrete valuation ring, its maximal ideal is `(p)`, and
its residue field is `𝔽_p`. -/
theorem padicInt_isCohenRing :
    IsDiscreteValuationRing ℤ_[p] ∧ maximalIdeal ℤ_[p] = Ideal.span {(p : ℤ_[p])} ∧
      IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p] ∧
      Nonempty (ResidueField ℤ_[p] ≃+* ZMod p) :=
  ⟨inferInstance, PadicInt.maximalIdeal_eq_span_p, inferInstance, ⟨PadicInt.residueField⟩⟩

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [CharP (ResidueField R) p]

omit [Fact p.Prime] [IsAdicComplete (maximalIdeal R) R] in
theorem natCast_mem_maximalIdeal_of_charP : (p : R) ∈ maximalIdeal R := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change residue R (p : R) = 0
  rw [map_natCast]
  exact CharP.cast_eq_zero _ p

/-- The map `ℤ/p^n → R/m^n`. It exists since `p ∈ m`. -/
noncomputable def zmodToQuotPow (n : ℕ) : ZMod (p ^ n) →+* R ⧸ maximalIdeal R ^ n :=
  (Ideal.Quotient.lift (Ideal.span {((p ^ n : ℕ) : ℤ)})
    (Int.castRingHom (R ⧸ maximalIdeal R ^ n)) (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
      have h0 : ((p ^ n : ℕ) : R ⧸ maximalIdeal R ^ n) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal R ^ n)),
          Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
        exact Ideal.pow_mem_pow (natCast_mem_maximalIdeal_of_charP p) n
      rw [map_mul, map_natCast, h0, zero_mul])).comp
    (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom

/-- The compatible maps `ℤ_p → ℤ/p^n → R/m^n`. -/
noncomputable def padicToQuotPow (n : ℕ) : ℤ_[p] →+* R ⧸ maximalIdeal R ^ n :=
  (zmodToQuotPow p n).comp (PadicInt.toZModPow n)

omit [IsAdicComplete (maximalIdeal R) R] in
theorem factorPow_comp_padicToQuotPow {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal R) hle).comp (padicToQuotPow p n) =
      padicToQuotPow (R := R) p m := by
  refine RingHom.ext fun x => ?_
  have h2 := RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow (p := p) m n hle) x
  have h3 := RingHom.congr_fun (Subsingleton.elim
    ((Ideal.Quotient.factorPow (maximalIdeal R) hle).comp (zmodToQuotPow (R := R) p n))
    ((zmodToQuotPow (R := R) p m).comp (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p ^ m)))))
    (PadicInt.toZModPow n x)
  simp only [padicToQuotPow, RingHom.coe_comp, Function.comp_apply] at h2 h3 ⊢
  rw [h3, h2]

/-- The map `ℤ_p → R` for a complete local ring `R` with residue field of characteristic `p`. -/
noncomputable def padicIntToComplete : ℤ_[p] →+* R :=
  IsAdicComplete.liftRingHom (maximalIdeal R) (padicToQuotPow p)
    (fun hle => factorPow_comp_padicToQuotPow p hle)

instance isLocalHom_padicIntToComplete : IsLocalHom (padicIntToComplete (R := R) p) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hnu
  have hxm : x ∈ maximalIdeal ℤ_[p] := hnu
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hxm
  obtain ⟨y, rfl⟩ := hxm
  rw [map_mul, map_natCast] at hx
  exact (mem_maximalIdeal _).1 (natCast_mem_maximalIdeal_of_charP (R := R) p)
    (isUnit_of_mul_isUnit_right hx)

/-- Volume 1, Theorem 4.4.9 of the handbook, part 2 for `κ = 𝔽_p`: let `R` be a complete local
ring whose residue field has characteristic `p`. Then there is a local homomorphism
`ℤ_p → R`. The map of residue fields is the unique map from `𝔽_p`, see
`ringHom_residueField_padicInt_subsingleton`. -/
theorem exists_isLocalHom_padicInt :
    ∃ φ : ℤ_[p] →+* R, IsLocalHom φ :=
  ⟨padicIntToComplete p, inferInstance⟩

theorem ringHom_residueField_padicInt_subsingleton (S : Type*) [Semiring S] :
    Subsingleton (ResidueField ℤ_[p] →+* S) := by
  refine ⟨fun f g => ?_⟩
  have : f.comp PadicInt.residueField.symm.toRingHom =
      g.comp PadicInt.residueField.symm.toRingHom := Subsingleton.elim _ _
  ext x
  simpa using congrArg (fun h => h (PadicInt.residueField x)) this

end CohenRing

section PowerSeriesBasis

variable {σ L K ι : Type*} [CommRing L] [CommRing K] [Algebra L K] [Fintype ι]

/-- The coordinates of a power series over `K` in a basis `b` of `K` over `L`. -/
noncomputable def mvPowerSeriesCoordEquiv (b : Module.Basis ι L K) :
    MvPowerSeries σ K ≃ₗ[MvPowerSeries σ L] (ι → MvPowerSeries σ L) where
  toFun f i := fun α => b.repr (MvPowerSeries.coeff α f) i
  invFun g := fun α => ∑ i, MvPowerSeries.coeff α (g i) • b i
  map_add' f g := by
    funext i
    ext α
    change b.repr (MvPowerSeries.coeff α (f + g)) i =
      b.repr (MvPowerSeries.coeff α f) i + b.repr (MvPowerSeries.coeff α g) i
    simp
  map_smul' P f := by
    classical
    funext i
    ext α
    change b.repr (MvPowerSeries.coeff α (P • f)) i = MvPowerSeries.coeff α
      (P * show MvPowerSeries σ L from fun β => b.repr (MvPowerSeries.coeff β f) i)
    rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply'', MvPowerSeries.coeff_mul,
      MvPowerSeries.coeff_mul]
    simp only [MvPowerSeries.coeff_map, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
    rfl
  left_inv f := by
    ext α
    change ∑ i, b.repr (MvPowerSeries.coeff α f) i • b i = MvPowerSeries.coeff α f
    exact b.sum_repr _
  right_inv g := by
    funext i
    ext α
    change b.repr (∑ j, MvPowerSeries.coeff α (g j) • b j) i = MvPowerSeries.coeff α (g i)
    rw [map_sum]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp

/-- A basis of `K` over `L` is a basis of `K[[X]]` over `L[[X]]`. -/
noncomputable def mvPowerSeriesBasis (b : Module.Basis ι L K) :
    Module.Basis ι (MvPowerSeries σ L) (MvPowerSeries σ K) :=
  Module.Basis.ofEquivFun (mvPowerSeriesCoordEquiv b)

/-- The step of Volume 1, Remark 6.4.8 of the handbook on the coefficients: if `K` is free of
finite rank over `L`, then `K[[X]]` is free over `L[[X]]` of the same rank. For `L = κ^p` and
`K = κ` with `[κ : κ^p] = p^r`, this is the claim that `κ[[y]]` is free of rank `p^r` over
`κ^p[[y]]`. -/
theorem free_mvPowerSeries_and_finrank [Nontrivial L] [Module.Free L K] [Module.Finite L K] :
    Module.Free (MvPowerSeries σ L) (MvPowerSeries σ K) ∧
      Module.finrank (MvPowerSeries σ L) (MvPowerSeries σ K) = Module.finrank L K := by
  let b := Module.Free.chooseBasis L K
  refine ⟨Module.Free.of_basis (mvPowerSeriesBasis (σ := σ) b), ?_⟩
  rw [Module.finrank_eq_card_basis (mvPowerSeriesBasis (σ := σ) b),
    Module.finrank_eq_card_basis b]

end PowerSeriesBasis

section SamuelDegree

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A part of Volume 1, Remark 3.1.7 of the handbook: there is an `m`-primary ideal `q` with
`dim R` generators, and for each finitely generated module `M` the Hilbert-Samuel function of `M`
with respect to `q` agrees for large `n` with a polynomial of degree at most `dim R`. -/
theorem exists_primary_isEventuallyPolynomial_hilbertSamuel (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] :
    ∃ s : Finset R, (Ideal.span (s : Set R)).radical = maximalIdeal R ∧
      (s.card : WithBot ℕ∞) = ringKrullDim R ∧
      IsEventuallyPolynomial (fun n => ((hilbertSamuel (Ideal.span (s : Set R)) M n).toNat : ℤ))
        (s.card + 1) := by
  obtain ⟨s, hs, hcard⟩ := exists_card_eq_ringKrullDim (R := R)
  refine ⟨s, hs, hcard, ?_⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (le_of_eq hs.symm)
    (IsNoetherian.noetherian (maximalIdeal R))
  have hfin := hilbertSamuel_ne_top (I := Ideal.span (s : Set R)) M (maximalIdeal R) hk 1
  rw [hilbertSamuel, pow_one] at hfin
  exact isEventuallyPolynomial_hilbertSamuel_of_span (M := M) s rfl hfin

end SamuelDegree

end Algebra

end Singularity
