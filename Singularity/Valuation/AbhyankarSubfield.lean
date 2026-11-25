/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.MonomialFiniteExtension

/-!
# The monomial subfield of an Abhyankar valuation

Let `V` be an Abhyankar valuation of a function field `K/k`. Let `r` be the rational rank of its value group `Γ`, and let `t` be the transcendence degree of its residue field `Kv` over `k`, so that `r + t = trdeg_k K`. The proof of the theorem of Knaf-Kuhlmann (Volume 5, Theorem 2.2.1 of the handbook) starts with the choice of a subfield `K₀ = k(x_1, ..., x_r, y_1, ..., y_t)` of `K`. This file formalizes this choice, and combines it with `Singularity.hasLocalUniformization_of_monomial_of_finrank_residueField_eq`.

Choose nonzero `x_1, ..., x_r ∈ K` whose values are linearly independent over `ℤ`, and `y_1, ..., y_t ∈ V` whose residues are algebraically independent over `k`. Then:

1. The elements `x, y` are algebraically independent over `k` (Volume 3, Theorem 2.1.4 of the handbook, for the trivially valued field `k`).
2. The field `K` is a finite extension of `K₀ = k(x, y)`, because `r + t = trdeg_k K` and `K` is finitely generated over `k` (Volume 3, proof of Theorem 2.2.2).
3. The restriction `v₀` of `V` to `K₀` is trivial on `k(y)` (Volume 5, Lemma 1.4.2).
4. The restriction `v₀` is the monomial valuation of `K₀ = k(y)(x_1, ..., x_r)` over `k(y)` with the weights `v(x_i)`, in the sense of `Singularity.IsMonomialValuation` (Volume 3, Lemma 2.2.1, and the first step of the proof of Volume 5, Theorem 2.2.1).

If also the residue extension `Kv/K₀v₀` is separable of degree `[K : K₀]`, then `V` has local uniformization (`Singularity.hasLocalUniformization_of_isAbhyankarValuation_of_finrank_residueField_eq`).

## Differences with the handbook

The handbook chooses the `x_i` such that their values are a basis of `Γ`. This uses that `Γ` is free of rank `r` (Volume 3, Corollary 2.2.4), which needs the finiteness of `Γ / Γ₀` for the finite extension `K/K₀` (Volume 3, Corollary 2.1.3). These are not in the library. Here the values of the `x_i` are only linearly independent over `ℤ`. There are `r` of them, so their images in `ℚ ⊗ Γ` are a basis (this step of linear algebra is not stated in Lean). But the value group `Γ₀` of `v₀`, which is free with basis `v(x_1), ..., v(x_r)`, can be a subgroup of finite index in `Γ`. The hypothesis of the last theorem, that `[Kv : K₀v₀] = [K : K₀]`, implies `Γ₀ = Γ` by the fundamental inequality, so this difference does not matter there.

The general theorem of Knaf-Kuhlmann allows several extensions of `v₀` to `K` and needs the henselization and the generalized stability theorem of Kuhlmann. These are not in the library. This file does not prove `Singularity.localUniformization_abhyankar`.

## Main results

* `Singularity.IsAbhyankarValuation.exists_isMonomialValuation_comap`: the choice of `x`, `y` and `K₀ = k(x, y)` with the four properties above.
* `Singularity.isMonomialValuation_comap_adjoin_sumElim`: the restriction of `V` to `k(x, y)` is monomial over `k(y)`, for each `y`.
* `Singularity.mem_comap_adjoin_sumElim_of_residue`: the restriction is trivial on `k(y)`.
* `Singularity.algebraicIndependent_sumElim_of_laurentMonomial`: the elements `x, y` are algebraically independent over `k`.
* `Singularity.finiteDimensional_adjoin_sumElim_of_isAbhyankarValuation`: `[K : k(x, y)]` is finite.
* `Singularity.hasLocalUniformization_of_isAbhyankarValuation_of_finrank_residueField_eq`: local uniformization if the residue extension `Kv/K₀v₀` is separable of degree `[K : K₀]`.
* `Singularity.linearIndependent_valuation_iff`: the values of `x_1, ..., x_n` are independent over `ℤ` if and only if a Laurent monomial `x^a` has value 1 only for `a = 0`.
-/

open IsLocalRing MvPolynomial TensorProduct

namespace Singularity

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### The elements of `k(z)` -/

section AdjoinRange

variable {ι : Type*}

variable (k) in
/-- The element `z_i` of `K` as an element of the subfield `k(z)` of `K` that the family `z` generates over `k`. -/
def adjoinRangeElem (z : ι → K) (i : ι) : IntermediateField.adjoin k (Set.range z) :=
  ⟨z i, IntermediateField.subset_adjoin k _ (Set.mem_range_self i)⟩

@[simp]
theorem coe_adjoinRangeElem (z : ι → K) (i : ι) : (adjoinRangeElem k z i : K) = z i :=
  rfl

/-- The elements `z_i` generate the field `k(z)` over `k`. -/
theorem adjoin_range_adjoinRangeElem (z : ι → K) :
    IntermediateField.adjoin k (Set.range (adjoinRangeElem k z)) = ⊤ := by
  set F := IntermediateField.adjoin k (Set.range z)
  apply IntermediateField.map_injective F.val
  rw [IntermediateField.adjoin_map, ← Set.range_comp]
  change IntermediateField.adjoin k (Set.range z) = (⊤ : IntermediateField k F).map F.val
  rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]

end AdjoinRange

/-! ### Values of Laurent monomials -/

section Values

variable {ι : Type*} [Fintype ι]

/-- Let `x_1, ..., x_n` be nonzero elements of `K`. The values `v(x_i)` are linearly independent over `ℤ` in the value group of `V` if and only if a Laurent monomial `x^a` has value 1 only for `a = 0`. -/
theorem linearIndependent_valuation_iff (V : ValuationSubring K) {x : ι → K}
    (hx0 : ∀ i, x i ≠ 0) :
    LinearIndependent ℤ (fun i => Additive.ofMul
        (Units.map (V.valuation : K →* V.ValueGroup) (Units.mk0 (x i) (hx0 i)))) ↔
      ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0 := by
  rw [Fintype.linearIndependent_iff]
  have key : ∀ a : ι → ℤ, (∑ i, a i • Additive.ofMul
      (Units.map (V.valuation : K →* V.ValueGroup) (Units.mk0 (x i) (hx0 i))) = 0) ↔
        V.valuation (laurentMonomial x a) = 1 := by
    intro a
    have h1 : (∑ i, a i • Additive.ofMul
        (Units.map (V.valuation : K →* V.ValueGroup) (Units.mk0 (x i) (hx0 i)))) =
          Additive.ofMul (∏ i, Units.map (V.valuation : K →* V.ValueGroup)
            (Units.mk0 (x i) (hx0 i)) ^ a i) := by
      simp [ofMul_prod, ofMul_zpow]
    rw [h1, ← ofMul_one, EmbeddingLike.apply_eq_iff_eq, ← Units.val_inj]
    simp [laurentMonomial, Units.coe_prod, map_prod, map_zpow₀]
  constructor
  · intro h a ha
    funext i
    exact h a ((key a).mpr ha) i
  · intro h a ha i
    rw [h a ((key a).mp ha)]
    rfl

end Values

/-! ### The finite extension `K/k(x, y)` -/

section Finite

variable {ι : Type*} [Fintype ι]

/-- Let `K` be a function field over `k`, and let `z_1, ..., z_n` be algebraically independent over `k` with `n ≥ trdeg_k K`. Then `K` is a finite extension of `k(z)`. -/
theorem finiteDimensional_adjoin_of_algebraicIndependent (hK : IsFunctionField k K) {z : ι → K}
    (hz : AlgebraicIndependent k z) (hn : Algebra.trdeg k K ≤ Fintype.card ι) :
    FiniteDimensional (IntermediateField.adjoin k (Set.range z)) K := by
  set K₀ := IntermediateField.adjoin k (Set.range z)
  have hb : IsTranscendenceBasis k z :=
    hz.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by simpa using hn)
  have halg : Algebra.IsAlgebraic K₀ K := hb.isAlgebraic_field
  obtain ⟨S, hS⟩ := hK
  have hS' : IntermediateField.adjoin K₀ (S : Set K) = ⊤ := by
    apply IntermediateField.restrictScalars_injective k
    rw [IntermediateField.restrictScalars_top, eq_top_iff, ← hS]
    exact IntermediateField.adjoin_le_iff.mpr fun c hc =>
      IntermediateField.subset_adjoin K₀ _ hc
  have : FiniteDimensional K₀ (IntermediateField.adjoin K₀ (S : Set K)) :=
    IntermediateField.finiteDimensional_adjoin fun c _ =>
      (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  rw [hS'] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end Finite

/-! ### The restriction to a subfield -/

section Comap

variable {ι κ : Type*} [Fintype ι] {V : ValuationSubring K}

/-- A nonzero element `c` has value 1 if and only if `c` and `c⁻¹` lie in the valuation ring. -/
theorem valuation_eq_one_iff_mem_inv_mem {L : Type*} [Field L] (A : ValuationSubring L) {c : L}
    (hc : c ≠ 0) : A.valuation c = 1 ↔ c ∈ A ∧ c⁻¹ ∈ A := by
  rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_inv₀,
    inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc))]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

/-- An element `c` of a subfield has value 1 for the restriction of `V` if and only if it has value 1 for `V`. -/
theorem valuation_comap_eq_one_iff {L : Type*} [Field L] (f : L →+* K) (c : L) :
    (V.comap f).valuation c = 1 ↔ V.valuation (f c) = 1 := by
  by_cases hc : c = 0
  · simp [hc]
  rw [valuation_eq_one_iff_mem_inv_mem _ hc,
    valuation_eq_one_iff_mem_inv_mem _ ((map_ne_zero f).mpr hc), ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, map_inv₀]

variable {K₀ : IntermediateField k K}

/-- **The restriction is monomial.** Let `K₀ = k(x_1, ..., x_r, y_1, ..., y_t)` be a subfield of `K`, and let `V` be a valuation subring of `K`. Assume that the `x_i` are not zero and that their values `v(x_i)` are linearly independent over `ℤ`. Then the restriction of `V` to `K₀` is a monomial valuation of `K₀ = k(y)(x_1, ..., x_r)` over the field `k(y)`, in the variables `x_i`, with the weights `v(x_i)`. -/
theorem isMonomialValuation_comap {x : ι → K₀} {y : κ → K₀}
    (htop : IntermediateField.adjoin k (Set.range x ∪ Set.range y) = ⊤) (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ a : ι → ℤ, V.valuation (laurentMonomial (fun i => (x i : K)) a) = 1 → a = 0) :
    IsMonomialValuation (IntermediateField.adjoin k (Set.range y))
      (V.comap (algebraMap K₀ K)) x where
  ne_zero := hx0
  adjoin_eq_top := by
    apply IntermediateField.restrictScalars_injective k
    rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top,
      Set.union_comm, htop]
  independent a ha := by
    apply hx a
    rw [valuation_comap_eq_one_iff] at ha
    convert ha using 2
    simp [laurentMonomial]

/-- Let `y_1, ..., y_t` be elements of a subfield `K₀` of `K`. If `V` is trivial on the subfield `k(y)` of `K`, then the restriction of `V` to `K₀` is trivial on the subfield `k(y)` of `K₀`. -/
theorem mem_comap_of_mem_adjoin {y : κ → K₀}
    (hyV : ∀ c ∈ IntermediateField.adjoin k (Set.range fun j => (y j : K)), c ∈ V) :
    ∀ c ∈ IntermediateField.adjoin k (Set.range y), c ∈ V.comap (algebraMap K₀ K) := by
  intro c hc
  apply hyV
  have h : (c : K) ∈ (IntermediateField.adjoin k (Set.range y)).map K₀.val := ⟨c, hc, rfl⟩
  rwa [IntermediateField.adjoin_map, ← Set.range_comp] at h

end Comap

/-! ### The subfield `k(x, y)` -/

section SumElim

variable {ι κ : Type*} [Fintype ι] {V : ValuationSubring K}

/-- **The restriction to `k(x, y)` is monomial.** Let `x_1, ..., x_r` be nonzero elements of `K` whose values `v(x_i)` are linearly independent over `ℤ`, and let `y_1, ..., y_t` be elements of `K`. Let `K₀ = k(x, y)`. Then the restriction of `V` to `K₀` is a monomial valuation of `K₀ = k(y)(x_1, ..., x_r)` over the field `k(y)`, in the variables `x_i`, with the weights `v(x_i)`. -/
theorem isMonomialValuation_comap_adjoin_sumElim {x : ι → K} {y : κ → K}
    (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0) :
    IsMonomialValuation
      (IntermediateField.adjoin k (Set.range fun j => adjoinRangeElem k (Sum.elim x y) (.inr j)))
      (V.comap (algebraMap (IntermediateField.adjoin k (Set.range (Sum.elim x y))) K))
      (fun i => adjoinRangeElem k (Sum.elim x y) (.inl i)) := by
  refine isMonomialValuation_comap ?_ (fun i h => hx0 i (congrArg Subtype.val h)) hx
  rw [← Set.Sum.elim_range, ← adjoin_range_adjoinRangeElem (k := k) (Sum.elim x y)]
  congr 2
  funext j
  cases j <;> rfl

omit [Fintype ι] in
/-- **The restriction to `k(x, y)` is trivial on `k(y)`.** Let `y_1, ..., y_t` be elements of the valuation ring `V` whose residues are algebraically independent over `k`, and let `x_1, ..., x_r` be elements of `K`. Let `K₀ = k(x, y)`. Then the restriction of `V` to `K₀` is trivial on the subfield `k(y)` of `K₀`. -/
theorem mem_comap_adjoin_sumElim_of_residue [Algebra k V] [IsScalarTower k V K] {x : ι → K}
    {y : κ → V} (hy : AlgebraicIndependent k fun j => residue V (y j)) :
    ∀ c ∈ IntermediateField.adjoin k
        (Set.range fun j => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inr j)),
      c ∈ V.comap (algebraMap
        (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K) :=
  mem_comap_of_mem_adjoin fun _ hc => mem_of_mem_adjoin_residue hy hc

/-- **Algebraic independence of `x, y`** (Volume 3, Theorem 2.1.4 of the handbook, for the trivially valued field `k`). Let `x_1, ..., x_r` be nonzero elements of `K` whose values are linearly independent over `ℤ`, and let `y_1, ..., y_t` be elements of `V` whose residues are algebraically independent over `k`. Then `x_1, ..., x_r, y_1, ..., y_t` are algebraically independent over `k`. -/
theorem algebraicIndependent_sumElim_of_laurentMonomial [Algebra k V] [IsScalarTower k V K]
    {x : ι → K} {y : κ → V} (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0)
    (hy : AlgebraicIndependent k fun j => residue V (y j)) :
    AlgebraicIndependent k (Sum.elim x fun j => (y j : K)) :=
  algebraicIndependent_sumElim_of_valuationSubring V (fun i => Units.mk0 (x i) (hx0 i))
    ((linearIndependent_valuation_iff V hx0).mpr hx) y hy

end SumElim

/-! ### Abhyankar valuations -/

section Abhyankar

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- Let the value group of `V` have rational rank `r`. Then there are nonzero `x_1, ..., x_r ∈ K` whose values are linearly independent over `ℤ`. -/
theorem exists_laurentMonomial_of_rank_eq {r : ℕ}
    (hr : Module.rank ℚ (ℚ ⊗[ℤ] Additive V.ValueGroupˣ) = r) :
    ∃ x : Fin r → K, (∀ i, x i ≠ 0) ∧
      ∀ a : Fin r → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0 := by
  rw [(TensorProduct.isBaseChange ℤ (Additive V.ValueGroupˣ) ℚ).rank_eq] at hr
  obtain ⟨s, hs, hli⟩ :=
    exists_set_linearIndependent_of_isDomain ℤ (Additive V.ValueGroupˣ)
  rw [hr, Cardinal.mk_eq_nat_iff] at hs
  obtain ⟨e⟩ := hs
  set b : Fin r → Additive V.ValueGroupˣ := fun i => (e.symm i : Additive V.ValueGroupˣ)
  have hb : LinearIndependent ℤ b := hli.linearIndependent.comp _ e.symm.injective
  have hx : ∀ i, ∃ z : K,
      V.valuation z = ((Additive.toMul (b i) : V.ValueGroupˣ) : V.ValueGroup) :=
    fun i => V.valuation_surjective _
  choose x hx using hx
  have hx0 : ∀ i, x i ≠ 0 := fun i h => by
    have := hx i
    rw [h, map_zero] at this
    exact (Additive.toMul (b i)).ne_zero this.symm
  refine ⟨x, hx0, (linearIndependent_valuation_iff V hx0).mp ?_⟩
  convert hb using 1
  funext i
  apply Additive.toMul.injective
  ext
  simp [hx i]

omit [Algebra k K] [IsScalarTower k V K] in
/-- Let the residue field of `V` have transcendence degree `t` over `k`. Then there are `y_1, ..., y_t ∈ V` whose residues are algebraically independent over `k`. -/
theorem exists_algebraicIndependent_residue_of_trdeg_eq {t : ℕ}
    (ht : Algebra.trdeg k (ResidueField V) = t) :
    ∃ y : Fin t → V, AlgebraicIndependent k fun j => residue V (y j) := by
  obtain ⟨ι, w, hw⟩ := exists_isTranscendenceBasis' k (ResidueField V)
  have hc := hw.cardinalMk_eq_trdeg
  rw [ht, Cardinal.mk_eq_nat_iff] at hc
  obtain ⟨e⟩ := hc
  have hy : ∀ j, ∃ a : V, residue V a = w (e.symm j) := fun j => residue_surjective _
  choose y hy using hy
  refine ⟨y, ?_⟩
  convert hw.1.comp _ e.symm.injective using 1
  funext j
  exact hy j

/-- **The extension `K/k(x, y)` is finite** (Volume 3, proof of Theorem 2.2.2 of the handbook, for the trivially valued field `k`). Let `V` be an Abhyankar valuation of the function field `K/k`, with value group of rational rank `r` and residue field of transcendence degree `t` over `k`. Let `x_1, ..., x_r` be nonzero elements of `K` whose values are linearly independent over `ℤ`, and let `y_1, ..., y_t` be elements of `V` whose residues are algebraically independent over `k`. Then `K` is a finite extension of `k(x, y)`. -/
theorem finiteDimensional_adjoin_sumElim_of_isAbhyankarValuation (hK : IsFunctionField k K)
    (hV : IsAbhyankarValuation k V) {ι κ : Type*} [Fintype ι] [Fintype κ] {x : ι → K}
    {y : κ → V} (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0)
    (hy : AlgebraicIndependent k fun j => residue V (y j))
    (hr : Module.rank ℚ (ℚ ⊗[ℤ] Additive V.ValueGroupˣ) = Fintype.card ι)
    (ht : Algebra.trdeg k (ResidueField V) = Fintype.card κ) :
    FiniteDimensional
      (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K := by
  refine finiteDimensional_adjoin_of_algebraicIndependent hK
    (algebraicIndependent_sumElim_of_laurentMonomial hx0 hx hy) ?_
  rw [← hV, hr, ht, Fintype.card_sum, Nat.cast_add]

/-- **The monomial subfield of an Abhyankar valuation** (the choice of the subfield in the proof of Volume 5, Theorem 2.2.1 of the handbook, with values that are independent over `ℤ`). Let `V` be an Abhyankar valuation of the function field `K/k`. Let `r` be the rational rank of its value group `Γ`, and let `t` be the transcendence degree of its residue field over `k`. Then there are `x_1, ..., x_r ∈ K` and `y_1, ..., y_t ∈ V` with the following properties.

1. The `x_i` are not zero, and their values are linearly independent over `ℤ`.
2. The residues of the `y_j` are algebraically independent over `k`.
3. The elements `x_1, ..., x_r, y_1, ..., y_t` are algebraically independent over `k`.
4. The field `K` is a finite extension of `K₀ = k(x, y)`.
5. The restriction of `V` to `K₀` is trivial on `k(y)`.
6. The restriction of `V` to `K₀` is the monomial valuation of `K₀ = k(y)(x_1, ..., x_r)` over `k(y)` with the weights `v(x_i)`.

The handbook chooses the `x_i` such that their values are a basis of `Γ`. This needs that `Γ` is free of rank `r` (Volume 3, Corollary 2.2.4), and this is not proved here. Here the values of the `x_i` are only independent over `ℤ`, so the value group of `K₀` can be a subgroup of finite index in `Γ`. -/
theorem IsAbhyankarValuation.exists_isMonomialValuation_comap (hK : IsFunctionField k K)
    (hV : IsAbhyankarValuation k V) :
    ∃ (r t : ℕ) (x : Fin r → K) (y : Fin t → V),
      Module.rank ℚ (ℚ ⊗[ℤ] Additive V.ValueGroupˣ) = r ∧
      Algebra.trdeg k (ResidueField V) = t ∧
      (∀ i, x i ≠ 0) ∧
      (∀ a : Fin r → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0) ∧
      AlgebraicIndependent k (fun j => residue V (y j)) ∧
      AlgebraicIndependent k (Sum.elim x fun j => (y j : K)) ∧
      FiniteDimensional
        (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K ∧
      (∀ c ∈ IntermediateField.adjoin k
          (Set.range fun j => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inr j)),
        c ∈ V.comap (algebraMap
          (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K)) ∧
      IsMonomialValuation
        (IntermediateField.adjoin k
          (Set.range fun j => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inr j)))
        (V.comap (algebraMap
          (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K))
        (fun i => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inl i)) := by
  have htr : Algebra.trdeg k K < Cardinal.aleph0 := by
    obtain ⟨S, hS⟩ := hK
    have : Algebra.IsAlgebraic (IntermediateField.adjoin k (S : Set K)) K := by
      rw [hS]
      exact ⟨fun z => isAlgebraic_algebraMap (⟨z, trivial⟩ : (⊤ : IntermediateField k K))⟩
    have halg := IntermediateField.isAlgebraic_adjoin_iff_top.mp this
    exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk k (S : Set K)).trans_lt
      (Cardinal.finset_card_lt_aleph0 S)
  rw [← hV] at htr
  obtain ⟨hr, ht⟩ := Cardinal.add_lt_aleph0_iff.mp htr
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp hr
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp ht
  obtain ⟨x, hx0, hx⟩ := exists_laurentMonomial_of_rank_eq hr
  obtain ⟨y, hy⟩ := exists_algebraicIndependent_residue_of_trdeg_eq ht
  refine ⟨r, t, x, y, hr, ht, hx0, hx, hy,
    algebraicIndependent_sumElim_of_laurentMonomial hx0 hx hy,
    finiteDimensional_adjoin_sumElim_of_isAbhyankarValuation hK hV hx0 hx hy
      (by rw [hr, Fintype.card_fin]) (by rw [ht, Fintype.card_fin]),
    mem_comap_adjoin_sumElim_of_residue hy, isMonomialValuation_comap_adjoin_sumElim hx0 hx⟩

end Abhyankar

/-! ### Local uniformization -/

section LocalUniformization

/-- **Local uniformization of an Abhyankar valuation over its monomial subfield, without ramification, defect and splitting** (Volume 5, Theorem 2.2.1 of the handbook, in the case of one extension with `e = d = 1`). Let `v` be an Abhyankar valuation of the function field `K/k`. Let `r` be the rational rank of its value group, and let `t` be the transcendence degree of its residue field `Kv` over `k`. Let `x_1, ..., x_r` be nonzero elements of `K` whose values are linearly independent over `ℤ`, and let `y_1, ..., y_t` be elements of the valuation ring whose residues are algebraically independent over `k`. Let `v₀` be the restriction of `v` to `K₀ = k(x, y)`. Assume that the residue extension `Kv/K₀v₀` is separable of degree `[K : K₀]`. Then `v` has local uniformization as a valuation of `K/k`.

The restriction `v₀` is trivial on `k(y)` and monomial over `k(y)` (`Singularity.IsAbhyankarValuation.exists_isMonomialValuation_comap`), and `[K : K₀]` is finite. So `Singularity.hasLocalUniformization_of_monomial_of_finrank_residueField_eq` applies. By the fundamental inequality, the hypothesis on the residue extension says that `e = d = 1` and that `v` is the only extension of `v₀` to `K`. The general theorem of Knaf-Kuhlmann needs the henselization and the generalized stability theorem of Kuhlmann. These are not proved here, and this theorem is not `Singularity.localUniformization_abhyankar`. -/
theorem hasLocalUniformization_of_isAbhyankarValuation_of_finrank_residueField_eq
    (hK : IsFunctionField k K) {Γ₀ Γ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) [Algebra k v.valuationSubring]
    [IsScalarTower k v.valuationSubring K] (hv : IsAbhyankarValuation k v.valuationSubring)
    {ι κ : Type*} [Fintype ι] [Fintype κ] {x : ι → K} {y : κ → v.valuationSubring}
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ a : ι → ℤ, v (laurentMonomial x a) = 1 → a = 0)
    (hy : AlgebraicIndependent k fun j => residue v.valuationSubring (y j))
    (hr : Module.rank ℚ (ℚ ⊗[ℤ] Additive v.valuationSubring.ValueGroupˣ) = Fintype.card ι)
    (ht : Algebra.trdeg k (ResidueField v.valuationSubring) = Fintype.card κ)
    (v₀ : Valuation
      (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) Γ₀)
    [v₀.HasExtension v]
    [Algebra.IsSeparable (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring)]
    (hf : Module.finrank (ResidueField v₀.valuationSubring) (ResidueField v.valuationSubring) =
      Module.finrank
        (IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))) K) :
    HasLocalUniformization k v.valuationSubring := by
  have hx' : ∀ a : ι → ℤ, v.valuationSubring.valuation (laurentMonomial x a) = 1 → a = 0 :=
    fun a ha => hx a ((Valuation.isEquiv_valuation_valuationSubring v).eq_one_iff_eq_one.mpr ha)
  have := finiteDimensional_adjoin_sumElim_of_isAbhyankarValuation hK hv hx0 hx' hy hr ht
  have hcomap := comap_valuationSubring_eq_of_hasExtension v₀ v
  have hyV := mem_comap_adjoin_sumElim_of_residue (x := x) hy
  have hV := isMonomialValuation_comap_adjoin_sumElim (k := k) (y := fun j => (y j : K)) hx0 hx'
  rw [hcomap] at hyV hV
  exact hasLocalUniformization_of_monomial_of_finrank_residueField_eq v₀ v hf hyV hV

end LocalUniformization

end Singularity
