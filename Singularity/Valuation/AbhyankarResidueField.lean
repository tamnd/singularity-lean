/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.AbhyankarValueGroup
import Singularity.Valuation.DecompositionField

/-!
# The residue field of an Abhyankar valuation is finitely generated

Let `V` be an Abhyankar valuation of a function field `K/k`. This file proves that the residue field `Kv` is finitely generated over `k` as a field (Volume 3, Corollary 2.2.4 of the handbook, the part on `Kv`). The part on the value group is `Singularity.IsAbhyankarValuation.free_valueGroup`.

The proof follows the handbook. Choose the subfield `K₀ = k(x, y)` of `Singularity.IsAbhyankarValuation.exists_isMonomialValuation_comap`. Then:

1. Let `E` be a subfield of `K`, and let `F` be a field that contains the residues of the elements of `E ∩ V`. Let `z_1, ..., z_m ∈ V` have residues that are linearly independent over `F`. Then the `z_i` are linearly independent over `E` (`Singularity.linearIndependent_of_linearIndependent_residue`). In a relation `∑ c_i z_i = 0`, divide by the coefficient of largest value and take residues. So if `[K : E]` is finite, then `Kv` is finite over `F` (`Singularity.finiteDimensional_residueField_of_residue_mem`).
2. Let `y_1, ..., y_t ∈ V` have residues that are algebraically independent over `k`. Then the residue of each element of `k(y)` is in `k(ȳ)` (`Singularity.residue_mem_adjoin_of_mem_adjoin`).
3. The restriction of `V` to `K₀` is monomial over `k(y)`. So each `c ∈ K₀ ∩ V` is `c' x^a` times a unit with residue `1`, with `c' ∈ k(y)`. If `v(c) = 1`, then `a = 0`, and the residue of `c` is the residue of `c'`. So the residues of `K₀ ∩ V` are in `k(ȳ)` (`Singularity.residue_mem_adjoin_of_mem_adjoin_sumElim`).
4. By step 1 for `E = K₀` and `F = k(ȳ)`, the field `Kv` is finite over `k(ȳ)`. So `Kv` is generated over `k` by `ȳ` and a basis over `k(ȳ)`.

## Main results

* `Singularity.IsAbhyankarValuation.fg_residueField`: the residue field of an Abhyankar valuation is finitely generated over `k`.
* `Singularity.IsAbhyankarValuation.finiteDimensional_residueField`: it is finite over `k(ȳ)`.
* `Singularity.finiteDimensional_residueField_of_residue_mem`: for a finite extension `K/E`, the residue field `Kv` is finite over each field that contains the residues of `E`.
* `Singularity.linearIndependent_of_linearIndependent_residue`: lifts of independent residues are linearly independent.
-/

open IsLocalRing MvPolynomial

namespace Singularity

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Lifts of independent residues -/

section Residues

variable (V : ValuationSubring K) {E : IntermediateField k K}

/-- **Lifts of independent residues** (Volume 3, proof of Corollary 2.1.3 of the handbook, the part on `f`). Let `E` be a subfield of `K`, and let `F` be a field with a map to `Kv` whose image contains the residues of the elements of `E ∩ V`. Let `z_1, ..., z_m ∈ V` have residues that are linearly independent over `F`. Then the `z_i` are linearly independent over `E`. -/
theorem linearIndependent_of_linearIndependent_residue {F : Type*} [Field F]
    [Algebra F (ResidueField V)]
    (hF : ∀ (c : E) (hc : (c : K) ∈ V), ∃ f : F, algebraMap F _ f = residue V ⟨c, hc⟩)
    {m : Type*} [Fintype m] {z : m → V}
    (hz : LinearIndependent F fun i => residue V (z i)) :
    LinearIndependent E fun i => (z i : K) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  simp only [not_forall] at hne
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
    (fun i => V.valuation (g i : K)) ⟨i₀, Finset.mem_univ _⟩
  have hgj : (g j : K) ≠ 0 := by
    intro h0
    have h1 := hj i₀ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hi₀ (by exact_mod_cast h1)
  have hpos : 0 < V.valuation (g j : K) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hgj
  have hdV : ∀ i, (g i : K) * (g j : K)⁻¹ ∈ V := fun i => by
    rw [← V.valuation_le_one_iff, map_mul, map_inv₀, mul_inv_le_iff₀ hpos, one_mul]
    exact hj i (Finset.mem_univ _)
  have hdE : ∀ i, (g i : K) * (g j : K)⁻¹ ∈ E := fun i =>
    E.mul_mem (g i).2 (E.inv_mem (g j).2)
  have hsum : ∑ i, (⟨_, hdV i⟩ : V) * z i = 0 := by
    apply Subtype.ext
    push_cast
    have hg' : ∑ i, (g i : K) * (z i : K) = 0 := by
      rw [← hg]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IntermediateField.smul_def, smul_eq_mul]
    calc ∑ i, (g i : K) * (g j : K)⁻¹ * (z i : K)
        = (g j : K)⁻¹ * ∑ i, (g i : K) * (z i : K) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = 0 := by rw [hg', mul_zero]
  have hf : ∀ i, ∃ f : F, algebraMap F _ f = residue V ⟨_, hdV i⟩ := fun i =>
    hF ⟨_, hdE i⟩ (hdV i)
  choose f hf using hf
  have hrel : ∑ i, f i • residue V (z i) = 0 := by
    have h2 := congrArg (residue V) hsum
    rw [map_sum, map_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, hf, map_mul]
  have hfj := Fintype.linearIndependent_iff.mp hz f hrel j
  have h1 : (⟨_, hdV j⟩ : V) = 1 := Subtype.ext (mul_inv_cancel₀ hgj)
  have h3 := hf j
  rw [hfj, map_zero, h1, map_one] at h3
  exact zero_ne_one h3

/-- **The residue degree of a finite extension is finite** (Volume 3, Corollary 2.1.3 of the handbook, the part on `f`). Let `E` be a subfield of `K` with `[K : E]` finite, and let `F` be a field with a map to `Kv` whose image contains the residues of the elements of `E ∩ V`. Then `Kv` is finite over `F`. -/
theorem finiteDimensional_residueField_of_residue_mem [FiniteDimensional E K] {F : Type*} [Field F]
    [Algebra F (ResidueField V)]
    (hF : ∀ (c : E) (hc : (c : K) ∈ V), ∃ f : F, algebraMap F _ f = residue V ⟨c, hc⟩) :
    FiniteDimensional F (ResidueField V) := by
  have hrank : Module.rank F (ResidueField V) ≤ Module.finrank E K := by
    refine rank_le fun s hs => ?_
    choose z hz using fun w : s => residue_surjective (R := V) (w : ResidueField V)
    have hs' : LinearIndependent F fun w : s => residue V (z w) := by
      simpa only [hz] using hs
    have := (linearIndependent_of_linearIndependent_residue V hF hs').fintype_card_le_finrank
    simpa only [Fintype.card_coe] using this
  exact Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0))

end Residues

/-! ### The residues of `k(y)` and of `k(x, y)` -/

section Adjoin

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

theorem aeval_mem_adjoin_range {κ : Type*} {L : Type*} [Field L] [Algebra k L] (w : κ → L)
    (P : MvPolynomial κ k) : aeval w P ∈ IntermediateField.adjoin k (Set.range w) :=
  IntermediateField.algebra_adjoin_le_adjoin k _
    (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨P, rfl⟩)

/-- **The residues of `k(y)`** (Volume 5, Lemma 1.4.2 of the handbook, a complement). Let `y_1, ..., y_t ∈ V` have residues `ȳ_j` that are algebraically independent over `k`. Then the residue of each element of `k(y)` is in `k(ȳ)`. -/
theorem residue_mem_adjoin_of_mem_adjoin {κ : Type*} {y : κ → V}
    (hy : AlgebraicIndependent k fun j => residue V (y j)) {c : K}
    (hc : c ∈ IntermediateField.adjoin k (Set.range fun j => (y j : K))) :
    residue V ⟨c, mem_of_mem_adjoin_residue hy hc⟩ ∈
      IntermediateField.adjoin k (Set.range fun j => residue V (y j)) := by
  have hcV := mem_of_mem_adjoin_residue hy hc
  obtain ⟨p, hp, q, hq, hpq⟩ := IntermediateField.mem_adjoin_iff_div.mp hc
  rw [Algebra.adjoin_range_eq_range_aeval] at hp hq
  obtain ⟨P, rfl⟩ := hp
  obtain ⟨Q, rfl⟩ := hq
  by_cases hQ : Q = 0
  · have hc0 : (⟨c, hcV⟩ : V) = 0 := by
      apply Subtype.ext
      change c = 0
      rw [hpq, hQ, map_zero, div_zero]
    rw [hc0, map_zero]
    exact zero_mem _
  have hres : residue V (aeval y Q) ≠ 0 := by
    rw [aeval_residue]
    intro h0
    exact hQ (hy (h0.trans (map_zero _).symm))
  have hQ0 : (aeval (fun j => (y j : K)) Q) ≠ 0 := by
    intro h0
    apply hres
    have : aeval y Q = 0 := Subtype.ext (by rw [coe_aeval]; exact h0)
    rw [this, map_zero]
  have hmul : (⟨c, hcV⟩ : V) * aeval y Q = aeval y P := by
    apply Subtype.ext
    change c * ((aeval y Q : V) : K) = ((aeval y P : V) : K)
    rw [coe_aeval, coe_aeval, hpq]
    exact div_mul_cancel₀ _ hQ0
  have h2 := congrArg (residue V) hmul
  rw [map_mul] at h2
  have h3 : residue V ⟨c, hcV⟩ = residue V (aeval y P) / residue V (aeval y Q) := by
    rw [← h2, mul_div_cancel_right₀ _ hres]
  rw [h3, aeval_residue, aeval_residue]
  exact div_mem (aeval_mem_adjoin_range _ P) (aeval_mem_adjoin_range _ Q)

variable {ι κ : Type*} [Fintype ι]

/-- **The residues of `K₀ = k(x, y)`** (Volume 3, proof of Corollary 2.2.4 of the handbook). Let `x_1, ..., x_r` be nonzero elements of `K` whose values are linearly independent over `ℤ`, and let `y_1, ..., y_t ∈ V` have residues `ȳ_j` that are algebraically independent over `k`. Then the residue of each element of `k(x, y) ∩ V` is in `k(ȳ)`. -/
theorem residue_mem_adjoin_of_mem_adjoin_sumElim {x : ι → K} {y : κ → V}
    (hx0 : ∀ i, x i ≠ 0)
    (hx : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0)
    (hy : AlgebraicIndependent k fun j => residue V (y j))
    (c : IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K))))
    (hc : (c : K) ∈ V) :
    residue V ⟨c, hc⟩ ∈ IntermediateField.adjoin k (Set.range fun j => residue V (y j)) := by
  let K₀ := IntermediateField.adjoin k (Set.range (Sum.elim x fun j => (y j : K)))
  let F : IntermediateField k K₀ := IntermediateField.adjoin k
    (Set.range fun j => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inr j))
  let W := V.comap (algebraMap K₀ K)
  have hyV := mem_comap_adjoin_sumElim_of_residue (x := x) hy
  let _ : Algebra F W := ((algebraMap F K₀).codRestrict W fun c => hyV c c.2).toAlgebra
  have _ : IsScalarTower F W K₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hV := isMonomialValuation_comap_adjoin_sumElim (k := k) (V := V)
    (y := fun j => (y j : K)) hx0 hx
  by_cases hc0 : c = 0
  · have : (⟨c, hc⟩ : V) = 0 := Subtype.ext (by simp [hc0])
    rw [this, map_zero]
    exact zero_mem _
  obtain ⟨c', a, Fm, G, hc', hFm, hG, h⟩ := MonomialValuation.exists_eq_mul_one_add hV hc0
  -- The element `c'` of `k(y)`, seen in `K`.
  have hc'K : (((algebraMap F K₀ c' : K₀)) : K) ∈
      IntermediateField.adjoin k (Set.range fun j => (y j : K)) := by
    have hmem : (algebraMap F K₀ c') ∈ F := c'.2
    have hmap : ((algebraMap F K₀ c' : K₀) : K) ∈ (IntermediateField.adjoin k
        (Set.range fun j => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inr j))).map
          K₀.val := by
      rw [← SetLike.mem_coe, IntermediateField.coe_map]
      exact ⟨_, hmem, rfl⟩
    rw [IntermediateField.adjoin_map, ← Set.range_comp] at hmap
    have hcomp : (⇑K₀.val ∘
        fun j => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inr j)) =
          fun j => (y j : K) := by
      funext j
      simp
    rw [hcomp] at hmap
    exact hmap
  have hc'V : (((algebraMap F K₀ c' : K₀)) : K) ∈ V := mem_of_mem_adjoin_residue hy hc'K
  have hFmV : V.valuation (Fm : K) < 1 := (valuation_comap_lt_one_iff V _ Fm).mp hFm
  have hGV : V.valuation (G : K) < 1 := (valuation_comap_lt_one_iff V _ G).mp hG
  have hhK : (c : K) * (1 + (G : K)) =
      ((algebraMap F K₀ c' : K₀) : K) * laurentMonomial x a * (1 + (Fm : K)) := by
    have hm : ((laurentMonomial
        (fun i => adjoinRangeElem k (Sum.elim x fun j => (y j : K)) (.inl i)) a : K₀) : K) =
          laurentMonomial x a := by
      change algebraMap K₀ K _ = _
      simp [laurentMonomial, map_prod, map_zpow₀]
    have h' := congrArg (fun z : K₀ => (z : K)) h
    simp only [IntermediateField.coe_mul, IntermediateField.coe_add, IntermediateField.coe_one]
      at h'
    rw [h', hm]
  have hc'1 : V.valuation (((algebraMap F K₀ c' : K₀)) : K) = 1 := by
    have hne : (((algebraMap F K₀ c' : K₀)) : K) ≠ 0 := by
      intro h0
      apply hc'
      have : algebraMap F K₀ c' = 0 := Subtype.ext h0
      exact (map_eq_zero_iff _ (algebraMap F K₀).injective).mp this
    have hinv : (((algebraMap F K₀ c' : K₀)) : K)⁻¹ ∈ V :=
      mem_of_mem_adjoin_residue hy (inv_mem hc'K)
    exact le_antisymm ((V.valuation_le_one_iff _).mpr hc'V) (by
      have h4 := (V.valuation_le_one_iff _).mpr hinv
      rw [map_inv₀] at h4
      have hpos : 0 < V.valuation (((algebraMap F K₀ c' : K₀)) : K) := by
        rw [zero_lt_iff]
        exact (Valuation.ne_zero_iff _).mpr hne
      rwa [inv_le_one₀ hpos] at h4)
  have hv := congrArg V.valuation hhK
  rw [map_mul, map_mul, map_mul, Valuation.map_one_add_of_lt _ hFmV,
    Valuation.map_one_add_of_lt _ hGV, mul_one, mul_one, hc'1, one_mul] at hv
  have hcle : V.valuation (c : K) ≤ 1 := (V.valuation_le_one_iff _).mpr hc
  rcases lt_or_eq_of_le hcle with hlt | heq
  · have : residue V ⟨c, hc⟩ = 0 := by
      rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      exact hlt
    rw [this]
    exact zero_mem _
  · have ha : a = 0 := hx a (hv ▸ heq)
    rw [ha, laurentMonomial_zero, mul_one] at hhK
    have hGV' : (G : K) ∈ V := (V.valuation_le_one_iff _).mp hGV.le
    have hFmV' : (Fm : K) ∈ V := (V.valuation_le_one_iff _).mp hFmV.le
    have hVeq : (⟨c, hc⟩ : V) * (1 + ⟨_, hGV'⟩) = ⟨_, hc'V⟩ * (1 + ⟨_, hFmV'⟩) :=
      Subtype.ext hhK
    have h5 := congrArg (residue V) hVeq
    have hG0 : residue V ⟨_, hGV'⟩ = 0 := by
      rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      exact hGV
    have hF0 : residue V ⟨_, hFmV'⟩ = 0 := by
      rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      exact hFmV
    rw [map_mul, map_mul, map_add, map_add, map_one, hG0, hF0, add_zero, mul_one, mul_one] at h5
    rw [h5]
    exact residue_mem_adjoin_of_mem_adjoin hy hc'K

end Adjoin

/-! ### The residue field of an Abhyankar valuation -/

section ResidueField

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- **The residue field is finite over `k(ȳ)`** (Volume 3, proof of Corollary 2.2.4 of the handbook). Let `V` be an Abhyankar valuation of the function field `K/k`. Then there are `y_1, ..., y_t ∈ V`, with `t` the transcendence degree of `Kv` over `k`, such that the residues `ȳ_j` are algebraically independent over `k` and `Kv` is finite over `k(ȳ)`. -/
theorem IsAbhyankarValuation.finiteDimensional_residueField (hK : IsFunctionField k K)
    (hV : IsAbhyankarValuation k V) :
    ∃ (t : ℕ) (y : Fin t → V), Algebra.trdeg k (ResidueField V) = t ∧
      AlgebraicIndependent k (fun j => residue V (y j)) ∧
      FiniteDimensional (IntermediateField.adjoin k (Set.range fun j => residue V (y j)))
        (ResidueField V) := by
  obtain ⟨r, t, x, y, -, ht, hx0, hx, hy, -, hfin, -, -⟩ :=
    hV.exists_isMonomialValuation_comap hK
  refine ⟨t, y, ht, hy, ?_⟩
  exact finiteDimensional_residueField_of_residue_mem V fun c hc =>
    ⟨⟨_, residue_mem_adjoin_of_mem_adjoin_sumElim hx0 hx hy c hc⟩, rfl⟩

/-- **The residue field of an Abhyankar valuation is finitely generated** (Volume 3, Corollary 2.2.4 of the handbook, the part on `Kv`). Let `V` be an Abhyankar valuation of the function field `K/k`. Then the residue field `Kv` is finitely generated over `k` as a field. -/
theorem IsAbhyankarValuation.fg_residueField (hK : IsFunctionField k K)
    (hV : IsAbhyankarValuation k V) : (⊤ : IntermediateField k (ResidueField V)).FG := by
  obtain ⟨t, y, -, -, hfin⟩ := hV.finiteDimensional_residueField hK
  set L := IntermediateField.adjoin k (Set.range fun j => residue V (y j))
  let b := Module.finBasis L (ResidueField V)
  rw [IntermediateField.fg_def]
  refine ⟨Set.range (fun j => residue V (y j)) ∪ Set.range b,
    (Set.finite_range _).union (Set.finite_range _), ?_⟩
  rw [eq_top_iff]
  rintro w -
  rw [← b.sum_repr w]
  refine sum_mem fun i _ => ?_
  rw [IntermediateField.smul_def, smul_eq_mul]
  refine mul_mem ?_ (IntermediateField.subset_adjoin k _ (Or.inr ⟨i, rfl⟩))
  have hle : L ≤ IntermediateField.adjoin k
      (Set.range (fun j => residue V (y j)) ∪ Set.range b) :=
    IntermediateField.adjoin_le_iff.mpr
      (Set.subset_union_left.trans (IntermediateField.subset_adjoin k _))
  exact hle (b.repr w i).2

end ResidueField

end Singularity
