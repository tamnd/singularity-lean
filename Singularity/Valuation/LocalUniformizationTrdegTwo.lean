/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.LocalUniformizationDivisorial
import Singularity.Valuation.MonomialGroundField

/-!
# Valuations with a residue field of large transcendence degree

This file proves Volume 5, Corollary 3.1.3 of the handbook, under the hypothesis of Volume 5, Proposition 3.1.2. Let `k` be a field of any characteristic, let `K/k` be a function field of transcendence degree `n`, and let `v` be a valuation of `K/k` with `trdeg_k κ_v ≥ n - 2`. Then `v` has local uniformization.

Proposition 3.1.2 states that each valuation of a function field of transcendence degree 2 over any field has local uniformization. Its proof in the handbook uses the theorem of Lipman on the resolution of excellent surfaces, which is not in Lean. So the corollary here takes Proposition 3.1.2 as the hypothesis `Singularity.LocalUniformizationTrdegTwo`.

* `Singularity.LocalUniformizationTrdegTwo`: the statement of Proposition 3.1.2 (not proved).
* `Singularity.hasLocalUniformization_of_trdeg_le_trdeg_residueField_add_two`: Corollary 3.1.3 of the handbook, from Proposition 3.1.2.

The proof is the proof of the handbook. Choose `y_1, ..., y_m ∈ V` whose residues form a transcendence basis of `κ_V` over `k`, and let `k' = k(y_1, ..., y_m)`. Then `k' ⊆ V`, and `K` is a function field over `k'` of transcendence degree at most 2. If the degree is at most 1, `V` has local uniformization over `k'` by `Singularity.hasLocalUniformization_of_trdeg_le_one`. If the degree is 2, it has local uniformization over `k'` by the hypothesis. The change of the ground field (Volume 5, Lemma 1.4.2, `Singularity.HasLocalUniformization.of_intermediateField`) gives local uniformization over `k`. The steps up to the choice of `k'` are the same as in the proof of `Singularity.essFiniteType_of_trdeg_le_trdeg_residueField_add_one`.
-/

open IsLocalRing Cardinal

universe u

namespace Singularity

/-- The statement of Volume 5, Proposition 3.1.2 of the handbook: let `k` be a field of any characteristic and let `K/k` be a function field of transcendence degree 2. Then each valuation of `K/k` has local uniformization. This file does not prove the statement. -/
def LocalUniformizationTrdegTwo : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K], IsFunctionField k K →
    Algebra.trdeg k K = 2 → ∀ (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K],
      HasLocalUniformization k V

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- **Volume 5, Corollary 3.1.3 of the handbook, from Proposition 3.1.2.** Let `K` be a function field over a field `k` of any characteristic, and let `V` be a valuation of `K/k` with `trdeg_k K ≤ trdeg_k κ_V + 2`. If Proposition 3.1.2 holds, then `V` has local uniformization. -/
theorem hasLocalUniformization_of_trdeg_le_trdeg_residueField_add_two
    (H : LocalUniformizationTrdegTwo.{u}) (hK : IsFunctionField k K)
    (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (htr : Algebra.trdeg k K ≤ Algebra.trdeg k (ResidueField V) + 2) :
    HasLocalUniformization k V := by
  classical
  have hKft : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hK
  have hfinK : Algebra.trdeg k K < ℵ₀ := trdeg_lt_aleph0 k K
  -- Step 0: elements `y j` of `V` whose residues form a transcendence basis of `κ_V`.
  obtain ⟨b, hb⟩ := exists_isTranscendenceBasis k (ResidueField V)
  choose y hy using fun e : b => residue_surjective (R := V) (e : ResidueField V)
  have hyres : AlgebraicIndependent k (fun j => residue V (y j)) := by
    convert hb.1 using 1
    funext j
    simp [hy j]
  have hyV : AlgebraicIndependent k y := by
    refine AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom k V (ResidueField V)) ?_
    convert hyres using 1
    funext j
    rfl
  set f : b → K := fun j => (y j : K)
  have hf : AlgebraicIndependent k f :=
    hyV.map' (f := IsScalarTower.toAlgHom k V K) Subtype.val_injective
  have hbκ : #b = Algebra.trdeg k (ResidueField V) := hb.cardinalMk_eq_trdeg
  -- Step 1: the field `k' = k(y)` lies in `V`.
  set k' : IntermediateField k K := IntermediateField.adjoin k (Set.range f)
  have h1 : ∀ P : MvPolynomial b k, MvPolynomial.aeval f P = ((MvPolynomial.aeval y P : V) : K) :=
    fun P => (MvPolynomial.comp_aeval_apply (f := y) (IsScalarTower.toAlgHom k V K) P).symm
  have h2 : ∀ P : MvPolynomial b k, MvPolynomial.aeval (fun j => residue V (y j)) P =
      residue V (MvPolynomial.aeval y P) := fun P => by
    have := MvPolynomial.comp_aeval_apply (f := y)
      (IsScalarTower.toAlgHom k V (ResidueField V)) P
    simpa using this.symm
  have hk'V : ∀ z ∈ k', z ∈ V := by
    intro z hz
    obtain ⟨r, hr, t, ht, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    rw [Algebra.adjoin_range_eq_range_aeval] at hr ht
    obtain ⟨P, rfl⟩ := hr
    obtain ⟨Q, rfl⟩ := ht
    by_cases hQ : Q = 0
    · simp [hQ]
    have hres : residue V (MvPolynomial.aeval y Q) ≠ 0 := by
      rw [← h2]
      exact fun h => hQ (algebraicIndependent_iff.mp hyres Q h)
    obtain ⟨u, hu⟩ := (residue_ne_zero_iff_isUnit _).mp hres
    have hu0 : ((u : V) : K) ≠ 0 := fun h0 => u.ne_zero (Subtype.ext h0)
    have : ((MvPolynomial.aeval y P : V) : K) / ((u : V) : K) =
        ((MvPolynomial.aeval y P * ↑u⁻¹ : V) : K) := by
      rw [div_eq_iff hu0]
      push_cast
      rw [mul_assoc, ← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one, mul_one]
    change MvPolynomial.aeval f P / MvPolynomial.aeval f Q ∈ V
    rw [h1, h1, ← hu, this]
    exact SetLike.coe_mem _
  -- The structures of `k'`-algebra on `V`.
  let ι : k' →+* V := (k'.val : k' →+* K).codRestrict V (fun z => hk'V z z.2)
  let : Algebra k' V := ι.toAlgebra
  have : IsScalarTower k' V K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower k k' V := IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext (by
    change (algebraMap k V a : K) = algebraMap k K a
    exact (IsScalarTower.algebraMap_apply k V K a).symm))
  -- Step 2: `K` is a function field over `k'` of transcendence degree at most 2.
  have hK' : IsFunctionField k' K := by
    have : Algebra.EssFiniteType k' K := Algebra.EssFiniteType.of_comp k k' K
    exact IntermediateField.fg_top_iff.mpr this
  have hadd := trdeg_add_eq k k' (A := K)
  have hbk' : #b ≤ Algebra.trdeg k k' := by
    let g : b → k' := fun j => ⟨f j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩
    have hg : AlgebraicIndependent k g := AlgebraicIndependent.of_comp k'.val hf
    exact hg.cardinalMk_le_trdeg
  have hfin' : Algebra.trdeg k k' < ℵ₀ :=
    lt_of_le_of_lt (hadd ▸ le_self_add) hfinK
  have htr' : Algebra.trdeg k' K ≤ 2 := by
    have : Algebra.trdeg k' K + Algebra.trdeg k k' ≤ 2 + Algebra.trdeg k k' := by
      rw [add_comm, hadd, add_comm 2]
      exact htr.trans (by rw [← hbκ]; gcongr)
    exact (add_le_add_iff_of_lt_aleph0 hfin').mp this
  -- Step 3: local uniformization over `k'`, then over `k`.
  have : Finite b := Cardinal.lt_aleph0_iff_finite.mp (hbk'.trans_lt hfin')
  have hk'fg : k'.FG := IntermediateField.fg_adjoin_of_finite (Set.finite_range f)
  have hV' : HasLocalUniformization k' V := by
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (htr'.trans_lt (by
      exact_mod_cast (natCast_lt_aleph0 : ((2 : ℕ) : Cardinal) < ℵ₀)))
    rw [hn] at htr'
    have hn2 : n ≤ 2 := by exact_mod_cast htr'
    rcases Nat.lt_or_eq_of_le hn2 with h | h
    · exact hasLocalUniformization_of_trdeg_le_one hK'
        (by rw [hn]; exact_mod_cast (by omega : n ≤ 1)) V
    · exact H k' K hK' (by rw [hn, h]; norm_num) V
  exact hV'.of_intermediateField hk'fg hk'V

end Singularity
