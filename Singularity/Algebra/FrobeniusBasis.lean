/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The monomial basis of a ring of power series over the power series in `x^q`

This file proves Volume 1, Proposition 6.1.5 of the handbook for power series. Let `K` be a commutative ring, let `q > 0` and let `S = K[[x_1, ..., x_n]]`. Let `S_e` be the subalgebra of the power series whose coefficients vanish outside the exponents in `q ℕ^n`. This is the ring `K[[x_1^q, ..., x_n^q]]`. Then `S` is a free `S_e`-module, with basis the monomials `x^α` with `0 ≤ α_i < q` for each `i`.

* `Singularity.Algebra.powSubalgebra`: the subalgebra `S_e`.
* `Singularity.Algebra.boxBasis`: the basis of the monomials `x^α` with `α_i < q`, Proposition 6.1.5 of the handbook.
* `Singularity.Algebra.finrank_powSubalgebra`: the rank of `S` over `S_e` is `q^n`.

The proof is the proof of the handbook. Each exponent `β` is `qγ + α` in exactly one way with `α_i < q`, namely `α_i = β_i % q`. For `f ∈ S`, the coordinate of `f` at `α` is the series `f_α` with coefficient `c_{β + α}` at each `β ∈ q ℕ^n`.

The handbook states the result for a field `K` of characteristic `p` and `q = p^e`. The proof uses neither hypothesis, so the Lean form is for each commutative ring `K` and each `q > 0`. The statement for the polynomial ring and Corollary 6.1.6 are not in this file.
-/

open MvPowerSeries

namespace Singularity.Algebra

variable (σ K : Type*) [CommRing K]

/-- The subalgebra `K[[x_1^q, ..., x_n^q]]` of `K[[x_1, ..., x_n]]`: the power series whose coefficient at `β` is zero unless `q` divides each `β_i`. -/
def powSubalgebra (q : ℕ) : Subalgebra K (MvPowerSeries σ K) where
  carrier := {f | ∀ β : σ →₀ ℕ, (¬ ∀ i, q ∣ β i) → coeff β f = 0}
  mul_mem' := by
    classical
    intro f g hf hg β hβ
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    by_cases h1 : ∀ i, q ∣ p.1 i
    · have h2 : ¬ ∀ i, q ∣ p.2 i := by
        intro h2
        apply hβ
        intro i
        rw [← hp, Finsupp.add_apply]
        exact dvd_add (h1 i) (h2 i)
      rw [hg _ h2, mul_zero]
    · rw [hf _ h1, zero_mul]
  add_mem' := by
    intro f g hf hg β hβ
    rw [map_add, hf β hβ, hg β hβ, add_zero]
  algebraMap_mem' := by
    classical
    intro a β hβ
    have h0 : β ≠ 0 := by rintro rfl; exact hβ fun i => by simp
    rw [Algebra.algebraMap_eq_smul_one, map_smul, coeff_one]
    simp [h0]

variable {σ K}

theorem mem_powSubalgebra {q : ℕ} {f : MvPowerSeries σ K} :
    f ∈ powSubalgebra σ K q ↔ ∀ β : σ →₀ ℕ, (¬ ∀ i, q ∣ β i) → coeff β f = 0 :=
  Iff.rfl

theorem mod_eq_of_dvd_sub {q n a : ℕ} (ha : a < q) (hle : a ≤ n) (h : q ∣ n - a) :
    n % q = a := by
  obtain ⟨k, hk⟩ := h
  have : n = a + q * k := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

variable [Fintype σ] [DecidableEq σ]

/-- The exponent `α ∈ ℕ^n` of an element `α` of the box `0 ≤ α_i < q`. -/
noncomputable def boxExp {q : ℕ} (α : σ → Fin q) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (α i : ℕ)

omit [DecidableEq σ] in
@[simp]
theorem boxExp_apply {q : ℕ} (α : σ → Fin q) (i : σ) : boxExp α i = α i := by
  simp [boxExp]

/-- The coefficient of `∑_α g_α x^α` at `m`. -/
theorem coeff_sum_mul_monomial {q : ℕ} (g : (σ → Fin q) → MvPowerSeries σ K) (m : σ →₀ ℕ) :
    coeff m (∑ α, g α * monomial (boxExp α) (1 : K)) =
      ∑ α, if boxExp α ≤ m then coeff (m - boxExp α) (g α) else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_mul_monomial, mul_one]

variable (K) in
theorem linearIndependent_boxMonomial {q : ℕ} :
    LinearIndependent (powSubalgebra σ K q)
      (fun α : σ → Fin q => (monomial (boxExp α) (1 : K) : MvPowerSeries σ K)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg α
  simp only [Subalgebra.smul_def, smul_eq_mul] at hg
  apply Subtype.ext
  ext β
  rw [ZeroMemClass.coe_zero, map_zero]
  by_cases hβ : ∀ i, q ∣ β i
  · have h := congrArg (coeff (β + boxExp α)) hg
    rw [coeff_sum_mul_monomial, map_zero, Finset.sum_eq_single α] at h
    · rwa [ite_eq_left le_add_self, add_tsub_cancel_right] at h
    · intro α' _ hne
      split_ifs with hle
      · apply (g α').2
        intro hdvd
        apply hne
        funext i
        apply Fin.ext
        have hle' := (Finsupp.le_def.1 hle) i
        rw [boxExp_apply, Finsupp.add_apply, boxExp_apply] at hle'
        have h1 : (β i + α i) % q = α' i := by
          refine mod_eq_of_dvd_sub (α' i).2 hle' ?_
          have := hdvd i
          rwa [Finsupp.tsub_apply, Finsupp.add_apply, boxExp_apply, boxExp_apply] at this
        have h2 : (β i + α i) % q = α i := by
          refine mod_eq_of_dvd_sub (α i).2 le_add_self ?_
          rw [Nat.add_sub_cancel]
          exact hβ i
        exact h1.symm.trans h2
      · rfl
    · intro h
      exact absurd (Finset.mem_univ α) h
  · exact (g α).2 β hβ

/-- The coordinate `f_α ∈ S_e` of `f` at `α`: the series with coefficient `c_{β + α}` at each `β ∈ q ℕ^n`. -/
noncomputable def boxCoord {q : ℕ} (f : MvPowerSeries σ K) (α : σ → Fin q) :
    powSubalgebra σ K q := by
  classical
  exact ⟨fun β => if ∀ i, q ∣ β i then coeff (β + boxExp α) f else 0, fun β hβ => by
    change (if ∀ i, q ∣ β i then coeff (β + boxExp α) f else 0) = 0
    rw [ite_eq_right hβ]⟩

omit [DecidableEq σ] in
theorem coeff_boxCoord {q : ℕ} (f : MvPowerSeries σ K) (α : σ → Fin q) (β : σ →₀ ℕ) :
    coeff β (boxCoord f α : MvPowerSeries σ K) =
      if ∀ i, q ∣ β i then coeff (β + boxExp α) f else 0 := by
  classical
  simp only [boxCoord]
  rfl

theorem sum_boxCoord_mul {q : ℕ} (hq : 0 < q) (f : MvPowerSeries σ K) :
    ∑ α : σ → Fin q, (boxCoord f α : MvPowerSeries σ K) * monomial (boxExp α) (1 : K) = f := by
  classical
  ext m
  rw [coeff_sum_mul_monomial]
  let α₀ : σ → Fin q := fun i => ⟨m i % q, Nat.mod_lt _ hq⟩
  have hle₀ : boxExp α₀ ≤ m := Finsupp.le_def.2 fun i => by
    rw [boxExp_apply]
    exact Nat.mod_le _ _
  rw [Finset.sum_eq_single α₀]
  · rw [ite_eq_left hle₀, coeff_boxCoord, ite_eq_left, tsub_add_cancel_of_le hle₀]
    intro i
    rw [Finsupp.tsub_apply, boxExp_apply]
    exact Nat.dvd_sub_mod _
  · intro α _ hne
    split_ifs with hle
    · rw [coeff_boxCoord, ite_eq_right]
      intro hdvd
      apply hne
      funext i
      apply Fin.ext
      have hle' := (Finsupp.le_def.1 hle) i
      rw [boxExp_apply] at hle'
      have := hdvd i
      rw [Finsupp.tsub_apply, boxExp_apply] at this
      exact (mod_eq_of_dvd_sub (α i).2 hle' this).symm
    · rfl
  · intro h
    exact absurd (Finset.mem_univ α₀) h

variable (σ K) in
/-- Volume 1, Proposition 6.1.5 of the handbook: the monomials `x^α` with `0 ≤ α_i < q` are a basis of `K[[x_1, ..., x_n]]` over `K[[x_1^q, ..., x_n^q]]`. -/
noncomputable def boxBasis {q : ℕ} (hq : 0 < q) :
    Module.Basis (σ → Fin q) (powSubalgebra σ K q) (MvPowerSeries σ K) :=
  Module.Basis.mk (linearIndependent_boxMonomial K) fun f _ => by
    rw [← sum_boxCoord_mul hq f]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [← smul_eq_mul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

theorem boxBasis_apply {q : ℕ} (hq : 0 < q) (α : σ → Fin q) :
    boxBasis σ K hq α = monomial (boxExp α) 1 :=
  Module.Basis.mk_apply _ _ _

variable (σ K) in
/-- The ring `K[[x_1, ..., x_n]]` is a free module of rank `q^n` over `K[[x_1^q, ..., x_n^q]]`. -/
theorem finrank_powSubalgebra [Nontrivial K] {q : ℕ} (hq : 0 < q) :
    Module.Free (powSubalgebra σ K q) (MvPowerSeries σ K) ∧
      Module.finrank (powSubalgebra σ K q) (MvPowerSeries σ K) = q ^ Fintype.card σ := by
  refine ⟨Module.Free.of_basis (boxBasis σ K hq), ?_⟩
  rw [Module.finrank_eq_card_basis (boxBasis σ K hq)]
  simp

end Singularity.Algebra
