/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.LocalUniformization
import Singularity.Valuation.LatticeLemma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.NNReal.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Local uniformization of monomial valuations

Let `k` be a field of any characteristic, let `K = k(x_1, ..., x_n)`, and let `V` be a valuation of `K/k` such that the values `v(x_1), ..., v(x_n)` are linearly independent over `ℤ`. Then `V` is the monomial valuation of `K` with these weights (Volume 5, Definition 2.1.1 of the handbook), and `V` is an Abhyankar valuation with residue field `k`. This file proves that `V` has local uniformization, if the value group has rank 1 (node SG0000004D, Volume 5, Theorem 2.1.5 of the handbook, in rank 1).

The proof has two parts. The algebraic part works for each monomial valuation. It takes the lattice lemma (Volume 5, Lemma 2.1.4) as a hypothesis. The combinatorial part is the lattice lemma. This file uses the case of rank 1, `Singularity.latticeLemma_real`.

## The proof

For `a ∈ ℤ^n` let `x^a = ∏ x_i ^ a_i` be the Laurent monomial (`Singularity.laurentMonomial`). Let `s` be a finite subset of `V`.

1. Leading terms. Distinct monomials have distinct values. So a nonzero polynomial `f` in the `x_i` is `c x^α (1 + F)`, where `c x^α` is its term of least value and `F` is a combination of Laurent monomials of positive value. Each `z ∈ s` is `f / g` for two polynomials. So `z (1 + G) = (c / d) x^{α - β} (1 + F)`, where `v(x^{α - β}) = v(z) ≥ 0` (`Singularity.MonomialValuation.exists_exponents`).
2. The lattice lemma gives a basis `b_1, ..., b_n` of `ℤ^n` with `v(x^{b_l}) > 0`, such that all the exponents of step 1 are combinations of the `b_l` with coefficients in `ℕ`. Let `u_l = x^{b_l}`. Then the exponents of step 1 give monomials in the `u_l`.
3. The `u_l` are algebraically independent over `k`, and `K = k(u_1, ..., u_n)`. Let `P` be the center of `V` on the polynomial ring `R = k[u_1, ..., u_n]`. Each `z ∈ s` lies in the subring `T = R_P` of `K`, because `z (1 + G) ∈ R` and `1 + G ∉ P`.
4. Let `A = k[u_1, ..., u_n, s]`. Then `s ⊆ A ⊆ T ⊆ V`, `A` is an affine model of `K/k`, and the localization of `A` at the center of `V` is `T`. The ring `T` is the localization of the polynomial ring `R` at a prime ideal, so it is a regular local ring.

## Main definitions

* `Singularity.laurentMonomial`: the Laurent monomial `x^a = ∏ x_i ^ a_i`.
* `Singularity.IsMonomialValuation`: `K = k(x_1, ..., x_n)`, and the values of the `x_i` are linearly independent over `ℤ`.

## Main results

* `Singularity.hasLocalUniformization_of_isMonomialValuation_of_lattice`: a monomial valuation has local uniformization, if the lattice lemma holds for its values. This works for each value group.
* `Singularity.hasLocalUniformization_of_isMonomialValuation_of_rankOne`: a monomial valuation of rank 1 has local uniformization.

The lattice lemma for value groups of higher rank (Volume 5, Lemma 2.1.4, with the cone lemma 2.1.3) is not in this file.
-/

open MvPolynomial IsLocalRing Matrix
open scoped NNReal

namespace Singularity

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- The Laurent monomial `x^a = ∏ x_i ^ a_i` in elements `x_i` of a field. -/
def laurentMonomial (x : ι → K) (a : ι → ℤ) : K :=
  ∏ i, x i ^ a i

section LaurentMonomial

variable {x : ι → K}

theorem laurentMonomial_eq_units (hx : ∀ i, x i ≠ 0) (a : ι → ℤ) :
    laurentMonomial x a = ((∏ i, Units.mk0 (x i) (hx i) ^ a i : Kˣ) : K) := by
  simp [laurentMonomial, Units.coe_prod, Units.val_zpow_eq_zpow_val]

theorem laurentMonomial_ne_zero (hx : ∀ i, x i ≠ 0) (a : ι → ℤ) : laurentMonomial x a ≠ 0 := by
  rw [laurentMonomial_eq_units hx]
  exact Units.ne_zero _

theorem laurentMonomial_zero (x : ι → K) : laurentMonomial x 0 = 1 := by
  simp [laurentMonomial]

theorem laurentMonomial_add (hx : ∀ i, x i ≠ 0) (a b : ι → ℤ) :
    laurentMonomial x (a + b) = laurentMonomial x a * laurentMonomial x b := by
  simp only [laurentMonomial_eq_units hx, ← Units.val_mul, Pi.add_apply, zpow_add,
    Finset.prod_mul_distrib]

theorem laurentMonomial_sub (hx : ∀ i, x i ≠ 0) (a b : ι → ℤ) :
    laurentMonomial x (a - b) = laurentMonomial x a / laurentMonomial x b := by
  rw [eq_div_iff (laurentMonomial_ne_zero hx b), ← laurentMonomial_add hx, sub_add_cancel]

theorem laurentMonomial_natCast (x : ι → K) (β : ι →₀ ℕ) :
    laurentMonomial x (fun i => (β i : ℤ)) = ∏ i, x i ^ β i := by
  simp [laurentMonomial, zpow_natCast]

theorem laurentMonomial_single [DecidableEq ι] (x : ι → K) (i : ι) :
    laurentMonomial x (Pi.single i 1) = x i := by
  rw [laurentMonomial, Finset.prod_eq_single i (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

omit [Fintype ι] in
private theorem units_zpow_sum (y : Kˣ) (s : Finset ι) (f : ι → ℤ) :
    y ^ (∑ i ∈ s, f i) = ∏ i ∈ s, y ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

/-- The monomial `x^{n B}` is the monomial `u^n` in the elements `u_l = x^{b_l}`, where `b_l` is the row `l` of `B`. -/
theorem laurentMonomial_vecMul (hx : ∀ i, x i ≠ 0) (n : ι → ℤ) (B : Matrix ι ι ℤ) :
    laurentMonomial x (n ᵥ* B) = laurentMonomial (fun l => laurentMonomial x (B l)) n := by
  have hu : ∀ l, laurentMonomial x (B l) ≠ 0 := fun l => laurentMonomial_ne_zero hx _
  rw [laurentMonomial_eq_units hx, laurentMonomial_eq_units hu]
  congr 1
  have h2 : ∀ l, Units.mk0 (laurentMonomial x (B l)) (hu l) = ∏ i, Units.mk0 (x i) (hx i) ^ B l i :=
    fun l => Units.ext (by rw [Units.val_mk0, laurentMonomial_eq_units hx])
  simp only [h2, vecMul, dotProduct, units_zpow_sum, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => Finset.prod_congr rfl fun i _ => ?_
  rw [mul_comm]

end LaurentMonomial

variable {k : Type*} [Field k] [Algebra k K]

variable (k) in
/-- The valuation `V` of `K/k` is a monomial valuation in the elements `x_1, ..., x_n` of `K`: the `x_i` are not zero, they generate `K` over `k` as a field, and their values are linearly independent over `ℤ`, that is, a Laurent monomial `x^a` has value 1 only if `a = 0`.

Then the `x_i` are algebraically independent over `k`, and the value of a polynomial `∑ c_a x^a` is the least value of its terms. So `V` is the monomial valuation of `K = k(x_1, ..., x_n)` with the weights `v(x_i)` (Volume 5, Definition 2.1.1 of the handbook). -/
structure IsMonomialValuation (V : ValuationSubring K) (x : ι → K) : Prop where
  ne_zero : ∀ i, x i ≠ 0
  adjoin_eq_top : IntermediateField.adjoin k (Set.range x) = ⊤
  independent : ∀ a : ι → ℤ, V.valuation (laurentMonomial x a) = 1 → a = 0

namespace MonomialValuation

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

theorem valuation_algebraMap_le_one (c : k) : V.valuation (algebraMap k K c) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply k V K]
  exact V.valuation_le_one _

theorem valuation_algebraMap_eq_one {c : k} (hc : c ≠ 0) : V.valuation (algebraMap k K c) = 1 := by
  rw [IsScalarTower.algebraMap_apply k V K]
  exact (V.valuation_eq_one_iff _).mp ((IsUnit.mk0 c hc).map (algebraMap k V))

variable (k V) in
/-- The `k`-subalgebra of `K` of the elements of `V`. -/
def subalgebra : Subalgebra k K :=
  { V.toSubring.toSubsemiring with
    algebraMap_mem' := fun c => by
      rw [IsScalarTower.algebraMap_apply k V K]
      exact (algebraMap k V c).2 }

theorem mem_subalgebra {z : K} : z ∈ subalgebra k V ↔ z ∈ V := Iff.rfl

/-- **Leading terms.** Let `y_1, ..., y_n` be nonzero elements of `K` whose values are linearly independent over `ℤ`, and let `f` be a nonzero polynomial over `k`. Then `f(y) = c y^α (1 + F)`, where `c ≠ 0`, and `F` is a combination of Laurent monomials `y^a` with `a` in a finite set `D` and `v(y^a) < 1`. In particular `v(F) < 1`. -/
theorem exists_leadingTerm {y : ι → K} (hy : ∀ i, y i ≠ 0)
    (hind : ∀ a : ι → ℤ, V.valuation (laurentMonomial y a) = 1 → a = 0)
    {f : MvPolynomial ι k} (hf : f ≠ 0) :
    ∃ (c : k) (α : ι → ℤ) (D : Finset (ι → ℤ)) (F : K), c ≠ 0 ∧
      aeval y f = algebraMap k K c * laurentMonomial y α * (1 + F) ∧
      (∀ a ∈ D, V.valuation (laurentMonomial y a) < 1) ∧
      (∀ S : Subalgebra k K, (∀ a ∈ D, laurentMonomial y a ∈ S) → F ∈ S) ∧
      V.valuation F < 1 := by
  classical
  set v := V.valuation
  let e : (ι →₀ ℕ) → (ι → ℤ) := fun β i => (β i : ℤ)
  have he : Function.Injective e := fun β β' h => Finsupp.ext fun i => by
    have := congrFun h i
    simpa [e] using this
  obtain ⟨α, hα, hmax⟩ := f.support.exists_max_image (fun β => v (laurentMonomial y (e β)))
    (MvPolynomial.support_nonempty.mpr hf)
  set c := f.coeff α with hcdef
  have hc : c ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  have hsplit : ∀ β, laurentMonomial y (e β) = laurentMonomial y (e β - e α) *
      laurentMonomial y (e α) := fun β => by
    rw [← laurentMonomial_add hy, sub_add_cancel]
  have hlt : ∀ β ∈ f.support.erase α, v (laurentMonomial y (e β - e α)) < 1 := by
    intro β hβ
    obtain ⟨hne, hβs⟩ := Finset.mem_erase.mp hβ
    have hle := hmax β hβs
    have h0 : v (laurentMonomial y (e α)) ≠ 0 :=
      (Valuation.ne_zero_iff v).mpr (laurentMonomial_ne_zero hy _)
    by_contra hge
    push Not at hge
    have h2 : v (laurentMonomial y (e α)) ≤ v (laurentMonomial y (e β)) := by
      rw [hsplit β, map_mul]
      calc v (laurentMonomial y (e α)) = 1 * v (laurentMonomial y (e α)) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_left hge _
    have h3 : v (laurentMonomial y (e β)) = v (laurentMonomial y (e α)) := le_antisymm hle h2
    rw [hsplit β, map_mul] at h3
    have h4 : v (laurentMonomial y (e β - e α)) = 1 := by
      calc v (laurentMonomial y (e β - e α))
          = v (laurentMonomial y (e β - e α)) * v (laurentMonomial y (e α)) /
            v (laurentMonomial y (e α)) := (mul_div_cancel_right₀ _ h0).symm
        _ = 1 := by rw [h3, div_self h0]
    exact hne (he (sub_eq_zero.mp (hind _ h4)))
  set D := (f.support.erase α).image fun β => e β - e α
  set F : K := ∑ β ∈ f.support.erase α,
    algebraMap k K (f.coeff β / c) * laurentMonomial y (e β - e α) with hF
  have hterm : ∀ β ∈ f.support.erase α,
      v (algebraMap k K (f.coeff β / c) * laurentMonomial y (e β - e α)) < 1 := by
    intro β hβ
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_algebraMap_le_one _)) (hlt β hβ)
  refine ⟨c, e α, D, F, hc, ?_, ?_, ?_, ?_⟩
  · have hsum : aeval y f = ∑ β ∈ f.support, algebraMap k K (f.coeff β) *
        laurentMonomial y (e β) := by
      conv_lhs => rw [f.as_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), laurentMonomial_natCast]
    rw [hsum, ← Finset.add_sum_erase _ _ hα, mul_add, mul_one, hF, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun β _ => ?_
    have hc' : algebraMap k K c ≠ 0 := (map_ne_zero _).mpr hc
    rw [hsplit β, map_div₀]
    field_simp
  · intro a ha
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp ha
    exact hlt β hβ
  · intro S hS
    refine Subalgebra.sum_mem _ fun β hβ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
    exact hS _ (Finset.mem_image_of_mem _ hβ)
  · exact Valuation.map_sum_lt v one_ne_zero hterm

/-- **Step 1.** Let `V` be a monomial valuation in `x_1, ..., x_n`, and let `z ∈ V`. Then there is a finite set `E` of exponents with `v(x^a) ≤ 1` for `a ∈ E`, such that `z g = f` with `f, g` in each subalgebra `S` that contains the monomials `x^a`, `a ∈ E`, and with `v(g) = 1`. -/
theorem exists_exponents {x : ι → K} (hV : IsMonomialValuation k V x) {z : K} (hz : z ∈ V) :
    ∃ E : Finset (ι → ℤ), (∀ a ∈ E, V.valuation (laurentMonomial x a) ≤ 1) ∧
      ∀ S : Subalgebra k K, (∀ a ∈ E, laurentMonomial x a ∈ S) →
        ∃ f g : K, f ∈ S ∧ g ∈ S ∧ V.valuation g = 1 ∧ z * g = f := by
  classical
  set v := V.valuation
  by_cases hz0 : z = 0
  · refine ⟨∅, by simp, fun S _ => ⟨0, 1, Subalgebra.zero_mem _, Subalgebra.one_mem _, map_one v,
      by rw [hz0, zero_mul]⟩⟩
  have hzK : z ∈ IntermediateField.adjoin k (Set.range x) := by
    rw [hV.adjoin_eq_top]
    exact IntermediateField.mem_top
  obtain ⟨f₀, hf₀, g₀, hg₀, hfg⟩ := IntermediateField.mem_adjoin_iff_div.mp hzK
  rw [Algebra.adjoin_range_eq_range_aeval] at hf₀ hg₀
  obtain ⟨P, rfl⟩ := hf₀
  obtain ⟨Q, rfl⟩ := hg₀
  replace hfg : z = aeval x P / aeval x Q := hfg
  have hP : P ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hfg
    exact hz0 hfg
  have hQ : Q ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero] at hfg
    exact hz0 hfg
  obtain ⟨c, α, D, F, hc, hPe, hD, hDS, hF⟩ := exists_leadingTerm hV.ne_zero hV.independent hP
  obtain ⟨d, β, D', G, hd, hQe, hD', hDS', hG⟩ := exists_leadingTerm hV.ne_zero hV.independent hQ
  have hF1 : v (1 + F) = 1 := Valuation.map_one_add_of_lt v hF
  have hG1 : v (1 + G) = 1 := Valuation.map_one_add_of_lt v hG
  have hG0 : 1 + G ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hG1
    exact zero_ne_one hG1
  have hxβ : laurentMonomial x β ≠ 0 := laurentMonomial_ne_zero hV.ne_zero β
  have hd' : algebraMap k K d ≠ 0 := (map_ne_zero _).mpr hd
  have hzeq : z * (1 + G) = algebraMap k K (c / d) * laurentMonomial x (α - β) * (1 + F) := by
    rw [hfg, hPe, hQe, laurentMonomial_sub hV.ne_zero, map_div₀]
    field_simp
  refine ⟨insert (α - β) (D ∪ D'), ?_, fun S hS => ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · have h2 := congrArg v hzeq
      rw [map_mul, map_mul, map_mul, hF1, hG1, mul_one, mul_one,
        valuation_algebraMap_eq_one (div_ne_zero hc hd), one_mul] at h2
      rw [← h2]
      exact V.valuation_le_one ⟨z, hz⟩
    · rcases Finset.mem_union.mp ha with ha | ha
      · exact (hD a ha).le
      · exact (hD' a ha).le
  · have hFS : F ∈ S := hDS S fun a ha => hS a (Finset.mem_insert_of_mem (Finset.mem_union_left _ ha))
    have hGS : G ∈ S :=
      hDS' S fun a ha => hS a (Finset.mem_insert_of_mem (Finset.mem_union_right _ ha))
    refine ⟨_, 1 + G, ?_, Subalgebra.add_mem _ (Subalgebra.one_mem _) hGS, hG1, hzeq⟩
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (hS _ (Finset.mem_insert_self _ _))) (Subalgebra.add_mem _ (Subalgebra.one_mem _) hFS)

/-- **Steps 3 and 4.** Let `V` be a monomial valuation in `x_1, ..., x_n`, let `B` and `C` be inverse integer matrices such that the monomials `u_l = x^{b_l}` of the rows of `B` have `v(u_l) < 1`, and let `s` be a finite subset of `V`. Assume that each `z ∈ s` has `z g = f` with `f, g ∈ k[u_1, ..., u_n]` and `v(g) = 1`. Then `V` has a regular center on an affine model that contains `s`. -/
theorem hasRegularCenter_of_basis [DecidableEq ι] {x : ι → K} (hV : IsMonomialValuation k V x)
    {B C : Matrix ι ι ℤ} (hBC : B * C = 1) (hCB : C * B = 1)
    (hpos : ∀ l, V.valuation (laurentMonomial x (B l)) < 1) (s : Finset K)
    (hs : ∀ z ∈ s, z ∈ V)
    (hgood : ∀ z ∈ s, ∃ f g : K, f ∈ Algebra.adjoin k (Set.range fun l => laurentMonomial x (B l)) ∧
      g ∈ Algebra.adjoin k (Set.range fun l => laurentMonomial x (B l)) ∧ V.valuation g = 1 ∧
        z * g = f) :
    HasRegularCenter k V s := by
  classical
  set v := V.valuation
  set u : ι → K := fun l => laurentMonomial x (B l) with hu
  have hu0 : ∀ l, u l ≠ 0 := fun l => laurentMonomial_ne_zero hV.ne_zero _
  -- The monomials in `u` are monomials in `x`.
  have hux : ∀ n, laurentMonomial u n = laurentMonomial x (n ᵥ* B) := fun n =>
    (laurentMonomial_vecMul hV.ne_zero n B).symm
  have huind : ∀ n : ι → ℤ, v (laurentMonomial u n) = 1 → n = 0 := by
    intro n hn
    rw [hux] at hn
    have h2 := hV.independent _ hn
    rw [← vecMul_one n, ← hBC, ← vecMul_vecMul, h2, zero_vecMul]
  -- The polynomial ring `R = k[u_1, ..., u_n]`.
  set ψ : MvPolynomial ι k →ₐ[k] K := aeval u with hψ
  have hψrange : ψ.range = Algebra.adjoin k (Set.range u) := (Algebra.adjoin_range_eq_range_aeval k u).symm
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    obtain ⟨c, α, D, F, hc, hpe, -, -, hF⟩ := exists_leadingTerm hu0 huind hp0
    have hF1 : v (1 + F) = 1 := Valuation.map_one_add_of_lt v hF
    have h1F : 1 + F ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hF1
      exact zero_ne_one hF1
    rw [hψ, hpe] at hp
    exact mul_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hc) (laurentMonomial_ne_zero hu0 α)) h1F hp
  have huV : ∀ l, u l ∈ V := fun l => (V.valuation_le_one_iff _).mp (hpos l).le
  have hψV : ∀ p, ψ p ∈ V := by
    intro p
    have hle : ψ.range ≤ subalgebra k V := by
      rw [hψrange]
      exact Algebra.adjoin_le fun z ⟨l, hl⟩ => hl ▸ huV l
    exact hle ⟨p, rfl⟩
  -- The center `P` of `V` on `R`.
  set φ : MvPolynomial ι k →+* V := (ψ : MvPolynomial ι k →+* K).codRestrict V hψV
  set P : Ideal (MvPolynomial ι k) := (maximalIdeal V).comap φ with hP
  have hmemP : ∀ p, p ∈ P ↔ v (ψ p) < 1 := fun p => V.valuation_lt_one_iff (φ p)
  have hψunit : ∀ q : P.primeCompl, IsUnit ((ψ : MvPolynomial ι k →+* K) q) := by
    intro q
    refine IsUnit.mk0 _ fun h0 => q.2 ((hmemP q).mpr ?_)
    change ψ q = 0 at h0
    rw [h0, map_zero]
    exact zero_lt_one
  -- The subring `T = R_P` of `K`.
  set L := Localization.AtPrime P
  set ι' : L →+* K := IsLocalization.lift (M := P.primeCompl) (g := (ψ : MvPolynomial ι k →+* K))
    hψunit with hι'
  have hι'inj : Function.Injective ι' := by
    rw [hι', IsLocalization.lift_injective_iff]
    intro p q
    have h1 := IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors P)
    exact ⟨fun h => by rw [h1 h], fun h => by rw [hψinj h]⟩
  set T : Subring K := ι'.range
  have hmemT : ∀ z, (∃ p q, v (ψ q) = 1 ∧ z * ψ q = ψ p) → z ∈ T := by
    rintro z ⟨p, q, hq, hz⟩
    have hqP : q ∈ P.primeCompl := fun h => by
      have h2 := (hmemP q).mp h
      rw [hq] at h2
      exact lt_irrefl _ h2
    refine ⟨IsLocalization.mk' L p ⟨q, hqP⟩, ?_⟩
    rw [hι', IsLocalization.lift_mk'_spec]
    change ψ p = ψ q * z
    rw [← hz, mul_comm]
  have hTmem : ∀ z ∈ T, ∃ p q, v (ψ q) = 1 ∧ z * ψ q = ψ p := by
    rintro z ⟨w, rfl⟩
    obtain ⟨p, q, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl w
    refine ⟨p, q, ?_, ?_⟩
    · have h2 := q.2
      rw [Ideal.mem_primeCompl_iff, hmemP] at h2
      exact le_antisymm (V.valuation_le_one ⟨_, hψV q⟩) (not_lt.mp h2)
    · have h2 : ι' (IsLocalization.mk' L p q) = ι' (IsLocalization.mk' L p q) := rfl
      rw [hι', IsLocalization.lift_mk'_spec] at h2
      rw [mul_comm]
      exact h2.symm
  -- The affine model `A = k[u_1, ..., u_n, s]`.
  set A : Subalgebra k K := Algebra.adjoin k (Set.range u ∪ (s : Set K)) with hA
  have hRA : Algebra.adjoin k (Set.range u) ≤ A := Algebra.adjoin_mono Set.subset_union_left
  have hψA : ∀ p, ψ p ∈ A := fun p => hRA (hψrange ▸ ⟨p, rfl⟩)
  have hAV : ∀ a : A, (a : K) ∈ V := by
    have hle : A ≤ subalgebra k V := by
      refine Algebra.adjoin_le fun z hz => ?_
      rcases hz with ⟨l, rfl⟩ | hz
      · exact huV l
      · exact hs z hz
    exact fun a => hle a.2
  have hAT : ∀ a : A, (a : K) ∈ T := by
    let Ts : Subalgebra k K :=
      { T with
        algebraMap_mem' := fun c => hmemT _ ⟨MvPolynomial.C c, 1, by rw [map_one, map_one], by simp [hψ]⟩ }
    have hle : A ≤ Ts := by
      refine Algebra.adjoin_le fun z hz => ?_
      rcases hz with ⟨l, rfl⟩ | hz
      · exact hmemT _ ⟨X l, 1, by rw [map_one, map_one], by simp [hψ]⟩
      · obtain ⟨f, g, hf, hg, hg1, hzg⟩ := hgood z hz
        rw [← hψrange] at hf hg
        obtain ⟨p, rfl⟩ := hf
        obtain ⟨q, rfl⟩ := hg
        exact hmemT _ ⟨p, q, hg1, hzg⟩
    exact fun a => hle a.2
  -- `K` is the fraction field of `A`.
  have hutop : IntermediateField.adjoin k (Set.range u) = ⊤ := by
    rw [eq_top_iff, ← hV.adjoin_eq_top, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    have h2 : x i = laurentMonomial u (C i) := by
      rw [hux, ← laurentMonomial_single x i]
      congr 1
      ext j
      have := congrFun (congrFun hCB i) j
      simp only [mul_apply, one_apply] at this
      simp [vecMul, dotProduct, this, Pi.single_apply, eq_comm]
    rw [h2, laurentMonomial]
    refine prod_mem fun l _ => zpow_mem (IntermediateField.subset_adjoin k _ (Set.mem_range_self l)) _
  have hfrac : IsFractionRing A K := by
    refine IsFractionRing.of_field A K fun z => ?_
    have hz : z ∈ IntermediateField.adjoin k (Set.range u) := by
      rw [hutop]
      exact IntermediateField.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨a, hRA ha⟩, ⟨b, hRA hb⟩, rfl⟩
  have hfg : A.FG := by
    refine ⟨Finset.univ.image u ∪ s, ?_⟩
    rw [hA, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  refine ⟨A, hAV, ⟨hfg, hfrac⟩, fun z hz => Algebra.subset_adjoin (Or.inr hz), ?_⟩
  -- The localization of `A` at the center of `V` is `T`.
  set q := valuationCenter V A hAV
  have hmemq : ∀ a : A, a ∈ q ↔ v a < 1 := fun a => V.valuation_lt_one_iff ⟨a, hAV a⟩
  let j : A →+* T := (A.val : A →+* K).codRestrict T hAT
  let : Algebra A T := j.toAlgebra
  have hj : ∀ a : A, ((algebraMap A T a : T) : K) = a := fun a => rfl
  have hloc : IsLocalization q.primeCompl T := by
    refine (isLocalization_iff q.primeCompl T).mpr ⟨fun a => ?_, fun z => ?_, fun {a b} h => ⟨1, ?_⟩⟩
    · have ha1 : v (a : A) = 1 := by
        have h2 := a.2
        rw [Ideal.mem_primeCompl_iff, hmemq] at h2
        exact le_antisymm (V.valuation_le_one ⟨_, hAV a⟩) (not_lt.mp h2)
      have ha0 : ((a : A) : K) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at ha1
        exact zero_ne_one ha1
      obtain ⟨p, r, hr, hpr⟩ := hTmem _ (hAT a)
      have hp : v (ψ p) = 1 := by rw [← hpr, map_mul, ha1, hr, one_mul]
      have hinv : ((a : A) : K)⁻¹ ∈ T := hmemT _ ⟨r, p, hp, by
        rw [← hpr]
        field_simp⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
      change ((a : A) : K) * ((a : A) : K)⁻¹ = 1
      exact mul_inv_cancel₀ ha0
    · obtain ⟨p, r, hr, hpr⟩ := hTmem _ z.2
      have hrq : (⟨ψ r, hψA r⟩ : A) ∈ q.primeCompl := by
        rw [Ideal.mem_primeCompl_iff, hmemq]
        change ¬ v (ψ r) < 1
        rw [hr]
        exact lt_irrefl _
      refine ⟨(⟨ψ p, hψA p⟩, ⟨_, hrq⟩), Subtype.ext ?_⟩
      exact hpr
    · have hab : (a : K) = b := congrArg (fun t : T => (t : K)) h
      rw [Subtype.ext hab]
  -- `T` is isomorphic to the localization of `R` at `P`, a regular local ring.
  have hreg : IsRegularLocalRing L := inferInstance
  let eT : L ≃+* T := RingEquiv.ofBijective ι'.rangeRestrict
    ⟨fun a b h => hι'inj (congrArg Subtype.val h), ι'.rangeRestrict_surjective⟩
  have hregT : IsRegularLocalRing T := IsRegularLocalRing.of_ringEquiv eT
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).toRingEquiv

end MonomialValuation

open MonomialValuation

variable {V : ValuationSubring K} [Algebra k V] [IsScalarTower k V K]

/-- **Local uniformization of monomial valuations, given the lattice lemma** (Volume 5, Theorem 2.1.5 of the handbook). Let `V` be a monomial valuation of `K = k(x_1, ..., x_n)` (`IsMonomialValuation`). Assume the lattice lemma for the values of `V`: for each finite set `E` of exponents with `v(x^a) ≤ 1`, there are inverse integer matrices `B` and `C` such that the rows `b_l` of `B` have `v(x^{b_l}) < 1` and each `a ∈ E` has coefficients `a ᵥ* C ≥ 0`. Then `V` has local uniformization.

The lattice lemma holds for each monomial valuation (Volume 5, Lemma 2.1.4). This library proves it in rank 1 (`Singularity.latticeLemma_real`). -/
theorem hasLocalUniformization_of_isMonomialValuation_of_lattice [DecidableEq ι] {x : ι → K}
    (hV : IsMonomialValuation k V x)
    (hlat : ∀ E : Finset (ι → ℤ), (∀ a ∈ E, V.valuation (laurentMonomial x a) ≤ 1) →
      ∃ B C : Matrix ι ι ℤ, B * C = 1 ∧ C * B = 1 ∧
        (∀ l, V.valuation (laurentMonomial x (B l)) < 1) ∧ ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l) :
    HasLocalUniformization k V := by
  classical
  intro s hs
  choose E hE hES using fun z : s => exists_exponents hV (hs z z.2)
  obtain ⟨B, C, hBC, hCB, hpos, hEC⟩ := hlat (Finset.univ.biUnion E) (by
    intro a ha
    obtain ⟨z, -, hz⟩ := Finset.mem_biUnion.mp ha
    exact hE z a hz)
  refine hasRegularCenter_of_basis hV hBC hCB hpos s hs fun z hz => ?_
  refine hES ⟨z, hz⟩ _ fun a ha => ?_
  -- A monomial `x^a` with `a ᵥ* C ≥ 0` is a monomial in the `u_l`.
  have hnn := hEC a (Finset.mem_biUnion.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, ha⟩)
  have h2 : a = (a ᵥ* C) ᵥ* B := by rw [vecMul_vecMul, hCB, vecMul_one]
  rw [h2, laurentMonomial_vecMul hV.ne_zero, laurentMonomial]
  refine prod_mem fun l _ => ?_
  rw [← Int.toNat_of_nonneg (hnn l), zpow_natCast]
  exact pow_mem (Algebra.subset_adjoin (Set.mem_range_self l)) _

/-- **Local uniformization of monomial valuations of rank 1** (Volume 5, Theorem 2.1.5 of the handbook, in rank 1). Let `k` be a field of any characteristic, and let `V` be a monomial valuation of `K = k(x_1, ..., x_n)` (`IsMonomialValuation`): the values of the `x_i` are linearly independent over `ℤ`. Assume that the value group of `V` has rank at most 1: there is an injective homomorphism of ordered groups `φ` from the value group to `ℝ≥0`. Then `V` has local uniformization.

The valuation `V` is an Abhyankar valuation with residue field `k`. So this is the case of `localUniformization_abhyankar` for the monomial valuations of rank 1. -/
theorem hasLocalUniformization_of_isMonomialValuation_of_rankOne {x : ι → K}
    (hV : IsMonomialValuation k V x) (φ : V.ValueGroup →*₀ ℝ≥0) (hφ : StrictMono φ) :
    HasLocalUniformization k V := by
  classical
  set v := V.valuation
  -- The real weights `γ_i = -log φ(v(x_i))`.
  have hpos : ∀ a, (0 : ℝ) < φ (v (laurentMonomial x a)) := by
    intro a
    have h0 : 0 < v (laurentMonomial x a) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (laurentMonomial_ne_zero hV.ne_zero a))
    have h1 := hφ h0
    rw [map_zero] at h1
    exact_mod_cast h1
  set γ : ι → ℝ := fun i => -Real.log (φ (v (x i))) with hγ
  have hx1 : ∀ i, x i = laurentMonomial x (Pi.single i 1) := fun i =>
    (laurentMonomial_single x i).symm
  have hlog : ∀ a, Real.log (φ (v (laurentMonomial x a))) = -∑ i, (a i : ℝ) * γ i := by
    intro a
    have hxi : ∀ i, (0 : ℝ) < φ (v (x i)) := fun i => by rw [hx1 i]; exact hpos _
    rw [laurentMonomial, map_prod, map_prod, NNReal.coe_prod, Real.log_prod]
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zpow₀, map_zpow₀, NNReal.coe_zpow, Real.log_zpow, hγ]
      ring
    · intro i _
      rw [map_zpow₀, map_zpow₀, NNReal.coe_zpow]
      exact (zpow_pos (hxi i) _).ne'
  have hle : ∀ a, v (laurentMonomial x a) ≤ 1 ↔ 0 ≤ ∑ i, (a i : ℝ) * γ i := by
    intro a
    rw [← hφ.le_iff_le, map_one, ← NNReal.coe_le_one, ← Real.log_nonpos_iff (hpos a).le, hlog]
    constructor <;> intro h <;> linarith
  have hlt : ∀ a, v (laurentMonomial x a) < 1 ↔ 0 < ∑ i, (a i : ℝ) * γ i := by
    intro a
    rw [← hφ.lt_iff_lt, map_one, ← NNReal.coe_lt_one, ← Real.log_neg_iff (hpos a), hlog]
    constructor <;> intro h <;> linarith
  have hind : ∀ a : ι → ℤ, ∑ i, (a i : ℝ) * γ i = 0 → a = 0 := by
    intro a ha
    refine hV.independent a (le_antisymm ((hle a).mpr ha.ge) ?_)
    by_contra h
    push Not at h
    rw [hlt a] at h
    rw [ha] at h
    exact lt_irrefl _ h
  refine hasLocalUniformization_of_isMonomialValuation_of_lattice hV fun E hE => ?_
  obtain ⟨B, C, hBC, hCB, hBpos, hEC⟩ :=
    latticeLemma_real γ hind E fun a ha => (hle a).mp (hE a ha)
  exact ⟨B, C, hBC, hCB, fun l => (hlt _).mpr (hBpos l), hEC⟩

end Singularity
