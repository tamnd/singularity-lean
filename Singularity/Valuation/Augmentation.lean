/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Valuation.KeyPolynomials

/-!
# The augmented valuation

Let `μ` be a valuation on `K[X]` and let `φ` be a key polynomial for `μ`. This file proves that the augmentation `[μ; φ, γ]` of Definition 3.3.4 is a valuation on `K[X]`. This is part 1 of Theorem 3.3.5 of Volume 3 of the handbook (MacLane-Vaquié). The file also proves part 2, and the first claim of part 3: `φ` is a key polynomial for `[μ; φ, γ]`.

The conventions are those of `Singularity/Valuation/KeyPolynomials.lean`. The valuations are multiplicative. Thus the handbook condition `γ > μ(φ)` is `γ < μ φ` here, the inequality `μ ≤ μ'` of the handbook is `μ' f ≤ μ f` here, and `γ = ∞` is `γ = 0`. The file assumes only `γ ≤ μ φ`. For `γ = μ φ` the augmentation is `μ` (`augmentedValuation_eq_self`).

## The proof

* The minimality of `φ` gives `μ (r + φ * q) = max (μ r) (μ (φ * q))` if `deg r < deg φ`. By induction, `μ f` is the maximum of `μ aⱼ * μ φ ^ j` for the `φ`-expansion `f = ∑ aⱼ φ ^ j`. The converse also holds (`isMuMinimal_iff`).
* Let `a` and `b` have degree less than the degree of `φ`. The irreducibility and the minimality of `φ` give `μ (a * b %ₘ φ) = μ (a * b)`. Otherwise `φ` `μ`-divides `a * b`, so it `μ`-divides `a` or `b`. This is false by minimality.
* For the product `f * g = ∑ φ ^ (i + j) * aᵢ * bⱼ`, the coefficient of index `k` of the `φ`-expansion is a sum of terms, one for each pair `(i, j)`. Each term is at most `μ aᵢ * γ ^ i * (μ bⱼ * γ ^ j)`. Let `i₀` and `j₀` be the smallest indices where the values of `f` and `g` are attained. For `k = i₀ + j₀`, the term of `(i₀, j₀)` is `aᵢ₀ * bⱼ₀ %ₘ φ`, and each other term is strictly smaller. This is the argument of Lemma 3.3.2.
* Let `ν = [μ; φ, γ]`. Then `φ` `ν`-divides `f` if and only if `μ (f %ₘ φ) < ν f`. In additive notation, the minimum of the terms of the `φ`-expansion of `f` is not attained at `j = 0`. If this minimum is attained at `j = 0` for `f` and for `g`, then the remainder of `f * g` has the value `ν f * ν g` by the second step. Thus `φ` is `ν`-irreducible. The criterion also gives the `ν`-minimality.

## Main results

* `Singularity.IsMuMinimal.map_eq_augmentedValuationFun` and `Singularity.isMuMinimal_iff`: the polynomial `φ` is `μ`-minimal if and only if `μ` is equal to the augmentation `[μ; φ, μ φ]`. In additive notation, `μ(∑ aⱼ φ ^ j) = min_j (μ(aⱼ) + jμ(φ))`.
* `Singularity.KeyPolynomial.map_mul_modByMonic`: the product of two polynomials of degree less than the degree of `φ`.
* `Singularity.KeyPolynomial.augmentedValuationFun_mul`: the augmented valuation is multiplicative.
* `Singularity.augmentedValuation`: the augmented valuation `[μ; φ, γ]` as a `Valuation` (Theorem 3.3.5 (1)).
* `Singularity.augmentedValuation_le`: `μ ≤ [μ; φ, γ]` in the notation of the handbook (Theorem 3.3.5 (2)).
* `Singularity.augmentedValuation_eq_zero_iff` and `Singularity.augmentedValuation_zero_eq_zero_iff`: the support is `0` if `γ ≠ 0` and `(φ)` if `γ = 0`, when `μ` has support `0` (Theorem 3.3.5 (1)).
* `Singularity.KeyPolynomial.keyPolynomial_augmentedValuation` and `Singularity.KeyPolynomial.keyPolynomial_of_forall_eq`: the polynomial `φ` is a key polynomial for `[μ; φ, γ]` (Theorem 3.3.5 (3), first claim). The theorem holds for each `γ ≤ μ φ`.
* `Singularity.muDvd_iff_of_forall_eq`: the criterion for `[μ; φ, γ]`-divisibility by `φ`.
* `Singularity.augmentedValuationFun_sum_mul_pow` and `Singularity.KeyPolynomial.muEquiv_augmentedValuation_mul_modByMonic`: two elementwise parts of the second claim of part 3. The first gives the value of `∑ cⱼ φ ^ j` for `cⱼ` of degree less than the degree of `φ`. The second says that for `γ < μ φ` a product `a * b` of such polynomials is `[μ; φ, γ]`-equivalent to its remainder modulo `φ`.

The file does not prove the rest of part 3 of Theorem 3.3.5, that is the description of the graded algebra of `[μ; φ, γ]` as a polynomial ring. It does not prove part 4.

## References

* [Mac36] S. MacLane, A construction for absolute values in polynomial rings.
* [Vaq07] M. Vaquié, Extension d'une valuation.
-/

open Polynomial

namespace Singularity

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section Sum

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

/-- If each term `v (F i) * c` is at most `C`, then `v (∑ F i) * c` is at most `C`. -/
theorem valuation_sum_mul_le {ι : Type*} {s : Finset ι} {F : ι → R} {c C : Γ₀}
    (h : ∀ i ∈ s, v (F i) * c ≤ C) : v (∑ i ∈ s, F i) * c ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc v (F a + ∑ i ∈ s, F i) * c ≤ max (v (F a)) (v (∑ i ∈ s, F i)) * c := by
          gcongr
          exact v.map_add _ _
      _ = max (v (F a) * c) (v (∑ i ∈ s, F i) * c) := max_mul _ _ _
      _ ≤ C := max_le (h a (Finset.mem_insert_self a s))
          (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- If `0 < C` and each term `v (F i) * c` is less than `C`, then `v (∑ F i) * c` is less than `C`. -/
theorem valuation_sum_mul_lt {ι : Type*} {s : Finset ι} {F : ι → R} {c C : Γ₀}
    (hC : 0 < C) (h : ∀ i ∈ s, v (F i) * c < C) : v (∑ i ∈ s, F i) * c < C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc v (F a + ∑ i ∈ s, F i) * c ≤ max (v (F a)) (v (∑ i ∈ s, F i)) * c := by
          gcongr
          exact v.map_add _ _
      _ = max (v (F a) * c) (v (∑ i ∈ s, F i) * c) := max_mul _ _ _
      _ < C := max_lt (h a (Finset.mem_insert_self a s))
          (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Sum

section Expansion

variable {φ : K[X]}

/-- The coefficients of the expansion of a finite sum are the sums of the coefficients. -/
theorem expansionCoeff_sum {ι : Type*} (s : Finset ι) (F : ι → K[X]) (j : ℕ) :
    expansionCoeff φ (∑ i ∈ s, F i) j = ∑ i ∈ s, expansionCoeff φ (F i) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expansionCoeff_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, expansionCoeff_add, ih]

/-- The coefficient `a₀` of `φ * h` is `0`. -/
theorem expansionCoeff_mul_left_zero (hφ : φ.Monic) (h : K[X]) :
    expansionCoeff φ (φ * h) 0 = 0 := by
  rw [expansionCoeff_zero_eq_modByMonic]
  exact (modByMonic_eq_zero_iff_dvd hφ).2 (dvd_mul_right φ h)

/-- The coefficients of `φ * h` after `a₀` are the coefficients of `h`. -/
theorem expansionCoeff_mul_left_succ (hφ : φ.Monic) (h : K[X]) (j : ℕ) :
    expansionCoeff φ (φ * h) (j + 1) = expansionCoeff φ h j := by
  rw [expansionCoeff_succ, mul_divByMonic_cancel_left h hφ]

/-- The coefficient of index `j + n` of `φ ^ n * h` is the coefficient of index `j` of `h`. -/
theorem expansionCoeff_pow_mul_add (hφ : φ.Monic) (h : K[X]) (n j : ℕ) :
    expansionCoeff φ (φ ^ n * h) (j + n) = expansionCoeff φ h j := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, ← add_assoc, expansionCoeff_mul_left_succ hφ, ih]

/-- The coefficient of index `j < n` of `φ ^ n * h` is `0`. -/
theorem expansionCoeff_pow_mul_of_lt (hφ : φ.Monic) (h : K[X]) {n j : ℕ} (hj : j < n) :
    expansionCoeff φ (φ ^ n * h) j = 0 := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    cases j with
    | zero => exact expansionCoeff_mul_left_zero hφ _
    | succ j => rw [expansionCoeff_mul_left_succ hφ]; exact ih (by omega)

end Expansion

section Minimal

variable {μ : Valuation K[X] Γ₀} {φ : K[X]}

/-- A `μ`-minimal polynomial does not `μ`-divide a polynomial of smaller degree. -/
theorem IsMuMinimal.not_muDvd_of_degree_lt (hmin : IsMuMinimal μ φ) {a : K[X]}
    (ha : a.degree < φ.degree) : ¬ MuDvd μ φ a := by
  intro hdvd
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact not_muDvd_zero φ hdvd
  have h1 := hmin a ha0 hdvd
  have h2 := natDegree_lt_natDegree ha0 ha
  omega

/-- Let `φ` be `μ`-minimal and let `r` have degree less than the degree of `φ`. Then `μ (r + φ * q)` is the maximum of `μ r` and `μ (φ * q)`. In additive notation, `μ(r + φq) = min(μ(r), μ(φq))`. -/
theorem IsMuMinimal.map_add_mul_eq_max (hmin : IsMuMinimal μ φ) {r : K[X]}
    (hr : r.degree < φ.degree) (q : K[X]) : μ (r + φ * q) = max (μ r) (μ (φ * q)) := by
  refine le_antisymm (Valuation.map_add _ _ _) ?_
  by_contra hlt
  rw [not_le] at hlt
  by_cases hne : μ r = μ (φ * q)
  · rw [← hne, max_self] at hlt
    refine hmin.not_muDvd_of_degree_lt hr ⟨-q, ?_⟩
    unfold MuEquiv
    rwa [mul_neg, sub_neg_eq_add]
  · rw [Valuation.map_add_of_distinct_val _ hne] at hlt
    exact lt_irrefl _ hlt

/-- Let `φ` be monic and `μ`-minimal. Then `μ f` is the maximum of `μ (f %ₘ φ)` and `μ (φ * (f /ₘ φ))`. -/
theorem IsMuMinimal.map_eq_max (hφ : φ.Monic) (hmin : IsMuMinimal μ φ) (f : K[X]) :
    μ f = max (μ (f %ₘ φ)) (μ (φ * (f /ₘ φ))) := by
  conv_lhs => rw [← modByMonic_add_div f φ]
  exact hmin.map_add_mul_eq_max (degree_modByMonic_lt f hφ) _

/-- Let `φ` be monic and `μ`-minimal. Then `μ (f %ₘ φ) ≤ μ f`. -/
theorem IsMuMinimal.map_modByMonic_le (hφ : φ.Monic) (hmin : IsMuMinimal μ φ) (f : K[X]) :
    μ (f %ₘ φ) ≤ μ f :=
  (hmin.map_eq_max hφ f).symm ▸ le_max_left _ _

/-- Let `φ` be monic and `μ`-minimal. Then each term `μ aⱼ * μ φ ^ j` of the `φ`-expansion of `f` is at most `μ f`. -/
theorem IsMuMinimal.map_expansionCoeff_mul_pow_le (hφ : φ.Monic) (hmin : IsMuMinimal μ φ)
    (f : K[X]) (j : ℕ) : μ (expansionCoeff φ f j) * μ φ ^ j ≤ μ f := by
  induction j generalizing f with
  | zero => simpa [expansionCoeff_zero_eq_modByMonic] using hmin.map_modByMonic_le hφ f
  | succ j ih =>
    rw [expansionCoeff_succ, pow_succ, ← mul_assoc]
    calc μ (expansionCoeff φ (f /ₘ φ) j) * μ φ ^ j * μ φ ≤ μ (f /ₘ φ) * μ φ := by
          gcongr
          exact ih _
      _ = μ (φ * (f /ₘ φ)) := by rw [Valuation.map_mul, mul_comm]
      _ ≤ μ f := (hmin.map_eq_max hφ f).symm ▸ le_max_right _ _

/-- Let `φ` be monic of positive degree and `μ`-minimal. Then `μ` is equal to the augmentation `[μ; φ, μ φ]`. In additive notation, `μ(∑ aⱼ φ ^ j) = min_j (μ(aⱼ) + jμ(φ))` for the `φ`-expansion. -/
theorem IsMuMinimal.map_eq_augmentedValuationFun (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hmin : IsMuMinimal μ φ) (f : K[X]) : μ f = augmentedValuationFun μ φ (μ φ) f :=
  le_antisymm (map_le_augmentedValuationFun hφ hd f)
    ((augmentedValuationFun_le_iff hφ hd).2 fun j => hmin.map_expansionCoeff_mul_pow_le hφ f j)

/-- A monic polynomial `φ` of positive degree is `μ`-minimal if and only if `μ` is equal to the augmentation `[μ; φ, μ φ]`. In additive notation, the condition is `μ(∑ aⱼ φ ^ j) = min_j (μ(aⱼ) + jμ(φ))` for each `φ`-expansion. -/
theorem isMuMinimal_iff (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    IsMuMinimal μ φ ↔ ∀ f, μ f = augmentedValuationFun μ φ (μ φ) f := by
  refine ⟨fun h f => h.map_eq_augmentedValuationFun hφ hd f, fun h f _ hdvd => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨g, hg⟩ := hdvd
  have hfd : f.degree < φ.degree := degree_lt_degree hlt
  have h0 : expansionCoeff φ (f - φ * g) 0 = f := by
    rw [expansionCoeff_zero_eq_modByMonic, sub_modByMonic, (modByMonic_eq_self_iff hφ).2 hfd,
      (modByMonic_eq_zero_iff_dvd hφ).2 (dvd_mul_right _ _), sub_zero]
  have hle := le_augmentedValuationFun (μ := μ) (γ := μ φ) hφ hd (f - φ * g) 0
  rw [h0, pow_zero, mul_one, ← h] at hle
  exact lt_irrefl _ (lt_of_le_of_lt hle hg)

end Minimal

section Augmented

variable {μ : Valuation K[X] Γ₀} {φ : K[X]} {γ : Γ₀}

/-- The augmented value is monotone in `γ`. -/
theorem augmentedValuationFun_mono (hφ : φ.Monic) (hd : 0 < φ.natDegree) {γ γ' : Γ₀}
    (h : γ ≤ γ') (f : K[X]) :
    augmentedValuationFun μ φ γ f ≤ augmentedValuationFun μ φ γ' f :=
  (augmentedValuationFun_le_iff hφ hd).2 fun j =>
    (by gcongr; exact zero_le :
      μ (expansionCoeff φ f j) * γ ^ j ≤ μ (expansionCoeff φ f j) * γ' ^ j).trans
      (le_augmentedValuationFun hφ hd f j)

/-- Let `φ` be monic of positive degree and `μ`-minimal, and let `γ ≤ μ φ`. Then the augmented value of `f` is at most `μ f`. In additive notation, `μ(f) ≤ μ'(f)`. -/
theorem IsMuMinimal.augmentedValuationFun_le (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hmin : IsMuMinimal μ φ) (hγ : γ ≤ μ φ) (f : K[X]) :
    augmentedValuationFun μ φ γ f ≤ μ f :=
  (augmentedValuationFun_mono hφ hd hγ f).trans (hmin.map_eq_augmentedValuationFun hφ hd f).ge

/-- The augmented value is the value of one term `μ aⱼ * γ ^ j`. -/
theorem exists_eq_augmentedValuationFun (f : K[X]) :
    ∃ j, μ (expansionCoeff φ f j) * γ ^ j = augmentedValuationFun μ φ γ f := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup (Finset.range (f.natDegree + 1))
    ⟨0, by simp⟩ fun j => μ (expansionCoeff φ f j) * γ ^ j
  exact ⟨j, hj.symm⟩

/-- Let `φ` be a key polynomial and let `a` and `b` have degree less than the degree of `φ`. Then `μ (a * b %ₘ φ) = μ (a * b)`. In additive notation, `μ(ab) = μ(r)` for the remainder `r` of `ab` modulo `φ`. -/
theorem KeyPolynomial.map_mul_modByMonic {μ : Valuation K[X] Γ₀} (hφ : KeyPolynomial μ φ)
    {a b : K[X]} (ha : a.degree < φ.degree) (hb : b.degree < φ.degree) :
    μ (a * b %ₘ φ) = μ (a * b) := by
  refine le_antisymm (hφ.isMuMinimal.map_modByMonic_le hφ.monic _) ?_
  by_contra hlt
  rw [not_le] at hlt
  have hdvd : MuDvd μ φ (a * b) := ⟨a * b /ₘ φ, by
    unfold MuEquiv
    rwa [sub_eq_of_eq_add (modByMonic_add_div (a * b) φ).symm]⟩
  rcases hφ.isMuIrreducible.2 a b hdvd with h | h
  · exact hφ.isMuMinimal.not_muDvd_of_degree_lt ha h
  · exact hφ.isMuMinimal.not_muDvd_of_degree_lt hb h

/-- Let `φ` be monic and `μ`-minimal, and let `γ ≤ μ φ`. Then the term of index `k` of the `φ`-expansion of `φ ^ n * p` satisfies `μ cₖ * γ ^ k ≤ μ p * γ ^ n`. -/
theorem IsMuMinimal.map_expansionCoeff_pow_mul_le (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hmin : IsMuMinimal μ φ) (hγ : γ ≤ μ φ) (p : K[X]) (n k : ℕ) :
    μ (expansionCoeff φ (φ ^ n * p) k) * γ ^ k ≤ μ p * γ ^ n := by
  rcases lt_or_ge k n with hk | hk
  · rw [expansionCoeff_pow_mul_of_lt hφ p hk, Valuation.map_zero, zero_mul]
    exact zero_le
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [expansionCoeff_pow_mul_add hφ, pow_add, ← mul_assoc]
    gcongr
    exact (le_augmentedValuationFun hφ hd p m).trans (hmin.augmentedValuationFun_le hφ hd hγ p)

/-- Theorem 3.3.5 (1) of the handbook (MacLane-Vaquié): for a key polynomial `φ` and `γ ≤ μ φ`, the augmented valuation `[μ; φ, γ]` is multiplicative. The handbook assumes `γ < μ φ` in multiplicative notation. -/
theorem KeyPolynomial.augmentedValuationFun_mul (hφ : KeyPolynomial μ φ) (hγ : γ ≤ μ φ)
    (f g : K[X]) : augmentedValuationFun μ φ γ (f * g) =
      augmentedValuationFun μ φ γ f * augmentedValuationFun μ φ γ g := by
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  have hmin := hφ.isMuMinimal
  set ν := augmentedValuationFun μ φ γ
  set N := f.natDegree + 1
  set M := g.natDegree + 1
  set a := expansionCoeff φ f
  set b := expansionCoeff φ g
  -- the product as a double sum
  have hfg : f * g =
      ∑ x ∈ Finset.range N ×ˢ Finset.range M, φ ^ (x.1 + x.2) * (a x.1 * b x.2) := by
    conv_lhs => rw [eq_sum_expansionCoeff hm hd f, eq_sum_expansionCoeff hm hd g]
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  have hcoeff : ∀ k, expansionCoeff φ (f * g) k = ∑ x ∈ Finset.range N ×ˢ Finset.range M,
      expansionCoeff φ (φ ^ (x.1 + x.2) * (a x.1 * b x.2)) k := fun k => by
    rw [hfg, expansionCoeff_sum]
  -- the bound for each term
  have hterm : ∀ i j k, μ (expansionCoeff φ (φ ^ (i + j) * (a i * b j)) k) * γ ^ k ≤
      (μ (a i) * γ ^ i) * (μ (b j) * γ ^ j) := fun i j k => by
    refine (hmin.map_expansionCoeff_pow_mul_le hm hd hγ _ _ k).trans_eq ?_
    rw [Valuation.map_mul, pow_add]
    exact mul_mul_mul_comm _ _ _ _
  refine le_antisymm ((augmentedValuationFun_le_iff hm hd).2 fun k => ?_) ?_
  · -- the upper bound
    rw [hcoeff]
    refine valuation_sum_mul_le μ fun x _ => (hterm _ _ _).trans ?_
    exact mul_le_mul' (le_augmentedValuationFun hm hd f _) (le_augmentedValuationFun hm hd g _)
  -- the lower bound
  by_cases hf : ν f = 0
  · rw [hf, zero_mul]
    exact zero_le
  by_cases hg : ν g = 0
  · rw [hg, mul_zero]
    exact zero_le
  classical
  have ef := exists_eq_augmentedValuationFun (μ := μ) (φ := φ) (γ := γ) f
  have eg := exists_eq_augmentedValuationFun (μ := μ) (φ := φ) (γ := γ) g
  set i₀ := Nat.find ef
  set j₀ := Nat.find eg
  have hfi₀ : μ (a i₀) * γ ^ i₀ = ν f := Nat.find_spec ef
  have hgj₀ : μ (b j₀) * γ ^ j₀ = ν g := Nat.find_spec eg
  have hlt_f : ∀ i < i₀, μ (a i) * γ ^ i < ν f := fun i hi =>
    lt_of_le_of_ne (le_augmentedValuationFun hm hd f i) (Nat.find_min ef hi)
  have hlt_g : ∀ j < j₀, μ (b j) * γ ^ j < ν g := fun j hj =>
    lt_of_le_of_ne (le_augmentedValuationFun hm hd g j) (Nat.find_min eg hj)
  have hi₀ : i₀ < N := by
    by_contra h
    apply hf
    have h0 : a i₀ = 0 := expansionCoeff_eq_zero hm hd (by omega)
    rw [← hfi₀, h0, Valuation.map_zero, zero_mul]
  have hj₀ : j₀ < M := by
    by_contra h
    apply hg
    have h0 : b j₀ = 0 := expansionCoeff_eq_zero hm hd (by omega)
    rw [← hgj₀, h0, Valuation.map_zero, zero_mul]
  set k := i₀ + j₀
  have hmem : (i₀, j₀) ∈ Finset.range N ×ˢ Finset.range M :=
    Finset.mem_product.2 ⟨Finset.mem_range.2 hi₀, Finset.mem_range.2 hj₀⟩
  have hpos : 0 < ν f * ν g := zero_lt_iff.2 (mul_ne_zero hf hg)
  -- the main term
  set t := expansionCoeff φ (φ ^ (i₀ + j₀) * (a i₀ * b j₀)) k with ht
  have hmain : μ t * γ ^ k = ν f * ν g := by
    have e : t = a i₀ * b j₀ %ₘ φ := by
      rw [ht, show k = 0 + (i₀ + j₀) from (zero_add _).symm, expansionCoeff_pow_mul_add hm,
        expansionCoeff_zero_eq_modByMonic]
    rw [e, hφ.map_mul_modByMonic (degree_expansionCoeff_lt hm f i₀)
      (degree_expansionCoeff_lt hm g j₀), Valuation.map_mul, ← hfi₀, ← hgj₀, pow_add]
    exact mul_mul_mul_comm _ _ _ _
  -- the other terms
  have hrest : ∀ x ∈ (Finset.range N ×ˢ Finset.range M).erase (i₀, j₀),
      μ (expansionCoeff φ (φ ^ (x.1 + x.2) * (a x.1 * b x.2)) k) * γ ^ k < ν f * ν g := by
    intro x hx
    have hne := Finset.ne_of_mem_erase hx
    rcases lt_or_ge k (x.1 + x.2) with hk | hk
    · rw [expansionCoeff_pow_mul_of_lt hm _ hk, Valuation.map_zero, zero_mul]
      exact hpos
    refine lt_of_le_of_lt (hterm _ _ _) ?_
    rcases lt_or_ge x.1 i₀ with h1 | h1
    · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hlt_f _ h1)
        (le_augmentedValuationFun hm hd g _) zero_le (zero_lt_iff.2 hg)
    · have h2 : x.2 < j₀ := by
        by_contra h2
        rw [not_lt] at h2
        exact hne (Prod.ext (by omega) (by omega))
      exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_augmentedValuationFun hm hd f _)
        (hlt_g _ h2) zero_le (zero_lt_iff.2 hf)
  have hsum := valuation_sum_mul_lt μ hpos hrest
  rw [← hmain] at hsum
  have hval : μ (expansionCoeff φ (f * g) k) = μ t := by
    rw [hcoeff, ← Finset.add_sum_erase _ _ hmem]
    exact Valuation.map_add_eq_of_lt_left _ (lt_of_mul_lt_mul_right' hsum)
  calc ν f * ν g = μ (expansionCoeff φ (f * g) k) * γ ^ k := by rw [hval, hmain]
    _ ≤ ν (f * g) := le_augmentedValuationFun hm hd _ _

variable (μ φ γ)

/-- The augmented valuation `[μ; φ, γ]` on `K[X]` for a key polynomial `φ` of `μ` and `γ ≤ μ φ` (Definition 3.3.4 and Theorem 3.3.5 (1) of Volume 3 of the handbook). The handbook assumes `γ < μ φ` in multiplicative notation. For `γ = μ φ` the augmentation is `μ` (`augmentedValuation_eq_self`). -/
noncomputable def augmentedValuation (hφ : KeyPolynomial μ φ) (hγ : γ ≤ μ φ) :
    Valuation K[X] Γ₀ where
  toFun := augmentedValuationFun μ φ γ
  map_zero' := augmentedValuationFun_zero
  map_one' := augmentedValuationFun_one hφ.monic hφ.natDegree_pos
  map_mul' := hφ.augmentedValuationFun_mul hγ
  map_add_le_max' := augmentedValuationFun_add_le_max hφ.monic hφ.natDegree_pos

variable {μ φ γ}

/-- The value of the augmented valuation is `augmentedValuationFun`. -/
@[simp]
theorem augmentedValuation_apply (hφ : KeyPolynomial μ φ) (hγ : γ ≤ μ φ) (f : K[X]) :
    augmentedValuation μ φ γ hφ hγ f = augmentedValuationFun μ φ γ f :=
  rfl

/-- Theorem 3.3.5 (2): `μ ≤ [μ; φ, γ]` in the additive notation of the handbook. In multiplicative notation, the augmented value of `f` is at most `μ f`. -/
theorem augmentedValuation_le (hφ : KeyPolynomial μ φ) (hγ : γ ≤ μ φ) (f : K[X]) :
    augmentedValuation μ φ γ hφ hγ f ≤ μ f :=
  hφ.isMuMinimal.augmentedValuationFun_le hφ.monic hφ.natDegree_pos hγ f

/-- Theorem 3.3.5 (2): the augmented valuation agrees with `μ` on the polynomials of degree less than the degree of `φ`. -/
theorem augmentedValuation_of_degree_lt (hφ : KeyPolynomial μ φ) (hγ : γ ≤ μ φ) {f : K[X]}
    (hf : f.degree < φ.degree) : augmentedValuation μ φ γ hφ hγ f = μ f :=
  augmentedValuationFun_of_degree_lt hφ.monic hφ.natDegree_pos hf

/-- Theorem 3.3.5 (1): the augmented valuation agrees with `μ` on the constants. Thus it extends `v` if `μ` extends `v`. -/
theorem augmentedValuation_C (hφ : KeyPolynomial μ φ) (hγ : γ ≤ μ φ) (c : K) :
    augmentedValuation μ φ γ hφ hγ (C c) = μ (C c) :=
  augmentedValuationFun_C hφ.monic hφ.natDegree_pos c

/-- Theorem 3.3.5 (2): the augmented valuation sends `φ` to `γ`. -/
theorem augmentedValuation_self (hφ : KeyPolynomial μ φ) (hγ : γ ≤ μ φ) :
    augmentedValuation μ φ γ hφ hγ φ = γ :=
  augmentedValuationFun_self hφ.monic hφ.natDegree_pos

/-- Theorem 3.3.5 (2): if `γ < μ φ`, then the augmented valuation differs from `μ` at `φ`. In additive notation, `μ'(φ) = γ > μ(φ)`. -/
theorem augmentedValuation_self_lt (hφ : KeyPolynomial μ φ) (hγ : γ < μ φ) :
    augmentedValuation μ φ γ hφ hγ.le φ < μ φ := by
  rw [augmentedValuation_self]
  exact hγ

/-- The augmentation `[μ; φ, μ φ]` is `μ`. -/
theorem augmentedValuation_eq_self (hφ : KeyPolynomial μ φ) :
    augmentedValuation μ φ (μ φ) hφ le_rfl = μ :=
  Valuation.ext fun f =>
    (hφ.isMuMinimal.map_eq_augmentedValuationFun hφ.monic hφ.natDegree_pos f).symm

/-- Theorem 3.3.5 (1): if `μ` has support `0` and `γ ≠ 0`, then the augmented valuation has support `0`. -/
theorem augmentedValuation_eq_zero_iff (hφ : KeyPolynomial μ φ) (hγ : γ ≤ μ φ)
    (hμ : ∀ f, μ f = 0 ↔ f = 0) (hγ0 : γ ≠ 0) {f : K[X]} :
    augmentedValuation μ φ γ hφ hγ f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ Valuation.map_zero _⟩
  rw [augmentedValuation_apply] at h
  have ha : ∀ j, expansionCoeff φ f j = 0 := fun j => by
    have hle := le_augmentedValuationFun (μ := μ) (γ := γ) hφ.monic hφ.natDegree_pos f j
    rw [h, le_zero_iff, mul_eq_zero] at hle
    rcases hle with hle | hle
    · exact (hμ _).1 hle
    · exact absurd hle (pow_ne_zero j hγ0)
  rw [eq_sum_expansionCoeff hφ.monic hφ.natDegree_pos f]
  simp [ha]

/-- The augmentation `[μ; φ, 0]` sends `f` to `μ (f %ₘ φ)`. -/
theorem augmentedValuationFun_zero_right (hφ : φ.Monic) (hd : 0 < φ.natDegree) (f : K[X]) :
    augmentedValuationFun μ φ 0 f = μ (f %ₘ φ) := by
  refine le_antisymm ((augmentedValuationFun_le_iff hφ hd).2 fun j => ?_) ?_
  · cases j with
    | zero => rw [expansionCoeff_zero_eq_modByMonic, pow_zero, mul_one]
    | succ j =>
      rw [zero_pow (Nat.succ_ne_zero j), mul_zero]
      exact zero_le
  · simpa [expansionCoeff_zero_eq_modByMonic] using
      le_augmentedValuationFun (μ := μ) (γ := 0) hφ hd f 0

/-- Theorem 3.3.5 (1): if `μ` has support `0`, then the augmented valuation `[μ; φ, 0]` has support `(φ)`. The value `0` is the value `∞` of the handbook. -/
theorem augmentedValuation_zero_eq_zero_iff (hφ : KeyPolynomial μ φ)
    (hμ : ∀ f, μ f = 0 ↔ f = 0) {f : K[X]} :
    augmentedValuation μ φ 0 hφ zero_le f = 0 ↔ φ ∣ f := by
  rw [augmentedValuation_apply, augmentedValuationFun_zero_right hφ.monic hφ.natDegree_pos, hμ,
    modByMonic_eq_zero_iff_dvd hφ.monic]

end Augmented

section KeyAugmented

variable {μ : Valuation K[X] Γ₀} {φ : K[X]} {γ : Γ₀}

/-- The value of the remainder of `f` modulo `φ` is at most the augmented value of `f`. In additive notation, `μ(a₀) ≥ μ'(f)` for the coefficient `a₀` of the `φ`-expansion of `f`. -/
theorem map_modByMonic_le_augmentedValuationFun (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (f : K[X]) : μ (f %ₘ φ) ≤ augmentedValuationFun μ φ γ f := by
  simpa [expansionCoeff_zero_eq_modByMonic] using
    le_augmentedValuationFun (μ := μ) (γ := γ) hφ hd f 0

/-- Let `ν` be a valuation with the values of the augmentation `[μ; φ, γ]`. Then `φ` `ν`-divides `f` if and only if `μ (f %ₘ φ) < ν f`. In additive notation, `φ` `μ'`-divides `f` if and only if `μ'(a₀) > μ'(f)`, that is, the minimum of the terms of the `φ`-expansion of `f` is not attained at `j = 0`. -/
theorem muDvd_iff_of_forall_eq (hφ : φ.Monic) (hd : 0 < φ.natDegree) {ν : Valuation K[X] Γ₀}
    (hν : ∀ f, ν f = augmentedValuationFun μ φ γ f) {f : K[X]} :
    MuDvd ν φ f ↔ μ (f %ₘ φ) < ν f := by
  constructor
  · rintro ⟨h, hh⟩
    have h0 : (f - φ * h) %ₘ φ = f %ₘ φ := by
      rw [sub_modByMonic, (modByMonic_eq_zero_iff_dvd hφ).2 (dvd_mul_right _ _), sub_zero]
    have hle := map_modByMonic_le_augmentedValuationFun (μ := μ) (γ := γ) hφ hd (f - φ * h)
    rw [h0, ← hν] at hle
    exact lt_of_le_of_lt hle hh
  · intro hf
    refine ⟨f /ₘ φ, ?_⟩
    unfold MuEquiv
    rwa [sub_eq_of_eq_add (modByMonic_add_div f φ).symm, hν,
      augmentedValuationFun_of_degree_lt hφ hd (degree_modByMonic_lt f hφ)]

/-- Theorem 3.3.5 (3) in part: let `φ` be a key polynomial for `μ` and let `ν` be a valuation with the values of the augmentation `[μ; φ, γ]`. Then `φ` is a key polynomial for `ν`. The proof uses the criterion `muDvd_iff_of_forall_eq`. If `φ` does not `ν`-divide `f` or `g`, then `μ (f %ₘ φ) = ν f` and `μ (g %ₘ φ) = ν g`. The remainder of `f * g` is the remainder of `(f %ₘ φ) * (g %ₘ φ)`, and by `KeyPolynomial.map_mul_modByMonic` it has the value `ν f * ν g = ν (f * g)`. Thus `φ` does not `ν`-divide `f * g`. -/
theorem KeyPolynomial.keyPolynomial_of_forall_eq (hφ : KeyPolynomial μ φ)
    {ν : Valuation K[X] Γ₀} (hν : ∀ f, ν f = augmentedValuationFun μ φ γ f) :
    KeyPolynomial ν φ := by
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  have hdvd := fun f => muDvd_iff_of_forall_eq (f := f) hm hd hν
  -- a polynomial of degree less than the degree of `φ` is not `ν`-divided by `φ`
  have hlow : ∀ f : K[X], f.degree < φ.degree → ¬ MuDvd ν φ f := fun f hf h => by
    rw [hdvd, (modByMonic_eq_self_iff hm).2 hf, hν, augmentedValuationFun_of_degree_lt hm hd hf]
      at h
    exact lt_irrefl _ h
  -- the value of the remainder of `f` is at most `ν f`
  have hle : ∀ f : K[X], μ (f %ₘ φ) ≤ ν f := fun f =>
    (hν f).symm ▸ map_modByMonic_le_augmentedValuationFun hm hd f
  refine ⟨hm, ⟨hlow 1 ?_, fun f g hfg => ?_⟩, fun f _ h => ?_⟩
  · rw [degree_one]
    exact natDegree_pos_iff_degree_pos.1 hd
  · rw [hdvd] at hfg
    rw [hdvd, hdvd]
    by_contra hne
    rw [not_or, not_lt, not_lt] at hne
    have hf := le_antisymm (hle f) hne.1
    have hg := le_antisymm (hle g) hne.2
    rw [mul_modByMonic, hφ.map_mul_modByMonic (degree_modByMonic_lt f hm)
      (degree_modByMonic_lt g hm), Valuation.map_mul, Valuation.map_mul, hf, hg] at hfg
    exact lt_irrefl _ hfg
  · by_contra hlt
    rw [not_le] at hlt
    exact hlow f (degree_lt_degree hlt) h

/-- Theorem 3.3.5 (3) in part: a key polynomial `φ` for `μ` is a key polynomial for the augmented valuation `[μ; φ, γ]`. The handbook assumes `γ < μ φ` and `γ ≠ 0` in multiplicative notation. The theorem holds for each `γ ≤ μ φ`. For `γ = μ φ` the augmentation is `μ`. For `γ = 0` the polynomial `φ` `ν`-divides no polynomial, because `ν f = μ (f %ₘ φ)`. -/
theorem KeyPolynomial.keyPolynomial_augmentedValuation (hφ : KeyPolynomial μ φ)
    (hγ : γ ≤ μ φ) : KeyPolynomial (augmentedValuation μ φ γ hφ hγ) φ :=
  hφ.keyPolynomial_of_forall_eq fun _ => rfl

/-- The `φ`-expansion is unique: if `c` has degree less than the degree of `φ`, then the coefficient of index `k` of the `φ`-expansion of `φ ^ n * c` is `c` for `k = n` and `0` otherwise. -/
theorem expansionCoeff_pow_mul_of_degree_lt (hφ : φ.Monic) {c : K[X]}
    (hc : c.degree < φ.degree) (n k : ℕ) :
    expansionCoeff φ (φ ^ n * c) k = if k = n then c else 0 := by
  rcases lt_trichotomy k n with hk | rfl | hk
  · rw [ite_eq_right hk.ne, expansionCoeff_pow_mul_of_lt hφ c hk]
  · have := expansionCoeff_pow_mul_add hφ c k 0
    rw [zero_add] at this
    rw [ite_eq_left rfl, this, expansionCoeff_zero_eq_modByMonic, (modByMonic_eq_self_iff hφ).2 hc]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
    rw [ite_eq_right (by omega), show n + m + 1 = m + 1 + n by omega, expansionCoeff_pow_mul_add hφ,
      expansionCoeff_succ, (divByMonic_eq_zero_iff hφ).2 hc, expansionCoeff_zero]

/-- The `φ`-expansion is unique: if each `cⱼ` has degree less than the degree of `φ`, then the coefficients of the `φ`-expansion of `∑ cⱼ φ ^ j` are the `cⱼ`. -/
theorem expansionCoeff_sum_mul_pow (hφ : φ.Monic) {c : ℕ → K[X]} {N : ℕ}
    (hc : ∀ j < N, (c j).degree < φ.degree) (k : ℕ) :
    expansionCoeff φ (∑ j ∈ Finset.range N, c j * φ ^ j) k = if k < N then c k else 0 := by
  rw [expansionCoeff_sum]
  rw [Finset.sum_congr rfl fun j hj => by
    rw [mul_comm, expansionCoeff_pow_mul_of_degree_lt hφ (hc j (Finset.mem_range.1 hj))]]
  simp only [Finset.sum_ite_eq, Finset.mem_range]

/-- Theorem 3.3.5 (3) in part, in elementwise form: if each `cⱼ` has degree less than the degree of `φ`, then the augmented value of `∑ cⱼ φ ^ j` is the maximum of `μ cⱼ * γ ^ j`. In additive notation, `μ'(∑ cⱼ φ ^ j) = min_j (μ(cⱼ) + jγ)`. Thus a sum of terms `in(cⱼ) (in φ) ^ j` of the same degree is not `0` in the graded algebra of `μ'` when some `cⱼ` has a nonzero value. This is the transcendence of `in φ` over the initial forms of the polynomials of degree less than the degree of `φ`. -/
theorem augmentedValuationFun_sum_mul_pow (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {c : ℕ → K[X]} {N : ℕ} (hc : ∀ j < N, (c j).degree < φ.degree) :
    augmentedValuationFun μ φ γ (∑ j ∈ Finset.range N, c j * φ ^ j) =
      (Finset.range N).sup fun j => μ (c j) * γ ^ j := by
  refine le_antisymm ((augmentedValuationFun_le_iff hφ hd).2 fun k => ?_)
    (Finset.sup_le fun j hj => ?_)
  · rw [expansionCoeff_sum_mul_pow hφ hc]
    split_ifs with hk
    · exact Finset.le_sup (f := fun j => μ (c j) * γ ^ j) (Finset.mem_range.2 hk)
    · rw [Valuation.map_zero, zero_mul]
      exact zero_le
  · have := le_augmentedValuationFun (μ := μ) (γ := γ) hφ hd
      (∑ j ∈ Finset.range N, c j * φ ^ j) j
    rwa [expansionCoeff_sum_mul_pow hφ hc, ite_eq_left (Finset.mem_range.1 hj)] at this

/-- Theorem 3.3.5 (3) in part: let `γ < μ φ` and let `a` and `b` have degree less than the degree of `φ`. Then `a * b` is `[μ; φ, γ]`-equivalent to its remainder modulo `φ`, if `μ (a * b) ≠ 0`. Thus the product of the initial forms of `a` and `b` is the initial form of a polynomial of degree less than the degree of `φ`. The strict inequality is needed. -/
theorem KeyPolynomial.muEquiv_augmentedValuation_mul_modByMonic (hφ : KeyPolynomial μ φ)
    (hγ : γ < μ φ) {a b : K[X]} (ha : a.degree < φ.degree) (hb : b.degree < φ.degree)
    (h0 : μ (a * b) ≠ 0) : MuEquiv (augmentedValuation μ φ γ hφ hγ.le) (a * b) (a * b %ₘ φ) := by
  have hm := hφ.monic
  have hd := hφ.natDegree_pos
  set q := a * b /ₘ φ
  have hab : a * b ≠ 0 := fun h => h0 (by rw [h, Valuation.map_zero])
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
  have hq : q.degree < φ.degree := by
    by_cases hq0 : q = 0
    · rw [hq0, degree_zero]
      exact bot_lt_iff_ne_bot.2 (fun h => hm.ne_zero (degree_eq_bot.1 h))
    · refine degree_lt_degree ?_
      have h1 := natDegree_lt_natDegree ha0 ha
      have h2 := natDegree_lt_natDegree hb0 hb
      have h3 := natDegree_mul_le (p := a) (q := b)
      rw [natDegree_divByMonic _ hm]
      omega
  have e : a * b - a * b %ₘ φ = φ * q := by
    rw [sub_eq_iff_eq_add']
    exact (modByMonic_add_div (a * b) φ).symm
  have hνab : augmentedValuation μ φ γ hφ hγ.le (a * b) = μ (a * b) := by
    rw [Valuation.map_mul, Valuation.map_mul, augmentedValuation_of_degree_lt hφ hγ.le ha,
      augmentedValuation_of_degree_lt hφ hγ.le hb]
  unfold MuEquiv
  rw [e, hνab, Valuation.map_mul (augmentedValuation μ φ γ hφ hγ.le), augmentedValuation_self,
    augmentedValuation_of_degree_lt hφ hγ.le hq]
  have hle : μ (φ * q) ≤ μ (a * b) := by
    rw [hφ.isMuMinimal.map_eq_max hm (a * b)]
    exact le_max_right _ _
  by_cases hq0 : μ q = 0
  · rw [hq0, mul_zero]
    exact zero_lt_iff.2 h0
  · rw [Valuation.map_mul] at hle
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hγ (zero_lt_iff.2 hq0)) hle

end KeyAugmented

end Singularity

