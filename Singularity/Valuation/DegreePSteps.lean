/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Statements.LocalUniformization
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The steps of degree p in the reduction of Cossart-Piltant

Cossart and Piltant reduce local uniformization of threefolds to the local study of two kinds of equations of degree `p` over a regular local ring of dimension 3 [CP19, Theorem 1.5 and Proposition 4.10]: purely inseparable equations `X ^ p - x`, that is `z ^ p + g`, and Artin-Schreier equations. Volume 6, Chapter 2 of the handbook gives the plan of this reduction (Proposition 2.2.1). This file proves the algebraic steps of the plan that do not need the deep results. It does not prove the reduction.

(a) Lemma 2.1.1. In characteristic `p`, the polynomial `X ^ p - a` is irreducible if and only if `a` is not a `p`-th power (`irreducible_X_pow_sub_C_iff`).

(b) The unique extension of a valuation (Lemma 2.1.5, first part). Let `L/K` be purely inseparable of exponential characteristic `p`, and let `V` be a valuation subring of `K`. The elements `b` of `L` with `b ^ p ^ n ∈ V` for some `n` form a valuation subring `purelyInseparableExtension p V` of `L` over `V`, and it is the only valuation subring of `L` over `V` (`existsUnique_valuationSubring_comap_eq`). The proof uses only that `b ^ p ^ n ∈ W` if and only if `b ∈ W` for a valuation subring `W`.

(c) Lemma 2.1.2 and Lemma 2.1.5. A finite purely inseparable extension `L/K` in characteristic `p` is a tower `K = E_0 ⊆ ... ⊆ E_r = L` with `E_{i+1} = E_i(θ_i)`, `θ_i ∉ E_i`, `θ_i ^ p ∈ E_i` and `[E_{i+1} : E_i] = p`, and `[L : K] = p ^ r`. The elements `θ_i` can be chosen in the unique extension `W` of `V` (`exists_purelyInseparable_tower`). So each step is the equation `X ^ p - x_i` with `x_i = θ_i ^ p` in the valuation ring `W ∩ E_i` of `E_i`. To choose `θ_i`, take `c ∉ E_i` and the least `e` with `c ^ p ^ e ∈ E_i`, put `c_1 = c ^ p ^ (e - 1)`, and replace `c_1` by `c_1⁻¹` if `c_1 ∉ W`.

(d) Lemma 2.2.2 for function fields. Let `V` be a valuation of `K/k` with local uniformization, and let `c ∈ K` not be a `p`-th power. Then `x = c` or `x = c⁻¹` lies in `V` and is not a `p`-th power, `X ^ p - x` is irreducible, and the center of `V` is regular on an affine model that contains `x` (`exists_inseparableStep_model`). A `p`-th root of `x` lies in each extension of `V` (`mem_valuationSubring_of_pow_eq`).

(e) Theorem 2.1.3, Part 2 (Artin-Schreier). A Galois extension `L/K` of degree `p` in characteristic `p` is `K(θ)` with `θ ^ p - θ ∈ K`, and some `σ` in the Galois group sends `θ` to `θ + 1` (`exists_artinSchreier_generator`). The proof uses the nilpotent map `N = σ - 1`. If `θ ^ p - θ = a` and `y = g θ`, then `y ^ p - g ^ (p - 1) y - g ^ p a = 0` (`artinSchreier_integral`).

(f) Lemma 2.3.1. Let `R` be an integrally closed domain of characteristic `p`, for example `k[x, y, w]`, and let `g ∈ R`. Then `R[z]/(z ^ p + g)` is reduced if and only if it is a domain, if and only if `z ^ p + g` is irreducible, if and only if `g` is not a `p`-th power in `R` (`X_pow_add_C_tfae`).

## What is not proved

The reduction itself, Proposition 2.2.1 of Volume 6 [CP19, Proposition 4.10], is not proved. It needs these facts, which the library does not have.

* Theorem 1.2.6 of Volume 6 [CP19, Theorem 1.5]: local uniformization for the equations of degree `p`. This is the main theorem of [CP19], and it is the hypothesis of the reduction.
* The patching of Zariski and the reduction to complete local domains of dimension 3 [CP19, Propositions 4.4, 4.6 and 4.8].
* The ramification theory of valuations [ZS2, Chapter VI]: the inertia and ramification fields, and the passage of local uniformization through the unramified and the tame steps [CP08, Theorem 8.1], [CP19, Proposition 4.13].
* The tower of Artin-Schreier steps for a Galois extension whose group is a `p`-group (Proposition 2.1.4 of Volume 6).
* In Step 3 of the reduction, a new model of `K(x ^ (1/p))` that contains a given finite subset of the extension of `V`.

## References

* [CP08] V. Cossart and O. Piltant, *Resolution of singularities of threefolds in positive characteristic I*, J. Algebra 320 (2008).
* [CP19] V. Cossart and O. Piltant, *Resolution of singularities of arithmetical threefolds*, J. Algebra 529 (2019).
* [ZS2] O. Zariski and P. Samuel, *Commutative Algebra*, Volume II.
-/

open Polynomial IntermediateField Module

namespace Singularity

section PowMem

variable {K : Type*} [Field K]

/-- For a valuation subring `V` and `n ≠ 0`, `b ^ n ∈ V` if and only if `b ∈ V`, because `v(b) ^ n ≤ 1` if and only if `v(b) ≤ 1`. -/
theorem valuationSubring_pow_mem_iff (V : ValuationSubring K) {b : K} {n : ℕ} (hn : n ≠ 0) :
    b ^ n ∈ V ↔ b ∈ V := by
  rw [← V.valuation_le_one_iff, ← V.valuation_le_one_iff, map_pow, pow_le_one_iff hn]

end PowMem

section Kummer

variable {K : Type*} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

/-- Lemma 2.1.1 of Volume 6 of the handbook: in characteristic `p`, the polynomial `X ^ p - a` is irreducible if and only if `a` is not a `p`-th power. If `a = b ^ p`, then `X ^ p - a = (X - b) ^ p`. -/
theorem irreducible_X_pow_sub_C_iff (a : K) :
    Irreducible (X ^ p - C a : K[X]) ↔ ∀ b : K, b ^ p ≠ a := by
  refine ⟨?_, X_pow_sub_C_irreducible_of_prime hp.out⟩
  rintro h b rfl
  rw [C_pow, ← sub_pow_char] at h
  exact not_irreducible_pow hp.out.one_lt.ne' h

end Kummer

section Extension

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (p : ℕ) [ExpChar K p]

include p in
/-- Each element `b` of a purely inseparable extension has a power `b ^ p ^ n` in `K`. -/
theorem exists_pow_mem_range [IsPurelyInseparable K L] (b : L) :
    ∃ n : ℕ, ∃ y : K, algebraMap K L y = b ^ p ^ n := by
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem K p b
  exact ⟨n, y, hy⟩

/-- The extension of a valuation subring `V` of `K` to a purely inseparable extension `L`: the elements `b` of `L` such that `b ^ p ^ n ∈ V` for some `n`. -/
def purelyInseparableExtension [IsPurelyInseparable K L] (V : ValuationSubring K) :
    ValuationSubring L where
  carrier := {b | ∃ n : ℕ, ∃ y ∈ V, algebraMap K L y = b ^ p ^ n}
  zero_mem' := ⟨0, 0, V.zero_mem, by simp⟩
  one_mem' := ⟨0, 1, V.one_mem, by simp⟩
  add_mem' := by
    have : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
    rintro a b ⟨n, y, hy, ha⟩ ⟨m, z, hz, hb⟩
    refine ⟨n + m, y ^ p ^ m + z ^ p ^ n, add_mem (pow_mem hy _) (pow_mem hz _), ?_⟩
    rw [add_pow_expChar_pow, map_add, map_pow, map_pow, ha, hb, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm m n]
  mul_mem' := by
    rintro a b ⟨n, y, hy, ha⟩ ⟨m, z, hz, hb⟩
    refine ⟨n + m, y ^ p ^ m * z ^ p ^ n, mul_mem (pow_mem hy _) (pow_mem hz _), ?_⟩
    rw [mul_pow, map_mul, map_pow, map_pow, ha, hb, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm m n]
  neg_mem' := by
    rintro a ⟨n, y, hy, ha⟩
    refine ⟨n, (-1) ^ p ^ n * y, mul_mem (pow_mem (V.neg_mem 1 V.one_mem) _) hy, ?_⟩
    rw [map_mul, map_pow, map_neg, map_one, ha, ← neg_pow]
  mem_or_inv_mem' b := by
    obtain ⟨n, y, hy⟩ := exists_pow_mem_range (K := K) p b
    rcases V.mem_or_inv_mem y with h | h
    · exact Or.inl ⟨n, y, h, hy⟩
    · exact Or.inr ⟨n, y⁻¹, h, by rw [map_inv₀, hy, inv_pow]⟩

/-- The definition of `purelyInseparableExtension p V`. -/
theorem mem_purelyInseparableExtension [IsPurelyInseparable K L] (V : ValuationSubring K) (b : L) :
    b ∈ purelyInseparableExtension p V ↔ ∃ n : ℕ, ∃ y ∈ V, algebraMap K L y = b ^ p ^ n :=
  Iff.rfl

/-- Let `W` be a valuation subring of `L` over `V`. If `algebraMap y = b ^ p ^ n`, then `b ∈ W` if and only if `y ∈ V`. -/
theorem mem_valuationSubring_iff_of_comap_eq (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : W.comap (algebraMap K L) = V) {b : L} {n : ℕ} {y : K} (hy : algebraMap K L y = b ^ p ^ n) :
    b ∈ W ↔ y ∈ V := by
  have hp : p ^ n ≠ 0 := pow_ne_zero _ (expChar_pos K p).ne'
  rw [← valuationSubring_pow_mem_iff W hp, ← hy, ← hW]
  rfl

/-- The valuation subring `purelyInseparableExtension p V` lies over `V`: its trace on `K` is `V`. -/
theorem comap_purelyInseparableExtension [IsPurelyInseparable K L] (V : ValuationSubring K) :
    (purelyInseparableExtension p V).comap (algebraMap K L) = V := by
  ext x
  change (∃ n : ℕ, ∃ y ∈ V, algebraMap K L y = algebraMap K L x ^ p ^ n) ↔ x ∈ V
  constructor
  · rintro ⟨n, y, hy, h⟩
    rw [← map_pow] at h
    rw [(algebraMap K L).injective h] at hy
    exact (valuationSubring_pow_mem_iff V (pow_ne_zero _ (expChar_pos K p).ne')).1 hy
  · intro hx
    exact ⟨0, x, hx, by simp⟩

include p in
/-- A valuation subring of a purely inseparable extension `L` of `K` is determined by its trace on `K`: if `W ∩ K = V`, then `W` is `purelyInseparableExtension p V`. -/
theorem eq_purelyInseparableExtension [IsPurelyInseparable K L] (V : ValuationSubring K)
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) :
    W = purelyInseparableExtension p V := by
  ext b
  obtain ⟨n, y, hy⟩ := exists_pow_mem_range (K := K) p b
  rw [mem_valuationSubring_iff_of_comap_eq p V W hW hy,
    mem_valuationSubring_iff_of_comap_eq p V _ (comap_purelyInseparableExtension p V) hy]

include p in
/-- Lemma 2.1.5 of Volume 6 of the handbook, first part: a valuation subring `V` of `K` has exactly one extension to a purely inseparable extension `L` of `K`. -/
theorem existsUnique_valuationSubring_comap_eq [IsPurelyInseparable K L] (V : ValuationSubring K) :
    ∃! W : ValuationSubring L, W.comap (algebraMap K L) = V :=
  ⟨purelyInseparableExtension p V, comap_purelyInseparableExtension p V,
    fun W hW ↦ eq_purelyInseparableExtension p V W hW⟩

end Extension

section Tower

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

/-- One purely inseparable step: if `θ ∉ M` and `θ ^ p ∈ M`, then `M ⊔ K⟮θ⟯` has degree `p` over `M`. -/
theorem relfinrank_sup_adjoin_eq (M : IntermediateField K L) {θ : L} (hθ : θ ∉ M)
    (hθp : θ ^ p ∈ M) : M.relfinrank (M ⊔ K⟮θ⟯) = p := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
  have hle : M ≤ M ⊔ K⟮θ⟯ := le_sup_left
  rw [relfinrank_eq_finrank_of_le hle]
  have hext : extendScalars hle = M⟮θ⟯ := by
    apply restrictScalars_injective K
    rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup]
  rw [hext]
  set a : M := ⟨θ ^ p, hθp⟩
  have hirr : Irreducible (X ^ p - C a : M[X]) := by
    refine X_pow_sub_C_irreducible_of_prime hp.out fun b hb ↦ hθ ?_
    have hb' : (b : L) ^ p = θ ^ p := by simpa [a] using congrArg (fun x : M ↦ (x : L)) hb
    have : ((b : L) - θ) ^ p = 0 := by rw [sub_pow_char, hb', sub_self]
    rw [← sub_eq_zero.1 (pow_eq_zero_iff hp.out.ne_zero |>.1 this)]
    exact b.2
  have hmonic : (X ^ p - C a : M[X]).Monic := monic_X_pow_sub_C a hp.out.ne_zero
  have hroot : aeval θ (X ^ p - C a : M[X]) = 0 := by
    simp [a]
  have hmin : minpoly M θ = X ^ p - C a :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
  have hint : IsIntegral M θ := ⟨_, hmonic, hroot⟩
  rw [adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]

end Tower

section ArtinSchreier

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

/-- The `n`-th power of `σ` as a linear map is the linear map of `σ ^ n`. -/
theorem algEquiv_toLinearMap_pow_apply (σ : L ≃ₐ[K] L) (n : ℕ) (x : L) :
    ((σ.toLinearMap : L →ₗ[K] L) ^ n) x = (σ ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, AlgEquiv.mul_apply]; rfl

/-- Artin-Schreier theorem, Part 2 (Theorem 2.1.3 of Volume 6 of the handbook): a Galois extension `L/K` of degree `p` in characteristic `p` is `K(θ)` with `θ ^ p - θ ∈ K`, and a generator `σ` of the Galois group sends `θ` to `θ + 1`. -/
theorem exists_artinSchreier_generator [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L = p) :
    ∃ θ : L, θ ^ p - θ ∈ (⊥ : IntermediateField K L) ∧ K⟮θ⟯ = ⊤ ∧
      ∃ σ : L ≃ₐ[K] L, σ θ = θ + 1 := by
  classical
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hcard : Nat.card (L ≃ₐ[K] L) = p := by rw [IsGalois.card_aut_eq_finrank, hd]
  have : Finite (L ≃ₐ[K] L) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.out.ne_zero)
  obtain ⟨σ, hσ⟩ : ∃ σ : L ≃ₐ[K] L, σ ≠ 1 := by
    by_contra! h
    have : Nat.card (L ≃ₐ[K] L) = 1 := Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b ↦ by
      rw [h a, h b]⟩, ⟨1⟩⟩
    exact hp.out.one_lt.ne' (hcard ▸ this)
  -- an element fixed by `σ` lies in `K`
  have hfix : ∀ x : L, σ x = x → x ∈ (⊥ : IntermediateField K L) := by
    intro x hx
    rw [IsGalois.mem_bot_iff_fixed]
    intro τ
    have hτ : τ ∈ Subgroup.zpowers σ := mem_zpowers_of_prime_card hcard hσ
    have hsub : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) x := by
      rw [Subgroup.zpowers_le]
      exact hx
    exact hsub hτ
  set N : Module.End K L := σ.toLinearMap - 1 with hN
  have hNapply : ∀ x, N x = σ x - x := fun x ↦ rfl
  have : CharP (Module.End K L) p := charP_of_injective_algebraMap'  K p
  have hNp : N ^ p = 0 := by
    rw [hN, sub_pow_char_of_commute (p := p) (h := Commute.one_right _), one_pow]
    ext x
    rw [LinearMap.sub_apply, algEquiv_toLinearMap_pow_apply, ← hcard, pow_card_eq_one']
    simp
  have hN0 : N ≠ 0 := by
    intro h
    apply hσ
    ext x
    have := congrArg (fun f : Module.End K L ↦ f x) h
    simp only [hNapply, LinearMap.zero_apply, sub_eq_zero] at this
    exact this
  have hex : ∃ k, N ^ k = 0 := ⟨p, hNp⟩
  set k := Nat.find hex with hk
  have hk0 : N ^ k = 0 := Nat.find_spec hex
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases hkv : k
    · rw [pow_zero] at hk0
      exact one_ne_zero hk0
    · rw [pow_one] at hk0
      exact hN0 hk0
  have hj : N ^ (k - 1) ≠ 0 := Nat.find_min hex (by omega)
  obtain ⟨w, hw⟩ : ∃ w, (N ^ (k - 1)) w ≠ 0 := by
    by_contra! h
    exact hj (LinearMap.ext h)
  set z := (N ^ (k - 2)) w
  set c := N z
  have hc : c = (N ^ (k - 1)) w := by
    rw [show k - 1 = (k - 2) + 1 by omega, pow_succ', Module.End.mul_apply]
  have hc0 : c ≠ 0 := hc ▸ hw
  have hNc : N c = 0 := by
    rw [hc, ← Module.End.mul_apply, ← pow_succ', show k - 1 + 1 = k by omega, hk0]
    rfl
  have hσc : σ c = c := by
    have := hNapply c
    rw [hNc] at this
    exact (sub_eq_zero.1 this.symm)
  have hσz : σ z = z + c := by
    have := hNapply z
    rw [eq_sub_iff_add_eq] at this
    rw [← this, add_comm]
  set θ := z / c
  have hσθ : σ θ = θ + 1 := by
    rw [map_div₀, hσz, hσc, add_div, div_self hc0]
  have hθK : θ ^ p - θ ∈ (⊥ : IntermediateField K L) := by
    apply hfix
    rw [map_sub, map_pow, hσθ, add_pow_char, one_pow]
    ring
  have hθ : θ ∉ (⊥ : IntermediateField K L) := by
    rw [IntermediateField.mem_bot]
    rintro ⟨a, ha⟩
    have h1 : σ θ = θ := by rw [← ha, AlgEquiv.commutes]
    rw [hσθ] at h1
    exact one_ne_zero (add_eq_left.1 h1)
  refine ⟨θ, hθK, ?_, σ, hσθ⟩
  have hdvd : finrank K K⟮θ⟯ ∣ p := by
    rw [← hd]
    exact (IntermediateField.finrank_dvd_of_le_right (le_top : K⟮θ⟯ ≤ ⊤)).trans
      (dvd_of_eq IntermediateField.finrank_top')
  rcases (Nat.dvd_prime hp.out).1 hdvd with h | h
  · rw [IntermediateField.finrank_eq_one_iff] at h
    exact absurd (h ▸ IntermediateField.mem_adjoin_simple_self K θ) hθ
  · exact IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [h, IntermediateField.finrank_top', hd])

/-- The integral form of an Artin-Schreier equation: if `θ ^ p - θ = a` and `y = g θ`, then `y ^ p - g ^ (p - 1) y - g ^ p a = 0`. -/
theorem artinSchreier_integral {R : Type*} [CommRing R] (θ a g : R) (h : θ ^ p - θ = a) :
    (g * θ) ^ p - g ^ (p - 1) * (g * θ) - g ^ p * a = 0 := by
  have : g ^ (p - 1) * g = g ^ p := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
  rw [← h, mul_pow, ← mul_assoc, this]
  ring

end ArtinSchreier

section TowerMain

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

/-- One step of the tower in an intermediate field `M`: `M' = M ⊔ K⟮θ⟯`, with `θ ∉ M`, `θ ^ p ∈ M`, `[M' : M] = p`, and `θ ∈ W`. -/
def IsInseparableStep (W : ValuationSubring L) (M M' : IntermediateField K L) (θ : L) : Prop :=
  M' = M ⊔ K⟮θ⟯ ∧ θ ∉ M ∧ θ ^ p ∈ M ∧ M.relfinrank M' = p ∧ θ ∈ W

/-- The tower of `exists_purelyInseparable_tower`, from a given intermediate field `M` to `L`, for a given valuation subring `W` of `L`. The proof is by induction on `[L : K] - [M : K]`. -/
theorem exists_purelyInseparable_tower_from [FiniteDimensional K L] [IsPurelyInseparable K L] (W : ValuationSubring L) :
    ∀ M : IntermediateField K L, ∃ (r : ℕ) (E : ℕ → IntermediateField K L) (θ : ℕ → L),
      E 0 = M ∧ E r = ⊤ ∧ ∀ i < r, IsInseparableStep p W (E i) (E (i + 1)) (θ i) := by
  classical
  have : ExpChar K p := ExpChar.prime hp.out
  intro M
  induction hm : finrank K L - finrank K M using Nat.strong_induction_on generalizing M with
  | _ m ih =>
  by_cases htop : M = ⊤
  · exact ⟨0, fun _ ↦ M, fun _ ↦ 0, rfl, htop, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  obtain ⟨c, hc⟩ : ∃ c : L, c ∉ M := by
    by_contra! h
    exact htop (eq_top_iff.2 fun x _ ↦ h x)
  have hex : ∃ n : ℕ, c ^ p ^ n ∈ M := by
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem K p c
    exact ⟨n, hy ▸ M.algebraMap_mem y⟩
  set e := Nat.find hex
  have he : c ^ p ^ e ∈ M := Nat.find_spec hex
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at he
    exact hc he
  set c₁ := c ^ p ^ (e - 1)
  have hc₁ : c₁ ∉ M := Nat.find_min hex (by omega)
  have hc₁p : c₁ ^ p ∈ M := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 he0)]
    exact he
  -- choose `θ = c₁` or `θ = c₁⁻¹`, so that `θ ∈ W`
  obtain ⟨θ, hθ, hθp, hθW⟩ : ∃ θ : L, θ ∉ M ∧ θ ^ p ∈ M ∧ θ ∈ W := by
    rcases W.mem_or_inv_mem c₁ with h | h
    · exact ⟨c₁, hc₁, hc₁p, h⟩
    · refine ⟨c₁⁻¹, fun h' ↦ hc₁ ?_, ?_, h⟩
      · simpa using M.inv_mem h'
      · rw [inv_pow]
        exact M.inv_mem hc₁p
  set M' := M ⊔ K⟮θ⟯
  have hrel : M.relfinrank M' = p := relfinrank_sup_adjoin_eq p M hθ hθp
  have hle : M ≤ M' := le_sup_left
  have hfin : finrank K M' = finrank K M * p := by
    rw [← relfinrank_bot_left, ← relfinrank_bot_left, ← hrel,
      relfinrank_mul_relfinrank bot_le hle]
  have hM'le : finrank K M' ≤ finrank K L := by
    exact (IntermediateField.finrank_le_of_le_right le_top).trans_eq IntermediateField.finrank_top'
  have hpos : 0 < finrank K M := Module.finrank_pos
  have hlt : finrank K L - finrank K M' < m := by
    have : finrank K M < finrank K M' := by
      rw [hfin]
      exact lt_mul_of_one_lt_right hpos hp.out.one_lt
    omega
  obtain ⟨r, E, θs, hE0, hEr, hstep⟩ := ih _ hlt M' rfl
  refine ⟨r + 1, fun i ↦ Nat.casesOn i M E, fun i ↦ Nat.casesOn i θ θs, rfl, hEr, ?_⟩
  intro i hi
  cases i with
  | zero =>
    show IsInseparableStep p W M (E 0) θ
    rw [hE0]
    exact ⟨rfl, hθ, hθp, hrel, hθW⟩
  | succ i => exact hstep i (by omega)

/-- The purely inseparable part of the reduction of Cossart-Piltant (Lemma 2.1.2 and Lemma 2.1.5 of Volume 6 of the handbook). Let `L/K` be a finite purely inseparable extension in characteristic `p`, and let `V` be a valuation subring of `K`. Then `V` has exactly one extension `W` to `L`, and there is a tower `K = E_0 ⊆ E_1 ⊆ ... ⊆ E_r = L` with `E_{i+1} = E_i(θ_i)`, `θ_i ∉ E_i`, `θ_i ^ p ∈ E_i` and `[E_{i+1} : E_i] = p`, in which each `θ_i` lies in `W`. So each step is given by the equation `X ^ p - x_i` with `x_i = θ_i ^ p` in the valuation ring `W ∩ E_i` of `E_i`, and `[L : K] = p ^ r`. -/
theorem exists_purelyInseparable_tower [FiniteDimensional K L] [IsPurelyInseparable K L]
    (V : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap (algebraMap K L) = V ∧
      (∀ W' : ValuationSubring L, W'.comap (algebraMap K L) = V → W' = W) ∧
      ∃ (r : ℕ) (E : ℕ → IntermediateField K L) (θ : ℕ → L), E 0 = ⊥ ∧ E r = ⊤ ∧
        finrank K L = p ^ r ∧ ∀ i < r, E (i + 1) = E i ⊔ K⟮θ i⟯ ∧ θ i ∉ E i ∧ θ i ^ p ∈ E i ∧
          (E i).relfinrank (E (i + 1)) = p ∧ θ i ∈ W := by
  have : ExpChar K p := ExpChar.prime hp.out
  obtain ⟨W, hW, huniq⟩ := existsUnique_valuationSubring_comap_eq (K := K) (L := L) p V
  obtain ⟨r, E, θ, hE0, hEr, hstep⟩ := exists_purelyInseparable_tower_from (K := K) p W ⊥
  refine ⟨W, hW, huniq, r, E, θ, hE0, hEr, ?_, hstep⟩
  have key : ∀ j ≤ r, finrank K (E j) = p ^ j := by
    intro j
    induction j with
    | zero => intro _; rw [hE0, IntermediateField.finrank_bot, pow_zero]
    | succ j ihj =>
      intro hj
      obtain ⟨-, -, -, hrel, -⟩ := hstep j (by omega)
      have hle : E j ≤ E (j + 1) := by rw [(hstep j (by omega)).1]; exact le_sup_left
      rw [← relfinrank_bot_left, ← relfinrank_mul_relfinrank bot_le hle, relfinrank_bot_left,
        ihj (by omega), hrel, pow_succ]
  rw [← IntermediateField.finrank_top', ← hEr, key r le_rfl]

end TowerMain

section Model

variable (p : ℕ) [hp : Fact p.Prime] {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The purely inseparable step for function fields (Lemma 2.2.2 of Volume 6 of the handbook). Let `V` be a valuation of `K/k` with local uniformization, and let `c ∈ K` not be a `p`-th power. Then `x = c` or `x = c⁻¹` lies in `V`, is not a `p`-th power, the polynomial `X ^ p - x` is irreducible over `K`, and there is an affine model `A` of `K/k` with `x ∈ A ⊆ V` whose local ring at the center of `V` is regular. -/
theorem exists_inseparableStep_model (V : ValuationSubring K) [Algebra k V] [IsScalarTower k V K]
    (hV : HasLocalUniformization k V) {c : K} (hc : ∀ b : K, b ^ p ≠ c) :
    ∃ x : K, (x = c ∨ x = c⁻¹) ∧ x ∈ V ∧ (∀ b : K, b ^ p ≠ x) ∧
      Irreducible (X ^ p - C x : K[X]) ∧ HasRegularCenter k V {x} := by
  have hc' : ∀ b : K, b ^ p ≠ c⁻¹ := fun b hb ↦ hc b⁻¹ (by rw [inv_pow, hb, inv_inv])
  obtain ⟨x, hx, hxV, hxp⟩ : ∃ x : K, (x = c ∨ x = c⁻¹) ∧ x ∈ V ∧ ∀ b : K, b ^ p ≠ x := by
    rcases V.mem_or_inv_mem c with h | h
    · exact ⟨c, Or.inl rfl, h, hc⟩
    · exact ⟨c⁻¹, Or.inr rfl, h, hc'⟩
  refine ⟨x, hx, hxV, hxp, X_pow_sub_C_irreducible_of_prime hp.out hxp, ?_⟩
  have := hV {x} (by simpa using hxV)
  simpa using this

/-- In the setting of `exists_inseparableStep_model`, let `θ` be a `p`-th root of `x` in an extension `L` of `K`. Then `θ` lies in each valuation subring of `L` over `V`. So the ring `A_P[θ] = A_P[X]/(X ^ p - x)` lies in the extension of `V`, and the center of this extension lies over the center `P` of `V`. -/
theorem mem_valuationSubring_of_pow_eq {L : Type*} [Field L] [Algebra K L] (V : ValuationSubring K)
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) {x : K} (hx : x ∈ V) {θ : L}
    (hθ : θ ^ p = algebraMap K L x) : θ ∈ W := by
  rw [← valuationSubring_pow_mem_iff W hp.out.ne_zero, hθ]
  rw [← hW] at hx
  exact hx

end Model

section Reduced

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] [IsDomain R] [CharP R p]

omit [IsDomain R] in
/-- If `g = a ^ p`, then `X ^ p + g = (X + a) ^ p`. -/
theorem X_pow_add_C_pow_eq (a : R) : (X ^ p + C (a ^ p) : R[X]) = (X + C a) ^ p := by
  rw [add_pow_char, C_pow]

/-- If `R[X]/(X ^ p + g)` is reduced, then `g` is not a `p`-th power. -/
theorem ne_pow_of_isReduced (g : R) (h : IsReduced (R[X] ⧸ Ideal.span {X ^ p + C g})) :
    ∀ a : R, a ^ p ≠ g := by
  rintro a rfl
  set f : R[X] := X + C a
  have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {X ^ p + C (a ^ p)}) f) := by
    refine ⟨p, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, ← X_pow_add_C_pow_eq p a]
    exact Ideal.subset_span rfl
  have h0 := h.eq_zero _ hnil
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
  have hdeg := natDegree_le_of_dvd h0 (X_add_C_ne_zero a)
  rw [natDegree_X_pow_add_C, natDegree_X_add_C] at hdeg
  exact absurd hdeg (not_le.2 hp.out.one_lt)

variable [IsIntegrallyClosed R]

/-- Let `R` be an integrally closed domain of characteristic `p` with fraction field `K`, and let `g ∈ R` not be a `p`-th power in `R`. Then `X ^ p + g` is irreducible over `K`. -/
theorem irreducible_map_X_pow_add_C {g : R} (hg : ∀ a : R, a ^ p ≠ g) :
    Irreducible ((X ^ p + C g : R[X]).map (algebraMap R (FractionRing R))) := by
  set K := FractionRing R
  have : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective R K) p
  rw [Polynomial.map_add, Polynomial.map_pow, map_X, map_C, ← sub_neg_eq_add, ← map_neg]
  refine X_pow_sub_C_irreducible_of_prime hp.out fun b hb ↦ ?_
  have hb' : (-b) ^ p = algebraMap R K g := by
    rw [neg_pow, neg_one_pow_char, hb, neg_one_mul, neg_neg]
  have hint : IsIntegral R (-b) := by
    refine ⟨X ^ p - C g, monic_X_pow_sub_C g hp.out.ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hb', sub_self]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine hg y (IsFractionRing.injective R K ?_)
  rw [map_pow, hy, hb']

/-- Lemma 2.3.1 of Volume 6 of the handbook: for an integrally closed domain `R` of characteristic `p` and `g ∈ R`, the following are equivalent: `R[X]/(X ^ p + g)` is reduced, it is a domain, `X ^ p + g` is irreducible in `R[X]`, and `g` is not a `p`-th power in `R`. -/
theorem X_pow_add_C_tfae (g : R) :
    List.TFAE [IsReduced (R[X] ⧸ Ideal.span {X ^ p + C g}),
      IsDomain (R[X] ⧸ Ideal.span {X ^ p + C g}),
      Irreducible (X ^ p + C g : R[X]), ∀ a : R, a ^ p ≠ g] := by
  set K := FractionRing R
  set h : R[X] := X ^ p + C g
  have hmonic : h.Monic := monic_X_pow_add_C g hp.out.ne_zero
  tfae_have 1 → 4 := ne_pow_of_isReduced p g
  tfae_have 4 → 3 := fun hg ↦
    (hmonic.irreducible_iff_irreducible_map_fraction_map (K := K)).2
      (irreducible_map_X_pow_add_C p hg)
  tfae_have 3 → 2 := by
    intro hirr
    have hirrK := (hmonic.irreducible_iff_irreducible_map_fraction_map (K := K)).1 hirr
    have hprime : (Ideal.span {h.map (algebraMap R K)}).IsPrime :=
      (PrincipalIdealRing.isMaximal_of_irreducible hirrK).isPrime
    have heq : Ideal.span {h} =
        (Ideal.span {h.map (algebraMap R K)}).comap (mapRingHom (algebraMap R K)) := by
      ext f
      rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton, coe_mapRingHom,
        ← modByMonic_eq_zero_iff_dvd hmonic, ← modByMonic_eq_zero_iff_dvd (hmonic.map _),
        ← map_modByMonic _ hmonic]
      exact (Polynomial.map_eq_zero_iff (IsFractionRing.injective R K)).symm
    rw [Ideal.Quotient.isDomain_iff_prime, heq]
    exact Ideal.IsPrime.comap _
  tfae_have 2 → 1 := fun _ ↦ inferInstance
  tfae_finish

/-- Lemma 2.3.1 of Volume 6 of the handbook for `R = k[x, y, w]`: the hypersurface `z ^ p + g(x, y, w) = 0` is reduced if and only if `g` is not a `p`-th power in `k[x, y, w]`. -/
theorem X_pow_add_C_tfae_threefold (k : Type*) [Field k] [CharP k p] (g : MvPolynomial (Fin 3) k) :
    List.TFAE [IsReduced ((MvPolynomial (Fin 3) k)[X] ⧸ Ideal.span {X ^ p + C g}),
      IsDomain ((MvPolynomial (Fin 3) k)[X] ⧸ Ideal.span {X ^ p + C g}),
      Irreducible (X ^ p + C g : (MvPolynomial (Fin 3) k)[X]),
      ∀ a : MvPolynomial (Fin 3) k, a ^ p ≠ g] :=
  X_pow_add_C_tfae p g

end Reduced

end Singularity
