/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Order
import Mathlib.RingTheory.MvPolynomial.Expand
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The residual order of a purely inseparable equation

Let `k` be a ring of characteristic `p > 0` and let `q = p^e`. A purely inseparable equation is a
polynomial `f = z^q + F(x)` in the variables `z, x_1, ..., x_n`, where `F` does not involve `z`.
This is the setting of Hauser and Perlega [HP19a, §2], and of the second step of each proof of
resolution in characteristic `p` (spec 03, spec 07 §7.5).

The change of coordinates `z ↦ z + h(x)` gives `f = z^q + (F + h^q)`, since the Frobenius is
additive. So the `q`-th powers in `F` carry no information. `F` is *clean* if no monomial of `F`
has an exponent in `q ℕ^n`. Cleaning removes these monomials.

The *residual order* of `f` is the order of `F` after the best choice of `z`. Adding `h^q` can
only remove monomials of `F` whose exponents lie in `q ℕ^n`, and it can create such monomials.
So the best choice of `z` makes the order of `F` as large as possible, and the residual order is
a supremum, not an infimum:

  `residualOrder q F = ⨆ h, ord (F + h^q)`.

If `F` is clean, `ord (F + h^q) ≤ ord F` for each `h`, so the residual order of a clean `F` is
`ord F` (`residualOrder_eq_ord_of_isClean`). Over a perfect field each `F` can be cleaned, and
the residual order is the order of the clean part (`residualOrder_eq_ord_cleanPart`).

With a normal crossings divisor `E = V(∏_{i ∈ Δ} x_i)`, [HP19a, §2] writes the clean `F` as
`F = ∏_{i ∈ Δ} x_i^{r_i} · G` with `r_i` the order of `F` along `x_i = 0`, and the residual order
of `f` along `E` is `ord G`. This is `residualOrderAlong Δ q F`.

The file also defines the chart of a point blowup [HP19a, §2] as a ring map on polynomials, and
states Moh's bound for one blowup as a proposition, `moh_bound`. The bound is proved in
`Singularity/Invariant/MohBound.lean` (`moh_bound_holds`).

## Main definitions

* `Singularity.IsClean q F`: no exponent of `F` lies in `q ℕ^σ`.
* `Singularity.cleanPart q F`: `F` without its monomials with exponent in `q ℕ^σ`.
* `Singularity.residualOrder q F`: `⨆ h, ord (F + h^q)`, the residual order.
* `Singularity.divisorExponent Δ F`, `Singularity.residualFactor Δ F`: the exponents `r_i` and
  the factor `G` in `F = ∏_{i ∈ Δ} x_i^{r_i} · G`.
* `Singularity.residualOrderAlong Δ q F`: the residual order along the divisor `Δ`.
* `Singularity.purelyInseparable q F`: the polynomial `z^q + F` in `k[z, x]`.
* `Singularity.zShift h`, `Singularity.pointChart j t`, `Singularity.pointChartZ j t`: the
  coordinate change `z ↦ z + h(x)` and the `x_j`-chart of a point blowup with translations `t`.
* `Singularity.blowupDivisor Δ j t`: the transform `Δ'` of the divisor.
* `Singularity.moh_bound`: the statement of Moh's bound, a `Prop`.

## Main results

* `zShift_purelyInseparable`: `z ↦ z + h` sends `z^q + F` to `z^q + (F + h^q)`.
* `coeff_pow_eq_zero_of_not_dvd`: `h^q` has no monomial outside `q ℕ^σ`.
* `cleanPart_add_pow`, `isClean_cleanPart`: cleaning does not see `h^q`, and gives a clean
  polynomial.
* `residualOrder_add_pow`: the residual order does not depend on the choice of `z`.
* `ord_le_residualOrder`, `residualOrder_le_ord_cleanPart`, `residualOrder_eq_ord_of_isClean`,
  `residualOrder_eq_ord_cleanPart`: the residual order is squeezed between `ord F` and the order
  of the clean part, and equals the latter over a perfect field.
* `residualFactor_monomial_mul`: `residualFactor Δ (x^r · G) = G` when no `x_i` with `i ∈ Δ`
  divides `G`.
* `pointChartZ_purelyInseparable`: the chart sends `z^q + F` to `x_j^q (z^q + F')` when
  `π(F) = x_j^q F'`, so `z^q + F'` is the weak transform.

## References

* [Moh87] T.-T. Moh, *On a stability theorem for local uniformization in characteristic `p`*,
  Publ. RIMS Kyoto Univ. 23 (1987), no. 6, 965-973.
* [Hau08] H. Hauser, *On the problem of resolution of singularities in positive characteristic
  (or: a proof we are still waiting for)*, arXiv:0811.4151, Bull. AMS 47 (2010), §B (Moh's
  bound).
* [HP19a] H. Hauser, S. Perlega, *Cycles of singularities appearing in the resolution problem in
  positive characteristic*, arXiv:1802.05010, J. Algebraic Geom. 28 (2019), §2 (setting), §3
  (Moh's bound and the flaw in the stability theorem).
-/

open MvPolynomial Finsupp

namespace Singularity

section Clean

variable {σ k : Type*} [CommSemiring k]

theorem coeff_add_apply (f g : MvPolynomial σ k) (d : σ →₀ ℕ) :
    (f + g).coeff d = f.coeff d + g.coeff d := by
  simp

/-- A polynomial is clean for `q` if none of its exponents lies in `q ℕ^σ`, that is, if no
monomial of `F` is a `q`-th power up to its coefficient [HP19a, §2]. -/
def IsClean (q : ℕ) (F : MvPolynomial σ k) : Prop :=
  ∀ d ∈ F.support, ¬ ∀ i, q ∣ d i

open Classical in
/-- The clean part of `F` for `q`: the sum of the terms of `F` whose exponent is not in
`q ℕ^σ`. -/
noncomputable def cleanPart (q : ℕ) (F : MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ d ∈ F.support.filter (fun d => ¬ ∀ i, q ∣ d i), monomial d (F.coeff d)

open Classical in
theorem coeff_cleanPart (q : ℕ) (F : MvPolynomial σ k) (d : σ →₀ ℕ) :
    (cleanPart q F).coeff d = if ∀ i, q ∣ d i then 0 else F.coeff d := by
  classical
  rw [cleanPart, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : ∀ i, q ∣ d i
  · simp [h]
  · by_cases hd : F.coeff d = 0
    · simp [h, hd]
    · simp [h, hd]

theorem isClean_cleanPart (q : ℕ) (F : MvPolynomial σ k) : IsClean q (cleanPart q F) := by
  intro d hd h
  rw [MvPolynomial.mem_support_iff, coeff_cleanPart, ite_eq_left h] at hd
  exact hd rfl

theorem cleanPart_eq_self {q : ℕ} {F : MvPolynomial σ k} (hF : IsClean q F) :
    cleanPart q F = F := by
  ext d
  rw [coeff_cleanPart]
  split_ifs with h
  · by_contra hd
    exact hF d (MvPolynomial.mem_support_iff.mpr (Ne.symm hd)) h
  · rfl

theorem isClean_iff_cleanPart_eq {q : ℕ} {F : MvPolynomial σ k} :
    IsClean q F ↔ cleanPart q F = F :=
  ⟨cleanPart_eq_self, fun h => h ▸ isClean_cleanPart q F⟩

@[simp]
theorem isClean_zero (q : ℕ) : IsClean q (0 : MvPolynomial σ k) := by
  intro d hd
  simp at hd

/-- Removing monomials does not lower the order. -/
theorem ord_le_ord_cleanPart (q : ℕ) (F : MvPolynomial σ k) : ord F ≤ ord (cleanPart q F) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => le_ord_iff.mpr fun d hd => ?_
  rw [coeff_cleanPart]
  split_ifs
  · rfl
  · exact le_ord_iff.mp hn d hd

section ExpChar

variable (p : ℕ) [ExpChar k p]

/-- A `p^e`-th power has no monomial outside `p^e ℕ^σ`. -/
theorem coeff_pow_eq_zero_of_not_dvd (e : ℕ) (h : MvPolynomial σ k) {d : σ →₀ ℕ}
    (hd : ¬ ∀ i, p ^ e ∣ d i) : (h ^ p ^ e).coeff d = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hd
  rw [← map_iterateFrobenius_expand p h e, coeff_map, coeff_expand_of_not_dvd _ hi, map_zero]

/-- Cleaning does not see the addition of a `p^e`-th power. -/
theorem cleanPart_add_pow (e : ℕ) (F h : MvPolynomial σ k) :
    cleanPart (p ^ e) (F + h ^ p ^ e) = cleanPart (p ^ e) F := by
  ext d
  rw [coeff_cleanPart, coeff_cleanPart]
  split_ifs with hd
  · rfl
  · rw [coeff_add_apply, coeff_pow_eq_zero_of_not_dvd p e h hd, add_zero]

/-- For each `h`, the order of `F + h^q` is at most the order of the clean part of `F`. -/
theorem ord_add_pow_le_ord_cleanPart (e : ℕ) (F h : MvPolynomial σ k) :
    ord (F + h ^ p ^ e) ≤ ord (cleanPart (p ^ e) F) := by
  rcases eq_or_ne (cleanPart (p ^ e) F) 0 with h0 | h0
  · simp [h0]
  obtain ⟨d, hd, hdeg⟩ := exists_coeff_ne_zero_and_ord_eq h0
  rw [hdeg]
  refine ord_le ?_
  have hnd : ¬ ∀ i, p ^ e ∣ d i := by
    intro hdiv
    rw [coeff_cleanPart, ite_eq_left hdiv] at hd
    exact hd rfl
  rw [coeff_cleanPart, ite_eq_right hnd] at hd
  rwa [coeff_add_apply, coeff_pow_eq_zero_of_not_dvd p e h hnd, add_zero]

/-- If `F` is clean, adding a `q`-th power does not raise the order. -/
theorem ord_add_pow_le_ord_of_isClean (e : ℕ) {F : MvPolynomial σ k} (hF : IsClean (p ^ e) F)
    (h : MvPolynomial σ k) : ord (F + h ^ p ^ e) ≤ ord F := by
  simpa [cleanPart_eq_self hF] using ord_add_pow_le_ord_cleanPart p e F h

/-- If `F` and `F + h^q` are both clean, then `h^q = 0`: the clean representative of `F` modulo
`q`-th powers is unique. -/
theorem pow_eq_zero_of_isClean (e : ℕ) {F h : MvPolynomial σ k} (hF : IsClean (p ^ e) F)
    (hF' : IsClean (p ^ e) (F + h ^ p ^ e)) : h ^ p ^ e = 0 := by
  ext d
  show (h ^ p ^ e).coeff d = 0
  by_cases hd : ∀ i, p ^ e ∣ d i
  · have h1 : F.coeff d = 0 := by
      by_contra h1
      exact hF d (MvPolynomial.mem_support_iff.mpr h1) hd
    have h2 : (F + h ^ p ^ e).coeff d = 0 := by
      by_contra h2
      exact hF' d (MvPolynomial.mem_support_iff.mpr h2) hd
    rwa [coeff_add_apply, h1, zero_add] at h2
  · exact coeff_pow_eq_zero_of_not_dvd p e h hd

end ExpChar

end Clean

section Residual

variable {σ k : Type*} [CommSemiring k]

/-- The residual order of `z^q + F`: the largest order of `F + h^q` over all polynomials `h`,
that is, over all coordinate changes `z ↦ z + h(x)` (see `zShift_purelyInseparable`). It is a
supremum because the best `z` removes the `q`-th powers of `F`, which raises the order. -/
noncomputable def residualOrder (q : ℕ) (F : MvPolynomial σ k) : ℕ∞ :=
  ⨆ h : MvPolynomial σ k, ord (F + h ^ q)

theorem ord_add_pow_le_residualOrder (q : ℕ) (F h : MvPolynomial σ k) :
    ord (F + h ^ q) ≤ residualOrder q F :=
  le_iSup (fun h : MvPolynomial σ k => ord (F + h ^ q)) h

/-- The residual order is at least the order: take `h = 0`. -/
theorem ord_le_residualOrder {q : ℕ} (hq : q ≠ 0) (F : MvPolynomial σ k) :
    ord F ≤ residualOrder q F := by
  simpa [zero_pow hq] using ord_add_pow_le_residualOrder q F 0

variable (p : ℕ) [ExpChar k p]

/-- The residual order is at most the order of the clean part. -/
theorem residualOrder_le_ord_cleanPart (e : ℕ) (F : MvPolynomial σ k) :
    residualOrder (p ^ e) F ≤ ord (cleanPart (p ^ e) F) :=
  iSup_le fun h => ord_add_pow_le_ord_cleanPart p e F h

/-- The residual order of a clean polynomial is its order. -/
theorem residualOrder_eq_ord_of_isClean (e : ℕ) {F : MvPolynomial σ k}
    (hF : IsClean (p ^ e) F) : residualOrder (p ^ e) F = ord F := by
  refine le_antisymm ?_ (ord_le_residualOrder (pow_ne_zero e (expChar_ne_zero k p)) F)
  simpa [cleanPart_eq_self hF] using residualOrder_le_ord_cleanPart p e F

end Residual

section ResidualRing

variable {σ k : Type*} [CommRing k] (p : ℕ) [ExpChar k p]

/-- The residual order does not depend on the choice of `z`: it is the same for `F` and
`F + h^q`. -/
theorem residualOrder_add_pow (e : ℕ) (F h : MvPolynomial σ k) :
    residualOrder (p ^ e) (F + h ^ p ^ e) = residualOrder (p ^ e) F := by
  refine le_antisymm (iSup_le fun h' => ?_) (iSup_le fun h' => ?_)
  · rw [add_assoc, ← add_pow_expChar_pow]
    exact ord_add_pow_le_residualOrder _ F _
  · have : F + h' ^ p ^ e = F + h ^ p ^ e + (h' - h) ^ p ^ e := by
      rw [sub_pow_expChar_pow]
      ring
    rw [this]
    exact ord_add_pow_le_residualOrder _ _ _

/-- If `F + h^q` is clean for some `h`, the residual order of `F` is the order of `F + h^q`. -/
theorem residualOrder_eq_ord_of_add_pow (e : ℕ) {F h : MvPolynomial σ k}
    (hF : IsClean (p ^ e) (F + h ^ p ^ e)) : residualOrder (p ^ e) F = ord (F + h ^ p ^ e) := by
  rw [← residualOrder_add_pow p e F h, residualOrder_eq_ord_of_isClean p e hF]

/-- Over a perfect ring each polynomial can be cleaned: some `F + h^q` is the clean part of
`F`. -/
theorem exists_add_pow_eq_cleanPart [PerfectRing k p] (e : ℕ) (F : MvPolynomial σ k) :
    ∃ h : MvPolynomial σ k, F + h ^ p ^ e = cleanPart (p ^ e) F := by
  classical
  have hfrob : ∀ x : MvPolynomial σ k, x ^ p ^ e = iterateFrobenius (MvPolynomial σ k) p e x :=
    fun x => rfl
  let root : k → k := fun c => (iterateFrobeniusEquiv k p e).symm c
  have hroot : ∀ c, root c ^ p ^ e = c := fun c =>
    (iterateFrobeniusEquiv k p e).apply_symm_apply c
  let S := F.support.filter (fun d => ∀ i, p ^ e ∣ d i)
  let a : (σ →₀ ℕ) → (σ →₀ ℕ) := fun d => Finsupp.mapRange (fun m => m / p ^ e) (Nat.zero_div _) d
  have ha : ∀ d ∈ S, p ^ e • a d = d := by
    intro d hd
    have hd' := (Finset.mem_filter.mp hd).2
    ext i
    simp [a, Nat.mul_div_cancel' (hd' i)]
  refine ⟨∑ d ∈ S, monomial (a d) (root (-F.coeff d)), ?_⟩
  have hpow : (∑ d ∈ S, monomial (a d) (root (-F.coeff d))) ^ p ^ e =
      ∑ d ∈ S, monomial d (-F.coeff d) := by
    rw [hfrob, map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← hfrob, monomial_pow, ha d hd, hroot]
  rw [hpow]
  ext d
  rw [coeff_add_apply, coeff_sum, coeff_cleanPart]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : ∀ i, p ^ e ∣ d i
  · rw [ite_eq_left h]
    by_cases hd : F.coeff d = 0
    · simp [S, hd]
    · simp [S, h, hd]
  · rw [ite_eq_right h]
    simp [S, h]

/-- Over a perfect ring the residual order is the order of the clean part. -/
theorem residualOrder_eq_ord_cleanPart [PerfectRing k p] (e : ℕ) (F : MvPolynomial σ k) :
    residualOrder (p ^ e) F = ord (cleanPart (p ^ e) F) := by
  obtain ⟨h, hh⟩ := exists_add_pow_eq_cleanPart p e F
  rw [← residualOrder_add_pow p e F h, hh,
    residualOrder_eq_ord_of_isClean p e (isClean_cleanPart _ F)]

end ResidualRing

/-! ### The residual order along a normal crossings divisor -/

section Divisor

variable {σ k : Type*} [CommSemiring k]

/-- The exponents `r_i`, `i ∈ Δ`, of the factorization `F = ∏_{i ∈ Δ} x_i^{r_i} · G`: `r_i` is
the smallest exponent of `x_i` in a monomial of `F`, the order of `F` along `x_i = 0`. -/
noncomputable def divisorExponent (Δ : Finset σ) (F : MvPolynomial σ k) : σ →₀ ℕ :=
  ∑ i ∈ Δ, Finsupp.single i (sInf ((fun d : σ →₀ ℕ => d i) '' (F.support : Set (σ →₀ ℕ))))

theorem divisorExponent_apply [DecidableEq σ] (Δ : Finset σ) (F : MvPolynomial σ k) (i : σ) :
    divisorExponent Δ F i =
      if i ∈ Δ then sInf ((fun d : σ →₀ ℕ => d i) '' (F.support : Set (σ →₀ ℕ))) else 0 := by
  rw [divisorExponent, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

/-- The residual factor `G` of `F = ∏_{i ∈ Δ} x_i^{r_i} · G`. -/
noncomputable def residualFactor (Δ : Finset σ) (F : MvPolynomial σ k) : MvPolynomial σ k :=
  divMonomial F (divisorExponent Δ F)

/-- The residual order of `z^q + F` along the divisor `E = V(∏_{i ∈ Δ} x_i)` [HP19a, §2]: the
order of the residual factor of the clean part of `F`. -/
noncomputable def residualOrderAlong (Δ : Finset σ) (q : ℕ) (F : MvPolynomial σ k) : ℕ∞ :=
  ord (residualFactor Δ (cleanPart q F))

/-- If `F = x^r · G`, where `r` is supported in `Δ` and no `x_i` with `i ∈ Δ` divides `G` (some
monomial of `G` does not contain `x_i`), then the residual factor of `F` is `G`. -/
theorem residualFactor_monomial_mul {Δ : Finset σ} {r : σ →₀ ℕ} {G : MvPolynomial σ k}
    (hr : ∀ i, i ∉ Δ → r i = 0) (hG : ∀ i ∈ Δ, ∃ d ∈ G.support, d i = 0) :
    residualFactor Δ (monomial r 1 * G) = G := by
  classical
  have hsupp : ∀ d, d ∈ (monomial r (1 : k) * G).support ↔ r ≤ d ∧ d - r ∈ G.support := by
    intro d
    rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, coeff_monomial_mul']
    split_ifs with h
    · simp [h]
    · simp [h]
  have hexp : divisorExponent Δ (monomial r 1 * G) = r := by
    ext i
    rw [divisorExponent_apply]
    split_ifs with hi
    · obtain ⟨d, hd, hdi⟩ := hG i hi
      have hmem : r i ∈ (fun d : σ →₀ ℕ => d i) '' ((monomial r (1 : k) * G).support : Set _) := by
        refine ⟨r + d, ?_, by simp [hdi]⟩
        rw [Finset.mem_coe, hsupp]
        simpa using hd
      refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
      rintro _ ⟨d', hd', rfl⟩
      exact ((hsupp d').mp hd').1 i
    · exact (hr i hi).symm
  rw [residualFactor, hexp, divMonomial_monomial_mul]

/-- The residual order along `Δ` of a clean `F = x^r · G`, with `r` supported in `Δ` and no `x_i`
with `i ∈ Δ` dividing `G`, is `ord G`. -/
theorem residualOrderAlong_eq {Δ : Finset σ} {q : ℕ} {r : σ →₀ ℕ} {G : MvPolynomial σ k}
    (hF : IsClean q (monomial r 1 * G)) (hr : ∀ i, i ∉ Δ → r i = 0)
    (hG : ∀ i ∈ Δ, ∃ d ∈ G.support, d i = 0) :
    residualOrderAlong Δ q (monomial r 1 * G) = ord G := by
  rw [residualOrderAlong, cleanPart_eq_self hF, residualFactor_monomial_mul hr hG]

/-- The residual order along `Δ` does not see the addition of a `q`-th power. -/
theorem residualOrderAlong_add_pow (p : ℕ) [ExpChar k p] (Δ : Finset σ) (e : ℕ)
    (F h : MvPolynomial σ k) :
    residualOrderAlong Δ (p ^ e) (F + h ^ p ^ e) = residualOrderAlong Δ (p ^ e) F := by
  rw [residualOrderAlong, residualOrderAlong, cleanPart_add_pow]

/-- Along the empty divisor the residual order is the order of the clean part. -/
theorem residualOrderAlong_empty (q : ℕ) (F : MvPolynomial σ k) :
    residualOrderAlong ∅ q F = ord (cleanPart q F) := by
  rw [residualOrderAlong, residualFactor, divisorExponent, Finset.sum_empty, divMonomial_zero]

end Divisor

/-! ### Purely inseparable equations, the choice of `z`, and point blowups -/

section Equation

variable {σ k : Type*} [CommSemiring k]

/-- The purely inseparable polynomial `z^q + F(x)` in `k[z, x]`, with `z = X none` and
`x_i = X (Option.some i)`, as in `Singularity/Statements/Core.lean`. -/
noncomputable def purelyInseparable (q : ℕ) (F : MvPolynomial σ k) : MvPolynomial (Option σ) k :=
  X none ^ q + rename Option.some F

/-- The coordinate change `z ↦ z + h(x)`, `x_i ↦ x_i`. -/
noncomputable def zShift (h : MvPolynomial σ k) :
    MvPolynomial (Option σ) k →ₐ[k] MvPolynomial (Option σ) k :=
  aeval fun o => Option.elim o (X none + rename Option.some h) fun i => X (Option.some i)

theorem zShift_rename (h F : MvPolynomial σ k) : zShift h (rename Option.some F) = rename Option.some F := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [zShift]

/-- The coordinate change `z ↦ z + h(x)` sends `z^q + F` to `z^q + (F + h^q)`. -/
theorem zShift_purelyInseparable (p : ℕ) [ExpChar k p] (e : ℕ) (h F : MvPolynomial σ k) :
    zShift h (purelyInseparable (p ^ e) F) = purelyInseparable (p ^ e) (F + h ^ p ^ e) := by
  rw [purelyInseparable, purelyInseparable, map_add, map_pow, zShift_rename]
  have hz : zShift h (X none) = X none + rename Option.some h := by simp [zShift]
  rw [hz, add_pow_expChar_pow, map_add, map_pow]
  ring

variable [DecidableEq σ]

/-- The `x_j`-chart of the point blowup with translations `t`, on the `x`-variables:
`x_j ↦ x_j` and `x_i ↦ x_j (x_i + t_i)` for `i ≠ j` [HP19a, §2]. -/
noncomputable def pointChart (j : σ) (t : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => if i = j then X j else X j * (X i + C (t i))

theorem pointChart_X_self (j : σ) (t : σ → k) : pointChart j t (X j) = X j := by
  simp [pointChart]

theorem pointChart_X_of_ne {j i : σ} (t : σ → k) (h : i ≠ j) :
    pointChart j t (X i) = X j * (X i + C (t i)) := by
  simp [pointChart, h]

/-- The `x_j`-chart of the point blowup on `k[z, x]`: `z ↦ x_j z`, and `pointChart j t` on the
`x`-variables. -/
noncomputable def pointChartZ (j : σ) (t : σ → k) :
    MvPolynomial (Option σ) k →ₐ[k] MvPolynomial (Option σ) k :=
  aeval fun o => Option.elim o (X (Option.some j) * X none) fun i => rename Option.some (pointChart j t (X i))

theorem pointChartZ_rename (j : σ) (t : σ → k) (F : MvPolynomial σ k) :
    pointChartZ j t (rename Option.some F) = rename Option.some (pointChart j t F) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [pointChartZ]

/-- If `π(F) = x_j^q F'`, the chart sends `z^q + F` to `x_j^q (z^q + F')`. So `z^q + F'` is the
weak transform of `z^q + F` [HP19a, §2]. -/
theorem pointChartZ_purelyInseparable {j : σ} {t : σ → k} {q : ℕ} {F F' : MvPolynomial σ k}
    (hF : pointChart j t F = X j ^ q * F') :
    pointChartZ j t (purelyInseparable q F) = X (Option.some j) ^ q * purelyInseparable q F' := by
  rw [purelyInseparable, purelyInseparable, map_add, map_pow, pointChartZ_rename, hF, map_mul,
    map_pow, rename_X]
  have hz : pointChartZ j t (X none) = X (Option.some j) * X none := by simp [pointChartZ]
  rw [hz]
  ring

/-- The transform of the divisor `E = V(∏_{i ∈ Δ} x_i)` under the `x_j`-chart with translations
`t`: `E' = V(x_j ∏_{i ∈ Δ \ B} x_i)` with `B = {j} ∪ {i : t_i ≠ 0}` [HP19a, §2]. -/
noncomputable def blowupDivisor [DecidableEq k] (Δ : Finset σ) (j : σ) (t : σ → k) : Finset σ :=
  insert j (Δ.filter fun i => i ≠ j ∧ t i = 0)

end Equation

/-! ### Moh's bound -/

/-- **Moh's bound** for one blowup. It is proved in `Singularity/Invariant/MohBound.lean`
(`moh_bound_holds`).

Let `k` be an algebraically closed field of characteristic `p`, let `q = p^e` with `e ≥ 1`, and
let `f = z^q + F(x)` with `F` clean and `ord F ≥ q`, so that `ord f = q`. Let `E` be the divisor
`V(∏_{i ∈ Δ} x_i)`. Blow up the origin and look at the `x_j`-chart with translations `t`, so that
`π(F) = x_j^q F'` and the weak transform is `f' = z^q + F'` (`pointChartZ_purelyInseparable`).
Assume `ord F' ≥ q`, so that the order of `f` stays `q`. Then the residual order along the
transformed divisor rises by at most `p^(e-1)`:

  `residualOrderAlong Δ' q F' ≤ residualOrderAlong Δ q F + p^(e-1)`.

This is Moh's proposition, [Moh87], as stated by Hauser [Hau08, §B, Proposition (Moh)] (with
`shade` for the residual order) and as used by Hauser and Perlega [HP19a, §3]: "the increase under
a single blowup is bounded by `p^(e-1)`". The statement here is for polynomials rather than power
series and for point blowups only; the hypotheses are those of [HP19a, §2]. The stability theorem
of [Moh87], which claims the same bound `d + p^(e-1)` along a whole sequence of blowups, is false
for `e ≥ 3` [HP19a, §4]; it is not stated here.

The residual order depends on the coordinates. The papers measure it in coordinates that the
resolution process chooses, and this statement measures it in the given coordinates. The bound
is true in the given coordinates. The proof (`residualOrderAlong_pointChart_le`) does not use
`IsAlgClosed k`, `1 ≤ e` or the hypothesis `ord F' ≥ q`. -/
def moh_bound : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (e n : ℕ) (Δ : Finset (Fin n)) (j : Fin n) (t : Fin n → k) (F F' : MvPolynomial (Fin n) k),
    1 ≤ e → IsClean (p ^ e) F → ((p ^ e : ℕ) : ℕ∞) ≤ ord F →
    pointChart j t F = X j ^ p ^ e * F' → ((p ^ e : ℕ) : ℕ∞) ≤ ord F' →
    residualOrderAlong (blowupDivisor Δ j t) (p ^ e) F' ≤
      residualOrderAlong Δ (p ^ e) F + ((p ^ (e - 1) : ℕ) : ℕ∞)

end Singularity
