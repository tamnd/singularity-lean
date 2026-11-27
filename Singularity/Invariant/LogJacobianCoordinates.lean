/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianBlowup
import Singularity.Invariant.LogJacobianTau

/-!
# `Θ(g)` does not depend on the adapted coordinates

Let `k` be a field of characteristic `p`, and let `E = V(∏_{i ∈ Δ} x_i)`. Part 3 of Lemma 3.6 of
research note 03 says that the log-Jacobian ideal `Θ(g)` depends only on `g` and on `E`, and not on
the coordinates. Corollary 3.8 of the note then says that the residual order in each system of
coordinates adapted to `E` is `ρ` or `ρ + 1`.

This file proves both statements for the changes of coordinates of `k[x]` that are adapted to `E`.
Let `φ` and `ψ` be inverse `k`-algebra endomorphisms of `k[x]`, with `φ(x_l) = c_l x_l` for each
`l ∈ Δ` and `c_l ∈ k`. The images `φ(x_j)` of the free coordinates `j ∉ Δ` are arbitrary. Then
(the second item needs only `ψ ∘ φ = id`):

* `φ(Θ(h)) = Θ(φ(h))` for each `h` (`map_logJacobian_eq_of_adapted`). This is part 3 of Lemma 3.6.
* If also `φ` and `ψ` fix the origin, and `g ≠ 0` is clean, then for each `F` with
  `Θ(F) = φ(Θ(g))`, the clean part of `F` has the same monomial factor and the same `ρ` as `g`, and
  `ρ ≤ d(F) ≤ ρ + 1` for the residual order `d(F)` of `z^p + F`
  (`logJacobianOrder_cleanPart_eq_of_adapted`, `logJacobianOrder_le_residualOrderAlong_of_adapted`,
  `residualOrderAlong_le_logJacobianOrder_add_one_of_adapted`). The case `F = φ(g) + h^p` covers
  each representative of `g` modulo `p`-th powers in the new coordinates
  (`logJacobian_map_add_pow_eq`). This is Corollary 3.8 of the note for these coordinates.

The proof of part 3. The chain rule `∂_i φ(h) = ∑_l φ(∂_l h) ∂_i φ(x_l)` (`pderiv_algHom`) writes
each generator of `Θ(φ(h))` as a combination of the `φ(∂_l h)` for `l ∉ Δ` and of the
`φ(x_l ∂_l h)` for `l ∈ Δ`, since `x_i ∂_i (c_l x_l)` and `∂_j (c_l x_l)` are multiples of
`c_l x_l`. So `Θ(φ(h)) ⊆ φ(Θ(h))` (`logJacobian_le_map_of_adapted`). The inverse `ψ` is adapted
too (`exists_eq_C_mul_X_of_inverse`), and this gives the other inclusion.

The coordinate changes of the power series ring with `x'_l = u_l x_l` for a unit `u_l` that is not
a constant are not covered.

## Main results

* `pderiv_algHom`: the chain rule.
* `logJacobian_le_map_of_adapted`, `map_logJacobian_eq_of_adapted`: part 3 of Lemma 3.6.
* `idealOrd_map_eq_of_inverse`: an automorphism that fixes the origin keeps the order of ideals.
* `divisorExponent_cleanPart_eq_of_adapted`, `logJacobianOrder_cleanPart_eq_of_adapted`: the
  monomial factor and `ρ` do not change.
* `logJacobianOrder_le_residualOrderAlong_of_adapted`,
  `residualOrderAlong_le_logJacobianOrder_add_one_of_adapted`: Corollary 3.8.

## References

* Research note 03, Sections 3.3 and 3.4: Lemma 3.6 and Corollary 3.8.
* Volume 7, Section 3.1 of the handbook.
-/

open MvPolynomial

namespace Singularity

section Chain

variable {σ k : Type*} [CommRing k] [DecidableEq σ] [Fintype σ]

omit [DecidableEq σ] in
/-- **The chain rule** for an endomorphism `φ` of `k[x]`:
`∂_i φ(h) = ∑_l φ(∂_l h) ∂_i φ(x_l)`. -/
theorem pderiv_algHom (φ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k) (i : σ)
    (h : MvPolynomial σ k) :
    pderiv i (φ h) = ∑ l, φ (pderiv l h) * pderiv i (φ (X l)) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P m hP =>
    rw [map_mul, pderiv_mul, hP]
    simp only [pderiv_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    · rw [Finset.sum_eq_single m]
      · rw [pderiv_X_self, map_one, mul_one]
      · intro l _ hl
        rw [pderiv_X_of_ne (Ne.symm hl), map_zero, mul_zero, zero_mul]
      · intro hm
        exact absurd (Finset.mem_univ m) hm

end Chain

section Adapted

variable {σ k : Type*} [Field k] [DecidableEq σ] [Fintype σ] {Δ : Finset σ}
  {φ ψ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k}

omit [Fintype σ] in
/-- For `φ(x_l) = c x_l` with `l ∈ Δ`, each log derivation sends `φ(x_l)` into `(φ(x_l))`: the
case of `x_i ∂_i` for `i ∈ Δ`. -/
theorem X_mul_pderiv_C_mul_X_mem (c : k) (i l : σ) :
    X i * pderiv i (C c * X l : MvPolynomial σ k) ∈ Ideal.span {C c * X l} := by
  rw [pderiv_C_mul]
  by_cases hil : i = l
  · subst hil
    rw [pderiv_X_self, mul_one, mul_comm]
    exact Ideal.mem_span_singleton_self _
  · rw [pderiv_X_of_ne (Ne.symm hil), mul_zero, mul_zero]
    exact Ideal.zero_mem _

omit [DecidableEq σ] [Fintype σ] in
/-- The case of `∂_j` for `j ≠ l`. -/
theorem pderiv_C_mul_X_of_ne (c : k) {j l : σ} (hjl : j ≠ l) :
    pderiv j (C c * X l : MvPolynomial σ k) = 0 := by
  rw [pderiv_C_mul, pderiv_X_of_ne (Ne.symm hjl), mul_zero]

/-- **`Θ(φ(h)) ⊆ φ(Θ(h))`** for a change of coordinates adapted to `Δ`: `φ(x_l) = c_l x_l` for
each `l ∈ Δ`. -/
theorem logJacobian_le_map_of_adapted (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l)
    (h : MvPolynomial σ k) :
    logJacobian Δ (φ h) ≤ Ideal.map φ (logJacobian Δ h) := by
  set J := Ideal.map φ (logJacobian Δ h)
  have hin : ∀ l ∈ Δ, ∀ y ∈ Ideal.span {φ (X l)}, φ (pderiv l h) * y ∈ J := by
    intro l hl y hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mul_left_comm, ← map_mul]
    refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [mul_comm]
    exact X_mul_pderiv_mem_logJacobian hl h
  have hout : ∀ l ∉ Δ, ∀ y, φ (pderiv l h) * y ∈ J := fun l hl y =>
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (pderiv_mem_logJacobian hl h))
  rw [logJacobian, Ideal.span_le]
  rintro _ (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
  · show X i * pderiv i (φ h) ∈ J
    rw [pderiv_algHom, Finset.mul_sum]
    refine Ideal.sum_mem _ fun l _ => ?_
    rw [mul_left_comm]
    by_cases hl : l ∈ Δ
    · refine hin l hl _ ?_
      obtain ⟨c, hc⟩ := hφ l hl
      rw [hc]
      exact X_mul_pderiv_C_mul_X_mem c i l
    · exact hout l hl _
  · show pderiv j (φ h) ∈ J
    have hj' : j ∉ Δ := by simpa using hj
    rw [pderiv_algHom]
    refine Ideal.sum_mem _ fun l _ => ?_
    by_cases hl : l ∈ Δ
    · refine hin l hl _ ?_
      obtain ⟨c, hc⟩ := hφ l hl
      have hjl : j ≠ l := fun e => hj' (e ▸ hl)
      rw [hc, pderiv_C_mul_X_of_ne c hjl]
      exact Ideal.zero_mem _
    · exact hout l hl _

omit [DecidableEq σ] [Fintype σ] in
/-- If `ψ ∘ φ = id` and `φ(x_l) = c x_l`, then `c ≠ 0` and `ψ(x_l) = c⁻¹ x_l`. So the inverse of
an adapted change of coordinates is adapted. -/
theorem exists_eq_C_mul_X_of_inverse (hψφ : ∀ h, ψ (φ h) = h) {l : σ} {c : k}
    (hc : φ (X l) = C c * X l) : ψ (X l) = C c⁻¹ * X l := by
  have h1 : X l = C c * ψ (X l) := by
    conv_lhs => rw [← hψφ (X l), hc]
    rw [map_mul, algHom_C, algebraMap_eq]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at h1
    exact X_ne_zero l h1
  calc ψ (X l) = C c⁻¹ * (C c * ψ (X l)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
    _ = C c⁻¹ * X l := by rw [← h1]

omit [DecidableEq σ] [Fintype σ] in
/-- `φ(ψ(I)) = I` if `φ ∘ ψ = id`. -/
theorem map_map_of_inverse (hφψ : ∀ h, φ (ψ h) = h) (I : Ideal (MvPolynomial σ k)) :
    Ideal.map φ (Ideal.map ψ I) = I := by
  refine le_antisymm (Ideal.map_le_of_le_comap (Ideal.map_le_of_le_comap fun x hx => ?_)) ?_
  · rw [Ideal.mem_comap, Ideal.mem_comap, hφψ]
    exact hx
  · intro x hx
    rw [← hφψ x]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)

/-- **Part 3 of Lemma 3.6 of research note 03**: `Θ(h)` does not depend on the adapted
coordinates. Let `φ` and `ψ` be inverse endomorphisms of `k[x]` with `φ(x_l) = c_l x_l` for each
`l ∈ Δ`. Then `φ(Θ(h)) = Θ(φ(h))`. -/
theorem map_logJacobian_eq_of_adapted (hψφ : ∀ h, ψ (φ h) = h) (hφψ : ∀ h, φ (ψ h) = h)
    (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l) (h : MvPolynomial σ k) :
    Ideal.map φ (logJacobian Δ h) = logJacobian Δ (φ h) := by
  have hψ : ∀ l ∈ Δ, ∃ c : k, ψ (X l) = C c * X l := fun l hl => by
    obtain ⟨c, hc⟩ := hφ l hl
    exact ⟨c⁻¹, exists_eq_C_mul_X_of_inverse hψφ hc⟩
  refine le_antisymm ?_ (logJacobian_le_map_of_adapted hφ h)
  have h1 := Ideal.map_mono (f := φ) (logJacobian_le_map_of_adapted hψ (φ h))
  rwa [hψφ, map_map_of_inverse hφψ] at h1

end Adapted

section Order

variable {σ k : Type*} [Field k] {φ ψ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k}

/-- An endomorphism that fixes the origin keeps `m^n`: `φ(m^n) ⊆ m^n` if `φ(x_i)(0) = 0` for each
`i`. -/
theorem map_pow_idealOfVars_le (hφ : ∀ i, constantCoeff (φ (X i)) = 0) (n : ℕ) :
    Ideal.map φ (idealOfVars σ k ^ n) ≤ idealOfVars σ k ^ n := by
  rw [Ideal.map_pow]
  refine Ideal.pow_right_mono ?_ n
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact mem_idealOfVars_iff.mpr (hφ i)

/-- An endomorphism that fixes the origin does not lower the order of an ideal. -/
theorem idealOrd_le_idealOrd_map (hφ : ∀ i, constantCoeff (φ (X i)) = 0)
    (I : Ideal (MvPolynomial σ k)) : idealOrd I ≤ idealOrd (Ideal.map φ I) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_idealOrd_iff] at hn ⊢
  exact (Ideal.map_mono hn).trans (map_pow_idealOfVars_le hφ n)

/-- **An automorphism that fixes the origin keeps the order of ideals.** -/
theorem idealOrd_map_eq_of_inverse (hψφ : ∀ h, ψ (φ h) = h)
    (hφ : ∀ i, constantCoeff (φ (X i)) = 0) (hψ : ∀ i, constantCoeff (ψ (X i)) = 0)
    (I : Ideal (MvPolynomial σ k)) : idealOrd (Ideal.map φ I) = idealOrd I := by
  refine le_antisymm ?_ (idealOrd_le_idealOrd_map hφ I)
  calc idealOrd (Ideal.map φ I) ≤ idealOrd (Ideal.map ψ (Ideal.map φ I)) :=
        idealOrd_le_idealOrd_map hψ _
    _ ≤ idealOrd I := by
        rw [map_map_of_inverse hψφ]

end Order

section Corollary

variable {σ k : Type*} [Field k] [DecidableEq σ] [Fintype σ] (p : ℕ) [CharP k p] {Δ : Finset σ}
  {φ ψ : MvPolynomial σ k →ₐ[k] MvPolynomial σ k} {g F : MvPolynomial σ k}

omit [Fintype σ] in
/-- An adapted change of coordinates keeps the ideal of a monomial in the coordinates of `Δ`:
`φ((x^s)) ⊆ (x^s)` if `s` is supported in `Δ` and `φ(x_l) = c_l x_l` for each `l ∈ Δ`. -/
theorem map_span_monomial_le_of_adapted (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l)
    {s : σ →₀ ℕ} (hs : ∀ i, i ∉ Δ → s i = 0) :
    Ideal.map φ (Ideal.span {monomial s (1 : k)}) ≤ Ideal.span {monomial s (1 : k)} := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_span_singleton]
  rw [monomial_eq, map_one, one_mul, map_finsuppProd, Finsupp.prod, Finsupp.prod]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun n hn => ?_
  have hnΔ : n ∈ Δ := by
    by_contra h
    exact Finsupp.mem_support_iff.mp hn (hs n h)
  obtain ⟨c, hc⟩ := hφ n hnΔ
  rw [map_pow, hc]
  exact pow_dvd_pow_of_dvd (Dvd.intro_left _ rfl) _

omit [Fintype σ] [DecidableEq σ] in
/-- The residual order of `z^q + P` depends only on the clean part of `P`. -/
theorem residualOrderAlong_cleanPart (q : ℕ) (Δ : Finset σ) (P : MvPolynomial σ k) :
    residualOrderAlong Δ q (cleanPart q P) = residualOrderAlong Δ q P := by
  rw [residualOrderAlong, residualOrderAlong, cleanPart_eq_self (isClean_cleanPart q P)]

omit [Fintype σ] [DecidableEq σ] in
/-- The exponents `r` are supported in `Δ`. -/
theorem divisorExponent_eq_zero_of_notMem (Δ : Finset σ) (P : MvPolynomial σ k) :
    ∀ i, i ∉ Δ → divisorExponent Δ P i = 0 := fun _ hi => divisorExponent_eq_zero hi

omit [DecidableEq σ] [Fintype σ] in
/-- The log-Jacobian ideal of a clean `g ≠ 0` is not `0`: its order `|r| + ρ` is finite. -/
theorem idealOrd_logJacobian_ne_top (hg : g ≠ 0) (hc : IsClean p g) :
    idealOrd (logJacobian Δ g) ≠ ⊤ := by
  rw [idealOrd_logJacobian]
  refine WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ?_⟩
  exact ne_top_of_le_ne_top (residualOrderAlong_ne_top p hg hc)
    (logJacobianOrder_le_residualOrderAlong p hc)

omit [DecidableEq σ] [Fintype σ] in
/-- The clean part of a representative `F` of `g` in the new coordinates is not `0`. -/
theorem cleanPart_ne_zero_of_adapted (hψφ : ∀ h, ψ (φ h) = h) (hg : g ≠ 0) (hc : IsClean p g)
    (hF : logJacobian Δ F = Ideal.map φ (logJacobian Δ g)) : cleanPart p F ≠ 0 := by
  intro h0
  have hbot : logJacobian Δ (0 : MvPolynomial σ k) = ⊥ := by
    simp [logJacobian]
  have h1 : logJacobian Δ g = ⊥ := by
    rw [← map_map_of_inverse hψφ (logJacobian Δ g), ← hF, ← logJacobian_cleanPart p Δ F, h0, hbot,
      Ideal.map_bot]
  exact idealOrd_logJacobian_ne_top p hg hc (by rw [h1, idealOrd_bot])

omit [Fintype σ] in
/-- **The monomial factor does not change** under an adapted change of coordinates. Let `g ≠ 0` be
clean, and let `Θ(F) = φ(Θ(g))`. Then the clean part of `F` has the same exponents `r` along `Δ`
as `g`. -/
theorem divisorExponent_cleanPart_eq_of_adapted (hψφ : ∀ h, ψ (φ h) = h)
    (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l) (hg : g ≠ 0)
    (hc : IsClean p g) (hF : logJacobian Δ F = Ideal.map φ (logJacobian Δ g)) :
    divisorExponent Δ (cleanPart p F) = divisorExponent Δ g := by
  have hψ : ∀ l ∈ Δ, ∃ c : k, ψ (X l) = C c * X l := fun l hl => by
    obtain ⟨c, hc⟩ := hφ l hl
    exact ⟨c⁻¹, exists_eq_C_mul_X_of_inverse hψφ hc⟩
  have hF1 : logJacobian Δ (cleanPart p F) = Ideal.map φ (logJacobian Δ g) := by
    rw [logJacobian_cleanPart, hF]
  have hne := cleanPart_ne_zero_of_adapted p hψφ hg hc hF
  refine le_antisymm ?_ ?_
  · refine le_divisorExponent_of_logJacobian_le p hg hc
      (divisorExponent_eq_zero_of_notMem Δ _) ?_
    rw [← map_map_of_inverse hψφ (logJacobian Δ g), ← hF1]
    exact (Ideal.map_mono (logJacobian_le_span_monomial Δ _)).trans
      (map_span_monomial_le_of_adapted hψ (divisorExponent_eq_zero_of_notMem Δ _))
  · refine le_divisorExponent_of_logJacobian_le p hne (isClean_cleanPart p F)
      (divisorExponent_eq_zero_of_notMem Δ g) ?_
    rw [hF1]
    exact (Ideal.map_mono (logJacobian_le_span_monomial Δ g)).trans
      (map_span_monomial_le_of_adapted hφ (divisorExponent_eq_zero_of_notMem Δ g))

omit [Fintype σ] in
/-- **`ρ` does not change** under an adapted change of coordinates that fixes the origin. Let
`g ≠ 0` be clean, and let `Θ(F) = φ(Θ(g))`. Then `ρ(F_c) = ρ(g)` for the clean part `F_c` of
`F`. -/
theorem logJacobianOrder_cleanPart_eq_of_adapted (hψφ : ∀ h, ψ (φ h) = h)
    (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l)
    (h0φ : ∀ i, constantCoeff (φ (X i)) = 0) (h0ψ : ∀ i, constantCoeff (ψ (X i)) = 0)
    (hg : g ≠ 0) (hc : IsClean p g) (hF : logJacobian Δ F = Ideal.map φ (logJacobian Δ g)) :
    logJacobianOrder Δ (cleanPart p F) = logJacobianOrder Δ g := by
  have h1 : idealOrd (logJacobian Δ (cleanPart p F)) = idealOrd (logJacobian Δ g) := by
    rw [logJacobian_cleanPart, hF, idealOrd_map_eq_of_inverse hψφ h0φ h0ψ]
  rw [idealOrd_logJacobian, idealOrd_logJacobian,
    divisorExponent_cleanPart_eq_of_adapted p hψφ hφ hg hc hF] at h1
  exact WithTop.add_left_cancel (ENat.natCast_ne_top _) h1

omit [Fintype σ] in
/-- **Corollary 3.8 of research note 03, lower bound**, for the adapted coordinates of `k[x]`
that fix the origin: `ρ(g) ≤ d(F)` for the residual order `d(F)` of `z^p + F`, for each `F` with
`Θ(F) = φ(Θ(g))`. -/
theorem logJacobianOrder_le_residualOrderAlong_of_adapted (hψφ : ∀ h, ψ (φ h) = h)
    (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l)
    (h0φ : ∀ i, constantCoeff (φ (X i)) = 0) (h0ψ : ∀ i, constantCoeff (ψ (X i)) = 0)
    (hg : g ≠ 0) (hc : IsClean p g) (hF : logJacobian Δ F = Ideal.map φ (logJacobian Δ g)) :
    logJacobianOrder Δ g ≤ residualOrderAlong Δ p F := by
  have h := logJacobianOrder_le_residualOrderAlong (Δ := Δ) p (isClean_cleanPart p F)
  rwa [logJacobianOrder_cleanPart_eq_of_adapted p hψφ hφ h0φ h0ψ hg hc hF,
    residualOrderAlong_cleanPart] at h

omit [Fintype σ] in
/-- **Corollary 3.8 of research note 03, upper bound**, for the adapted coordinates of `k[x]`
that fix the origin: `d(F) ≤ ρ(g) + 1` for each `F` with `Θ(F) = φ(Θ(g))`. -/
theorem residualOrderAlong_le_logJacobianOrder_add_one_of_adapted (hψφ : ∀ h, ψ (φ h) = h)
    (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l)
    (h0φ : ∀ i, constantCoeff (φ (X i)) = 0) (h0ψ : ∀ i, constantCoeff (ψ (X i)) = 0)
    (hg : g ≠ 0) (hc : IsClean p g) (hF : logJacobian Δ F = Ideal.map φ (logJacobian Δ g)) :
    residualOrderAlong Δ p F ≤ logJacobianOrder Δ g + 1 := by
  have h := residualOrderAlong_le_logJacobianOrder_add_one (Δ := Δ) p (isClean_cleanPart p F)
  rwa [logJacobianOrder_cleanPart_eq_of_adapted p hψφ hφ h0φ h0ψ hg hc hF,
    residualOrderAlong_cleanPart] at h

/-- The representatives of `g` modulo `p`-th powers in the new coordinates:
`Θ(φ(g) + h^p) = φ(Θ(g))`. -/
theorem logJacobian_map_add_pow_eq (hψφ : ∀ h, ψ (φ h) = h) (hφψ : ∀ h, φ (ψ h) = h)
    (hφ : ∀ l ∈ Δ, ∃ c : k, φ (X l) = C c * X l) (g h : MvPolynomial σ k) :
    logJacobian Δ (φ g + h ^ p) = Ideal.map φ (logJacobian Δ g) := by
  rw [logJacobian_add_pow, map_logJacobian_eq_of_adapted hψφ hφψ hφ]

end Corollary

end Singularity
