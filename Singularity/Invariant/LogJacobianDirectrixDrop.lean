/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianDirectrixCaseA

/-!
# `τ_ρ` can go down from case A to case A if `|r| + d = 0` in `k`

Theorem 3.9.1 (`finrank_logJacobianDirectrix_cleanPart_le_of_caseA`) has the hypothesis that
`|r| + d` is not `0` in `k`. This file gives an example where `|r| + d = 0` in `k`, the old and the
new points are of case A, `ρ` stays, and `τ_ρ` goes down (Volume 7, Section 3.9 of the handbook,
Example 3.9.5). So the hypothesis is necessary.

Over `𝔽₂`, the coordinates `(x, y, z, w, u)` are `X 0`, ..., `X 4`. Let `E = V(x y z w)`, so
`Δ = {0, 1, 2, 3}`. Let `g = x z^2 w u^2 + x y z w u^2`. Then `g` is clean and `ord g = 6`. The
exponents are `r = (1, 0, 1, 1, 0)` and `G = (y + z) u^2`, so `|r| = 3`, `d = 3` and
`|r| + d = 6 = 0` in `𝔽₂`.

* The old point. The generators of `Θ̃₀(G)` are `e_x = e_w = G` and `e_y = e_z = y u^2`, since
  `∂_u G = 0`. So `ρ(g) = 3`, the point is of case A, and `T_ρ(g) = {y = z = u = 0}` has
  dimension `2`.
* The new point. Take the `w`-chart with `t_x = 1` and `t_i = 0` for `i ≠ x`. Then `g` goes to
  `w^2 g'` with `g' = w^4 (x + 1) (z^2 + y z) u^2`. The monomial `z^2 w^4 u^2` is a square, so
  `g'_c = w^4 (x z^2 u^2 + (x + 1) y z u^2)`. The new divisor is `V(y z w)`. The exponents are
  `r' = (0, 0, 1, 4, 0)` and `G' = x z u^2 + (x + 1) y u^2`. The generators of `Θ̃₀(G')` are
  `e'_y = e'_z = (x + 1) y u^2`, `e'_w = 4 G' = 0`, and the `x_m ∂_x G'` of order `4`. So
  `ρ(g'_c) = 3`, the point is of case A, and `T_ρ(g'_c) = {y = u = 0}` has dimension `3`.

Thus `τ_ρ` goes down from `3` to `2`.

## Main results

* `tauRhoDropExample_hyp`: the data of the example.
* `tauRhoDropExample_cases`: the old and the new points are of case A.
* `tauRhoDropExample_finrank`, `tauRhoDropExample_codim`: `ρ` stays `3`, and the dimension of
  `T_ρ` goes up from `2` to `3`.

## References

* Volume 7, Section 3.9 of the handbook: Theorem 3.9.1 and Example 3.9.5.
-/

open MvPolynomial Finsupp Module

namespace Singularity

section Example

/-! The data of Example 3.9.5. The coordinates `(x, y, z, w, u)` are `X 0`, ..., `X 4`. -/

local notation "dΔ" => ({0, 1, 2, 3} : Finset (Fin 5))
local notation "dΔ'" => ({1, 2, 3} : Finset (Fin 5))
local notation "dt" => (Pi.single 0 1 : Fin 5 → ZMod 2)
local notation "dg" =>
  (X 0 * X 2 ^ 2 * X 3 * X 4 ^ 2 + X 0 * X 1 * X 2 * X 3 * X 4 ^ 2 : MvPolynomial (Fin 5) (ZMod 2))
local notation "dg'" =>
  (X 3 ^ 4 * (X 0 + 1) * (X 2 ^ 2 + X 1 * X 2) * X 4 ^ 2 : MvPolynomial (Fin 5) (ZMod 2))
local notation "dgc" =>
  (X 3 ^ 4 * (X 0 * X 2 ^ 2 * X 4 ^ 2 + (X 0 + 1) * X 1 * X 2 * X 4 ^ 2) :
    MvPolynomial (Fin 5) (ZMod 2))
local notation "dG" => ((X 1 + X 2) * X 4 ^ 2 : MvPolynomial (Fin 5) (ZMod 2))
local notation "dG'" =>
  (X 0 * X 2 * X 4 ^ 2 + (X 0 + 1) * X 1 * X 4 ^ 2 : MvPolynomial (Fin 5) (ZMod 2))
local notation "dA" => (X 1 * X 4 ^ 2 : MvPolynomial (Fin 5) (ZMod 2))
local notation "dB" => (X 2 * X 4 ^ 2 : MvPolynomial (Fin 5) (ZMod 2))
local notation "dr" => (single 0 1 + single 2 1 + single 3 1 : Fin 5 →₀ ℕ)
local notation "dr'" => (single 2 1 + single 3 4 : Fin 5 →₀ ℕ)
local notation "dv" => (![1, 2, 4] : Fin 3 → Fin 5)
local notation "dv'" => (![1, 4] : Fin 2 → Fin 5)

/-! ### General facts on the data -/

private theorem tdx_mon (a b : Fin 5 →₀ ℕ) :
    monomial (a + b) (1 : ZMod 2) = monomial a 1 * monomial b 1 := by
  rw [monomial_mul_monomial, mul_one]

private theorem tdx_ne {a b : Fin 5 →₀ ℕ} (i : Fin 5) (h : a i ≠ b i) : a ≠ b :=
  fun hab => h (by rw [hab])

private theorem tdx_ord_A : ord dA = ((3 : ℕ) : ℕ∞) := ord_X_mul_X_pow 1 4 2

private theorem tdx_ord_B : ord dB = ((3 : ℕ) : ℕ∞) := ord_X_mul_X_pow 2 4 2

private theorem tdx_hom_A : IsHomogeneous dA 3 :=
  (isHomogeneous_X _ 1).mul (isHomogeneous_X_pow 4 2)

private theorem tdx_hom_B : IsHomogeneous dB 3 :=
  (isHomogeneous_X _ 2).mul (isHomogeneous_X_pow 4 2)

private theorem tdx_ord_AB : ((3 : ℕ) : ℕ∞) ≤ ord (dA + dB) :=
  le_ord_add tdx_ord_A.ge tdx_ord_B.ge

private theorem tdx_lt_X_mul {f : MvPolynomial (Fin 5) (ZMod 2)} (hf : ((3 : ℕ) : ℕ∞) ≤ ord f)
    (m : Fin 5) : ((3 : ℕ) : ℕ∞) < ord (X m * f) :=
  lt_of_lt_of_le (by norm_num) (natCast_succ_le_ord_X_mul hf m)

private theorem tdx_ord_A0 : ord (dA + X 0 * dA) = ((3 : ℕ) : ℕ∞) := by
  rw [ord_add_of_lt (tdx_ord_A ▸ tdx_lt_X_mul tdx_ord_A.ge 0), tdx_ord_A]

private theorem tdx_hc_A0 : homogeneousComponent 3 (dA + X 0 * dA) = dA := by
  rw [map_add, homogeneousComponent_eq_self tdx_hom_A,
    homogeneousComponent_eq_zero_of_lt_ord (tdx_lt_X_mul tdx_ord_A.ge 0), add_zero]

/-- The directrix of `x_i x_j^2` over `𝔽₂` is `{v_i = v_j = 0}`. -/
private theorem tdx_mem_directrix_iff {i j : Fin 5} (hij : i ≠ j) {w : Fin 5 → ZMod 2} :
    w ∈ directrix (X i * X j ^ 2 : MvPolynomial (Fin 5) (ZMod 2)) ↔ w i = 0 ∧ w j = 0 := by
  rw [mem_directrix_iff]
  constructor
  · intro h
    have key : ∀ a b : ZMod 2, (a + w i) * (b + w j) ^ 2 = a * b ^ 2 := by
      intro a b
      have h' := congrArg (MvPolynomial.eval fun o : Option (Fin 5) =>
        Option.elim o (1 : ZMod 2) fun l => if l = i then a else if l = j then b else 0) h
      simpa [translate, hij, Ne.symm hij] using h'
    have h1 := key 0 0
    have h2 := key 0 1
    have h3 := key 1 0
    generalize w i = p at h1 h2 h3 ⊢
    generalize w j = q at h1 h2 h3 ⊢
    revert p q
    decide
  · rintro ⟨hi, hj⟩
    simp [translate, hi, hj]

private theorem tdx_finrank_ker {m : ℕ} (f : Fin m → Fin 5) (hf : Function.Injective f) :
    finrank (ZMod 2) (LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) f)) + m = 5 := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.funLeft (ZMod 2) (ZMod 2) f)
  rw [LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective _ _ f hf),
    finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

private theorem tdx_mem_ker {w : Fin 5 → ZMod 2} :
    w ∈ LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) dv) ↔ w 1 = 0 ∧ w 2 = 0 ∧ w 4 = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1, by simpa using congrFun h 2⟩
  · rintro ⟨h1, h2, h4⟩
    funext k
    fin_cases k <;> simp [h1, h2, h4]

private theorem tdx_mem_ker' {w : Fin 5 → ZMod 2} :
    w ∈ LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) dv') ↔ w 1 = 0 ∧ w 4 = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨h1, h4⟩
    funext k
    fin_cases k <;> simp [h1, h4]

/-! ### The old point -/

private theorem tdx_g_monomials : dg =
    monomial (single 0 1 + single 2 2 + single 3 1 + single 4 2) 1 +
      monomial (single 0 1 + single 1 1 + single 2 1 + single 3 1 + single 4 2) 1 := by
  simp only [tdx_mon, ← X_pow_eq_monomial]
  ring

private theorem tdx_isClean_g : IsClean 2 dg := by
  rw [tdx_g_monomials]
  exact isClean_add (isClean_monomial (fun h => absurd (h 0) (by simp)) _)
    (isClean_monomial (fun h => absurd (h 0) (by simp)) _)

private theorem tdx_g_ne : dg ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval ![1, 0, 1, 1, 1]) h
  simp at this

private theorem tdx_ord_g : ((6 : ℕ) : ℕ∞) ≤ ord dg := by
  refine le_ord_add ?_ ?_
  · rw [ord_mul, ord_mul, ord_mul, ord_X, ord_X, ord_X_pow, ord_X_pow]
    norm_num
  · rw [ord_mul, ord_mul, ord_mul, ord_mul, ord_X, ord_X, ord_X, ord_X, ord_X_pow]
    norm_num

private theorem tdx_monomial_r : (monomial dr 1 : MvPolynomial (Fin 5) (ZMod 2)) =
    X 0 * X 2 * X 3 := by
  simp only [tdx_mon, ← X_pow_eq_monomial, pow_one]

private theorem tdx_g_eq : dg = monomial dr 1 * dG := by
  rw [tdx_monomial_r]
  ring

private theorem tdx_G_monomials : dG =
    monomial (single 1 1 + single 4 2) 1 + monomial (single 2 1 + single 4 2) 1 := by
  simp only [tdx_mon, ← X_pow_eq_monomial]
  ring

private theorem tdx_mem_G1 : (single 1 1 + single 4 2 : Fin 5 →₀ ℕ) ∈ (dG).support := by
  rw [tdx_G_monomials, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tdx_ne (a := single 2 1 + single 4 2) (b := single 1 1 + single 4 2) 1
    (by simp)]

private theorem tdx_mem_G2 : (single 2 1 + single 4 2 : Fin 5 →₀ ℕ) ∈ (dG).support := by
  rw [tdx_G_monomials, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tdx_ne (a := single 1 1 + single 4 2) (b := single 2 1 + single 4 2) 1
    (by simp)]

private theorem tdx_hr : ∀ i, i ∉ dΔ → (dr : Fin 5 →₀ ℕ) i = 0 := by
  intro i hi
  fin_cases i <;> simp at hi ⊢

private theorem tdx_hG : ∀ i ∈ dΔ, ∃ d ∈ (dG).support, d i = 0 := by
  intro i hi
  fin_cases i
  · exact ⟨_, tdx_mem_G1, by simp⟩
  · exact ⟨_, tdx_mem_G2, by simp⟩
  · exact ⟨_, tdx_mem_G1, by simp⟩
  · exact ⟨_, tdx_mem_G1, by simp⟩
  · simp at hi

private theorem tdx_rF : residualFactor dΔ dg = dG := by
  rw [tdx_g_eq]
  exact residualFactor_monomial_mul tdx_hr tdx_hG

private theorem tdx_dE : divisorExponent dΔ dg = dr := by
  have hG0 : dG ≠ 0 := ne_zero_iff.mpr ⟨_, MvPolynomial.mem_support_iff.mp tdx_mem_G1⟩
  have h1 : monomial (divisorExponent dΔ dg) (1 : ZMod 2) * dG = monomial dr 1 * dG := by
    calc _ = dg := by
          rw [← tdx_rF]
          exact monomial_mul_residualFactor _ _
      _ = _ := tdx_g_eq
  exact monomial_left_injective one_ne_zero (mul_right_cancel₀ hG0 h1)

private theorem tdx_deg : degree dr = 3 := by
  rw [map_add, map_add, degree_single, degree_single, degree_single]

private theorem tdx_ord_G : ((3 : ℕ) : ℕ∞) ≤ ord dG := by
  rw [show dG = dA + dB by ring]
  exact tdx_ord_AB

private theorem tdx_e0 : ((dr 0 : ℕ) : ZMod 2) • dG + X 0 * pderiv 0 dG = dA + dB := by
  simp [pderiv_X]
  ring

private theorem tdx_e1 : ((dr 1 : ℕ) : ZMod 2) • dG + X 1 * pderiv 1 dG = dA := by
  simp [pderiv_X]

private theorem tdx_e2 : ((dr 2 : ℕ) : ZMod 2) • dG + X 2 * pderiv 2 dG = dA := by
  simp [pderiv_X]
  linear_combination dB * two_eq_zero_mvPolynomial_zmod (Fin 5)

private theorem tdx_e3 : ((dr 3 : ℕ) : ZMod 2) • dG + X 3 * pderiv 3 dG = dA + dB := by
  simp [pderiv_X]
  ring

private theorem tdx_pd4 : pderiv 4 dG = 0 := by
  conv_lhs => simp [pderiv_X]
  linear_combination (X 1 * X 4 + X 2 * X 4) * two_eq_zero_mvPolynomial_zmod (Fin 5)

private theorem tdx_l4 {l : Fin 5} (hl : l ∉ dΔ) : l = 4 := by
  revert hl
  fin_cases l <;> simp

private theorem tdx_rho : logJacobianOrder dΔ dg = ((3 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, tdx_dE, tdx_rF]
  refine le_antisymm ?_ ?_
  · have hm : ((dr 1 : ℕ) : ZMod 2) • dG + X 1 * pderiv 1 dG ∈ residualLogJacobian dΔ dr dG :=
      Ideal.subset_span (Or.inl ⟨1, by simp, rfl⟩)
    rw [tdx_e1] at hm
    exact (idealOrd_le_ord hm).trans tdx_ord_A.le
  · refine le_idealOrd_span ?_
    rintro s (⟨i, -, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact le_ord_smul_add_X_mul_pderiv tdx_ord_G _ i
    · obtain rfl := tdx_l4 (by simpa using hl)
      dsimp only
      rw [tdx_pd4, ord_zero]
      exact le_top

private theorem tdx_mem_A : monomial dr 1 * dA ∈ logJacobianTangent dΔ dg := by
  have h := X_mul_pderiv_mem_logJacobianTangent (Δ := dΔ) (i := 1) (by simp) dg
  rwa [show X 1 * pderiv 1 dg = monomial dr 1 * dA by
    rw [tdx_g_eq, X_mul_pderiv_monomial_mul, tdx_e1]] at h

private theorem tdx_mem_B : monomial dr 1 * dB ∈ logJacobianTangent dΔ dg := by
  have h := X_mul_pderiv_mem_logJacobianTangent (Δ := dΔ) (i := 0) (by simp) dg
  rw [show X 0 * pderiv 0 dg = monomial dr 1 * (dA + dB) by
    rw [tdx_g_eq, X_mul_pderiv_monomial_mul, tdx_e0]] at h
  have := sub_mem h tdx_mem_A
  rwa [← mul_sub, add_sub_cancel_left] at this

/-- At the old point, `Θ₀(g)` has order `6 = |r| + ρ(g)` (case A). -/
private theorem tdx_caseA : idealOrd (logJacobianTangent dΔ dg) =
    degree (divisorExponent dΔ dg) + logJacobianOrder dΔ dg := by
  rw [tdx_dE, tdx_rho, tdx_deg]
  refine le_antisymm ((idealOrd_le_ord tdx_mem_A).trans (le_of_eq ?_)) ?_
  · rw [ord_mul, ord_monomial one_ne_zero, tdx_deg, tdx_ord_A]
  · refine le_trans (le_of_eq ?_) (le_idealOrd_logJacobianTangent (Δ := dΔ) tdx_ord_g)
    norm_num

/-- The parts of degree `3` of the generators of `Θ̃₀(G)` are in the span of `y u^2` and
`z u^2`. -/
private theorem tdx_gen (s : MvPolynomial (Fin 5) (ZMod 2))
    (hs : s ∈ (fun i => ((dr i : ℕ) : ZMod 2) • dG + X i * pderiv i dG) '' (dΔ : Set (Fin 5)) ∪
      (fun a : Fin 5 × Fin 5 => X a.1 * pderiv a.2 dG) '' {a | a.2 ∉ dΔ}) :
    ((3 : ℕ) : ℕ∞) ≤ ord s ∧
      homogeneousComponent 3 s ∈ Submodule.span (ZMod 2) {dA, dB} := by
  have hAB : homogeneousComponent 3 (dA + dB) ∈ Submodule.span (ZMod 2) {dA, dB} := by
    rw [map_add, homogeneousComponent_eq_self tdx_hom_A, homogeneousComponent_eq_self tdx_hom_B]
    exact add_mem (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  have hA : homogeneousComponent 3 dA ∈ Submodule.span (ZMod 2) {dA, dB} := by
    rw [homogeneousComponent_eq_self tdx_hom_A]
    exact Submodule.subset_span (by simp)
  rcases hs with ⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩
  · refine ⟨le_ord_smul_add_X_mul_pderiv tdx_ord_G _ i, ?_⟩
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simpa using hi
    all_goals dsimp only
    · rw [tdx_e0]
      exact hAB
    · rw [tdx_e1]
      exact hA
    · rw [tdx_e2]
      exact hA
    · rw [tdx_e3]
      exact hAB
  · obtain rfl : l = 4 := tdx_l4 hl
    dsimp only
    rw [tdx_pd4, mul_zero, ord_zero, map_zero]
    exact ⟨le_top, zero_mem _⟩

private theorem tdx_T : logJacobianDirectrix dΔ dg =
    LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) dv) := by
  have hset : ∀ ψ, ψ ∈ logJacobianDirectrixSet dΔ dg ↔
      ord ψ = ((3 : ℕ) : ℕ∞) ∧ monomial dr 1 * ψ ∈ logJacobianTangent dΔ dg := by
    intro ψ
    rw [logJacobianDirectrixSet, Set.mem_ofPred_eq, logJacobianCaseIdeal_of_eq tdx_caseA,
      tdx_dE, tdx_rho]
  have hn : (logJacobianOrder dΔ dg).toNat = 3 := by
    rw [tdx_rho]
    rfl
  refine le_antisymm ?_ ?_
  · intro w hw
    have h1 := logJacobianDirectrix_le ((hset dA).mpr ⟨tdx_ord_A, tdx_mem_A⟩) hw
    have h2 := logJacobianDirectrix_le ((hset dB).mpr ⟨tdx_ord_B, tdx_mem_B⟩) hw
    rw [hn, homogeneousComponent_eq_self tdx_hom_A, tdx_mem_directrix_iff (by decide)] at h1
    rw [hn, homogeneousComponent_eq_self tdx_hom_B, tdx_mem_directrix_iff (by decide)] at h2
    exact tdx_mem_ker.mpr ⟨h1.1, h2.1, h1.2⟩
  · refine le_logJacobianDirectrix fun ψ hψ => ?_
    rw [hset] at hψ
    rw [hn]
    have hψ' := mem_residualLogJacobianTangent (Δ := dΔ) (g := dg) (ψ := ψ)
      (by rw [tdx_dE]; exact hψ.2)
    rw [tdx_dE, tdx_rF] at hψ'
    refine le_directrix_of_mem_span ?_ (homogeneousComponent_mem_of_mem_span tdx_gen hψ')
    rintro s (rfl | rfl) w hw <;> obtain ⟨h1, h2, h4⟩ := tdx_mem_ker.mp hw
    · exact (tdx_mem_directrix_iff (by decide)).mpr ⟨h1, h4⟩
    · exact (tdx_mem_directrix_iff (by decide)).mpr ⟨h2, h4⟩

/-! ### The new point -/

private theorem tdx_pointChart : pointChart 3 dt dg = X 3 ^ 2 * dg' := by
  simp [pointChart]
  ring

private theorem tdx_blowupDivisor : blowupDivisor dΔ 3 dt = dΔ' := by
  decide

private theorem tdx_gc_monomials : dgc =
    monomial (single 0 1 + single 2 2 + single 3 4 + single 4 2) 1 +
      monomial (single 0 1 + single 1 1 + single 2 1 + single 3 4 + single 4 2) 1 +
      monomial (single 1 1 + single 2 1 + single 3 4 + single 4 2) 1 := by
  simp only [tdx_mon, ← X_pow_eq_monomial]
  ring

private theorem tdx_isClean_gc : IsClean 2 dgc := by
  rw [tdx_gc_monomials]
  exact isClean_add (isClean_add (isClean_monomial (fun h => absurd (h 0) (by simp)) _)
    (isClean_monomial (fun h => absurd (h 0) (by simp)) _))
    (isClean_monomial (fun h => absurd (h 1) (by simp)) _)

private theorem tdx_cleanPart : cleanPart 2 dg' = dgc := by
  have h := cleanPart_add_pow 2 1 dgc (X 2 * X 3 ^ 2 * X 4)
  simp only [pow_one] at h
  rw [show dg' = dgc + (X 2 * X 3 ^ 2 * X 4) ^ 2 by ring, h]
  exact cleanPart_eq_self tdx_isClean_gc

private theorem tdx_monomial_r' : (monomial dr' 1 : MvPolynomial (Fin 5) (ZMod 2)) =
    X 2 * X 3 ^ 4 := by
  simp only [tdx_mon, ← X_pow_eq_monomial, pow_one]

private theorem tdx_gc_eq : dgc = monomial dr' 1 * dG' := by
  rw [tdx_monomial_r']
  ring

private theorem tdx_G'_monomials : dG' =
    monomial (single 0 1 + single 2 1 + single 4 2) 1 +
      monomial (single 0 1 + single 1 1 + single 4 2) 1 + monomial (single 1 1 + single 4 2) 1 := by
  simp only [tdx_mon, ← X_pow_eq_monomial]
  ring

private theorem tdx_mem_G'1 : (single 1 1 + single 4 2 : Fin 5 →₀ ℕ) ∈ (dG').support := by
  rw [tdx_G'_monomials, MvPolynomial.mem_support_iff]
  simp [coeff_monomial,
    tdx_ne (a := single 0 1 + single 2 1 + single 4 2) (b := single 1 1 + single 4 2) 0 (by simp),
    tdx_ne (a := single 0 1 + single 1 1 + single 4 2) (b := single 1 1 + single 4 2) 0 (by simp)]

private theorem tdx_mem_G'2 :
    (single 0 1 + single 2 1 + single 4 2 : Fin 5 →₀ ℕ) ∈ (dG').support := by
  rw [tdx_G'_monomials, MvPolynomial.mem_support_iff]
  simp [coeff_monomial,
    tdx_ne (a := single 0 1 + single 1 1 + single 4 2) (b := single 0 1 + single 2 1 + single 4 2)
      2 (by simp),
    tdx_ne (a := single 1 1 + single 4 2) (b := single 0 1 + single 2 1 + single 4 2) 0 (by simp)]

private theorem tdx_hr' : ∀ i, i ∉ dΔ' → (dr' : Fin 5 →₀ ℕ) i = 0 := by
  intro i hi
  fin_cases i <;> simp at hi ⊢

private theorem tdx_hG' : ∀ i ∈ dΔ', ∃ d ∈ (dG').support, d i = 0 := by
  intro i hi
  fin_cases i
  · simp at hi
  · exact ⟨_, tdx_mem_G'2, by simp⟩
  · exact ⟨_, tdx_mem_G'1, by simp⟩
  · exact ⟨_, tdx_mem_G'1, by simp⟩
  · simp at hi

private theorem tdx_rF' : residualFactor dΔ' dgc = dG' := by
  rw [tdx_gc_eq]
  exact residualFactor_monomial_mul tdx_hr' tdx_hG'

private theorem tdx_dE' : divisorExponent dΔ' dgc = dr' := by
  have hG0 : dG' ≠ 0 := ne_zero_iff.mpr ⟨_, MvPolynomial.mem_support_iff.mp tdx_mem_G'1⟩
  have h1 : monomial (divisorExponent dΔ' dgc) (1 : ZMod 2) * dG' = monomial dr' 1 * dG' := by
    calc _ = dgc := by
          rw [← tdx_rF']
          exact monomial_mul_residualFactor _ _
      _ = _ := tdx_gc_eq
  exact monomial_left_injective one_ne_zero (mul_right_cancel₀ hG0 h1)

private theorem tdx_deg' : degree dr' = 5 := by
  rw [map_add, degree_single, degree_single]

private theorem tdx_ord_G' : ((3 : ℕ) : ℕ∞) ≤ ord dG' := by
  rw [show dG' = dA + X 0 * (dA + dB) by ring]
  exact le_ord_add tdx_ord_A.ge (tdx_lt_X_mul tdx_ord_AB 0).le

private theorem tdx_ord_gc : ((8 : ℕ) : ℕ∞) ≤ ord dgc := by
  rw [tdx_gc_eq, ord_mul, ord_monomial one_ne_zero, tdx_deg']
  calc ((8 : ℕ) : ℕ∞) = ((5 : ℕ) : ℕ∞) + ((3 : ℕ) : ℕ∞) := by norm_num
    _ ≤ _ := add_le_add le_rfl tdx_ord_G'

private theorem tdx_e'1 : ((dr' 1 : ℕ) : ZMod 2) • dG' + X 1 * pderiv 1 dG' = dA + X 0 * dA := by
  simp [pderiv_X]
  ring

private theorem tdx_e'2 : ((dr' 2 : ℕ) : ZMod 2) • dG' + X 2 * pderiv 2 dG' = dA + X 0 * dA := by
  simp [pderiv_X]
  linear_combination (X 0 * X 2 * X 4 ^ 2) * two_eq_zero_mvPolynomial_zmod (Fin 5)

private theorem tdx_e'3 : ((dr' 3 : ℕ) : ZMod 2) • dG' + X 3 * pderiv 3 dG' = 0 := by
  rw [show ((dr' 3 : ℕ) : ZMod 2) = 0 by simp; decide, zero_smul, zero_add]
  simp [pderiv_X]

private theorem tdx_pd0' : pderiv 0 dG' = dA + dB := by
  simp [pderiv_X]
  ring

private theorem tdx_pd4' : pderiv 4 dG' = 0 := by
  conv_lhs => simp [pderiv_X]
  linear_combination (X 0 * X 2 * X 4 + (X 0 + 1) * X 1 * X 4) *
    two_eq_zero_mvPolynomial_zmod (Fin 5)

private theorem tdx_l04 {l : Fin 5} (hl : l ∉ dΔ') : l = 0 ∨ l = 4 := by
  revert hl
  fin_cases l <;> simp

private theorem tdx_rho' : logJacobianOrder dΔ' dgc = ((3 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, tdx_dE', tdx_rF']
  refine le_antisymm ?_ ?_
  · have hm : ((dr' 1 : ℕ) : ZMod 2) • dG' + X 1 * pderiv 1 dG' ∈
        residualLogJacobian dΔ' dr' dG' :=
      Ideal.subset_span (Or.inl ⟨1, by simp, rfl⟩)
    rw [tdx_e'1] at hm
    exact (idealOrd_le_ord hm).trans tdx_ord_A0.le
  · refine le_idealOrd_span ?_
    rintro s (⟨i, -, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact le_ord_smul_add_X_mul_pderiv tdx_ord_G' _ i
    · rcases tdx_l04 (by simpa using hl) with rfl | rfl
      · dsimp only
        rw [tdx_pd0']
        exact tdx_ord_AB
      · dsimp only
        rw [tdx_pd4', ord_zero]
        exact le_top

private theorem tdx_mem' : monomial dr' 1 * (dA + X 0 * dA) ∈ logJacobianTangent dΔ' dgc := by
  have h := X_mul_pderiv_mem_logJacobianTangent (Δ := dΔ') (i := 1) (by simp) dgc
  rwa [show X 1 * pderiv 1 dgc = monomial dr' 1 * (dA + X 0 * dA) by
    rw [tdx_gc_eq, X_mul_pderiv_monomial_mul, tdx_e'1]] at h

/-- At the new point, `Θ₀(g'_c)` has order `8 = |r'| + ρ(g'_c)` (case A). -/
private theorem tdx_caseA' : idealOrd (logJacobianTangent dΔ' dgc) =
    degree (divisorExponent dΔ' dgc) + logJacobianOrder dΔ' dgc := by
  rw [tdx_dE', tdx_rho', tdx_deg']
  refine le_antisymm ((idealOrd_le_ord tdx_mem').trans (le_of_eq ?_)) ?_
  · rw [ord_mul, ord_monomial one_ne_zero, tdx_deg', tdx_ord_A0]
  · refine le_trans (le_of_eq ?_) (le_idealOrd_logJacobianTangent (Δ := dΔ') tdx_ord_gc)
    norm_num

/-- The parts of degree `3` of the generators of `Θ̃₀(G')` are multiples of `y u^2`. -/
private theorem tdx_gen' (s : MvPolynomial (Fin 5) (ZMod 2))
    (hs : s ∈ (fun i => ((dr' i : ℕ) : ZMod 2) • dG' + X i * pderiv i dG') '' (dΔ' : Set (Fin 5)) ∪
      (fun a : Fin 5 × Fin 5 => X a.1 * pderiv a.2 dG') '' {a | a.2 ∉ dΔ'}) :
    ((3 : ℕ) : ℕ∞) ≤ ord s ∧ homogeneousComponent 3 s ∈ Submodule.span (ZMod 2) {dA} := by
  rcases hs with ⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩
  · refine ⟨le_ord_smul_add_X_mul_pderiv tdx_ord_G' _ i, ?_⟩
    obtain rfl | rfl | rfl : i = 1 ∨ i = 2 ∨ i = 3 := by simpa using hi
    all_goals dsimp only
    · rw [tdx_e'1, tdx_hc_A0]
      exact Submodule.mem_span_singleton_self _
    · rw [tdx_e'2, tdx_hc_A0]
      exact Submodule.mem_span_singleton_self _
    · rw [tdx_e'3, map_zero]
      exact zero_mem _
  · have hl' : l ∉ dΔ' := hl
    dsimp only
    rcases tdx_l04 hl' with rfl | rfl
    · rw [tdx_pd0']
      refine ⟨(tdx_lt_X_mul tdx_ord_AB a).le, ?_⟩
      rw [homogeneousComponent_eq_zero_of_lt_ord (tdx_lt_X_mul tdx_ord_AB a)]
      exact zero_mem _
    · rw [tdx_pd4', mul_zero, ord_zero, map_zero]
      exact ⟨le_top, zero_mem _⟩

private theorem tdx_T' : logJacobianDirectrix dΔ' dgc =
    LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) dv') := by
  have hset : ∀ ψ, ψ ∈ logJacobianDirectrixSet dΔ' dgc ↔
      ord ψ = ((3 : ℕ) : ℕ∞) ∧ monomial dr' 1 * ψ ∈ logJacobianTangent dΔ' dgc := by
    intro ψ
    rw [logJacobianDirectrixSet, Set.mem_ofPred_eq, logJacobianCaseIdeal_of_eq tdx_caseA',
      tdx_dE', tdx_rho']
  have hn : (logJacobianOrder dΔ' dgc).toNat = 3 := by
    rw [tdx_rho']
    rfl
  refine le_antisymm ?_ ?_
  · intro w hw
    have h1 := logJacobianDirectrix_le ((hset _).mpr ⟨tdx_ord_A0, tdx_mem'⟩) hw
    rw [hn, tdx_hc_A0, tdx_mem_directrix_iff (by decide)] at h1
    exact tdx_mem_ker'.mpr h1
  · refine le_logJacobianDirectrix fun ψ hψ => ?_
    rw [hset] at hψ
    rw [hn]
    have hψ' := mem_residualLogJacobianTangent (Δ := dΔ') (g := dgc) (ψ := ψ)
      (by rw [tdx_dE']; exact hψ.2)
    rw [tdx_dE', tdx_rF'] at hψ'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (homogeneousComponent_mem_of_mem_span tdx_gen' hψ')
    rw [← hc]
    intro w hw
    exact directrix_le_directrix_smul c _
      ((tdx_mem_directrix_iff (by decide)).mpr (tdx_mem_ker'.mp hw))

/-! ### The results -/

/-- **Example 3.9.5, the data** (Volume 7, Section 3.9 of the handbook). Over `𝔽₂`, let
`g = x z^2 w u^2 + x y z w u^2` and `E = V(x y z w)`. Then `g ≠ 0`, `g` is clean for `p = 2`, and
`ord g ≥ 2`. In the `w`-chart with `t_x = 1` and `t_i = 0` for `i ≠ x`, `g` goes to `w^2 g'`
with `g' = w^4 (x + 1) (z^2 + y z) u^2`. The new divisor is `V(y z w)`, and
`g'_c = w^4 (x z^2 u^2 + (x + 1) y z u^2)`. The exponents of `g` are `r = (1, 0, 1, 1, 0)`, and
`G = (y + z) u^2`. So `|r| + d = 6 = 0` in `𝔽₂`, and the hypothesis `|r| + d ≠ 0` of
Theorem 3.9.1 fails. -/
theorem tauRhoDropExample_hyp :
    dg ≠ 0 ∧ IsClean 2 dg ∧ ((2 : ℕ) : ℕ∞) ≤ ord dg ∧ pointChart 3 dt dg = X 3 ^ 2 * dg' ∧
      blowupDivisor dΔ 3 dt = dΔ' ∧ cleanPart 2 dg' = dgc ∧
      divisorExponent dΔ dg = dr ∧ residualFactor dΔ dg = dG ∧
      ((degree (divisorExponent dΔ dg) + 3 : ℕ) : ZMod 2) = 0 := by
  refine ⟨tdx_g_ne, tdx_isClean_g, le_trans (by norm_num) tdx_ord_g, tdx_pointChart,
    tdx_blowupDivisor, tdx_cleanPart, tdx_dE, tdx_rF, ?_⟩
  rw [tdx_dE, tdx_deg]
  rfl

/-- **Example 3.9.5, the cases** (Volume 7, Section 3.9 of the handbook). Over `𝔽₂`, let
`g = x z^2 w u^2 + x y z w u^2` and `E = V(x y z w)`. The point is of case A: the order of `Θ₀(g)`
is `|r| + ρ(g)`. In the `w`-chart with `t_x = 1` and `t_i = 0` for `i ≠ x`, the new point is of
case A too: the order of `Θ₀(g'_c)` is `|r'| + ρ(g'_c)`. -/
theorem tauRhoDropExample_cases :
    idealOrd (logJacobianTangent dΔ dg) =
        degree (divisorExponent dΔ dg) + logJacobianOrder dΔ dg ∧
      idealOrd (logJacobianTangent (blowupDivisor dΔ 3 dt) (cleanPart 2 dg')) =
        degree (divisorExponent (blowupDivisor dΔ 3 dt) (cleanPart 2 dg')) +
          logJacobianOrder (blowupDivisor dΔ 3 dt) (cleanPart 2 dg') := by
  rw [tdx_blowupDivisor, tdx_cleanPart]
  exact ⟨tdx_caseA, tdx_caseA'⟩

/-- **Example 3.9.5: the hypothesis `|r| + d ≠ 0` of Theorem 3.9.1 is necessary** (Volume 7,
Section 3.9 of the handbook). Over `𝔽₂`, let `g = x z^2 w u^2 + x y z w u^2` and
`E = V(x y z w)`. Then `ρ(g) = 3` and `T_ρ(g) = {y = z = u = 0}` has dimension `2`. In the
`w`-chart with `t_x = 1` and `t_i = 0` for `i ≠ x`, `ρ(g'_c) = 3`, and `T_ρ(g'_c) = {y = u = 0}`
has dimension `3`. Both points are of case A (`tauRhoDropExample_cases`). So `τ_ρ` goes down from
case A to case A. -/
theorem tauRhoDropExample_finrank :
    logJacobianOrder dΔ dg = 3 ∧
      logJacobianOrder (blowupDivisor dΔ 3 dt) (cleanPart 2 dg') = 3 ∧
      finrank (ZMod 2) (logJacobianDirectrix dΔ dg) = 2 ∧
      finrank (ZMod 2) (logJacobianDirectrix (blowupDivisor dΔ 3 dt) (cleanPart 2 dg')) = 3 := by
  rw [tdx_blowupDivisor, tdx_cleanPart, tdx_T, tdx_T']
  refine ⟨by exact_mod_cast tdx_rho, by exact_mod_cast tdx_rho', ?_, ?_⟩
  · have := tdx_finrank_ker dv (by decide)
    omega
  · have := tdx_finrank_ker dv' (by decide)
    omega

/-- **Example 3.9.5, the form with the codimension** (Volume 7, Section 3.9 of the handbook).
Over `𝔽₂`, let `g = x z^2 w u^2 + x y z w u^2` and `E = V(x y z w)`. Then `τ_ρ(g) = 3`, and in the
`w`-chart with `t_x = 1` and `t_i = 0` for `i ≠ x`, `τ_ρ(g'_c) = 2`. -/
theorem tauRhoDropExample_codim :
    logJacobianDirectrixCodim dΔ dg = 3 ∧
      logJacobianDirectrixCodim (blowupDivisor dΔ 3 dt) (cleanPart 2 dg') = 2 := by
  obtain ⟨-, -, h1, h2⟩ := tauRhoDropExample_finrank
  unfold logJacobianDirectrixCodim
  rw [h1, h2, Fintype.card_fin]
  exact ⟨rfl, rfl⟩

end Example

end Singularity
