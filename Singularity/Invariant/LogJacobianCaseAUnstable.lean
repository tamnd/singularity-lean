/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianCaseAStable

/-!
# The first case is not stable if `p` divides `|r| + d`

Proposition 3.9.7 (`idealOrd_logJacobianTangent_cleanPart_of_caseA`) has the hypothesis `hpd`
that `|r| + d` is not `0` in `k`. This file gives an example where `|r| + d = 0` in `k`, the old
point is of case A, `ρ` stays, and the new point is of case B (Volume 7, Section 3.9 of the
handbook, Example 3.9.9). So the hypothesis `hpd` is necessary.

Over `𝔽₃`, the coordinates `(x, y, z)` are `X 0`, `X 1` and `X 2`. Let `E = V(x z)`, so
`Δ = {0, 2}`. Let `g = x^3 y^2 z^3 + 2 x^2 y^3 z`. Then `g` is clean and `ord g = 6`. The exponents
are `r = (2, 0, 1)` and `G = x y^2 z^2 + 2 y^3`, so `|r| = 3`, `d = ord G = 3` and
`|r| + d = 6 = 0` in `𝔽₃`.

* The old point. The generators of `Θ̃₀(G)` are `e_x = y^3`, `e_z = 2 y^3`, and the
  `x_m ∂_y G = 2 x_m x y z^2` of order `5`. So `ρ(g) = 3`, the order of `Θ₀(g)` is `|r| + 3`, the
  point is of case A, and `T_ρ(g) = {y = 0}` has dimension `2`.
* The new point. Take the `x`-chart with `t_z = 1` and `t_x = t_y = 0`. Then `g` goes to `x^3 g'`
  with `g' = x^5 y^2 (z + 1)^3 + 2 x^3 y^3 (z + 1)`. The monomial `2 x^3 y^3 = (2 x y)^3` is a cube,
  so `g'_c = x^5 y^2 z^3 + x^5 y^2 + 2 x^3 y^3 z`. The new divisor is `V(x)`. The exponents are
  `r' = (3, 0, 0)` and `G' = x^2 y^2 (z^3 + 1) + 2 y^3 z`. Each monomial of `g'_c` has degree at
  least `7`, and `y ∂_z g'_c = 2 x^3 y^4`. So the order of `Θ₀(g'_c)` is `7 = |r'| + 4`. Also
  `∂_y G' = 2 x^2 y (z^3 + 1)` and `∂_z G' = 2 y^3` have order `3`. So `ρ(g'_c) = 3`, the point is
  of case B, and `T_ρ(g'_c) = {x = y = 0}` has dimension `1`.

The proof of Proposition 3.9.7 fails here because the Euler element is `6 G = 0` in `𝔽₃`.

## Main results

* `caseAToCaseBExample_hyp`: the data of the example.
* `caseAToCaseBExample_cases`: the old point is of case A, and the new point is of case B.
* `caseAToCaseBExample_rho`: `ρ` stays `3`.
* `caseAToCaseBExample_not_caseA`: the hypothesis `hpd` and the conclusion of Proposition 3.9.7
  both fail.
* `caseAToCaseBExample_finrank`, `caseAToCaseBExample_codim`: the dimension of `T_ρ` goes down
  from `2` to `1`, so `τ_ρ` goes up from `1` to `2`.

## References

* Volume 7, Section 3.9 of the handbook: Proposition 3.9.7 and Example 3.9.9.
-/

open MvPolynomial Finsupp Module

namespace Singularity

section Example

/-! The data of Example 3.9.9. The coordinates `(x, y, z)` are `X 0`, `X 1` and `X 2`. -/

local notation "dΔ" => ({0, 2} : Finset (Fin 3))
local notation "dΔ'" => ({0} : Finset (Fin 3))
local notation "dt" => (Pi.single 2 1 : Fin 3 → ZMod 3)
local notation "dg" =>
  (X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 3 + 2 * X 0 ^ 2 * X 1 ^ 3 * X 2 : MvPolynomial (Fin 3) (ZMod 3))
local notation "dg'" =>
  (X 0 ^ 5 * X 1 ^ 2 * (X 2 + 1) ^ 3 + 2 * X 0 ^ 3 * X 1 ^ 3 * (X 2 + 1) :
    MvPolynomial (Fin 3) (ZMod 3))
local notation "dgc" =>
  (X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 3 + X 0 ^ 5 * X 1 ^ 2 + 2 * X 0 ^ 3 * X 1 ^ 3 * X 2 :
    MvPolynomial (Fin 3) (ZMod 3))
local notation "dG" => (X 0 * X 1 ^ 2 * X 2 ^ 2 + 2 * X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 3))
local notation "dG'" =>
  (X 0 ^ 2 * X 1 ^ 2 * (X 2 ^ 3 + 1) + 2 * X 1 ^ 3 * X 2 : MvPolynomial (Fin 3) (ZMod 3))
local notation "dP" => (X 1 * X 0 ^ 2 : MvPolynomial (Fin 3) (ZMod 3))
local notation "dψ" => (X 1 * X 0 ^ 2 + X 1 * X 0 ^ 2 * X 2 ^ 3 : MvPolynomial (Fin 3) (ZMod 3))
local notation "dr" => (single 0 2 + single 2 1 : Fin 3 →₀ ℕ)
local notation "dr'" => (single 0 3 : Fin 3 →₀ ℕ)
local notation "dv" => (![1] : Fin 1 → Fin 3)
local notation "dv'" => (![0, 1] : Fin 2 → Fin 3)

/-! ### General facts on the data -/

private theorem tcb_three : (3 : MvPolynomial (Fin 3) (ZMod 3)) = 0 :=
  three_eq_zero_mvPolynomial_zmod (Fin 3)

private theorem tcb_two : (2 : MvPolynomial (Fin 3) (ZMod 3)) = C 2 :=
  (map_ofNat C 2).symm

private theorem tcb_pd_two (i : Fin 3) : pderiv i (2 : MvPolynomial (Fin 3) (ZMod 3)) = 0 := by
  rw [tcb_two, pderiv_C]

private theorem tcb_ord_two : ord (2 : MvPolynomial (Fin 3) (ZMod 3)) = 0 := by
  rw [tcb_two, ord_C (by decide)]

private theorem tcb_ord_two_mul (f : MvPolynomial (Fin 3) (ZMod 3)) : ord (2 * f) = ord f := by
  rw [ord_mul, tcb_ord_two, zero_add]

private theorem tcb_hc_two_mul (n : ℕ) (f : MvPolynomial (Fin 3) (ZMod 3)) :
    homogeneousComponent n (2 * f) = (2 : ZMod 3) • homogeneousComponent n f := by
  rw [tcb_two, C_mul', map_smul]

private theorem tcb_mon (a b : Fin 3 →₀ ℕ) :
    monomial (a + b) (1 : ZMod 3) = monomial a 1 * monomial b 1 := by
  rw [monomial_mul_monomial, mul_one]

private theorem tcb_mon2 (a : Fin 3 →₀ ℕ) : monomial a (2 : ZMod 3) = 2 * monomial a 1 := by
  rw [tcb_two, C_mul_monomial, mul_one]

private theorem tcb_ne {a b : Fin 3 →₀ ℕ} (i : Fin 3) (h : a i ≠ b i) : a ≠ b :=
  fun hab => h (by rw [hab])

private theorem tcb_ord_P : ord dP = ((3 : ℕ) : ℕ∞) := ord_X_mul_X_pow 1 0 2

private theorem tcb_hom_P : IsHomogeneous dP 3 :=
  (isHomogeneous_X _ 1).mul (isHomogeneous_X_pow 0 2)

private theorem tcb_lt_P : ((3 : ℕ) : ℕ∞) < ord (X 1 * X 0 ^ 2 * X 2 ^ 3 :
    MvPolynomial (Fin 3) (ZMod 3)) := by
  rw [ord_mul, tcb_ord_P, ord_X_pow]
  norm_num

private theorem tcb_ord_ψ : ord dψ = ((3 : ℕ) : ℕ∞) := by
  rw [ord_add_of_lt (by rw [tcb_ord_P]; exact tcb_lt_P), tcb_ord_P]

private theorem tcb_hc_ψ : homogeneousComponent 3 dψ = dP := by
  rw [map_add, homogeneousComponent_eq_self tcb_hom_P,
    homogeneousComponent_eq_zero_of_lt_ord tcb_lt_P, add_zero]

private theorem tcb_hc_Y : homogeneousComponent 3 (X 1 ^ 3 : MvPolynomial (Fin 3) (ZMod 3)) =
    X 1 ^ 3 :=
  homogeneousComponent_eq_self (isHomogeneous_X_pow 1 3)

/-- The directrix of `x_i x_j^2` over `𝔽₃` is `{v_i = v_j = 0}`. -/
private theorem tcb_mem_directrix_iff {i j : Fin 3} (hij : i ≠ j) {w : Fin 3 → ZMod 3} :
    w ∈ directrix (X i * X j ^ 2 : MvPolynomial (Fin 3) (ZMod 3)) ↔ w i = 0 ∧ w j = 0 := by
  rw [mem_directrix_iff]
  constructor
  · intro h
    have key : ∀ a b : ZMod 3, (a + w i) * (b + w j) ^ 2 = a * b ^ 2 := by
      intro a b
      have h' := congrArg (MvPolynomial.eval fun o : Option (Fin 3) =>
        Option.elim o (1 : ZMod 3) fun l => if l = i then a else if l = j then b else 0) h
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

private theorem tcb_finrank_ker {m : ℕ} (f : Fin m → Fin 3) (hf : Function.Injective f) :
    finrank (ZMod 3) (LinearMap.ker (LinearMap.funLeft (ZMod 3) (ZMod 3) f)) + m = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.funLeft (ZMod 3) (ZMod 3) f)
  rw [LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective _ _ f hf),
    finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

private theorem tcb_mem_ker {w : Fin 3 → ZMod 3} :
    w ∈ LinearMap.ker (LinearMap.funLeft (ZMod 3) (ZMod 3) dv) ↔ w 1 = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    simpa using congrFun h 0
  · intro h1
    funext k
    fin_cases k
    simp [h1]

private theorem tcb_mem_ker' {w : Fin 3 → ZMod 3} :
    w ∈ LinearMap.ker (LinearMap.funLeft (ZMod 3) (ZMod 3) dv') ↔ w 0 = 0 ∧ w 1 = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext k
    fin_cases k <;> simp [h0, h1]

/-! ### The old point -/

private theorem tcb_g_monomials : dg =
    monomial (single 0 3 + single 1 2 + single 2 3) 1 +
      monomial (single 0 2 + single 1 3 + single 2 1) 2 := by
  simp only [tcb_mon2, tcb_mon, ← X_pow_eq_monomial]
  ring

private theorem tcb_isClean_g : IsClean 3 dg := by
  rw [tcb_g_monomials]
  exact isClean_add (isClean_monomial (fun h => absurd (h 1) (by norm_num)) _)
    (isClean_monomial (fun h => absurd (h 0) (by norm_num)) _)

private theorem tcb_monomial_r : (monomial dr 1 : MvPolynomial (Fin 3) (ZMod 3)) =
    X 0 ^ 2 * X 2 := by
  simp only [tcb_mon, ← X_pow_eq_monomial, pow_one]

private theorem tcb_g_eq : dg = monomial dr 1 * dG := by
  rw [tcb_monomial_r]
  ring

private theorem tcb_G_monomials : dG =
    monomial (single 0 1 + single 1 2 + single 2 2) 1 + monomial (single 1 3) 2 := by
  simp only [tcb_mon2, tcb_mon, ← X_pow_eq_monomial]
  ring

private theorem tcb_mem_G : (single 1 3 : Fin 3 →₀ ℕ) ∈ (dG).support := by
  rw [tcb_G_monomials, MvPolynomial.mem_support_iff]
  simp [coeff_monomial, tcb_ne (a := single 0 1 + single 1 2 + single 2 2) (b := single 1 3) 0
    (by simp)]
  decide

private theorem tcb_hr : ∀ i, i ∉ dΔ → (dr : Fin 3 →₀ ℕ) i = 0 := by
  intro i hi
  fin_cases i <;> simp at hi ⊢

private theorem tcb_hG : ∀ i ∈ dΔ, ∃ d ∈ (dG).support, d i = 0 := by
  intro i hi
  fin_cases i
  · exact ⟨_, tcb_mem_G, by simp⟩
  · simp at hi
  · exact ⟨_, tcb_mem_G, by simp⟩

private theorem tcb_rF : residualFactor dΔ dg = dG := by
  rw [tcb_g_eq]
  exact residualFactor_monomial_mul tcb_hr tcb_hG

private theorem tcb_dE : divisorExponent dΔ dg = dr := by
  have hG0 : dG ≠ 0 := ne_zero_iff.mpr ⟨_, MvPolynomial.mem_support_iff.mp tcb_mem_G⟩
  have h1 : monomial (divisorExponent dΔ dg) (1 : ZMod 3) * dG = monomial dr 1 * dG := by
    calc _ = dg := by
          rw [← tcb_rF]
          exact monomial_mul_residualFactor _ _
      _ = _ := tcb_g_eq
  exact monomial_left_injective one_ne_zero (mul_right_cancel₀ hG0 h1)

private theorem tcb_deg : degree dr = 3 := by
  rw [map_add, degree_single, degree_single]

private theorem tcb_ord_G : ord dG = ((3 : ℕ) : ℕ∞) := by
  rw [add_comm, ord_add_of_lt, tcb_ord_two_mul, ord_X_pow]
  rw [tcb_ord_two_mul, ord_X_pow, ord_mul, ord_mul, ord_X, ord_X_pow, ord_X_pow]
  norm_num

private theorem tcb_ord_g : ord dg = ((6 : ℕ) : ℕ∞) := by
  rw [tcb_g_eq, ord_mul, ord_monomial one_ne_zero, tcb_deg, tcb_ord_G]
  norm_num

private theorem tcb_g_ne : dg ≠ 0 := by
  intro h
  have := tcb_ord_g
  rw [h, ord_zero] at this
  exact ENat.top_ne_natCast 6 this

private theorem tcb_e0 : ((dr 0 : ℕ) : ZMod 3) • dG + X 0 * pderiv 0 dG = X 1 ^ 3 := by
  rw [show ((dr 0 : ℕ) : ZMod 3) = 2 by simp, smul_eq_C_mul, ← tcb_two]
  simp [pderiv_X, tcb_pd_two]
  linear_combination (X 0 * X 1 ^ 2 * X 2 ^ 2 + X 1 ^ 3) * tcb_three

private theorem tcb_e2 : ((dr 2 : ℕ) : ZMod 3) • dG + X 2 * pderiv 2 dG = 2 * X 1 ^ 3 := by
  simp [pderiv_X, tcb_pd_two]
  linear_combination (X 0 * X 1 ^ 2 * X 2 ^ 2) * tcb_three

private theorem tcb_pd1 : pderiv 1 dG = 2 * (X 0 * X 1 * X 2 ^ 2) := by
  simp [pderiv_X, tcb_pd_two]
  linear_combination (2 * X 1 ^ 2) * tcb_three

private theorem tcb_l1 {l : Fin 3} (hl : l ∉ dΔ) : l = 1 := by
  revert hl
  fin_cases l <;> simp

private theorem tcb_lt_pd1 (a : Fin 3) : ((3 : ℕ) : ℕ∞) < ord (X a * pderiv 1 dG) := by
  simp only [tcb_pd1, ord_mul, ord_X, ord_X_pow, tcb_ord_two]
  norm_num

private theorem tcb_rho : logJacobianOrder dΔ dg = ((3 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, tcb_dE, tcb_rF]
  refine le_antisymm ?_ ?_
  · have hm : ((dr 0 : ℕ) : ZMod 3) • dG + X 0 * pderiv 0 dG ∈ residualLogJacobian dΔ dr dG :=
      Ideal.subset_span (Or.inl ⟨0, by simp, rfl⟩)
    rw [tcb_e0] at hm
    exact (idealOrd_le_ord hm).trans (ord_X_pow 1 3).le
  · refine le_idealOrd_span ?_
    rintro s (⟨i, -, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact le_ord_smul_add_X_mul_pderiv tcb_ord_G.ge _ i
    · obtain rfl := tcb_l1 (by simpa using hl)
      dsimp only
      rw [tcb_pd1, tcb_ord_two_mul, ord_mul, ord_mul, ord_X, ord_X, ord_X_pow]
      norm_num

private theorem tcb_mem_Y : monomial dr 1 * X 1 ^ 3 ∈ logJacobianTangent dΔ dg := by
  have h := X_mul_pderiv_mem_logJacobianTangent (Δ := dΔ) (i := 0) (by simp) dg
  rwa [show X 0 * pderiv 0 dg = monomial dr 1 * X 1 ^ 3 by
    rw [tcb_g_eq, X_mul_pderiv_monomial_mul, tcb_e0]] at h

/-- At the old point, `Θ₀(g)` has order `6 = |r| + ρ(g)` (case A). -/
private theorem tcb_caseA : idealOrd (logJacobianTangent dΔ dg) =
    degree (divisorExponent dΔ dg) + logJacobianOrder dΔ dg := by
  rw [tcb_dE, tcb_rho, tcb_deg]
  refine le_antisymm ((idealOrd_le_ord tcb_mem_Y).trans (le_of_eq ?_)) ?_
  · rw [ord_mul, ord_monomial one_ne_zero, tcb_deg, ord_X_pow]
  · refine le_trans (le_of_eq ?_) (le_idealOrd_logJacobianTangent (Δ := dΔ) tcb_ord_g.ge)
    norm_num

/-- The parts of degree `3` of the generators of `Θ̃₀(G)` are multiples of `y^3`. -/
private theorem tcb_gen (s : MvPolynomial (Fin 3) (ZMod 3))
    (hs : s ∈ (fun i => ((dr i : ℕ) : ZMod 3) • dG + X i * pderiv i dG) '' (dΔ : Set (Fin 3)) ∪
      (fun a : Fin 3 × Fin 3 => X a.1 * pderiv a.2 dG) '' {a | a.2 ∉ dΔ}) :
    ((3 : ℕ) : ℕ∞) ≤ ord s ∧ homogeneousComponent 3 s ∈ Submodule.span (ZMod 3) {X 1 ^ 3} := by
  rcases hs with ⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩
  · refine ⟨le_ord_smul_add_X_mul_pderiv tcb_ord_G.ge _ i, ?_⟩
    obtain rfl | rfl : i = 0 ∨ i = 2 := by simpa using hi
    all_goals dsimp only
    · rw [tcb_e0, tcb_hc_Y]
      exact Submodule.mem_span_singleton_self _
    · rw [tcb_e2, tcb_hc_two_mul, tcb_hc_Y]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · obtain rfl : l = 1 := tcb_l1 hl
    dsimp only
    refine ⟨(tcb_lt_pd1 a).le, ?_⟩
    rw [homogeneousComponent_eq_zero_of_lt_ord (tcb_lt_pd1 a)]
    exact zero_mem _

private theorem tcb_T : logJacobianDirectrix dΔ dg =
    LinearMap.ker (LinearMap.funLeft (ZMod 3) (ZMod 3) dv) := by
  have hset : ∀ ψ, ψ ∈ logJacobianDirectrixSet dΔ dg ↔
      ord ψ = ((3 : ℕ) : ℕ∞) ∧ monomial dr 1 * ψ ∈ logJacobianTangent dΔ dg := by
    intro ψ
    rw [logJacobianDirectrixSet, Set.mem_ofPred_eq, logJacobianCaseIdeal_of_eq tcb_caseA,
      tcb_dE, tcb_rho]
  have hn : (logJacobianOrder dΔ dg).toNat = 3 := by
    rw [tcb_rho]
    rfl
  refine le_antisymm ?_ ?_
  · intro w hw
    have h1 := logJacobianDirectrix_le ((hset _).mpr ⟨ord_X_pow 1 3, tcb_mem_Y⟩) hw
    rw [hn, tcb_hc_Y, mem_directrix_X_pow_iff (by norm_num)] at h1
    exact tcb_mem_ker.mpr h1
  · refine le_logJacobianDirectrix fun ψ hψ => ?_
    rw [hset] at hψ
    rw [hn]
    have hψ' := mem_residualLogJacobianTangent (Δ := dΔ) (g := dg) (ψ := ψ)
      (by rw [tcb_dE]; exact hψ.2)
    rw [tcb_dE, tcb_rF] at hψ'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (homogeneousComponent_mem_of_mem_span tcb_gen hψ')
    rw [← hc]
    intro w hw
    exact directrix_le_directrix_smul c _
      ((mem_directrix_X_pow_iff (by norm_num)).mpr (tcb_mem_ker.mp hw))

/-! ### The new point -/

private theorem tcb_pointChart : pointChart 0 dt dg = X 0 ^ 3 * dg' := by
  simp [pointChart, map_ofNat]
  ring

private theorem tcb_blowupDivisor : blowupDivisor dΔ 0 dt = dΔ' := by
  decide

private theorem tcb_gc_monomials : dgc =
    monomial (single 0 5 + single 1 2 + single 2 3) 1 + monomial (single 0 5 + single 1 2) 1 +
      monomial (single 0 3 + single 1 3 + single 2 1) 2 := by
  simp only [tcb_mon2, tcb_mon, ← X_pow_eq_monomial]
  ring

private theorem tcb_isClean_gc : IsClean 3 dgc := by
  rw [tcb_gc_monomials]
  exact isClean_add (isClean_add (isClean_monomial (fun h => absurd (h 1) (by norm_num)) _)
    (isClean_monomial (fun h => absurd (h 1) (by norm_num)) _))
    (isClean_monomial (fun h => absurd (h 2) (by norm_num)) _)

private theorem tcb_cleanPart : cleanPart 3 dg' = dgc := by
  have h := cleanPart_add_pow 3 1 dgc (2 * X 0 * X 1)
  simp only [pow_one] at h
  rw [show dg' = dgc + (2 * X 0 * X 1) ^ 3 by
    linear_combination (X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 5 * X 1 ^ 2 * X 2 -
      2 * X 0 ^ 3 * X 1 ^ 3) * tcb_three, h]
  exact cleanPart_eq_self tcb_isClean_gc

private theorem tcb_monomial_r' : (monomial dr' 1 : MvPolynomial (Fin 3) (ZMod 3)) = X 0 ^ 3 :=
  X_pow_eq_monomial.symm

private theorem tcb_gc_eq : dgc = monomial dr' 1 * dG' := by
  rw [tcb_monomial_r']
  ring

private theorem tcb_G'_monomials : dG' =
    monomial (single 0 2 + single 1 2 + single 2 3) 1 + monomial (single 0 2 + single 1 2) 1 +
      monomial (single 1 3 + single 2 1) 2 := by
  simp only [tcb_mon2, tcb_mon, ← X_pow_eq_monomial]
  ring

private theorem tcb_mem_G' : (single 1 3 + single 2 1 : Fin 3 →₀ ℕ) ∈ (dG').support := by
  rw [tcb_G'_monomials, MvPolynomial.mem_support_iff]
  simp [coeff_monomial,
    tcb_ne (a := single 0 2 + single 1 2 + single 2 3) (b := single 1 3 + single 2 1) 0 (by simp),
    tcb_ne (a := single 0 2 + single 1 2) (b := single 1 3 + single 2 1) 0 (by simp)]
  decide

private theorem tcb_hr' : ∀ i, i ∉ dΔ' → (dr' : Fin 3 →₀ ℕ) i = 0 := by
  intro i hi
  fin_cases i <;> simp at hi ⊢

private theorem tcb_hG' : ∀ i ∈ dΔ', ∃ d ∈ (dG').support, d i = 0 := by
  intro i hi
  obtain rfl : i = 0 := by simpa using hi
  exact ⟨_, tcb_mem_G', by simp⟩

private theorem tcb_rF' : residualFactor dΔ' dgc = dG' := by
  rw [tcb_gc_eq]
  exact residualFactor_monomial_mul tcb_hr' tcb_hG'

private theorem tcb_dE' : divisorExponent dΔ' dgc = dr' := by
  have hG0 : dG' ≠ 0 := ne_zero_iff.mpr ⟨_, MvPolynomial.mem_support_iff.mp tcb_mem_G'⟩
  have h1 : monomial (divisorExponent dΔ' dgc) (1 : ZMod 3) * dG' = monomial dr' 1 * dG' := by
    calc _ = dgc := by
          rw [← tcb_rF']
          exact monomial_mul_residualFactor _ _
      _ = _ := tcb_gc_eq
  exact monomial_left_injective one_ne_zero (mul_right_cancel₀ hG0 h1)

private theorem tcb_deg' : degree dr' = 3 :=
  degree_single 0 3

private theorem tcb_ord_G' : ((4 : ℕ) : ℕ∞) ≤ ord dG' := by
  refine le_ord_add ?_ ?_
  · rw [ord_mul, ord_mul, ord_X_pow, ord_X_pow]
    exact le_trans (by norm_num) le_self_add
  · simp only [ord_mul, ord_X, ord_X_pow, tcb_ord_two]
    norm_num

private theorem tcb_ord_gc : ((7 : ℕ) : ℕ∞) ≤ ord dgc := by
  rw [tcb_gc_eq, ord_mul, ord_monomial one_ne_zero, tcb_deg']
  calc ((7 : ℕ) : ℕ∞) = ((3 : ℕ) : ℕ∞) + ((4 : ℕ) : ℕ∞) := by norm_num
    _ ≤ _ := add_le_add le_rfl tcb_ord_G'

private theorem tcb_pd1' : pderiv 1 dG' = 2 * dψ := by
  simp [pderiv_X, tcb_pd_two]
  linear_combination (2 * X 1 ^ 2 * X 2) * tcb_three

private theorem tcb_pd2' : pderiv 2 dG' = 2 * X 1 ^ 3 := by
  simp [pderiv_X, tcb_pd_two]
  linear_combination tcb_three

private theorem tcb_pd1c : pderiv 1 dgc = 2 * (X 0 ^ 3 * dψ) := by
  simp [pderiv_X, tcb_pd_two]
  linear_combination (2 * X 0 ^ 3 * X 1 ^ 2 * X 2) * tcb_three

private theorem tcb_pd2c : pderiv 2 dgc = 2 * (X 0 ^ 3 * X 1 ^ 3) := by
  simp [pderiv_X, tcb_pd_two]
  linear_combination (X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 2) * tcb_three

private theorem tcb_l12 {l : Fin 3} (hl : l ∉ dΔ') : l = 1 ∨ l = 2 := by
  revert hl
  fin_cases l <;> simp

private theorem tcb_rho' : logJacobianOrder dΔ' dgc = ((3 : ℕ) : ℕ∞) := by
  rw [logJacobianOrder, tcb_dE', tcb_rF']
  refine le_antisymm ?_ ?_
  · have hm : pderiv 2 dG' ∈ residualLogJacobian dΔ' dr' dG' :=
      Ideal.subset_span (Or.inr ⟨2, by simp, rfl⟩)
    rw [tcb_pd2'] at hm
    refine (idealOrd_le_ord hm).trans (le_of_eq ?_)
    rw [tcb_ord_two_mul, ord_X_pow]
  · refine le_idealOrd_span ?_
    rintro s (⟨i, -, rfl⟩ | ⟨l, -, rfl⟩)
    · exact le_trans (by norm_num) (le_ord_smul_add_X_mul_pderiv tcb_ord_G' _ i)
    · exact le_trans (by norm_num) (le_ord_pderiv tcb_ord_G' l)

/-- At the new point, `Θ₀(g'_c)` has order `7 = |r'| + ρ(g'_c) + 1`. The element
`y ∂_z g'_c = 2 x^3 y^4` gives the upper bound. -/
private theorem tcb_idealOrd' : idealOrd (logJacobianTangent dΔ' dgc) = ((7 : ℕ) : ℕ∞) := by
  refine le_antisymm ?_ (le_idealOrd_logJacobianTangent (Δ := dΔ') tcb_ord_gc)
  have h := X_mul_pderiv_mem_logJacobianTangent_of_notMem (Δ := dΔ') (l := 2) (by decide) 1 dgc
  refine (idealOrd_le_ord h).trans (le_of_eq ?_)
  rw [tcb_pd2c, ord_mul, tcb_ord_two_mul, ord_mul, ord_X, ord_X_pow, ord_X_pow]
  norm_num

/-- At the new point, `Θ₀(g'_c)` has order `|r'| + ρ(g'_c) + 1` (case B). -/
private theorem tcb_caseB' : idealOrd (logJacobianTangent dΔ' dgc) =
    degree (divisorExponent dΔ' dgc) + logJacobianOrder dΔ' dgc + 1 := by
  rw [tcb_idealOrd', tcb_dE', tcb_deg', tcb_rho']
  norm_num

private theorem tcb_caseB'_ne : idealOrd (logJacobianTangent dΔ' dgc) ≠
    degree (divisorExponent dΔ' dgc) + logJacobianOrder dΔ' dgc := by
  rw [tcb_idealOrd', tcb_dE', tcb_deg', tcb_rho']
  norm_num

/-- If `x^{r'} ψ ∈ Θ(g'_c)`, then `ψ ∈ Θ̃(G')`. -/
private theorem tcb_mem_residualLogJacobian {ψ : MvPolynomial (Fin 3) (ZMod 3)}
    (hψ : monomial dr' 1 * ψ ∈ logJacobian dΔ' dgc) : ψ ∈ residualLogJacobian dΔ' dr' dG' := by
  rw [logJacobian_eq_mul, tcb_dE', tcb_rF'] at hψ
  obtain ⟨z, hz, hzeq⟩ := Ideal.mem_span_singleton_mul.mp hψ
  have hne : (monomial dr' (1 : ZMod 3)) ≠ 0 := by
    rw [Ne, monomial_eq_zero]
    exact one_ne_zero
  rwa [← mul_left_cancel₀ hne hzeq]

private theorem tcb_mem_ψ : monomial dr' 1 * dψ ∈ logJacobian dΔ' dgc := by
  rw [show monomial dr' 1 * dψ = 2 * pderiv 1 dgc by
    rw [tcb_monomial_r', tcb_pd1c]
    linear_combination (-(X 0 ^ 3 * dψ)) * tcb_three]
  exact Ideal.mul_mem_left _ 2 (pderiv_mem_logJacobian (j := 1) (by decide) dgc)

private theorem tcb_mem_Y' : monomial dr' 1 * X 1 ^ 3 ∈ logJacobian dΔ' dgc := by
  rw [show monomial dr' 1 * X 1 ^ 3 = 2 * pderiv 2 dgc by
    rw [tcb_monomial_r', tcb_pd2c]
    linear_combination (-(X 0 ^ 3 * X 1 ^ 3)) * tcb_three]
  exact Ideal.mul_mem_left _ 2 (pderiv_mem_logJacobian (j := 2) (by decide) dgc)

/-- The parts of degree `3` of the generators of `Θ̃(G')` are in the span of `x^2 y` and `y^3`. -/
private theorem tcb_gen' (s : MvPolynomial (Fin 3) (ZMod 3))
    (hs : s ∈ (fun i => ((dr' i : ℕ) : ZMod 3) • dG' + X i * pderiv i dG') '' (dΔ' : Set (Fin 3)) ∪
      (fun j => pderiv j dG') '' (dΔ' : Set (Fin 3))ᶜ) :
    ((3 : ℕ) : ℕ∞) ≤ ord s ∧
      homogeneousComponent 3 s ∈ Submodule.span (ZMod 3) {dP, X 1 ^ 3} := by
  rcases hs with ⟨i, -, rfl⟩ | ⟨l, hl, rfl⟩
  · have h3 : ((3 : ℕ) : ℕ∞) < ord (((dr' i : ℕ) : ZMod 3) • dG' + X i * pderiv i dG') :=
      lt_of_lt_of_le (by norm_num) (le_ord_smul_add_X_mul_pderiv tcb_ord_G' _ i)
    refine ⟨h3.le, ?_⟩
    rw [homogeneousComponent_eq_zero_of_lt_ord h3]
    exact zero_mem _
  · dsimp only
    obtain rfl | rfl := tcb_l12 (by simpa using hl)
    · rw [tcb_pd1', tcb_ord_two_mul, tcb_hc_two_mul, tcb_ord_ψ, tcb_hc_ψ]
      exact ⟨le_rfl, Submodule.smul_mem _ _ (Submodule.subset_span (by simp))⟩
    · rw [tcb_pd2', tcb_ord_two_mul, tcb_hc_two_mul, ord_X_pow, tcb_hc_Y]
      exact ⟨le_rfl, Submodule.smul_mem _ _ (Submodule.subset_span (by simp))⟩

private theorem tcb_T' : logJacobianDirectrix dΔ' dgc =
    LinearMap.ker (LinearMap.funLeft (ZMod 3) (ZMod 3) dv') := by
  have hset : ∀ ψ, ψ ∈ logJacobianDirectrixSet dΔ' dgc ↔
      ord ψ = ((3 : ℕ) : ℕ∞) ∧ monomial dr' 1 * ψ ∈ logJacobian dΔ' dgc := by
    intro ψ
    rw [logJacobianDirectrixSet, Set.mem_ofPred_eq, logJacobianCaseIdeal_of_ne tcb_caseB'_ne,
      tcb_dE', tcb_rho']
  have hn : (logJacobianOrder dΔ' dgc).toNat = 3 := by
    rw [tcb_rho']
    rfl
  refine le_antisymm ?_ ?_
  · intro w hw
    have h1 := logJacobianDirectrix_le ((hset _).mpr ⟨tcb_ord_ψ, tcb_mem_ψ⟩) hw
    rw [hn, tcb_hc_ψ, tcb_mem_directrix_iff (by decide)] at h1
    exact tcb_mem_ker'.mpr ⟨h1.2, h1.1⟩
  · refine le_logJacobianDirectrix fun ψ hψ => ?_
    rw [hset] at hψ
    rw [hn]
    refine le_directrix_of_mem_span ?_
      (homogeneousComponent_mem_of_mem_span tcb_gen' (tcb_mem_residualLogJacobian hψ.2))
    rintro s (rfl | rfl) w hw <;> obtain ⟨h0, h1⟩ := tcb_mem_ker'.mp hw
    · exact (tcb_mem_directrix_iff (by decide)).mpr ⟨h1, h0⟩
    · exact (mem_directrix_X_pow_iff (by norm_num)).mpr h1

/-! ### The results -/

/-- **Example 3.9.9, the data** (Volume 7, Section 3.9 of the handbook). Over `𝔽₃`, let
`g = x^3 y^2 z^3 + 2 x^2 y^3 z` and `E = V(x z)`. Then `g ≠ 0`, `g` is clean for `p = 3`, and
`ord g ≥ 3`. In the `x`-chart with `t_z = 1` and `t_x = t_y = 0`, `g` goes to `x^3 g'` with
`g' = x^5 y^2 (z + 1)^3 + 2 x^3 y^3 (z + 1)`. The new divisor is `V(x)`, and
`g'_c = x^5 y^2 z^3 + x^5 y^2 + 2 x^3 y^3 z`. The exponents of `g` are `r = (2, 0, 1)`, and
`G = x y^2 z^2 + 2 y^3` has order `d = 3`. So `|r| + d = 6 = 0` in `𝔽₃`, and the hypothesis `hpd`
of Proposition 3.9.7 (`idealOrd_logJacobianTangent_cleanPart_of_caseA`) fails. The exponents of
`g'_c` are `r' = (3, 0, 0)`, and `G' = x^2 y^2 (z^3 + 1) + 2 y^3 z`. -/
theorem caseAToCaseBExample_hyp :
    dg ≠ 0 ∧ IsClean 3 dg ∧ ((3 : ℕ) : ℕ∞) ≤ ord dg ∧ pointChart 0 dt dg = X 0 ^ 3 * dg' ∧
      blowupDivisor dΔ 0 dt = dΔ' ∧ cleanPart 3 dg' = dgc ∧
      divisorExponent dΔ dg = dr ∧ residualFactor dΔ dg = dG ∧ ord dG = 3 ∧
      ((degree (divisorExponent dΔ dg) + 3 : ℕ) : ZMod 3) = 0 ∧
      divisorExponent dΔ' dgc = dr' ∧ residualFactor dΔ' dgc = dG' := by
  refine ⟨tcb_g_ne, tcb_isClean_g, le_trans (by norm_num) tcb_ord_g.ge, tcb_pointChart,
    tcb_blowupDivisor, tcb_cleanPart, tcb_dE, tcb_rF, by exact_mod_cast tcb_ord_G, ?_, tcb_dE',
    tcb_rF'⟩
  rw [tcb_dE, tcb_deg]
  rfl

/-- **Example 3.9.9, the cases** (Volume 7, Section 3.9 of the handbook). Over `𝔽₃`, let
`g = x^3 y^2 z^3 + 2 x^2 y^3 z` and `E = V(x z)`. The point is of case A: the order of `Θ₀(g)` is
`|r| + ρ(g)`. In the `x`-chart with `t_z = 1` and `t_x = t_y = 0`, the new point is of case B: the
order of `Θ₀(g'_c)` is `|r'| + ρ(g'_c) + 1`. -/
theorem caseAToCaseBExample_cases :
    idealOrd (logJacobianTangent dΔ dg) =
        degree (divisorExponent dΔ dg) + logJacobianOrder dΔ dg ∧
      idealOrd (logJacobianTangent (blowupDivisor dΔ 0 dt) (cleanPart 3 dg')) =
        degree (divisorExponent (blowupDivisor dΔ 0 dt) (cleanPart 3 dg')) +
          logJacobianOrder (blowupDivisor dΔ 0 dt) (cleanPart 3 dg') + 1 := by
  rw [tcb_blowupDivisor, tcb_cleanPart]
  exact ⟨tcb_caseA, tcb_caseB'⟩

/-- **Example 3.9.9, the order `ρ`** (Volume 7, Section 3.9 of the handbook). Over `𝔽₃`, let
`g = x^3 y^2 z^3 + 2 x^2 y^3 z` and `E = V(x z)`. Then `ρ(g) = 3`, and in the `x`-chart with
`t_z = 1` and `t_x = t_y = 0`, `ρ(g'_c) = 3`. So `ρ` stays. -/
theorem caseAToCaseBExample_rho :
    logJacobianOrder dΔ dg = 3 ∧
      logJacobianOrder (blowupDivisor dΔ 0 dt) (cleanPart 3 dg') = 3 := by
  rw [tcb_blowupDivisor, tcb_cleanPart]
  exact ⟨by exact_mod_cast tcb_rho, by exact_mod_cast tcb_rho'⟩

/-- **Example 3.9.9: the hypothesis `hpd` of Proposition 3.9.7 is necessary** (Volume 7,
Section 3.9 of the handbook). Over `𝔽₃`, let `g = x^3 y^2 z^3 + 2 x^2 y^3 z` and `E = V(x z)`, and
take the `x`-chart with `t_z = 1` and `t_x = t_y = 0`. The other hypotheses of
`idealOrd_logJacobianTangent_cleanPart_of_caseA` hold with `p = d = 3`
(`caseAToCaseBExample_hyp`, `caseAToCaseBExample_rho`). But `|r| + d = 0` in `𝔽₃`, and the order of
`Θ₀(g'_c)` is not `|r'| + d`. -/
theorem caseAToCaseBExample_not_caseA :
    ((degree (divisorExponent dΔ dg) + 3 : ℕ) : ZMod 3) = 0 ∧
      idealOrd (logJacobianTangent (blowupDivisor dΔ 0 dt) (cleanPart 3 dg')) ≠
        ((degree (divisorExponent (blowupDivisor dΔ 0 dt) (cleanPart 3 dg')) + 3 : ℕ) : ℕ∞) := by
  rw [tcb_blowupDivisor, tcb_cleanPart, tcb_dE, tcb_dE', tcb_deg, tcb_deg', tcb_idealOrd']
  exact ⟨rfl, by norm_num⟩

/-- **Example 3.9.9, the dimensions** (Volume 7, Section 3.9 of the handbook). Over `𝔽₃`, let
`g = x^3 y^2 z^3 + 2 x^2 y^3 z` and `E = V(x z)`. Then `T_ρ(g) = {y = 0}` has dimension `2`. In the
`x`-chart with `t_z = 1` and `t_x = t_y = 0`, the new point is of case B, and
`T_ρ(g'_c) = {x = y = 0}` has dimension `1`. -/
theorem caseAToCaseBExample_finrank :
    finrank (ZMod 3) (logJacobianDirectrix dΔ dg) = 2 ∧
      finrank (ZMod 3) (logJacobianDirectrix (blowupDivisor dΔ 0 dt) (cleanPart 3 dg')) = 1 := by
  rw [tcb_blowupDivisor, tcb_cleanPart, tcb_T, tcb_T']
  refine ⟨?_, ?_⟩
  · have := tcb_finrank_ker dv (by decide)
    omega
  · have := tcb_finrank_ker dv' (by decide)
    omega

/-- **Example 3.9.9, the form with the codimension** (Volume 7, Section 3.9 of the handbook).
Over `𝔽₃`, let `g = x^3 y^2 z^3 + 2 x^2 y^3 z` and `E = V(x z)`. Then `τ_ρ(g) = 1`, and in the
`x`-chart with `t_z = 1` and `t_x = t_y = 0`, `τ_ρ(g'_c) = 2`. -/
theorem caseAToCaseBExample_codim :
    logJacobianDirectrixCodim dΔ dg = 1 ∧
      logJacobianDirectrixCodim (blowupDivisor dΔ 0 dt) (cleanPart 3 dg') = 2 := by
  obtain ⟨h1, h2⟩ := caseAToCaseBExample_finrank
  unfold logJacobianDirectrixCodim
  rw [h1, h2, Fintype.card_fin]
  exact ⟨rfl, rfl⟩

end Example

end Singularity
