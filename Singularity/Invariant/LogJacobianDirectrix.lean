/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianNearPoint

/-!
# The codimension of the directrix of the log-Jacobian order

Let `k` be a field of characteristic `p`, let `g ≠ 0` be a clean polynomial in `k[x_i : i ∈ σ]`
with `ord g ≥ p`, and let `Δ` give the divisor `E = V(∏_{i ∈ Δ} x_i)`. Write `g = x^r G`, with
`r = divisorExponent Δ g`, and let `ρ = logJacobianOrder Δ g`. Let `Θ(g)` be the log-Jacobian
ideal and `Θ₀(g)` the ideal `logJacobianTangent Δ g`. The order of `Θ₀(g)` is `|r| + ρ` (case A)
or `|r| + ρ + 1` (case B). Let `T_ρ(g)` be the intersection of the directrices `T(ψ_ρ)` of the
parts `ψ_ρ` of degree `ρ` of the `ψ` with `ord ψ = ρ` and `x^r ψ ∈ Θ₀(g)` in case A, and
`x^r ψ ∈ Θ(g)` in case B (`logJacobianDirectrix`). Let `τ_ρ(g)` be the codimension of `T_ρ(g)`
(`logJacobianDirectrixCodim`). This file proves that `τ_ρ` does not go down at the points of a
point blowup where `ρ` stays and the new point is of case B (Volume 7, Section 3.8 of the handbook,
Proposition 3.8.2). This is the analogue for `ρ` of the theorem of Hironaka that `τ` does not go
down at the points where the order stays [Hir67].

The proof has two steps.

1. The dimension inequality (`finrank_iInf_directrix_pointChart_le`). Let `ψ_i` be polynomials
   with `ord ψ_i ≥ m`, let the chart send `ψ_i` to `x_j^m ψ'_i`, and let `ord ψ'_i ≥ m`. Let
   `F_i` and `F'_i` be the parts of degree `m` of `ψ_i` and `ψ'_i`. The substitution `x_j ↦ 0`
   sends `F'_i` to `ρ(F_i)`, and `ρ(F_i)` is `F_i` after a linear change of the coordinates that
   fixes the hyperplane `w_j = 0`. So each `w` in the directrix of `F'_i` with `w_j = 0` is in the
   directrix of `F_i` (`mem_directrix_of_mem_directrix_pointChart`). The vector `v` of the chart is
   in each directrix of `F_i` and has `v_j = 1`. So the dimension of the intersection of the
   directrices of the `F'_i` is at most the dimension of the intersection of the directrices of
   the `F_i` (`finrank_le_finrank_of_mem_of_forall_mem`).
2. The transforms. Let `ρ(g'_c) = ρ(g) = m`. For each `ψ` of the definition of `T_ρ(g)`, the
   chart sends `ψ` to `x_j^m ψ'` with `ord ψ' = m`, and `x^{r'} U ψ' ∈ Θ(g'_c)`, with
   `r' = divisorExponent Δ' g'_c` and the factor `U = chartUnit j t r` with a nonzero constant
   term (`monomial_mul_chartUnit_mul_mem_logJacobian_cleanPart`). The proof is the proof of
   Theorem 3.2.4: the chart sends an element `f` of `Θ₀(g)` to `x_j^p x^b U ψ'` with
   `x^b U ψ' ∈ Θ(g'_c)`, `b ≤ r'`, and `|b| = |r'|` since `ρ` stays. If the new point is of
   case B, then `U ψ'` is in the definition of `T_ρ(g'_c)`, and the directrix of its part of
   degree `m` is the directrix of `ψ'_m`. So step 1 gives the proposition.

The case condition is necessary. Over `𝔽₂`, for `g = x y z^2 + y^2 z + x z^2` and `E = ∅`, the
point is of case B with `T_ρ(g)` of dimension `1`. At the origin of the `x`-chart, `ρ` stays `2`,
the new point is of case A, and `T_ρ(g'_c)` has dimension `2` (Example 3.8.3).

## Main definitions

* `logJacobianCaseIdeal Δ g`: `Θ₀(g)` in case A and `Θ(g)` in case B.
* `logJacobianDirectrix Δ g`: the directrix `T_ρ(g)`.
* `logJacobianDirectrixCodim Δ g`: the codimension `τ_ρ(g)` of `T_ρ(g)`.

## Main results

* `le_directrix_homogeneousComponent_of_mem_span`: if each generator of an ideal has order at
  least `n`, then a subspace in the directrix of the part of degree `n` of each generator is in the
  directrix of the part of degree `n` of each element of the ideal.
* `finrank_iInf_directrix_pointChart_le`: the dimension inequality for the weak transforms of a
  family of polynomials.
* `finrank_logJacobianDirectrix_cleanPart_le`, `logJacobianDirectrixCodim_le_cleanPart`:
  Proposition 3.8.2.
* `tauRhoExample_finrank`: Example 3.8.3.

## References

* [Hir67] H. Hironaka, *Characteristic polyhedra of singularities*, J. Math. Kyoto Univ. 7 (1967).
* Volume 7, Section 3.8 of the handbook: Proposition 3.8.2 and Example 3.8.3.
-/

open MvPolynomial Finsupp Module

namespace Singularity

/-! ### The directrix of a linear combination -/

section Linear

variable {σ k : Type*} [Field k]

/-- For a fixed vector `v`, the polynomials `F` with `v ∈ T(F)`. They form a `k`-subspace. -/
noncomputable def directrixPolys (v : σ → k) : Submodule k (MvPolynomial σ k) :=
  LinearMap.ker ((translate v).toLinearMap -
    (rename some : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k).toLinearMap)

theorem mem_directrixPolys_iff {v : σ → k} {F : MvPolynomial σ k} :
    F ∈ directrixPolys v ↔ v ∈ directrix F := by
  rw [directrixPolys, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, mem_directrix_iff]
  rfl

/-- A subspace in the directrix of each element of `S` is in the directrix of each linear
combination of elements of `S`. -/
theorem le_directrix_of_mem_span {W : Submodule k (σ → k)} {S : Set (MvPolynomial σ k)}
    (hS : ∀ s ∈ S, W ≤ directrix s) {F : MvPolynomial σ k} (hF : F ∈ Submodule.span k S) :
    W ≤ directrix F := fun _ hv =>
  mem_directrixPolys_iff.mp
    (Submodule.span_le.mpr (fun s hs => mem_directrixPolys_iff.mpr (hS s hs hv)) hF)

/-- `T(F) ⊆ T(c F)` for each constant `c`. -/
theorem directrix_le_directrix_smul (c : k) (F : MvPolynomial σ k) :
    directrix F ≤ directrix (c • F) :=
  le_directrix_of_mem_span (S := {F}) (fun s hs => by rw [Set.mem_singleton_iff.mp hs])
    (Submodule.smul_mem _ c (Submodule.subset_span rfl))

/-- The part of degree `n` of `q` is `0` if `n < ord q`. -/
theorem homogeneousComponent_eq_zero_of_lt_ord {n : ℕ} {q : MvPolynomial σ k}
    (h : (n : ℕ∞) < ord q) : homogeneousComponent n q = 0 := by
  ext d
  rw [coeff_homogeneousComponent]
  split_ifs with hd
  · rw [coeff_eq_zero_of_lt_ord (by rw [hd]; exact h)]
    simp
  · simp

/-- The part of degree `n` of `a f` is `a(0) f_n` if `ord f ≥ n`. -/
theorem homogeneousComponent_mul_of_le_ord {n : ℕ} {f : MvPolynomial σ k}
    (hf : (n : ℕ∞) ≤ ord f) (a : MvPolynomial σ k) :
    homogeneousComponent n (a * f) = C (constantCoeff a) * homogeneousComponent n f := by
  have ha : a = C (constantCoeff a) + (a - C (constantCoeff a)) := by ring
  have h1 : (1 : ℕ∞) ≤ ord (a - C (constantCoeff a)) :=
    one_le_ord_iff.mpr (by rw [map_sub, constantCoeff_C, sub_self])
  have h2 : homogeneousComponent n ((a - C (constantCoeff a)) * f) = 0 := by
    refine homogeneousComponent_eq_zero_of_lt_ord ?_
    rw [ord_mul]
    calc (n : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
      _ = 1 + (n : ℕ∞) := by push_cast; ring
      _ ≤ _ := add_le_add h1 hf
  conv_lhs => rw [ha, add_mul, map_add, h2, add_zero]
  exact homogeneousComponent_C_mul _ _ _

/-- **The degree `n` part of an ideal of order at least `n`.** If each element of `S` has order at
least `n`, then the part of degree `n` of each element of the ideal generated by `S` is a
`k`-linear combination of the parts of degree `n` of the elements of `S`. -/
theorem homogeneousComponent_mem_span_of_mem_span {S : Set (MvPolynomial σ k)} {n : ℕ}
    (hS : ∀ s ∈ S, (n : ℕ∞) ≤ ord s) {f : MvPolynomial σ k} (hf : f ∈ Ideal.span S) :
    homogeneousComponent n f ∈ Submodule.span k (homogeneousComponent n '' S) := by
  have hI : ∀ x ∈ Ideal.span S, (n : ℕ∞) ≤ ord x := fun x hx =>
    (le_idealOrd_span hS).trans (idealOrd_le_ord hx)
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx' hx =>
    rw [smul_eq_mul, homogeneousComponent_mul_of_le_ord (hI x hx') a, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/-- **The directrix of an element of an ideal of order at least `n`.** If each element of `S` has
order at least `n` and `W` is in the directrix of the part of degree `n` of each element of `S`,
then `W` is in the directrix of the part of degree `n` of each element of the ideal generated by
`S`. -/
theorem le_directrix_homogeneousComponent_of_mem_span {S : Set (MvPolynomial σ k)} {n : ℕ}
    (hS : ∀ s ∈ S, (n : ℕ∞) ≤ ord s) {W : Submodule k (σ → k)}
    (hW : ∀ s ∈ S, W ≤ directrix (homogeneousComponent n s)) {f : MvPolynomial σ k}
    (hf : f ∈ Ideal.span S) : W ≤ directrix (homogeneousComponent n f) := by
  refine le_directrix_of_mem_span ?_ (homogeneousComponent_mem_span_of_mem_span hS hf)
  rintro _ ⟨s, hs, rfl⟩
  exact hW s hs

end Linear

/-! ### The restriction to the hyperplane `w_j = 0` -/

section Restriction

variable {σ k : Type*} [Field k] [DecidableEq σ]

/-- The substitution `x_j ↦ 0` on `k[x, s]`. -/
noncomputable def killVarOpt (j : σ) : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial (Option σ) k :=
  aeval fun o => Option.elim o (X none) fun i => if i = j then 0 else X (some i)

theorem killVarOpt_comp_translate {j : σ} {w : σ → k} (hw : w j = 0) :
    (killVarOpt j).comp (translate w) = (translate w).comp (killVar j) := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [killVarOpt, translate, killVar, hw]
  · simp [killVarOpt, translate, killVar, h]

theorem killVarOpt_comp_rename (j : σ) :
    (killVarOpt j).comp (rename some : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k) =
      (rename some).comp (killVar j) := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [killVarOpt, killVar]
  · simp [killVarOpt, killVar, h]

/-- If `w_j = 0` and `w ∈ T(F)`, then `w ∈ T(F|_{x_j = 0})`. -/
theorem mem_directrix_killVar {j : σ} {w : σ → k} (hw : w j = 0) {F : MvPolynomial σ k}
    (h : w ∈ directrix F) : w ∈ directrix (killVar j F) := by
  rw [mem_directrix_iff] at h ⊢
  have h' := congrArg (killVarOpt j) h
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, killVarOpt_comp_translate hw,
    killVarOpt_comp_rename, AlgHom.comp_apply, AlgHom.comp_apply] at h'

/-- The substitution `x_i ↦ x_i - t_i x_j` for `i ≠ j` on `k[x, s]`. -/
noncomputable def chartUnlinear (j : σ) (t : σ → k) :
    MvPolynomial (Option σ) k →ₐ[k] MvPolynomial (Option σ) k :=
  aeval fun o => Option.elim o (X none) fun i =>
    if i = j then X (some j) else X (some i) - C (t i) * X (some j)

theorem chartUnlinear_comp_translate_comp_chartLinear {j : σ} (t : σ → k) {w : σ → k}
    (hw : w j = 0) :
    ((chartUnlinear j t).comp (translate w)).comp (chartLinear j t) = translate w := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [chartUnlinear, translate, chartLinear, hw]
  · simp [chartUnlinear, translate, chartLinear, h, hw]
    ring

theorem chartUnlinear_comp_rename_comp_chartLinear (j : σ) (t : σ → k) :
    ((chartUnlinear j t).comp
      (rename some : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k)).comp (chartLinear j t) =
        rename some := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [chartUnlinear, chartLinear]
  · simp [chartUnlinear, chartLinear, h]

/-- If `w_j = 0` and `w` is in the directrix of `λ(F)`, with `λ` the linear substitution
`x_i ↦ x_i + t_i x_j` (`chartLinear`), then `w ∈ T(F)`. -/
theorem mem_directrix_of_mem_directrix_chartLinear {j : σ} {t : σ → k} {w : σ → k}
    (hw : w j = 0) {F : MvPolynomial σ k} (h : w ∈ directrix (chartLinear j t F)) :
    w ∈ directrix F := by
  rw [mem_directrix_iff] at h ⊢
  have h' := congrArg (chartUnlinear j t) h
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply,
    chartUnlinear_comp_translate_comp_chartLinear t hw,
    chartUnlinear_comp_rename_comp_chartLinear] at h'

omit [DecidableEq σ] in
/-- A polynomial with `ord q ≥ m` and total degree at most `m` is homogeneous of degree `m`. -/
theorem isHomogeneous_of_le_ord {m : ℕ} {q : MvPolynomial σ k} (h1 : (m : ℕ∞) ≤ ord q)
    (h2 : q.totalDegree ≤ m) : q.IsHomogeneous m := by
  intro d hd
  have h3 : m ≤ degree d := by
    by_contra hlt
    exact hd (le_ord_iff.mp h1 d (by omega))
  have h4 : degree d ≤ m := (le_totalDegree (MvPolynomial.mem_support_iff.mpr hd)).trans h2
  rw [show (1 : σ → ℕ) = fun _ => 1 from rfl, ← Finsupp.degree_eq_weight_one]
  omega

omit [DecidableEq σ] in
theorem le_ord_homogeneousComponent (m : ℕ) (f : MvPolynomial σ k) :
    (m : ℕ∞) ≤ ord (homogeneousComponent m f) := by
  refine le_ord_iff.mpr fun d hd => ?_
  rw [coeff_homogeneousComponent, ite_eq_right (by omega)]

omit [DecidableEq σ] in
/-- `ord (f - f_m) > m` if `ord f ≥ m`. -/
theorem lt_ord_sub_homogeneousComponent {m : ℕ} {f : MvPolynomial σ k} (hf : (m : ℕ∞) ≤ ord f) :
    ((m + 1 : ℕ) : ℕ∞) ≤ ord (f - homogeneousComponent m f) := by
  refine le_ord_iff.mpr fun d hd => ?_
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases hdm : degree d = m
  · rw [ite_eq_left hdm, sub_self]
  · rw [ite_eq_right hdm, sub_zero]
    exact coeff_eq_zero_of_lt_ord (lt_of_lt_of_le (by exact_mod_cast (by omega : degree d < m)) hf)

theorem totalDegree_killVar_le (j : σ) (q : MvPolynomial σ k) :
    (killVar j q).totalDegree ≤ q.totalDegree := by
  refine totalDegree_aeval_le (fun i => ?_) q
  split_ifs <;> simp

/-- **The restriction step.** Let `ord f ≥ m`, let the `x_j`-chart with translations `t` send `f`
to `x_j^m f'`, and let `ord f' ≥ m`. If `w_j = 0` and `w` is in the directrix of the part of
degree `m` of `f'`, then `w` is in the directrix of the part of degree `m` of `f`. The proof: the
substitution `x_j ↦ 0` sends `f'_m` to `ρ(f_m) = λ(f_m)`. -/
theorem mem_directrix_of_mem_directrix_pointChart {j : σ} {t : σ → k} {f f' : MvPolynomial σ k}
    {m : ℕ} (hf : (m : ℕ∞) ≤ ord f) (h : pointChart j t f = X j ^ m * f')
    (hf' : (m : ℕ∞) ≤ ord f') {w : σ → k} (hw : w j = 0)
    (hmem : w ∈ directrix (homogeneousComponent m f')) :
    w ∈ directrix (homogeneousComponent m f) := by
  have h' := pointChart_eq_X_pow_mul_chartTransform j t hf
  rw [h] at h'
  have hf'_eq := mul_left_cancel₀ (pow_ne_zero m (X_ne_zero j)) h'
  have hg := homogeneousComponent_isHomogeneous m f
  -- `f'|_{x_j = 0} = ρ(f_m)`, homogeneous of degree `m`.
  have hk : killVar j f' = chartRest j t (homogeneousComponent m f) := by
    rw [hf'_eq, killVar_chartTransform j t hf, homogeneousComponent_apply]
  have hH : (chartRest j t (homogeneousComponent m f)).IsHomogeneous m := by
    refine isHomogeneous_of_le_ord ?_ ((totalDegree_chartRest_le j t _).trans hg.totalDegree_le)
    rw [← hk]
    exact hf'.trans (ord_le_ord_killVar j f')
  -- `f'_m|_{x_j = 0} = ρ(f_m)`.
  have hk' : killVar j (homogeneousComponent m f') = chartRest j t (homogeneousComponent m f) := by
    have hR := lt_ord_sub_homogeneousComponent hf'
    have hsplit : killVar j (homogeneousComponent m f') =
        chartRest j t (homogeneousComponent m f) - killVar j (f' - homogeneousComponent m f') := by
      rw [← hk, map_sub, sub_sub_cancel]
    have hdeg : (killVar j (homogeneousComponent m f')).totalDegree ≤ m :=
      (totalDegree_killVar_le j _).trans (homogeneousComponent_isHomogeneous m f').totalDegree_le
    ext d
    by_cases hd : degree d ≤ m
    · rw [hsplit, coeff_sub, coeff_eq_zero_of_lt_ord (f := killVar j _), sub_zero]
      exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hd)
        (hR.trans (ord_le_ord_killVar j _))
    · rw [coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hdeg (show m < degree d by omega)),
        hH.coeff_eq_zero (by omega)]
  have h1 := mem_directrix_killVar hw hmem
  rw [hk', ← chartLinear_eq_chartRest hg hH] at h1
  exact mem_directrix_of_mem_directrix_chartLinear hw h1

omit [DecidableEq σ] in
/-- **The dimension of a subspace and its hyperplane section.** Let `T` and `T'` be subspaces of
`k^σ`. If `v ∈ T` with `v_j ≠ 0`, and each `w ∈ T'` with `w_j = 0` lies in `T`, then
`dim T' ≤ dim T`. -/
theorem finrank_le_finrank_of_mem_of_forall_mem [Fintype σ] {T T' : Submodule k (σ → k)}
    {j : σ} {v : σ → k} (hv : v ∈ T) (hvj : v j ≠ 0) (hle : ∀ w ∈ T', w j = 0 → w ∈ T) :
    finrank k T' ≤ finrank k T := by
  set K := LinearMap.ker (LinearMap.proj j : (σ → k) →ₗ[k] k)
  have hK : ∀ w, w ∈ K ↔ w j = 0 := fun w => by simp [K]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq T' K
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq T K
  have h3 : T ⊔ K = ⊤ := by
    refine eq_top_iff.mpr fun w _ => Submodule.mem_sup.mpr
      ⟨(w j / v j) • v, T.smul_mem _ hv, w - (w j / v j) • v, (hK _).mpr ?_, by abel⟩
    simp [div_mul_cancel₀ _ hvj]
  have h4 : T' ⊓ K ≤ T ⊓ K := fun w hw =>
    ⟨hle w hw.1 ((hK w).mp hw.2), hw.2⟩
  have h5 := Submodule.finrank_mono h4
  have h6 := Submodule.finrank_le (T' ⊔ K)
  rw [h3, finrank_top] at h2
  omega

/-- **The dimension inequality for the weak transforms** (Volume 7, Section 3.8 of the handbook).
Let `ψ_i` be polynomials with `ord ψ_i ≥ m`, let the `x_j`-chart with translations `t` send `ψ_i`
to `x_j^m ψ'_i`, and let `ord ψ'_i ≥ m`. Then the dimension of the intersection of the directrices
of the parts of degree `m` of the `ψ'_i` is at most the dimension of the intersection of the
directrices of the parts of degree `m` of the `ψ_i`. -/
theorem finrank_iInf_directrix_pointChart_le [Fintype σ] {ι : Type*} {j : σ} {t : σ → k} {m : ℕ}
    {ψ ψ' : ι → MvPolynomial σ k} (hψ : ∀ i, (m : ℕ∞) ≤ ord (ψ i))
    (h : ∀ i, pointChart j t (ψ i) = X j ^ m * ψ' i) (hψ' : ∀ i, (m : ℕ∞) ≤ ord (ψ' i)) :
    finrank k (⨅ i, directrix (homogeneousComponent m (ψ' i)) : Submodule k (σ → k)) ≤
      finrank k (⨅ i, directrix (homogeneousComponent m (ψ i)) : Submodule k (σ → k)) := by
  refine finrank_le_finrank_of_mem_of_forall_mem (j := j) (v := chartVector j t)
    (Submodule.mem_iInf _ |>.mpr fun i =>
      mem_directrix_of_le_ord_pointChart (hψ i) (h i) (hψ' i)) (by simp [chartVector])
    fun w hw hwj => Submodule.mem_iInf _ |>.mpr fun i =>
      mem_directrix_of_mem_directrix_pointChart (hψ i) (h i) (hψ' i) hwj
        ((Submodule.mem_iInf _).mp hw i)

end Restriction

/-! ### The directrix `T_ρ(g)` -/

section Def

variable {σ k : Type*} [Field k]

/-- The ideal of the case of `g`: `Θ₀(g)` if the order of `Θ₀(g)` is `|r| + ρ` (case A), and
`Θ(g)` otherwise (case B, the order of `Θ₀(g)` is then `|r| + ρ + 1`). -/
noncomputable def logJacobianCaseIdeal (Δ : Finset σ) (g : MvPolynomial σ k) :
    Ideal (MvPolynomial σ k) :=
  if idealOrd (logJacobianTangent Δ g) = degree (divisorExponent Δ g) + logJacobianOrder Δ g then
    logJacobianTangent Δ g
  else logJacobian Δ g

/-- The polynomials `ψ` of the definition of `T_ρ(g)`: `ord ψ = ρ` and `x^r ψ` is in the ideal of
the case of `g`. -/
def logJacobianDirectrixSet (Δ : Finset σ) (g : MvPolynomial σ k) : Set (MvPolynomial σ k) :=
  {ψ | ord ψ = logJacobianOrder Δ g ∧
    monomial (divisorExponent Δ g) 1 * ψ ∈ logJacobianCaseIdeal Δ g}

/-- **The directrix `T_ρ(g)` of the log-Jacobian order** (Volume 7, Section 3.8 of the handbook).
The intersection of the directrices of the parts `ψ_ρ` of degree `ρ` of the `ψ` with `ord ψ = ρ`
and `x^r ψ ∈ Θ₀(g)` in case A, and `x^r ψ ∈ Θ(g)` in case B. -/
noncomputable def logJacobianDirectrix (Δ : Finset σ) (g : MvPolynomial σ k) :
    Submodule k (σ → k) :=
  ⨅ ψ ∈ logJacobianDirectrixSet Δ g,
    directrix (homogeneousComponent (logJacobianOrder Δ g).toNat ψ)

/-- The codimension `τ_ρ(g)` of the directrix `T_ρ(g)`. -/
noncomputable def logJacobianDirectrixCodim [Fintype σ] (Δ : Finset σ) (g : MvPolynomial σ k) :
    ℕ :=
  Fintype.card σ - finrank k (logJacobianDirectrix Δ g)

theorem logJacobianCaseIdeal_of_eq {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : idealOrd (logJacobianTangent Δ g) = degree (divisorExponent Δ g) + logJacobianOrder Δ g) :
    logJacobianCaseIdeal Δ g = logJacobianTangent Δ g :=
  ite_eq_left h

theorem logJacobianCaseIdeal_of_ne {Δ : Finset σ} {g : MvPolynomial σ k}
    (h : idealOrd (logJacobianTangent Δ g) ≠ degree (divisorExponent Δ g) + logJacobianOrder Δ g) :
    logJacobianCaseIdeal Δ g = logJacobian Δ g :=
  ite_eq_right h

theorem logJacobianDirectrix_le {Δ : Finset σ} {g : MvPolynomial σ k} {ψ : MvPolynomial σ k}
    (hψ : ψ ∈ logJacobianDirectrixSet Δ g) :
    logJacobianDirectrix Δ g ≤
      directrix (homogeneousComponent (logJacobianOrder Δ g).toNat ψ) :=
  iInf₂_le ψ hψ

theorem le_logJacobianDirectrix {Δ : Finset σ} {g : MvPolynomial σ k} {W : Submodule k (σ → k)}
    (h : ∀ ψ ∈ logJacobianDirectrixSet Δ g,
      W ≤ directrix (homogeneousComponent (logJacobianOrder Δ g).toNat ψ)) :
    W ≤ logJacobianDirectrix Δ g :=
  le_iInf₂ h

end Def

/-! ### The transforms of the `ψ` -/

section Transform

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- **The element of `Θ(g'_c)` from an element of `Θ₀(g)`.** Let `g ≠ 0` be clean with
`ord g ≥ p`, let `π(g) = x_j^p g'`, and let `τ` be the order of `Θ₀(g)`. Let `f ∈ Θ₀(g)` with
`π(f) = x_j^τ x^e W`, with `e = chartExponent j t r`. Let `b = (τ - p) e_j + e`. Then `b` is
supported in the new divisor, `x^b` divides each element of `Θ(g'_c)`, and `x^b W ∈ Θ(g'_c)`. The
proof is the proof of Theorem 3.2.4 (Volume 7, Section 3.2 of the handbook). -/
theorem monomial_mul_mem_logJacobian_cleanPart (hg : g ≠ 0) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g') {τ : ℕ}
    (hτ : idealOrd (logJacobianTangent Δ g) = τ) {f W : MvPolynomial σ k}
    (hf : f ∈ logJacobianTangent Δ g)
    (hπ : pointChart j t f = X j ^ τ * (monomial (chartExponent j t (divisorExponent Δ g)) 1 * W)) :
    (∀ i, i ∉ blowupDivisor Δ j t →
      (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) i = 0) ∧
    logJacobian (blowupDivisor Δ j t) (cleanPart p g') ≤
      Ideal.span {monomial (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) 1} ∧
    monomial (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) 1 * W ∈
      logJacobian (blowupDivisor Δ j t) (cleanPart p g') := by
  have _ := hg
  -- Each element of `Θ₀(g)` is divisible by `x^r`.
  have hdvd₀ : ∀ f ∈ logJacobianTangent Δ g, monomial (divisorExponent Δ g) (1 : k) ∣ f :=
    fun f hf => Ideal.mem_span_singleton.mp
      (logJacobian_le_span_monomial Δ g (logJacobianTangent_le Δ g hf))
  -- `p ≤ τ` and `|r| ≤ τ`.
  have hpτ : p ≤ τ := by
    have := le_idealOrd_logJacobianTangent (Δ := Δ) hord
    rw [hτ] at this
    exact_mod_cast this
  have hrτ : degree (divisorExponent Δ g) ≤ τ := by
    obtain ⟨h₀, hh₀, hord₀⟩ := exists_mem_ord_eq_idealOrd (logJacobianTangent Δ g)
    rw [hτ] at hord₀
    obtain ⟨q, hq⟩ := hdvd₀ h₀ hh₀
    have : ((degree (divisorExponent Δ g) : ℕ) : ℕ∞) ≤ τ := by
      rw [← hord₀, hq, ord_mul, ord_monomial one_ne_zero]
      exact le_self_add
    exact_mod_cast this
  -- `π(Θ₀(g)) ⊆ (x_j^τ x^e)`.
  have hB1 : Ideal.map (pointChart j t) (logJacobianTangent Δ g) ≤
      Ideal.span {X j ^ τ * monomial (chartExponent j t (divisorExponent Δ g)) (1 : k)} := by
    have := map_pointChart_span_le (j := j) (t := t) (S := (logJacobianTangent Δ g : Set _))
      (c := τ - degree (divisorExponent Δ g)) fun s hs => ⟨hdvd₀ s hs, by
        rw [Nat.add_sub_cancel' hrτ, ← hτ]
        exact idealOrd_le_ord hs⟩
    rwa [Ideal.span_eq, Nat.add_sub_cancel' hrτ] at this
  -- The monomial `x^b` with `x_j^p x^b = x_j^τ x^e`.
  have hXb : X j ^ τ * monomial (chartExponent j t (divisorExponent Δ g)) (1 : k) =
      X j ^ p * monomial (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) 1 := by
    rw [monomial_single_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hpτ]
  have hb : ∀ i, i ∉ blowupDivisor Δ j t →
      (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) i = 0 :=
    fun i hi => chartN_eq_zero (fun l hl => divisorExponent_eq_zero hl) (τ - p) hi
  -- `Θ'(g') ⊆ (x^b)`.
  have hB : logJacobian (blowupDivisor Δ j t) g' ≤
      Ideal.span {monomial (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) 1} := by
    intro φ hφ
    have h2 := span_mul_logJacobian_le_map_pointChart p (Δ := Δ) h
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hφ)
    have h3 := Ideal.mem_span_singleton.mp (hB1 h2)
    rw [hXb, mul_assoc] at h3
    have h4 := (mul_dvd_mul_iff_left (pow_ne_zero p (X_ne_zero j))).mp h3
    exact Ideal.mem_span_singleton.mpr
      (monomial_one_dvd_of_dvd_mul (constantCoeff_blowupUnit_ne_zero Δ j t) h4)
  -- `π(f) = x_j^p φ` with `φ ∈ Θ'(g')`, and `φ = x^b W`.
  obtain ⟨φ, hφ, hφeq⟩ := Ideal.mem_span_singleton_mul.mp
    (map_pointChart_logJacobianTangent_le_span_mul p (Δ := Δ) h (Ideal.mem_map_of_mem _ hf))
  have hφW : φ = monomial (single j (τ - p) + chartExponent j t (divisorExponent Δ g)) 1 * W := by
    refine mul_left_cancel₀ (pow_ne_zero p (X_ne_zero j (R := k))) ?_
    rw [hφeq, hπ, ← mul_assoc, hXb, mul_assoc]
  refine ⟨hb, ?_, ?_⟩
  · rw [logJacobian_cleanPart]
    exact hB
  · rw [logJacobian_cleanPart, ← hφW]
    exact hφ

/-- **The transform of `ψ` lies in `Θ(g'_c)`.** Let `g ≠ 0` be clean with `ord g ≥ p`, let
`π(g) = x_j^p g'`, let `τ` be the order of `Θ₀(g)`, and let `f ∈ Θ₀(g)` with
`π(f) = x_j^τ x^e U ψ'`, with `e = chartExponent j t r` and `U = chartUnit j t r`. If
`ρ(g'_c) = ord ψ' = m`, then `x^{r'} U ψ' ∈ Θ(g'_c)`, with `r' = divisorExponent Δ' g'_c`. Since
`ρ` stays, the monomial `x^b` of `monomial_mul_mem_logJacobian_cleanPart` is `x^{r'}`. -/
theorem monomial_mul_chartUnit_mul_mem_logJacobian_cleanPart (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {τ : ℕ}
    (hτ : idealOrd (logJacobianTangent Δ g) = τ) {f ψ' : MvPolynomial σ k}
    (hf : f ∈ logJacobianTangent Δ g)
    (hπ : pointChart j t f = X j ^ τ * (monomial (chartExponent j t (divisorExponent Δ g)) 1 *
      (chartUnit j t (divisorExponent Δ g) * ψ'))) {m : ℕ}
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m) (hψ' : ord ψ' = m) :
    monomial (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) 1 *
      (chartUnit j t (divisorExponent Δ g) * ψ') ∈
        logJacobian (blowupDivisor Δ j t) (cleanPart p g') := by
  obtain ⟨hb, hle, hmem⟩ := monomial_mul_mem_logJacobian_cleanPart p hg hord h hτ hf hπ
  set b := single j (τ - p) + chartExponent j t (divisorExponent Δ g)
  set r' := divisorExponent (blowupDivisor Δ j t) (cleanPart p g')
  have hcl := (logJacobianOrder_cleanPart_le p (Δ := Δ) hg hc hord h).1
  have hbr : b ≤ r' := le_divisorExponent_of_logJacobian_le p hcl (isClean_cleanPart p g') hb hle
  -- `|r'| ≤ |b|`, from the order of `x^b U ψ'`.
  have hdeg : degree r' ≤ degree b := by
    have h1 := idealOrd_le_ord hmem
    rw [idealOrd_logJacobian, hρ', ord_mul, ord_mul, ord_monomial one_ne_zero, ord_chartUnit,
      zero_add, hψ'] at h1
    have h2 : ((degree r' + m : ℕ) : ℕ∞) ≤ ((degree b + m : ℕ) : ℕ∞) := by
      push_cast
      exact h1
    have h3 : degree r' + m ≤ degree b + m := by exact_mod_cast h2
    omega
  have hrb : r' = b := by
    obtain ⟨c, hc⟩ := exists_add_of_le hbr
    have hc0 : degree c = 0 := by
      have := congrArg degree hc
      rw [map_add] at this
      omega
    rw [hc, (Finsupp.degree_eq_zero_iff c).mp hc0, add_zero]
  rw [hrb]
  exact hmem

omit [DecidableEq σ] [DecidableEq k] [Fintype σ] in
/-- The directrix of the part of degree `m` of `U ψ'` is the directrix of `ψ'_m`, for `U` with a
nonzero constant term and `ord ψ' ≥ m`. -/
theorem directrix_homogeneousComponent_mul {m : ℕ} {u ψ' : MvPolynomial σ k}
    (hu : constantCoeff u ≠ 0) (hψ' : (m : ℕ∞) ≤ ord ψ') :
    directrix (homogeneousComponent m (u * ψ')) = directrix (homogeneousComponent m ψ') := by
  rw [homogeneousComponent_mul_of_le_ord hψ', ← smul_eq_C_mul, directrix_smul hu]

omit [Fintype σ] in
/-- For each `ψ` of the definition of `T_ρ(g)`, the chart sends `x^r ψ` (case A) or `x_j x^r ψ`
(case B) to `x_j^τ x^e U ψ'`, with `τ` the order of `Θ₀(g)`, and this element lies in `Θ₀(g)`. -/
theorem exists_mem_logJacobianTangent_of_mem_logJacobianDirectrixSet {m : ℕ}
    (hρ : logJacobianOrder Δ g = m) {ψ ψ' : MvPolynomial σ k}
    (hψ : ψ ∈ logJacobianDirectrixSet Δ g) (hψ' : pointChart j t ψ = X j ^ m * ψ') :
    ∃ f ∈ logJacobianTangent Δ g, ∃ τ : ℕ, idealOrd (logJacobianTangent Δ g) = τ ∧
      pointChart j t f = X j ^ τ * (monomial (chartExponent j t (divisorExponent Δ g)) 1 *
        (chartUnit j t (divisorExponent Δ g) * ψ')) := by
  obtain ⟨hψo, hψm⟩ := hψ
  rw [hρ] at hψo
  by_cases hA : idealOrd (logJacobianTangent Δ g) =
      degree (divisorExponent Δ g) + logJacobianOrder Δ g
  · rw [logJacobianCaseIdeal_of_eq hA] at hψm
    refine ⟨_, hψm, degree (divisorExponent Δ g) + m, ?_, pointChart_monomial_mul_eq hψ'⟩
    rw [hA, hρ, Nat.cast_add]
  · rw [logJacobianCaseIdeal_of_ne hA] at hψm
    have hf : X j * (monomial (divisorExponent Δ g) 1 * ψ) ∈ logJacobianTangent Δ g :=
      span_range_X_mul_logJacobian_le Δ g (Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) hψm)
    refine ⟨_, hf, degree (divisorExponent Δ g) + m + 1, ?_, ?_⟩
    · have h1 : idealOrd (logJacobianTangent Δ g) ≤
          ((degree (divisorExponent Δ g) + m + 1 : ℕ) : ℕ∞) := by
        refine (idealOrd_le_ord hf).trans (le_of_eq ?_)
        rw [ord_mul, ord_mul, ord_X, ord_monomial one_ne_zero, hψo]
        push_cast
        ring
      have h2 : ((degree (divisorExponent Δ g) + m : ℕ) : ℕ∞) ≤
          idealOrd (logJacobianTangent Δ g) := by
        rw [Nat.cast_add, ← hρ, ← idealOrd_logJacobian]
        exact idealOrd_anti (logJacobianTangent_le Δ g)
      rw [hρ, ← Nat.cast_add] at hA
      cases hτ : idealOrd (logJacobianTangent Δ g) using ENat.recTopCoe with
      | top => rw [hτ] at h1; exact absurd h1 (by simp)
      | coe a =>
        rw [hτ] at h1 h2 hA
        have h1' : a ≤ degree (divisorExponent Δ g) + m + 1 := by exact_mod_cast h1
        have h2' : degree (divisorExponent Δ g) + m ≤ a := by exact_mod_cast h2
        have hA' : a ≠ degree (divisorExponent Δ g) + m := fun h => hA (by rw [h])
        exact_mod_cast (by omega : a = degree (divisorExponent Δ g) + m + 1)
    · rw [map_mul, pointChart_X_self, pointChart_monomial_mul_eq hψ', pow_succ]
      ring

end Transform

/-! ### Proposition 3.8.2 -/

section Proposition

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]
  {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- **`τ_ρ` does not go down at a new point of case B** (Volume 7, Section 3.8 of the handbook,
Proposition 3.8.2). Let `g ≠ 0` be clean with `ord g ≥ p`, let `π(g) = x_j^p g'` in the chart
`π = pointChart j t`, and let `ρ(g'_c) = ρ(g) = m` for the new divisor `Δ' = blowupDivisor Δ j t`.
If the new point is of case B, that is the order of `Θ₀(g'_c)` is `|r'| + m + 1` with
`r' = divisorExponent Δ' g'_c`, then `dim T_ρ(g'_c) ≤ dim T_ρ(g)`. -/
theorem finrank_logJacobianDirectrix_cleanPart_le (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + m + 1 : ℕ) : ℕ∞)) :
    finrank k (logJacobianDirectrix (blowupDivisor Δ j t) (cleanPart p g')) ≤
      finrank k (logJacobianDirectrix Δ g) := by
  -- The facts on the transform `ψ'` of each `ψ` of the old definition.
  have key : ∀ ψ ∈ logJacobianDirectrixSet Δ g,
      (m : ℕ∞) ≤ ord ψ ∧ (m : ℕ∞) ≤ ord (chartTransform j t m ψ) ∧
        chartUnit j t (divisorExponent Δ g) * chartTransform j t m ψ ∈
          logJacobianDirectrixSet (blowupDivisor Δ j t) (cleanPart p g') := by
    intro ψ hψ
    have hψo : ord ψ = m := by rw [hψ.1, hρ]
    have hψ' := pointChart_eq_X_pow_mul_chartTransform j t hψo.ge
    obtain ⟨f, hf, τ, hτ, hπ⟩ :=
      exists_mem_logJacobianTangent_of_mem_logJacobianDirectrixSet hρ hψ hψ'
    have hle := logJacobianOrder_cleanPart_le_ord_of_pointChart_eq p hg hc hord h hτ hf hπ
    rw [hρ'] at hle
    have hψ'o : ord (chartTransform j t m ψ) = m :=
      le_antisymm (ord_le_of_pointChart hψo hψ') hle
    refine ⟨hψo.ge, hle, ?_, ?_⟩
    · rw [ord_mul, ord_chartUnit, zero_add, hψ'o, hρ']
    · rw [logJacobianCaseIdeal_of_ne]
      · exact monomial_mul_chartUnit_mul_mem_logJacobian_cleanPart p hg hc hord h hτ hf hπ hρ'
          hψ'o
      · rw [hB, hρ', ← Nat.cast_add]
        norm_cast
        omega
  have hU : constantCoeff (chartUnit j t (divisorExponent Δ g)) ≠ 0 := fun h0 => by
    have := one_le_ord_iff.mpr h0
    rw [ord_chartUnit] at this
    exact absurd this (by norm_num)
  refine finrank_le_finrank_of_mem_of_forall_mem (j := j) (v := chartVector j t) ?_
    (by simp [chartVector]) ?_
  · refine (Submodule.mem_iInf _).mpr fun ψ => (Submodule.mem_iInf _).mpr fun hψ => ?_
    obtain ⟨h1, h2, -⟩ := key ψ hψ
    rw [hρ, ENat.toNat_natCast]
    exact mem_directrix_of_le_ord_pointChart h1 (pointChart_eq_X_pow_mul_chartTransform j t h1) h2
  · intro w hw hwj
    refine (Submodule.mem_iInf _).mpr fun ψ => (Submodule.mem_iInf _).mpr fun hψ => ?_
    obtain ⟨h1, h2, h3⟩ := key ψ hψ
    have h4 := logJacobianDirectrix_le h3 hw
    rw [hρ', ENat.toNat_natCast, directrix_homogeneousComponent_mul hU h2] at h4
    rw [hρ, ENat.toNat_natCast]
    exact mem_directrix_of_mem_directrix_pointChart h1
      (pointChart_eq_X_pow_mul_chartTransform j t h1) h2 hwj h4

/-- **`τ_ρ` does not go down at a new point of case B**, the form with the codimension
(Volume 7, Section 3.8 of the handbook, Proposition 3.8.2). -/
theorem logJacobianDirectrixCodim_le_cleanPart (hg : g ≠ 0) (hc : IsClean p g)
    (hord : (p : ℕ∞) ≤ ord g) (h : pointChart j t g = X j ^ p * g') {m : ℕ}
    (hρ : logJacobianOrder Δ g = m)
    (hρ' : logJacobianOrder (blowupDivisor Δ j t) (cleanPart p g') = m)
    (hB : idealOrd (logJacobianTangent (blowupDivisor Δ j t) (cleanPart p g')) =
      ((degree (divisorExponent (blowupDivisor Δ j t) (cleanPart p g')) + m + 1 : ℕ) : ℕ∞)) :
    logJacobianDirectrixCodim Δ g ≤
      logJacobianDirectrixCodim (blowupDivisor Δ j t) (cleanPart p g') := by
  have := finrank_logJacobianDirectrix_cleanPart_le p hg hc hord h hρ hρ' hB
  unfold logJacobianDirectrixCodim
  omega

end Proposition

/-! ### Example 3.8.3 -/

section ExampleGeneral

variable {σ k : Type*} [Field k]

/-- The directrix of `0` is the whole space. -/
theorem directrix_zero : directrix (0 : MvPolynomial σ k) = ⊤ := by
  ext v
  simp [mem_directrix_iff]

/-- The directrix of `x_i^n` for `n ≠ 0` is the hyperplane `w_i = 0`. -/
theorem mem_directrix_X_pow_iff {i : σ} {n : ℕ} (hn : n ≠ 0) {w : σ → k} :
    w ∈ directrix (X i ^ n : MvPolynomial σ k) ↔ w i = 0 := by
  rw [mem_directrix_iff]
  constructor
  · intro h
    have h' := congrArg (MvPolynomial.eval fun o : Option σ => Option.elim o (1 : k) fun _ => 0) h
    simpa [translate, hn] using h'
  · intro h
    simp [translate, h]

theorem span_singleton_le_directrix_X_pow {i : σ} {n : ℕ} (hn : n ≠ 0) {w : σ → k}
    (hw : w i = 0) : Submodule.span k {w} ≤ directrix (X i ^ n : MvPolynomial σ k) :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr ((mem_directrix_X_pow_iff hn).mpr hw)

/-- The part of degree `n + 1` of `x_i f` is `x_i f_n` if `ord f ≥ n`. -/
theorem homogeneousComponent_X_mul {n : ℕ} {f : MvPolynomial σ k} (hf : (n : ℕ∞) ≤ ord f)
    (i : σ) : homogeneousComponent (n + 1) (X i * f) = X i * homogeneousComponent n f := by
  have h1 : X i * f = X i * homogeneousComponent n f + X i * (f - homogeneousComponent n f) := by
    ring
  have h2 : homogeneousComponent (n + 1) (X i * (f - homogeneousComponent n f)) = 0 := by
    refine homogeneousComponent_eq_zero_of_lt_ord ?_
    have := natCast_succ_le_ord_X_mul (lt_ord_sub_homogeneousComponent hf) i
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self (n + 1)) this
  rw [h1, map_add, h2, add_zero]
  refine homogeneousComponent_eq_self ?_
  rw [add_comm]
  exact (isHomogeneous_X k i).mul (homogeneousComponent_isHomogeneous n f)

/-- The part of degree `n` of `x_i^n + q` is `x_i^n` if `ord q > n`. -/
theorem homogeneousComponent_X_pow_add {i : σ} {n : ℕ} {q : MvPolynomial σ k}
    (hq : (n : ℕ∞) < ord q) : homogeneousComponent n (X i ^ n + q) = X i ^ n := by
  rw [map_add, homogeneousComponent_eq_self (isHomogeneous_X_pow i n),
    homogeneousComponent_eq_zero_of_lt_ord hq, add_zero]

/-- The order of `x_i^n + q` is `n` if `ord q > n`. -/
theorem ord_X_pow_add {i : σ} {n : ℕ} {q : MvPolynomial σ k} (hq : (n : ℕ∞) < ord q) :
    ord (X i ^ n + q) = n := by
  refine le_antisymm (ord_le_of_homogeneousComponent_ne_zero ?_) (le_ord_add (ord_X_pow i n).ge hq.le)
  rw [homogeneousComponent_X_pow_add hq]
  exact pow_ne_zero _ (X_ne_zero i)

/-- If each element of `S` has order at least `n` and a part of degree `n` in `V`, then the part
of degree `n` of each element of the ideal generated by `S` is in `V`. -/
theorem homogeneousComponent_mem_of_mem_span {S : Set (MvPolynomial σ k)} {n : ℕ}
    {V : Submodule k (MvPolynomial σ k)}
    (hS : ∀ s ∈ S, (n : ℕ∞) ≤ ord s ∧ homogeneousComponent n s ∈ V) {f : MvPolynomial σ k}
    (hf : f ∈ Ideal.span S) : homogeneousComponent n f ∈ V := by
  refine Submodule.span_le.mpr ?_ (homogeneousComponent_mem_span_of_mem_span
    (fun s hs => (hS s hs).1) hf)
  rintro _ ⟨s, hs, rfl⟩
  exact (hS s hs).2

theorem isClean_monomial {q : ℕ} {a : σ →₀ ℕ} (ha : ¬ ∀ i, q ∣ a i) (c : k) :
    IsClean q (monomial a c) := by
  classical
  intro d hd
  obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hd)
  exact ha

theorem isClean_add {q : ℕ} {F G : MvPolynomial σ k} (hF : IsClean q F) (hG : IsClean q G) :
    IsClean q (F + G) := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hF d h
  · exact hG d h

end ExampleGeneral

section Example

/-! The data of Example 3.8.3. The coordinates `(x, y, z)` are `X 0`, `X 1` and `X 2`. -/

local notation "tgA" =>
  (X 0 * X 1 * X 2 ^ 2 + X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2))
local notation "tgB" =>
  (X 0 ^ 2 * X 1 * X 2 ^ 2 + X 0 * X 1 ^ 2 * X 2 + X 0 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2))

private theorem tex_A_eq : tgA =
    monomial (single 0 1 + single 1 1 + single 2 2) 1 + monomial (single 1 2 + single 2 1) 1 +
      monomial (single 0 1 + single 2 2) 1 := by
  simp only [X_pow_eq_monomial]
  rw [show (X 0 : MvPolynomial (Fin 3) (ZMod 2)) = monomial (single 0 1) 1 from rfl,
    show (X 1 : MvPolynomial (Fin 3) (ZMod 2)) = monomial (single 1 1) 1 from rfl,
    show (X 2 : MvPolynomial (Fin 3) (ZMod 2)) = monomial (single 2 1) 1 from rfl]
  simp only [monomial_mul_monomial, one_mul]

private theorem tex_B_eq : tgB =
    monomial (single 0 2 + single 1 1 + single 2 2) 1 +
      monomial (single 0 1 + single 1 2 + single 2 1) 1 + monomial (single 0 1 + single 2 2) 1 := by
  simp only [X_pow_eq_monomial]
  rw [show (X 0 : MvPolynomial (Fin 3) (ZMod 2)) = monomial (single 0 1) 1 from rfl,
    show (X 1 : MvPolynomial (Fin 3) (ZMod 2)) = monomial (single 1 1) 1 from rfl,
    show (X 2 : MvPolynomial (Fin 3) (ZMod 2)) = monomial (single 2 1) 1 from rfl]
  simp only [monomial_mul_monomial, one_mul]

private theorem tex_ne13 :
    (single 0 2 + single 1 1 + single 2 2 : Fin 3 →₀ ℕ) ≠ single 0 1 + single 2 2 := by
  intro h
  have := DFunLike.congr_fun h 0
  simp at this

private theorem tex_ne23 :
    (single 0 1 + single 1 2 + single 2 1 : Fin 3 →₀ ℕ) ≠ single 0 1 + single 2 2 := by
  intro h
  have := DFunLike.congr_fun h 1
  simp at this

private theorem tex_isClean_A : IsClean 2 tgA := by
  rw [tex_A_eq]
  exact isClean_add (isClean_add (isClean_monomial (fun h => absurd (h 0) (by simp)) _)
    (isClean_monomial (fun h => absurd (h 2) (by simp)) _))
    (isClean_monomial (fun h => absurd (h 0) (by simp)) _)

private theorem tex_isClean_B : IsClean 2 tgB := by
  rw [tex_B_eq]
  exact isClean_add (isClean_add (isClean_monomial (fun h => absurd (h 1) (by simp)) _)
    (isClean_monomial (fun h => absurd (h 0) (by simp)) _))
    (isClean_monomial (fun h => absurd (h 0) (by simp)) _)

private theorem tex_A_ne : tgA ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval fun _ => (1 : ZMod 2)) h
  simp only [map_add, map_mul, map_pow, eval_X, map_zero, one_pow, mul_one] at this
  exact absurd this (by decide)

private theorem tex_ord_A : ((3 : ℕ) : ℕ∞) ≤ ord tgA := by
  refine le_ord_add (le_ord_add ?_ ?_) ?_
  · rw [ord_mul, ord_mul, ord_X, ord_X, ord_X_pow]
    norm_num
  · rw [ord_mul, ord_X, ord_X_pow]
    norm_num
  · rw [ord_mul, ord_X, ord_X_pow]
    norm_num

private theorem tex_ord_B : ((3 : ℕ) : ℕ∞) ≤ ord tgB := by
  refine le_ord_add (le_ord_add ?_ ?_) ?_
  · rw [ord_mul, ord_mul, ord_X, ord_X_pow, ord_X_pow]
    norm_num
  · rw [ord_mul, ord_mul, ord_X, ord_X, ord_X_pow]
    norm_num
  · rw [ord_mul, ord_X, ord_X_pow]
    norm_num

private theorem tex_pointChart : pointChart 0 (0 : Fin 3 → ZMod 2) tgA = X 0 ^ 2 * tgB := by
  simp [pointChart]
  ring

private theorem tex_dE_A : divisorExponent ∅ tgA = 0 := by
  ext i
  simpa using divisorExponent_eq_zero (Δ := ∅) (P := tgA) (i := i) (by simp)

private theorem tex_blowupDivisor :
    blowupDivisor (∅ : Finset (Fin 3)) 0 (0 : Fin 3 → ZMod 2) = {0} := by
  decide

private theorem tex_cleanPart : cleanPart 2 tgB = tgB :=
  cleanPart_eq_self tex_isClean_B

private theorem tex_dE_B : divisorExponent {0} tgB = single 0 1 := by
  rw [tex_B_eq]
  set P : MvPolynomial (Fin 3) (ZMod 2) := monomial (single 0 2 + single 1 1 + single 2 2) 1 +
      monomial (single 0 1 + single 1 2 + single 2 1) 1 + monomial (single 0 1 + single 2 2) 1
  have hb : (single 0 1 + single 2 2 : Fin 3 →₀ ℕ) ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial, coeff_monomial, coeff_monomial, ite_eq_right tex_ne13, ite_eq_right tex_ne23, ite_eq_left rfl]
    decide
  have hP : P ≠ 0 := MvPolynomial.ne_zero_iff.mpr ⟨_, MvPolynomial.mem_support_iff.mp hb⟩
  have h1 := divisorExponent_le (Δ := {0}) hb
  have h2 : (single 0 1 : Fin 3 →₀ ℕ) ≤ divisorExponent {0} P := by
    refine le_divisorExponent hP (fun i hi => ?_) fun β hβ => ?_
    · rw [Finset.mem_singleton] at hi
      simp [Ne.symm hi]
    · rcases Finset.mem_union.mp (MvPolynomial.support_add hβ) with h | h
      · rcases Finset.mem_union.mp (MvPolynomial.support_add h) with h | h <;>
          obtain rfl := Finset.mem_singleton.mp (support_monomial_subset h) <;>
          intro i <;> fin_cases i <;> simp
      · obtain rfl := Finset.mem_singleton.mp (support_monomial_subset h)
        intro i
        fin_cases i <;> simp
  ext i
  fin_cases i
  · exact le_antisymm (by simpa using h1 0) (by simpa using h2 0)
  · simpa using divisorExponent_eq_zero (Δ := {0}) (P := P) (i := 1) (by decide)
  · simpa using divisorExponent_eq_zero (Δ := {0}) (P := P) (i := 2) (by decide)

private theorem tex_pd0 : pderiv 0 tgA = X 2 ^ 2 + X 1 * X 2 ^ 2 := by
  simp [pderiv_X]
  ring

private theorem tex_pd1 : pderiv 1 tgA = X 0 * X 2 ^ 2 := by
  simp [pderiv_X]
  linear_combination (X 1 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) *
    two_eq_zero_mvPolynomial_zmod (Fin 3)

private theorem tex_pd2 : pderiv 2 tgA = X 1 ^ 2 := by
  simp [pderiv_X]
  linear_combination (X 0 * X 1 * X 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) *
    two_eq_zero_mvPolynomial_zmod (Fin 3)

private theorem tex_pd0' : pderiv 0 tgB = X 2 ^ 2 + X 1 ^ 2 * X 2 := by
  simp [pderiv_X]
  linear_combination (X 0 * X 1 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) *
    two_eq_zero_mvPolynomial_zmod (Fin 3)

private theorem tex_pd1' : pderiv 1 tgB = X 0 ^ 2 * X 2 ^ 2 := by
  simp [pderiv_X]
  linear_combination (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) *
    two_eq_zero_mvPolynomial_zmod (Fin 3)

private theorem tex_pd2' : pderiv 2 tgB = X 0 * X 1 ^ 2 := by
  simp [pderiv_X]
  linear_combination (X 0 ^ 2 * X 1 * X 2 + X 0 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) *
    two_eq_zero_mvPolynomial_zmod (Fin 3)

private theorem tex_lt_X_mul_X_pow (i j : Fin 3) :
    ((2 : ℕ) : ℕ∞) < ord (X i * X j ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) := by
  rw [ord_X_mul_X_pow]
  norm_num

private theorem tex_lt_X_pow_mul_X (i j : Fin 3) :
    ((2 : ℕ) : ℕ∞) < ord (X i ^ 2 * X j : MvPolynomial (Fin 3) (ZMod 2)) := by
  rw [mul_comm, ord_X_mul_X_pow]
  norm_num

/-- The generators `∂_l g` of `Θ(g)` have order at least `2`, and the line `k e_0` is in the
directrix of their parts of degree `2`. -/
private theorem tex_gen_A (l : Fin 3) :
    ((2 : ℕ) : ℕ∞) ≤ ord (pderiv l tgA) ∧
      Submodule.span (ZMod 2) {(Pi.single 0 1 : Fin 3 → ZMod 2)} ≤
        directrix (homogeneousComponent 2 (pderiv l tgA)) := by
  have h0 : ((2 : ℕ) : ℕ∞) ≤ ord (pderiv 0 tgA) ∧
      Submodule.span (ZMod 2) {(Pi.single 0 1 : Fin 3 → ZMod 2)} ≤
        directrix (homogeneousComponent 2 (pderiv 0 tgA)) := by
    rw [tex_pd0, ord_X_pow_add (tex_lt_X_mul_X_pow 1 2),
      homogeneousComponent_X_pow_add (tex_lt_X_mul_X_pow 1 2)]
    exact ⟨le_rfl, span_singleton_le_directrix_X_pow two_ne_zero (by simp)⟩
  have h1 : ((2 : ℕ) : ℕ∞) ≤ ord (pderiv 1 tgA) ∧
      Submodule.span (ZMod 2) {(Pi.single 0 1 : Fin 3 → ZMod 2)} ≤
        directrix (homogeneousComponent 2 (pderiv 1 tgA)) := by
    rw [tex_pd1, homogeneousComponent_eq_zero_of_lt_ord (tex_lt_X_mul_X_pow 0 2), directrix_zero]
    exact ⟨(tex_lt_X_mul_X_pow 0 2).le, le_top⟩
  have h2 : ((2 : ℕ) : ℕ∞) ≤ ord (pderiv 2 tgA) ∧
      Submodule.span (ZMod 2) {(Pi.single 0 1 : Fin 3 → ZMod 2)} ≤
        directrix (homogeneousComponent 2 (pderiv 2 tgA)) := by
    rw [tex_pd2, ord_X_pow, homogeneousComponent_eq_self (isHomogeneous_X_pow _ _)]
    exact ⟨le_rfl, span_singleton_le_directrix_X_pow two_ne_zero (by simp)⟩
  fin_cases l
  · exact h0
  · exact h1
  · exact h2

/-- **Example 3.8.3, the data.** Over `𝔽₂`, the polynomial `g = x y z^2 + y^2 z + x z^2` is not
`0`, is clean for `p = 2`, has order at least `2`, and in the `x`-chart at the origin it goes to
`x^2 g'` with `g' = x^2 y z^2 + x y^2 z + x z^2`. -/
theorem tauRhoExample_hyp :
    tgA ≠ 0 ∧ IsClean 2 tgA ∧ ((2 : ℕ) : ℕ∞) ≤ ord tgA ∧
      pointChart 0 (0 : Fin 3 → ZMod 2) tgA = X 0 ^ 2 * tgB :=
  ⟨tex_A_ne, tex_isClean_A, le_trans (by norm_num) tex_ord_A, tex_pointChart⟩

private theorem tex_rho_A : logJacobianOrder ∅ tgA = 2 := by
  have hI := idealOrd_logJacobian ∅ tgA
  rw [tex_dE_A, map_zero, Nat.cast_zero, zero_add] at hI
  rw [← hI]
  refine le_antisymm ?_ ?_
  · refine (idealOrd_le_ord (pderiv_mem_logJacobian (j := 2) (by simp) _)).trans ?_
    rw [tex_pd2, ord_X_pow]
    norm_num
  · have : ((2 : ℕ) : ℕ∞) ≤ idealOrd (logJacobian ∅ tgA) := by
      unfold logJacobian
      refine le_idealOrd_span ?_
      rintro s (⟨i, hi, rfl⟩ | ⟨l, -, rfl⟩)
      · simp at hi
      · exact (tex_gen_A l).1
    exact_mod_cast this

private theorem tex_rho_B : logJacobianOrder {0} tgB = 2 := by
  have hle := (logJacobianOrder_cleanPart_le 2 (Δ := ∅) tex_A_ne tex_isClean_A
    (le_trans (by norm_num) tex_ord_A) tex_pointChart).2
  rw [tex_rho_A, tex_blowupDivisor, tex_cleanPart] at hle
  refine le_antisymm hle ?_
  have hI := idealOrd_logJacobian {0} tgB
  rw [tex_dE_B, degree_single] at hI
  have h3 : ((3 : ℕ) : ℕ∞) ≤ idealOrd (logJacobian {0} tgB) := by
    refine le_idealOrd_span ?_
    rintro s (⟨i, hi, rfl⟩ | ⟨l, hl, rfl⟩)
    · obtain rfl : i = 0 := by simpa using hi
      dsimp only
      rw [tex_pd0', ord_mul, ord_X, ord_X_pow_add (tex_lt_X_pow_mul_X 1 2)]
      norm_num
    · have hl' : l ∉ ({0} : Finset (Fin 3)) := hl
      have h1 : ((3 : ℕ) : ℕ∞) ≤ ord (pderiv 1 tgB) := by
        rw [tex_pd1', ord_mul, ord_X_pow, ord_X_pow]
        norm_num
      have h2 : ((3 : ℕ) : ℕ∞) ≤ ord (pderiv 2 tgB) := by
        rw [tex_pd2', ord_X_mul_X_pow]
      revert hl'
      fin_cases l
      · decide
      · exact fun _ => h1
      · exact fun _ => h2
  rw [hI] at h3
  cases h : logJacobianOrder {0} tgB using ENat.recTopCoe with
  | top => exact le_top
  | coe a =>
    rw [h] at h3
    have : 3 ≤ 1 + a := by exact_mod_cast h3
    exact_mod_cast (by omega : 2 ≤ a)

/-- At the old point, `Θ₀(g)` has order at least `3 = |r| + ρ(g) + 1` (case B). -/
private theorem tex_caseB_A :
    idealOrd (logJacobianTangent ∅ tgA) ≠ degree (divisorExponent ∅ tgA) + logJacobianOrder ∅ tgA := by
  rw [tex_dE_A, tex_rho_A, map_zero, Nat.cast_zero, zero_add]
  intro h
  have := le_idealOrd_logJacobianTangent (Δ := ∅) tex_ord_A
  rw [h] at this
  norm_num at this

/-- At the new point, `Θ₀(g'_c)` has order `3 = |r'| + ρ(g'_c)` (case A). -/
private theorem tex_caseA_B : idealOrd (logJacobianTangent {0} tgB) =
    degree (divisorExponent {0} tgB) + logJacobianOrder {0} tgB := by
  rw [tex_dE_B, tex_rho_B, degree_single]
  refine le_antisymm ?_ ?_
  · refine (idealOrd_le_ord (X_mul_pderiv_mem_logJacobianTangent (Δ := {0}) (i := 0) (by simp)
      tgB)).trans ?_
    rw [tex_pd0', ord_mul, ord_X, ord_X_pow_add (tex_lt_X_pow_mul_X 1 2)]
    norm_num
  · have := le_idealOrd_logJacobianTangent (Δ := {0}) tex_ord_B
    refine le_trans (le_of_eq ?_) this
    norm_num

private theorem tex_T_A :
    logJacobianDirectrix ∅ tgA = Submodule.span (ZMod 2) {(Pi.single 0 1 : Fin 3 → ZMod 2)} := by
  have hset : ∀ ψ, ψ ∈ logJacobianDirectrixSet ∅ tgA ↔ ord ψ = 2 ∧ ψ ∈ logJacobian ∅ tgA := by
    intro ψ
    rw [logJacobianDirectrixSet, Set.mem_ofPred_eq, logJacobianCaseIdeal_of_ne tex_caseB_A,
      tex_dE_A, tex_rho_A, monomial_zero', C_1, one_mul]
  have hn : (logJacobianOrder ∅ tgA).toNat = 2 := by
    rw [tex_rho_A]
    rfl
  refine le_antisymm ?_ ?_
  · intro w hw
    have hm1 : (X 1 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) ∈ logJacobian ∅ tgA := by
      have := pderiv_mem_logJacobian (Δ := ∅) (j := 2) (Finset.notMem_empty 2) tgA
      rwa [tex_pd2] at this
    have hm2 : (X 2 ^ 2 + X 1 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) ∈ logJacobian ∅ tgA := by
      have := pderiv_mem_logJacobian (Δ := ∅) (j := 0) (Finset.notMem_empty 0) tgA
      rwa [tex_pd0] at this
    have ho1 : ord (X 1 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) = 2 :=
      (ord_X_pow (R := ZMod 2) (1 : Fin 3) 2).trans (by norm_num)
    have ho2 : ord (X 2 ^ 2 + X 1 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) = 2 :=
      (ord_X_pow_add (tex_lt_X_mul_X_pow 1 2)).trans (by norm_num)
    have h1 := logJacobianDirectrix_le ((hset (X 1 ^ 2)).mpr ⟨ho1, hm1⟩) hw
    have h2 := logJacobianDirectrix_le ((hset (X 2 ^ 2 + X 1 * X 2 ^ 2)).mpr ⟨ho2, hm2⟩) hw
    rw [hn, homogeneousComponent_eq_self (isHomogeneous_X_pow _ _),
      mem_directrix_X_pow_iff two_ne_zero] at h1
    rw [hn, homogeneousComponent_X_pow_add (tex_lt_X_mul_X_pow 1 2),
      mem_directrix_X_pow_iff two_ne_zero] at h2
    refine Submodule.mem_span_singleton.mpr ⟨w 0, ?_⟩
    funext i
    fin_cases i <;> simp [h1, h2]
  · refine le_logJacobianDirectrix fun ψ hψ => ?_
    rw [hset] at hψ
    rw [hn]
    refine le_directrix_homogeneousComponent_of_mem_span (n := 2) ?_ ?_ hψ.2
    · rintro s (⟨i, hi, rfl⟩ | ⟨l, -, rfl⟩)
      · simp at hi
      · exact (tex_gen_A l).1
    · rintro s (⟨i, hi, rfl⟩ | ⟨l, -, rfl⟩)
      · simp at hi
      · exact (tex_gen_A l).2

/-- The generators `x_m ∂_l g'` with `l ≠ 0` of `Θ₀(g')` have order at least `4`. -/
private theorem tex_high {F : MvPolynomial (Fin 3) (ZMod 2)} (h : ((3 : ℕ) : ℕ∞) ≤ ord F)
    (a : Fin 3) (V : Submodule (ZMod 2) (MvPolynomial (Fin 3) (ZMod 2))) :
    ((3 : ℕ) : ℕ∞) ≤ ord (X a * F) ∧ homogeneousComponent 3 (X a * F) ∈ V := by
  have h4 : ((4 : ℕ) : ℕ∞) ≤ ord (X a * F) := natCast_succ_le_ord_X_mul h a
  refine ⟨le_trans (by norm_num) h4, ?_⟩
  rw [homogeneousComponent_eq_zero_of_lt_ord (lt_of_lt_of_le (by norm_num) h4)]
  exact zero_mem V

private theorem tex_T_B :
    logJacobianDirectrix {0} tgB =
      LinearMap.ker (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) := by
  have hset : ∀ ψ, ψ ∈ logJacobianDirectrixSet {0} tgB ↔
      ord ψ = 2 ∧ X 0 * ψ ∈ logJacobianTangent {0} tgB := by
    intro ψ
    rw [logJacobianDirectrixSet, Set.mem_ofPred_eq, logJacobianCaseIdeal_of_eq tex_caseA_B,
      tex_dE_B, tex_rho_B]
    rfl
  have hn : (logJacobianOrder {0} tgB).toNat = 2 := by
    rw [tex_rho_B]
    rfl
  refine le_antisymm ?_ ?_
  · intro w hw
    have h1 := logJacobianDirectrix_le ((hset (X 2 ^ 2 + X 1 ^ 2 * X 2)).mpr
      ⟨(ord_X_pow_add (tex_lt_X_pow_mul_X 1 2)).trans (by norm_num), by
        have := X_mul_pderiv_mem_logJacobianTangent (Δ := {0}) (i := 0)
          (Finset.mem_singleton_self 0) tgB
        rwa [tex_pd0'] at this⟩) hw
    rw [hn, homogeneousComponent_X_pow_add (tex_lt_X_pow_mul_X 1 2),
      mem_directrix_X_pow_iff two_ne_zero] at h1
    simpa using h1
  · refine le_logJacobianDirectrix fun ψ hψ => ?_
    rw [hset] at hψ
    rw [hn]
    intro w hw
    have hw2 : w 2 = 0 := by simpa using hw
    have hψ2 : ((2 : ℕ) : ℕ∞) ≤ ord ψ := by
      rw [hψ.1]
      norm_num
    have hmem : homogeneousComponent (2 + 1) (X 0 * ψ) ∈
        Submodule.span (ZMod 2) {(X 0 * X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2))} := by
      refine homogeneousComponent_mem_of_mem_span ?_ hψ.2
      rintro s (⟨i, hi, rfl⟩ | ⟨⟨a, l⟩, hl, rfl⟩)
      · obtain rfl : i = 0 := by simpa using hi
        dsimp only
        have h2 : ((2 : ℕ) : ℕ∞) ≤ ord (X 2 ^ 2 + X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) :=
          (ord_X_pow_add (tex_lt_X_pow_mul_X 1 2)).ge
        rw [tex_pd0', homogeneousComponent_X_mul h2,
          homogeneousComponent_X_pow_add (tex_lt_X_pow_mul_X 1 2)]
        exact ⟨natCast_succ_le_ord_X_mul h2 0, Submodule.mem_span_singleton_self _⟩
      · have hl' : l ∉ ({0} : Finset (Fin 3)) := hl
        have h1 : ((3 : ℕ) : ℕ∞) ≤ ord (pderiv 1 tgB) := by
          rw [tex_pd1', ord_mul, ord_X_pow, ord_X_pow]
          norm_num
        have h2 : ((3 : ℕ) : ℕ∞) ≤ ord (pderiv 2 tgB) := by
          rw [tex_pd2', ord_X_mul_X_pow]
        dsimp only
        obtain rfl | rfl : l = 1 ∨ l = 2 := by
          revert hl'
          fin_cases l <;> decide
        · exact tex_high h1 a _
        · exact tex_high h2 a _
    rw [homogeneousComponent_X_mul hψ2] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hψ' : homogeneousComponent 2 ψ = c • X 2 ^ 2 :=
      mul_left_cancel₀ (X_ne_zero (0 : Fin 3)) (by rw [← hc, mul_smul_comm])
    rw [hψ']
    exact directrix_le_directrix_smul c _ ((mem_directrix_X_pow_iff two_ne_zero).mpr hw2)

/-- **Example 3.8.3, the cases.** Over `𝔽₂`, let `g = x y z^2 + y^2 z + x z^2` and `E = ∅`. The
point is of case B: the order of `Θ₀(g)` is not `|r| + ρ(g)`. At the origin of the `x`-chart, the
new divisor is `V(x)`, and the new point is of case A: the order of `Θ₀(g'_c)` is
`|r'| + ρ(g'_c)`. -/
theorem tauRhoExample_cases :
    idealOrd (logJacobianTangent ∅ tgA) ≠
        degree (divisorExponent ∅ tgA) + logJacobianOrder ∅ tgA ∧
      idealOrd (logJacobianTangent (blowupDivisor ∅ 0 (0 : Fin 3 → ZMod 2)) (cleanPart 2 tgB)) =
        degree (divisorExponent (blowupDivisor ∅ 0 (0 : Fin 3 → ZMod 2)) (cleanPart 2 tgB)) +
          logJacobianOrder (blowupDivisor ∅ 0 (0 : Fin 3 → ZMod 2)) (cleanPart 2 tgB) := by
  rw [tex_blowupDivisor, tex_cleanPart]
  exact ⟨tex_caseB_A, tex_caseA_B⟩

/-- **Example 3.8.3: the case condition of Proposition 3.8.2 is necessary** (Volume 7,
Section 3.8 of the handbook). Over `𝔽₂`, let `g = x y z^2 + y^2 z + x z^2` and `E = ∅`. Then
`ρ(g) = 2` and `T_ρ(g)` has dimension `1`. At the origin of the `x`-chart, `ρ(g'_c) = 2`, but
`T_ρ(g'_c)` has dimension `2`. So `τ_ρ` goes down from `2` to `1` at this new point of case A. -/
theorem tauRhoExample_finrank :
    logJacobianOrder ∅ tgA = 2 ∧
      logJacobianOrder (blowupDivisor ∅ 0 (0 : Fin 3 → ZMod 2)) (cleanPart 2 tgB) = 2 ∧
      finrank (ZMod 2) (logJacobianDirectrix ∅ tgA) = 1 ∧
      finrank (ZMod 2)
        (logJacobianDirectrix (blowupDivisor ∅ 0 (0 : Fin 3 → ZMod 2)) (cleanPart 2 tgB)) = 2 := by
  rw [tex_blowupDivisor, tex_cleanPart, tex_T_A, tex_T_B]
  refine ⟨tex_rho_A, tex_rho_B, finrank_span_singleton ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · have h := LinearMap.finrank_range_add_finrank_ker
      (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    rw [LinearMap.range_eq_top.mpr (fun c => ⟨fun _ => c, rfl⟩), finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at h
    omega

end Example

end Singularity
