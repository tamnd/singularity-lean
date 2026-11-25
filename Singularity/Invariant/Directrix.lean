/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.OrderBlowup

/-!
# The directrix and the points where the order stays the same

Let `k` be a field and let `g` be a polynomial in `k[x_i : i ∈ σ]`. The directrix `T(g)` of `g` is
the set of the vectors `v` with `g(x + s v) = g(x)` in the polynomial ring `k[x, s]` with one more
variable `s` [Hir67]. It is a linear subspace of `k^σ` (`directrix`).

Let `f` be a polynomial with `ord f = m`, and let the `x_j`-chart with translations `t` send `f`
to `x_j^m f'` (`pointChart`). The vector of the chart is `v` with `v_j = 1` and `v_i = t_i` for
`i ≠ j` (`chartVector`). If `ord f' = m`, then `v` lies in the directrix of the part `f_m` of `f`
of degree `m` (`mem_directrix_of_ord_pointChart_eq`). The field can have any characteristic.

The proof. Let `ρ` be the substitution `x_j ↦ 1` and `x_i ↦ x_i + t_i` (`chartRest`), and let
`h = ρ(f_m)`. The substitution `x_j ↦ 0` sends `f'` to `h`, so `m ≤ ord h`. The total degree of
`h` is at most `m`. So `h` is homogeneous of degree `m`. Let `λ` be the linear substitution
`x_j ↦ x_j` and `x_i ↦ x_i + t_i x_j` (`chartLinear`). The chart is the chart with translations
`0` after `λ`. Both `λ(f_m)` and `h` go to `x_j^m h` under the chart with translations `0`, and
this chart is injective. So `λ(f_m) = h`. The polynomial `h` does not contain `x_j`. Put
`x_j ↦ x_j + s` and `x_i ↦ x_i - t_i x_j` in the equation `λ(f_m) = h`. The left side becomes
`f_m(x + s v)`, and the right side does not contain `s`. With `s = 0` the left side becomes
`f_m(x)`. So `f_m(x + s v) = f_m(x)`.

## Main definitions

* `translate v`: the substitution `x_i ↦ x_i + v_i s` into `k[x, s]`, with `s` the variable
  `none` of `Option σ`.
* `directrix g`: the subspace of the vectors `v` with `g(x + s v) = g(x)`.
* `chartVector j t`: the vector of the `x_j`-chart with translations `t`.

## Main results

* `aeval_add_smul_of_mem_directrix`: if `v ∈ T(g)`, then `g(x + c v) = g(x)` for each `c ∈ k`.
* `mem_directrix_of_isHomogeneous`: if `g` and `ρ(g)` are homogeneous of degree `m`, then the
  vector of the chart lies in `T(g)`.
* `mem_directrix_of_ord_pointChart_eq`: if `ord f = m`, the chart sends `f` to `x_j^m f'` and
  `ord f' = m`, then the vector of the chart lies in `T(f_m)`.
* `mem_directrix_of_le_ord_pointChart`: the same with `m ≤ ord f` and `m ≤ ord f'`.

## References

* [Hir67] H. Hironaka, *Characteristic polyhedra of singularities*, J. Math. Kyoto Univ. 7 (1967).
-/

open MvPolynomial Finsupp

namespace Singularity

variable {σ k : Type*} [Field k]

/-! ### The directrix -/

/-- The substitution `x_i ↦ x_i + v_i s` from `k[x]` into `k[x, s]`. The variable `x_i` of
`k[x, s]` is `X (some i)` and the variable `s` is `X none`. -/
noncomputable def translate (v : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k :=
  aeval fun i => X (some i) + C (v i) * X none

theorem translate_zero : translate (0 : σ → k) = rename some := by
  refine algHom_ext fun i => ?_
  simp [translate]

/-- The substitution `s ↦ c s` sends `g(x + s v)` to `g(x + s (c v))`. -/
theorem scaleVar_comp_translate (c : k) (v : σ → k) :
    (aeval fun o : Option σ => Option.elim o (C c * X none) fun i => X (some i)).comp
      (translate v) = translate (c • v) := by
  refine algHom_ext fun i => ?_
  simp [translate]
  ring

theorem scaleVar_comp_rename (c : k) :
    (aeval fun o : Option σ => Option.elim o (C c * X none) fun i => X (some i)).comp
      (rename some : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k) = rename some := by
  refine algHom_ext fun i => ?_
  simp

/-- The substitution `x ↦ x + s w` sends `g(x + s v)` to `g(x + s (v + w))`. -/
theorem shiftVar_comp_translate (v w : σ → k) :
    (aeval fun o : Option σ => Option.elim o (X none) fun i => X (some i) + C (w i) * X none).comp
      (translate v) = translate (v + w) := by
  refine algHom_ext fun i => ?_
  simp [translate]
  ring

theorem shiftVar_comp_rename (w : σ → k) :
    (aeval fun o : Option σ => Option.elim o (X none) fun i => X (some i) + C (w i) * X none).comp
      (rename some : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k) = translate w := by
  refine algHom_ext fun i => ?_
  simp [translate]

/-- The directrix `T(g)` of a polynomial `g` [Hir67]: the vectors `v` with `g(x + s v) = g(x)` in
the polynomial ring `k[x, s]`. It is a linear subspace of `k^σ`. Over an infinite field it is the
set of the vectors `v` with `g(x + c v) = g(x)` for each `c ∈ k`. Over a finite field this second
set can be larger. -/
noncomputable def directrix (g : MvPolynomial σ k) : Submodule k (σ → k) where
  carrier := {v | translate v g = rename some g}
  zero_mem' := by
    show translate 0 g = rename some g
    rw [translate_zero]
  add_mem' := by
    intro v w hv hw
    show translate (v + w) g = rename some g
    have hv' : translate v g = rename some g := hv
    have hw' : translate w g = rename some g := hw
    rw [← shiftVar_comp_translate, AlgHom.comp_apply, hv', ← AlgHom.comp_apply,
      shiftVar_comp_rename, hw']
  smul_mem' := by
    intro c v hv
    show translate (c • v) g = rename some g
    have hv' : translate v g = rename some g := hv
    rw [← scaleVar_comp_translate, AlgHom.comp_apply, hv', ← AlgHom.comp_apply,
      scaleVar_comp_rename]

theorem mem_directrix_iff {g : MvPolynomial σ k} {v : σ → k} :
    v ∈ directrix g ↔ translate v g = rename some g :=
  Iff.rfl

/-- If `v ∈ T(g)`, then `g(x + c v) = g(x)` for each `c ∈ k`. -/
theorem aeval_add_smul_of_mem_directrix {g : MvPolynomial σ k} {v : σ → k}
    (hv : v ∈ directrix g) (c : k) : aeval (fun i => X i + C (c * v i)) g = g := by
  have h := congrArg (aeval fun o : Option σ => Option.elim o (C c) X) (mem_directrix_iff.mp hv)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply] at h
  have h1 : (aeval fun o : Option σ => Option.elim o (C c) X).comp (translate v) =
      aeval fun i => X i + C (c * v i) := by
    refine algHom_ext fun i => ?_
    simp [translate]
    ring
  have h2 : (aeval fun o : Option σ => Option.elim o (C c) X).comp
      (rename some : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k) = AlgHom.id k _ := by
    refine algHom_ext fun i => ?_
    simp
  rwa [h1, h2, AlgHom.id_apply] at h

/-! ### The vector of a chart -/

variable [DecidableEq σ]

/-- The vector of the `x_j`-chart with translations `t`: the entry `1` at `j` and `t_i` at
`i ≠ j`. The chart is centered on the line of this vector. -/
def chartVector (j : σ) (t : σ → k) : σ → k :=
  fun i => if i = j then 1 else t i

/-- The linear substitution `x_j ↦ x_j` and `x_i ↦ x_i + t_i x_j` for `i ≠ j`. -/
noncomputable def chartLinear (j : σ) (t : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => if i = j then X j else X i + C (t i) * X j

/-- The chart with translations `t` is the chart with translations `0` after `chartLinear`. -/
theorem pointChart_zero_comp_chartLinear (j : σ) (t : σ → k) :
    (pointChart j 0).comp (chartLinear j t) = pointChart j t := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [pointChart, chartLinear]
  · simp [pointChart, chartLinear, h]
    ring

theorem chartRest_zero (j : σ) : chartRest j (0 : σ → k) = dehomogenize j := by
  refine algHom_ext fun i => ?_
  simp [chartRest, dehomogenize]

theorem dehomogenize_comp_chartRest (j : σ) (t : σ → k) :
    (dehomogenize j).comp (chartRest j t) = chartRest j t := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [chartRest, dehomogenize]
  · simp [chartRest, dehomogenize, h]

/-- On a homogeneous polynomial of degree `m`, the chart is `x_j^m` times `ρ`. -/
theorem pointChart_of_isHomogeneous (j : σ) (t : σ → k) {m : ℕ} {p : MvPolynomial σ k}
    (hp : p.IsHomogeneous m) : pointChart j t p = X j ^ m * chartRest j t p := by
  rw [pointChart_eq_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hdeg : degree a = m := by
    by_contra hne
    exact MvPolynomial.mem_support_iff.mp ha (hp.coeff_eq_zero hne)
  rw [hdeg]

theorem totalDegree_chartRest_le (j : σ) (t : σ → k) (p : MvPolynomial σ k) :
    (chartRest j t p).totalDegree ≤ p.totalDegree := by
  refine totalDegree_aeval_le (fun i => ?_) p
  split_ifs
  · simp
  · exact (totalDegree_add _ _).trans (by simp)

/-- If `g` and `ρ(g)` are homogeneous of degree `m`, then `λ(g) = ρ(g)`. -/
theorem chartLinear_eq_chartRest {j : σ} {t : σ → k} {m : ℕ} {g : MvPolynomial σ k}
    (hg : g.IsHomogeneous m) (hh : (chartRest j t g).IsHomogeneous m) :
    chartLinear j t g = chartRest j t g := by
  refine pointChart_injective j 0 ?_
  rw [← AlgHom.comp_apply, pointChart_zero_comp_chartLinear, pointChart_of_isHomogeneous j t hg,
    pointChart_of_isHomogeneous j 0 hh, chartRest_zero, ← AlgHom.comp_apply,
    dehomogenize_comp_chartRest]

/-- The substitution `x_j ↦ x_j + s` and `x_i ↦ x_i - t_i x_j` into `k[x, s]`. -/
noncomputable def chartUnshift (j : σ) (t : σ → k) (b : MvPolynomial (Option σ) k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k :=
  aeval fun i => if i = j then X (some j) + b else X (some i) - C (t i) * X (some j)

theorem chartUnshift_comp_chartLinear (j : σ) (t : σ → k) (b : MvPolynomial (Option σ) k) :
    (chartUnshift j t b).comp (chartLinear j t) =
      aeval fun i => X (some i) + C (chartVector j t i) * b := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [chartUnshift, chartLinear, chartVector]
  · simp [chartUnshift, chartLinear, chartVector, h]
    ring

theorem chartUnshift_comp_chartRest (j : σ) (t : σ → k) (b : MvPolynomial (Option σ) k) :
    (chartUnshift j t b).comp (chartRest j t) = (chartUnshift j t 0).comp (chartRest j t) := by
  refine algHom_ext fun i => ?_
  by_cases h : i = j
  · subst h
    simp [chartUnshift, chartRest]
  · simp [chartUnshift, chartRest, h]

/-- If `g` and `ρ(g)` are homogeneous of degree `m`, then the vector of the chart lies in the
directrix of `g`. -/
theorem mem_directrix_of_isHomogeneous {j : σ} {t : σ → k} {m : ℕ} {g : MvPolynomial σ k}
    (hg : g.IsHomogeneous m) (hh : (chartRest j t g).IsHomogeneous m) :
    chartVector j t ∈ directrix g := by
  have he := chartLinear_eq_chartRest hg hh
  have hs : translate (chartVector j t) g = chartUnshift j t (X none) (chartLinear j t g) := by
    rw [← AlgHom.comp_apply, chartUnshift_comp_chartLinear]
    rfl
  have h0 : rename some g = chartUnshift j t 0 (chartLinear j t g) := by
    rw [← AlgHom.comp_apply, chartUnshift_comp_chartLinear]
    have : (aeval fun i => X (some i) + C (chartVector j t i) * (0 : MvPolynomial (Option σ) k)) =
        (rename some : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k) := by
      refine algHom_ext fun i => ?_
      simp
    rw [this]
  rw [mem_directrix_iff, hs, h0, he, ← AlgHom.comp_apply, chartUnshift_comp_chartRest,
    AlgHom.comp_apply]

/-- **The points where the order stays the same lie in the directrix**, the form with
inequalities. Let `m ≤ ord f`, and let the `x_j`-chart with translations `t` send `f` to
`x_j^m f'`. If `m ≤ ord f'`, then the vector of the chart lies in the directrix of the part `f_m`
of `f` of degree `m`. -/
theorem mem_directrix_of_le_ord_pointChart {j : σ} {t : σ → k} {f f' : MvPolynomial σ k} {m : ℕ}
    (hf : (m : ℕ∞) ≤ ord f) (h : pointChart j t f = X j ^ m * f') (hf' : (m : ℕ∞) ≤ ord f') :
    chartVector j t ∈ directrix (homogeneousComponent m f) := by
  have h' := pointChart_eq_X_pow_mul_chartTransform j t hf
  rw [h] at h'
  have hf'_eq := mul_left_cancel₀ (pow_ne_zero m (X_ne_zero j)) h'
  have hg := homogeneousComponent_isHomogeneous m f
  refine mem_directrix_of_isHomogeneous hg ?_
  have hk : killVar j f' = chartRest j t (homogeneousComponent m f) := by
    rw [hf'_eq, killVar_chartTransform j t hf, homogeneousComponent_apply]
  have hord : (m : ℕ∞) ≤ ord (chartRest j t (homogeneousComponent m f)) := by
    rw [← hk]
    exact hf'.trans (ord_le_ord_killVar j f')
  have hdeg : (chartRest j t (homogeneousComponent m f)).totalDegree ≤ m :=
    (totalDegree_chartRest_le j t _).trans hg.totalDegree_le
  intro d hd
  have h1 : m ≤ degree d := by
    by_contra hlt
    exact hd (le_ord_iff.mp hord d (by omega))
  have h2 : degree d ≤ m :=
    (le_totalDegree (MvPolynomial.mem_support_iff.mpr hd)).trans hdeg
  rw [show (1 : σ → ℕ) = fun _ => 1 from rfl, ← Finsupp.degree_eq_weight_one]
  omega

/-- **The points where the order stays the same lie in the directrix** [Hir67]. Let `ord f = m`,
and let the `x_j`-chart with translations `t` send `f` to `x_j^m f'`. If `ord f' = m`, then the
vector of the chart lies in the directrix of the part `f_m` of `f` of degree `m`. -/
theorem mem_directrix_of_ord_pointChart_eq {j : σ} {t : σ → k} {f f' : MvPolynomial σ k} {m : ℕ}
    (hf : ord f = m) (h : pointChart j t f = X j ^ m * f') (hf' : ord f' = m) :
    chartVector j t ∈ directrix (homogeneousComponent m f) :=
  mem_directrix_of_le_ord_pointChart hf.ge h hf'.ge

end Singularity
