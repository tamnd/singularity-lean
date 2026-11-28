/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.OriginChartIota
import Singularity.Invariant.CossartPiltantOmegaBounds
import Singularity.Invariant.IotaIndexOrder

/-!
# The induction on `ι`, the choice of the center, and Example 3.2.13

This file proves three results of Volume 6, Section 3.2 of the handbook, in part.

## Proposition 3.2.12: the induction on `ι`

The proposition is a well founded induction. We state it for an abstract type `X` of states. A
state stands for a triple `(S, h, E)` with a point `x` and a valuation `μ` with center `x`. The
relation `step a b` is one local Hironaka-permissible blowup along `μ`, and `stepE a b` is one
local Hironaka-permissible blowup with respect to `E` along `μ`. A finite sequence of blowups is
the reflexive transitive closure `Relation.ReflTransGen`.

* `exists_regular_of_wellFounded`: the proposition for an invariant with values in any type with a
  well founded `<`. It has one more hypothesis: a point with `m < p` has a smaller invariant than
  a point with `m = p`.
* `IotaIndex.exists_regular`: the proposition for `ι` with values in
  `I = {1, ..., p} × ℕ × {1, 2, 3, 4}`, where `m` and `ω` are read off from `ι`. Here the extra
  hypothesis holds by the lexicographic order, and the four properties are the ones of the
  handbook.

Not proved: that the class of the handbook has the four properties. These are theorems of Cossart
and Piltant. Also not proved: that the composite sequence is independent of the valuation.

## Proposition 3.2.9: the choice of the set `J`

Let `r_j` be the exponents of the monomial `u^r` and let `p ≥ 1`. The file proves the
combinatorial part of the proof of the proposition.

* `exists_minimal_subset_sum_ge`: if `∑_{j ∈ s} r_j ≥ p`, then there is a set `J ⊆ s` with
  `R = ∑_{j ∈ J} r_j ≥ p` that is minimal for inclusion.
* `sum_erase_lt_of_minimal`, `one_le_of_minimal`: for such a `J` and `j ∈ J`, `R - r_j ≤ p - 1`
  and `r_j ≥ 1`.
* `sum_sub_add_le_of_minimal`: the bound (3.2), `|a| = |r| - p + ∑_{j ∈ J_0} r_j ≤ |r| - 1` for
  `J_0 ⊆ J \ {j_0}`.
* `sum_sub_add_le_two_of_minimal`: the improved bound `|a| ≤ |r| - 2` of case 2, if
  `J_0 ⊆ J \ {j_0, i}` with `i ∈ J \ {j_0}`.

Not proved: the permissibility of the center, the computation of the charts, the bounds (3.3) for
the clean part, the three cases, and the final bound `δ(x') ≤ δ(x) - 1/p`.

## Example 3.2.13

Let `f = u_1^2 u_2^2 u_3` in the polynomial ring `k[u_1, u_2, u_3]` over a field `k`, with
`u_i = X (i - 1)`, and `E = div(u_1 u_2 u_3)`. The file proves:

* `example_3_2_13_isClean`, `example_3_2_13_ord`, `example_3_2_13_residualFactor`,
  `example_3_2_13_cpOmega`, `example_3_2_13_cpIota`: `f` is clean for `3`, `ord f = 5`, `G = 1`,
  so `ε = 0`, `ω = 0` and `ι = (3, 0, 1)`.
* `example_3_2_13_minimal_iff`: the sets `J` with `R ≥ 3` that are minimal for inclusion are
  `{1, 2}`, `{1, 3}` and `{2, 3}`; `example_3_2_13_not_minimal_univ`: `{1, 2, 3}` is not minimal.
* The charts of the blowup along `V(Z, u_1, u_2)`: the `u_1`-chart at `t_2`
  (`example_3_2_13_chart12`), with `ord f' = 4` for `t_2 = 0` and `ord f' = 2` for `t_2 ≠ 0`,
  and the origin of the `u_2`-chart with `ord f' = 4`. At `t_2 = 0` also `ε' = ω' = 0`.
* The charts of the blowup along `V(Z, u_1, u_3)`: the `u_1`-chart at `t_3`, with `ord f' = 3`
  for `t_3 = 0` and `ord f' = 2` for `t_3 ≠ 0`, and the origin of the `u_3`-chart with
  `ord f' = 4`.
* The point blowup: at the origin of the `u_3`-chart `f' = v_1^2 v_2^2 u_3^2`, which is clean,
  with `ord f' = 6`, `ε' = ω' = 0` and `ι(x') = (3, 0, 1)`.

Not proved: the polyhedra and `δ` (the link `δ = ord f / p` is Proposition 3.2.4(2), which has no
Lean proof), the multiplicity `m(x') < 3` for the points with order `2`, the center
`V(Z, u_2, u_3)` (it is the same as `V(Z, u_1, u_3)` with `u_1` and `u_2` exchanged), and the
blowups as schemes. The series ring `k[[u_1, u_2, u_3]]` is replaced by the polynomial ring.
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### Proposition 3.2.12 -/

section Induction

open Relation

variable {X I : Type*} [LT I] [WellFoundedLT I]

/-- **Proposition 3.2.12** (Volume 6, Section 3.2 of the handbook), for an invariant `ι` with
values in a type with a well founded `<`. The predicate `low a` is `m(x) < p`, and `zero a` is
`(m(x), ω(x)) = (p, 0)`. The hypothesis `hlow` says that `ι` drops when `m` drops below `p`. The
four hypotheses `h1` to `h4` are the four properties of the proposition. -/
theorem exists_regular_of_wellFounded (C : X → Prop) (step stepE : X → X → Prop)
    (regular low zero : X → Prop) (ι : X → I) (hE : ∀ a b, stepE a b → step a b)
    (hlow : ∀ a b, ¬ low a → low b → ι b < ι a)
    (h1 : ∀ a b, C a → stepE a b → C b)
    (h2 : ∀ a, C a → low a → ∃ b, ReflTransGen step a b ∧ regular b)
    (h3 : ∀ a, C a → zero a → ∃ b, ReflTransGen stepE a b ∧ low b)
    (h4 : ∀ a, C a → ¬ low a → ¬ zero a → ∃ b, ReflTransGen stepE a b ∧ ι b < ι a) :
    ∀ a, C a → ∃ b, ReflTransGen step a b ∧ regular b := by
  have hC : ∀ a b, C a → ReflTransGen stepE a b → C b := by
    intro a b ha hab
    induction hab with
    | refl => exact ha
    | tail _ hbc ih => exact h1 _ _ ih hbc
  have hmono : ∀ a b, ReflTransGen stepE a b → ReflTransGen step a b := by
    intro a b hab
    induction hab with
    | refl => exact ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail (hE _ _ hbc)
  intro a
  induction a using (InvImage.wf ι wellFounded_lt).induction with
  | _ a ih =>
    intro ha
    by_cases hl : low a
    · exact h2 a ha hl
    · have key : ∃ b, ReflTransGen stepE a b ∧ ι b < ι a := by
        by_cases hz : zero a
        · obtain ⟨b, hab, hb⟩ := h3 a ha hz
          exact ⟨b, hab, hlow a b hl hb⟩
        · exact h4 a ha hl hz
      obtain ⟨b, hab, hlt⟩ := key
      obtain ⟨c, hbc, hc⟩ := ih b hlt (hC a b ha hab)
      exact ⟨c, (hmono a b hab).trans hbc, hc⟩

end Induction

namespace IotaIndex

open Relation

variable {p : ℕ} {X : Type*}

/-- The multiplicity `m`, the first coordinate of `ι ∈ I`. -/
def multCoord (i : IotaIndex p) : ℕ := (ofLex i).1.1

/-- The invariant `ω`, the second coordinate of `ι ∈ I`. -/
def omegaCoord (i : IotaIndex p) : ℕ := (ofLex (ofLex i).2).1

/-- If `m(b) < p = m(a)`, then `ι(b) < ι(a)` in the lexicographic order. -/
theorem lt_of_multCoord_lt {a b : IotaIndex p} (ha : ¬ multCoord a < p)
    (hb : multCoord b < p) : b < a := by
  have hap : multCoord a ≤ p := (ofLex a).1.2.2
  have hlt : (ofLex b).1 < (ofLex a).1 := by
    show multCoord b < multCoord a
    omega
  exact Prod.Lex.left _ _ hlt

/-- **Proposition 3.2.12** (Volume 6, Section 3.2 of the handbook), for `ι` with values in
`I = {1, ..., p} × ℕ × {1, 2, 3, 4}`. A state `a` stands for a triple `(S, h, E)` with a point `x`
and a valuation `μ` with center `x`. The relation `step` is one local Hironaka-permissible blowup
along `μ`, and `stepE` is one local Hironaka-permissible blowup with respect to `E` along `μ`. The
hypotheses `h1` to `h4` are the four properties of the proposition. Then from each state in `C`
there is a finite sequence of blowups along `μ` to a regular point. -/
theorem exists_regular (C : X → Prop) (step stepE : X → X → Prop) (regular : X → Prop)
    (ι : X → IotaIndex p) (hE : ∀ a b, stepE a b → step a b)
    (h1 : ∀ a b, C a → stepE a b → C b)
    (h2 : ∀ a, C a → multCoord (ι a) < p → ∃ b, ReflTransGen step a b ∧ regular b)
    (h3 : ∀ a, C a → multCoord (ι a) = p → omegaCoord (ι a) = 0 →
      ∃ b, ReflTransGen stepE a b ∧ multCoord (ι b) < p)
    (h4 : ∀ a, C a → multCoord (ι a) = p → 0 < omegaCoord (ι a) →
      ∃ b, ReflTransGen stepE a b ∧ ι b < ι a) :
    ∀ a, C a → ∃ b, ReflTransGen step a b ∧ regular b := by
  have hle : ∀ a, multCoord (ι a) ≤ p := fun a => (ofLex (ι a)).1.2.2
  refine exists_regular_of_wellFounded C step stepE regular (fun a => multCoord (ι a) < p)
    (fun a => multCoord (ι a) = p ∧ omegaCoord (ι a) = 0) ι hE
    (fun a b ha hb => lt_of_multCoord_lt ha hb) h1 h2
    (fun a ha hz => h3 a ha hz.1 hz.2) ?_
  intro a ha hl hz
  have hm : multCoord (ι a) = p := le_antisymm (hle a) (not_lt.mp hl)
  exact h4 a ha hm (Nat.pos_of_ne_zero fun h0 => hz ⟨hm, h0⟩)

end IotaIndex

/-! ### Proposition 3.2.9: the combinatorics of the set `J` -/

section Minimal

variable {ι : Type*} (r : ι → ℕ) {p : ℕ}

/-- Volume 6, proof of Proposition 3.2.9 of the handbook: if `∑_{j ∈ s} r_j ≥ p`, then there is a
set `J ⊆ s` with `∑_{j ∈ J} r_j ≥ p` that is minimal for inclusion among the sets with this
property. -/
theorem exists_minimal_subset_sum_ge {s : Finset ι} (hs : p ≤ ∑ j ∈ s, r j) :
    ∃ J ⊆ s, p ≤ ∑ j ∈ J, r j ∧ ∀ J' ⊂ J, ∑ j ∈ J', r j < p := by
  classical
  set T := s.powerset.filter fun J => p ≤ ∑ j ∈ J, r j
  have hT : T.Nonempty := ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self s, hs⟩⟩
  obtain ⟨J, hJ, hmin⟩ := Finset.exists_min_image T Finset.card hT
  obtain ⟨hJs, hJp⟩ := Finset.mem_filter.mp hJ
  refine ⟨J, Finset.mem_powerset.mp hJs, hJp, fun J' hJ' => ?_⟩
  by_contra h
  have hmem : J' ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (hJ'.subset.trans (Finset.mem_powerset.mp hJs)), not_lt.mp h⟩
  exact absurd (hmin J' hmem) (not_le.mpr (Finset.card_lt_card hJ'))

variable {r} [DecidableEq ι] {J : Finset ι}

/-- Volume 6, proof of Proposition 3.2.9 of the handbook: if `J` is minimal, then
`R - r_j ≤ p - 1` for each `j ∈ J`. -/
theorem sum_erase_lt_of_minimal (hmin : ∀ J' ⊂ J, ∑ j ∈ J', r j < p) {j : ι} (hj : j ∈ J) :
    ∑ i ∈ J.erase j, r i < p :=
  hmin _ (Finset.erase_ssubset hj)

/-- Volume 6, proof of Proposition 3.2.9 of the handbook: if `J` is minimal, then `r_j ≥ 1` for
each `j ∈ J`. -/
theorem one_le_of_minimal (hJ : p ≤ ∑ j ∈ J, r j) (hmin : ∀ J' ⊂ J, ∑ j ∈ J', r j < p) {j : ι}
    (hj : j ∈ J) : 1 ≤ r j := by
  have h1 := sum_erase_lt_of_minimal hmin hj
  have h2 := Finset.add_sum_erase J r hj
  omega

/-- The bound (3.2) of Volume 6, proof of Proposition 3.2.9 of the handbook. Let `J` be minimal,
let `j_0 ∈ J`, let `J_0 ⊆ J \ {j_0}`, and let `p ≤ n`, where `n = |r|`. Then
`n - p + ∑_{j ∈ J_0} r_j ≤ n - 1`. -/
theorem sum_sub_add_le_of_minimal (hp : 1 ≤ p) (hmin : ∀ J' ⊂ J, ∑ j ∈ J', r j < p) {j₀ : ι}
    (hj₀ : j₀ ∈ J) {J₀ : Finset ι} (hJ₀ : J₀ ⊆ J.erase j₀) {n : ℕ} (hn : p ≤ n) :
    n - p + ∑ j ∈ J₀, r j ≤ n - 1 := by
  have h1 := sum_erase_lt_of_minimal hmin hj₀
  have h2 : ∑ j ∈ J₀, r j ≤ ∑ j ∈ J.erase j₀, r j := Finset.sum_le_sum_of_subset hJ₀
  omega

/-- The improved bound of case 2 of Volume 6, proof of Proposition 3.2.9 of the handbook. Let `J`
be minimal, let `j_0 ∈ J`, let `i ∈ J \ {j_0}`, and let `J_0 ⊆ J \ {j_0, i}`. Then
`∑_{j ∈ J_0} r_j + 2 ≤ p`, and `n - p + ∑_{j ∈ J_0} r_j ≤ n - 2` for `p ≤ n`. -/
theorem sum_sub_add_le_two_of_minimal (hJ : p ≤ ∑ j ∈ J, r j)
    (hmin : ∀ J' ⊂ J, ∑ j ∈ J', r j < p) {j₀ i : ι} (hj₀ : j₀ ∈ J) (hi : i ∈ J.erase j₀)
    {J₀ : Finset ι} (hJ₀ : J₀ ⊆ (J.erase j₀).erase i) {n : ℕ} (hn : p ≤ n) :
    ∑ j ∈ J₀, r j + 2 ≤ p ∧ n - p + ∑ j ∈ J₀, r j ≤ n - 2 := by
  have h1 := sum_erase_lt_of_minimal hmin hj₀
  have h2 : ∑ j ∈ J₀, r j ≤ ∑ j ∈ (J.erase j₀).erase i, r j := Finset.sum_le_sum_of_subset hJ₀
  have h3 := Finset.add_sum_erase (J.erase j₀) r hi
  have h4 := one_le_of_minimal hJ hmin (Finset.mem_of_mem_erase hi)
  omega

end Minimal

namespace Examples

/-! ### Example 3.2.13 -/

section Example3213

variable {k : Type*} [Field k]

/-- A monomial whose exponent is not in `q ℕ^σ` is clean for `q`. -/
private theorem ex3213_isClean_monomial {σ : Type*} {q : ℕ} {d : σ →₀ ℕ} (c : k)
    (h : ¬ ∀ i, q ∣ d i) : IsClean q (monomial d c) := by
  classical
  intro d' hd'
  have := support_monomial_subset hd'
  rw [Finset.mem_singleton] at this
  rw [this]
  exact h

private theorem ex3213_mon3 (a b c : Fin 3 →₀ ℕ) :
    monomial (a + b + c) (1 : k) = monomial a 1 * monomial b 1 * monomial c 1 := by
  rw [monomial_mul_monomial, monomial_mul_monomial, mul_one, mul_one]

/-- The residual factor of a monomial for `E = div(u_1 u_2 u_3)` is `1`. -/
private theorem ex3213_residualFactor_monomial (d : Fin 3 →₀ ℕ) :
    residualFactor Finset.univ (monomial d (1 : k)) = 1 := by
  have h := residualFactor_monomial_mul (k := k) (G := 1) (r := d) (Δ := Finset.univ)
    (fun i hi => absurd (Finset.mem_univ i) hi)
    (fun i _ => ⟨0, MvPolynomial.mem_support_iff.mpr (by simp), by simp⟩)
  rwa [mul_one] at h

/-- `ι = (3, 0, 1)` for a monomial of order at least `3` and `E = div(u_1 u_2 u_3)`. -/
private theorem ex3213_cpIota_monomial (d : Fin 3 →₀ ℕ) (h : (3 : ℕ∞) ≤ ord (monomial d (1 : k))) :
    cpIota 3 Finset.univ (monomial d (1 : k)) = toLex ((3 : ℕ∞), toLex ((0 : ℕ∞), 1)) := by
  have hω : cpOmega Finset.univ (monomial d (1 : k)) = 0 := by
    rw [cpOmega_eq_of_forall_mem Finset.mem_univ, ex3213_residualFactor_monomial, ord_one]
  have h3 : ((3 : ℕ) : ℕ∞) ≤ ord (monomial d (1 : k)) := by exact_mod_cast h
  have hκ : cpKappa 3 Finset.univ (monomial d (1 : k)) = 1 :=
    cpKappa_eq_one_iff.mpr (by rw [cpOmegaAt_of_le _ h3, hω])
  rw [cpIota, cpMult_of_le h3, cpOmegaAt_of_le _ h3, hω, hκ]
  rfl

/-- The polynomial `f = u_1^2 u_2^2 u_3` of Example 3.2.13 as a monomial. -/
private theorem ex3213_f_eq : (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
    monomial (single 0 2 + single 1 2 + single 2 1) 1 := by
  rw [ex3213_mon3, ← X_pow_eq_monomial, ← X_pow_eq_monomial, ← X_pow_eq_monomial, pow_one]

/-- `f = u_1^2 u_2^2 u_3` is clean for `3`. Volume 6, Example 3.2.13 of the handbook. -/
theorem example_3_2_13_isClean : IsClean 3 (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) := by
  rw [ex3213_f_eq]
  refine ex3213_isClean_monomial 1 fun h => ?_
  have h2 := h 2
  simp at h2

/-- `ord f = 5` for `f = u_1^2 u_2^2 u_3`. Volume 6, Example 3.2.13 of the handbook. -/
theorem example_3_2_13_ord : ord (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = 5 := by
  rw [ord_mul, ord_mul, ord_X_pow, ord_X_pow, ord_X]
  rfl

/-- `G = 1` for `f = u_1^2 u_2^2 u_3` and `E = div(u_1 u_2 u_3)`, so `ε = 0`. Volume 6,
Example 3.2.13 of the handbook. -/
theorem example_3_2_13_residualFactor :
    residualFactor Finset.univ (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = 1 := by
  rw [ex3213_f_eq, ex3213_residualFactor_monomial]

/-- `ω = 0` for `f = u_1^2 u_2^2 u_3` and `E = div(u_1 u_2 u_3)`. Volume 6, Example 3.2.13 of
the handbook. -/
theorem example_3_2_13_cpOmega :
    cpOmega Finset.univ (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = 0 := by
  rw [cpOmega_eq_of_forall_mem Finset.mem_univ, example_3_2_13_residualFactor, ord_one]

/-- `ι(x) = (3, 0, 1)` for `h = Z^3 + u_1^2 u_2^2 u_3` and `E = div(u_1 u_2 u_3)`. Volume 6,
Example 3.2.13 of the handbook. -/
theorem example_3_2_13_cpIota :
    cpIota 3 Finset.univ (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
      toLex ((3 : ℕ∞), toLex ((0 : ℕ∞), 1)) := by
  have h : (3 : ℕ∞) ≤ ord (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) := by
    rw [example_3_2_13_ord]
    decide
  rw [ex3213_f_eq] at h ⊢
  exact ex3213_cpIota_monomial _ h

/-- The sets `J ⊆ {1, 2, 3}` with `R = ∑_{j ∈ J} r_j ≥ 3` that are minimal for inclusion are
`{1, 2}`, `{1, 3}` and `{2, 3}`, for `r = (2, 2, 1)`. The indices are shifted by one. Volume 6,
Example 3.2.13 of the handbook. -/
theorem example_3_2_13_minimal_iff (J : Finset (Fin 3)) :
    (3 ≤ ∑ j ∈ J, ![2, 2, 1] j ∧ ∀ J' ⊂ J, ∑ j ∈ J', ![2, 2, 1] j < 3) ↔
      J = {0, 1} ∨ J = {0, 2} ∨ J = {1, 2} := by
  revert J
  decide

/-- The set `{1, 2, 3}` has `R = 5 ≥ 3`, but it is not minimal. Volume 6, Example 3.2.13 of the
handbook. -/
theorem example_3_2_13_not_minimal_univ :
    3 ≤ ∑ j ∈ (Finset.univ : Finset (Fin 3)), ![2, 2, 1] j ∧
      ¬ ∀ J' ⊂ (Finset.univ : Finset (Fin 3)), ∑ j ∈ J', ![2, 2, 1] j < 3 := by
  decide

/-- The `u_1`-chart at `t_2` of the blowup along `V(Z, u_1, u_2)`: `u_2 = u_1 (v_2 + t_2)`, and
`f = u_1^3 f'` with `f' = u_1 (v_2 + t_2)^2 u_3`. Volume 6, Example 3.2.13 of the handbook. -/
theorem example_3_2_13_chart12 (t : k) :
    aeval ![X 0, X 0 * (X 1 + C t), X 2] (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
      X 0 ^ 3 * (X 0 * (X 1 + C t) ^ 2 * X 2) := by
  simp only [map_mul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- At `t_2 = 0`, `f' = u_1 v_2^2 u_3` is clean, `ord f' = 4 = 5 - 1`, and `ι(x') = (3, 0, 1)`
for the new divisor `div(u_1 v_2 u_3)`. Volume 6, Example 3.2.13 of the handbook. -/
theorem example_3_2_13_chart12_zero :
    IsClean 3 (X 0 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) ∧
      ord (X 0 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = 4 ∧
      cpIota 3 Finset.univ (X 0 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
        toLex ((3 : ℕ∞), toLex ((0 : ℕ∞), 1)) := by
  have he : (X 0 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
      monomial (single 0 1 + single 1 2 + single 2 1) 1 := by
    rw [ex3213_mon3, ← X_pow_eq_monomial, ← X_pow_eq_monomial, ← X_pow_eq_monomial, pow_one,
      pow_one]
  have hord : ord (X 0 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) = 4 := by
    rw [ord_mul, ord_mul, ord_X_pow, ord_X, ord_X]
    rfl
  refine ⟨?_, hord, ?_⟩
  · rw [he]
    refine ex3213_isClean_monomial 1 fun h => ?_
    have h0 := h 0
    simp at h0
  · have h : (3 : ℕ∞) ≤ ord (X 0 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) := by
      rw [hord]
      decide
    rw [he] at h ⊢
    exact ex3213_cpIota_monomial _ h

/-- If `c ≠ 0` and `B` has order at least `3`, then `c u_i u_j + B` has order `2`. -/
private theorem ex3213_ord_two {i j : Fin 3} {c : k} (hc : c ≠ 0) {B : MvPolynomial (Fin 3) k}
    (hB : (3 : ℕ∞) ≤ ord B) : ord (C c * (X i * X j) + B) = 2 := by
  have hA : ord (C c * (X i * X j) : MvPolynomial (Fin 3) k) = 2 := by
    rw [ord_mul, ord_mul, ord_C hc, ord_X, ord_X]
    rfl
  have hlt : ord (C c * (X i * X j) : MvPolynomial (Fin 3) k) < ord B := by
    rw [hA]
    exact lt_of_lt_of_le (by decide) hB
  rw [ord_add_of_lt hlt, hA]

/-- A lower bound: `ord (C c * A) ≥ ord A`. -/
private theorem ex3213_le_ord_C_mul (c : k) (A : MvPolynomial (Fin 3) k) :
    ord A ≤ ord (C c * A) := by
  have h := le_ord_mul (C c) A
  exact le_trans (le_add_self) h

/-- At `t_2 ≠ 0`, `f' = u_1 (v_2 + t_2)^2 u_3` has order `2 < 3`. Volume 6, Example 3.2.13 of the
handbook. -/
theorem example_3_2_13_chart12_ne {t : k} (ht : t ≠ 0) :
    ord (X 0 * (X 1 + C t) ^ 2 * X 2 : MvPolynomial (Fin 3) k) = 2 := by
  have he : (X 0 * (X 1 + C t) ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
      C (t ^ 2) * (X 0 * X 2) + (X 0 * X 1 ^ 2 * X 2 + C (2 * t) * (X 0 * X 1 * X 2)) := by
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [he]
  refine ex3213_ord_two (pow_ne_zero 2 ht) (le_ord_add ?_ ?_)
  · rw [ord_mul, ord_mul, ord_X_pow, ord_X, ord_X]
    decide
  · refine le_trans ?_ (ex3213_le_ord_C_mul _ _)
    rw [ord_mul, ord_mul, ord_X, ord_X, ord_X]
    decide

/-- The origin of the `u_2`-chart of the blowup along `V(Z, u_1, u_2)`: `u_1 = u_2 v_1`,
`f = u_2^3 f'` with `f' = v_1^2 u_2 u_3`, and `ord f' = 4`. Volume 6, Example 3.2.13 of the
handbook. -/
theorem example_3_2_13_chart12_u2 :
    aeval (![X 1 * X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) k)
      (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
      X 1 ^ 3 * (X 0 ^ 2 * X 1 * X 2) ∧
      ord (X 0 ^ 2 * X 1 * X 2 : MvPolynomial (Fin 3) k) = 4 := by
  refine ⟨?_, ?_⟩
  · simp only [map_mul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  · rw [ord_mul, ord_mul, ord_X_pow, ord_X, ord_X]
    rfl

/-- The `u_1`-chart at `t_3` of the blowup along `V(Z, u_1, u_3)`: `u_3 = u_1 (v_3 + t_3)`, and
`f = u_1^3 f'` with `f' = u_2^2 (v_3 + t_3)`. Volume 6, Example 3.2.13 of the handbook. -/
theorem example_3_2_13_chart13 (t : k) :
    aeval ![X 0, X 1, X 0 * (X 2 + C t)] (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
      X 0 ^ 3 * (X 1 ^ 2 * (X 2 + C t)) := by
  simp only [map_mul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- At `t_3 = 0`, `f' = u_2^2 v_3` has order `3`. Volume 6, Example 3.2.13 of the handbook. -/
theorem example_3_2_13_chart13_zero :
    ord (X 1 ^ 2 * (X 2 + C 0) : MvPolynomial (Fin 3) k) = 3 := by
  rw [map_zero, add_zero, ord_mul, ord_X_pow, ord_X]
  rfl

/-- At `t_3 ≠ 0`, `f' = u_2^2 (v_3 + t_3)` has order `2`. Volume 6, Example 3.2.13 of the
handbook. -/
theorem example_3_2_13_chart13_ne {t : k} (ht : t ≠ 0) :
    ord (X 1 ^ 2 * (X 2 + C t) : MvPolynomial (Fin 3) k) = 2 := by
  have he : (X 1 ^ 2 * (X 2 + C t) : MvPolynomial (Fin 3) k) =
      C t * (X 1 * X 1) + X 1 ^ 2 * X 2 := by
    ring
  rw [he]
  refine ex3213_ord_two ht ?_
  rw [ord_mul, ord_X_pow, ord_X]
  decide

/-- The origin of the `u_3`-chart of the blowup along `V(Z, u_1, u_3)`: `u_1 = u_3 v_1`,
`f = u_3^3 f'` with `f' = v_1^2 u_2^2`, and `ord f' = 4`. Volume 6, Example 3.2.13 of the
handbook. -/
theorem example_3_2_13_chart13_u3 :
    aeval (![X 2 * X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) k)
      (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
      X 2 ^ 3 * (X 0 ^ 2 * X 1 ^ 2) ∧
      ord (X 0 ^ 2 * X 1 ^ 2 : MvPolynomial (Fin 3) k) = 4 := by
  refine ⟨?_, ?_⟩
  · simp only [map_mul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  · rw [ord_mul, ord_X_pow, ord_X_pow]
    rfl

/-- The point blowup at the origin of the `u_3`-chart: `u_1 = u_3 v_1`, `u_2 = u_3 v_2`, and
`f = u_3^3 f'` with `f' = v_1^2 v_2^2 u_3^2`. Volume 6, Example 3.2.13 of the handbook. -/
theorem example_3_2_13_pointChart :
    pointChart 2 0 (X 0 ^ 2 * X 1 ^ 2 * X 2 : MvPolynomial (Fin 3) k) =
      X 2 ^ 3 * (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2) := by
  rw [map_mul, map_mul, map_pow, map_pow, pointChart_X_self,
    pointChart_X_of_ne 0 (by decide : (0 : Fin 3) ≠ 2),
    pointChart_X_of_ne 0 (by decide : (1 : Fin 3) ≠ 2)]
  simp only [Pi.zero_apply, map_zero, add_zero]
  ring

/-- After the point blowup, `f' = v_1^2 v_2^2 u_3^2` is clean, `ord f' = 6 > 5`, and
`ι(x') = (3, 0, 1) = ι(x)` for the divisor `div(v_1 v_2 u_3)`. So `δ` goes up. Volume 6,
Example 3.2.13 of the handbook. -/
theorem example_3_2_13_pointChart_invariants :
    IsClean 3 (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) ∧
      ord (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = 6 ∧
      cpOmega Finset.univ (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = 0 ∧
      cpIota 3 Finset.univ (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
        toLex ((3 : ℕ∞), toLex ((0 : ℕ∞), 1)) := by
  have he : (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
      monomial (single 0 2 + single 1 2 + single 2 2) 1 := by
    rw [ex3213_mon3, ← X_pow_eq_monomial, ← X_pow_eq_monomial, ← X_pow_eq_monomial]
  have hord : ord (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) = 6 := by
    rw [ord_mul, ord_mul, ord_X_pow, ord_X_pow, ord_X_pow]
    rfl
  refine ⟨?_, hord, ?_, ?_⟩
  · rw [he]
    refine ex3213_isClean_monomial 1 fun h => ?_
    have h0 := h 0
    simp at h0
  · rw [cpOmega_eq_of_forall_mem Finset.mem_univ, he, ex3213_residualFactor_monomial, ord_one]
  · have h : (3 : ℕ∞) ≤ ord (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) k) := by
      rw [hord]
      decide
    rw [he] at h ⊢
    exact ex3213_cpIota_monomial _ h

end Example3213

end Examples

end Singularity
