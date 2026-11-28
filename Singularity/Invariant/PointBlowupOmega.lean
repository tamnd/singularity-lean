/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.OriginChartIota
import Singularity.Invariant.CossartPiltantOmegaBounds
import Singularity.Invariant.MohBound

/-!
# Corollary 4.3.2 for point blowups, and cores of Theorems 3.2.6 and 3.2.7

This file proves results of Volume 6 of the handbook on the invariant `ι = (m, ω, κ)` of Cossart
and Piltant (Definition 3.2.5, `cpIota`).

## Corollary 4.3.2 (Volume 6, Section 4.3)

Let `k` be a field of characteristic `p`, with `p` prime. Let `g ≠ 0` be clean with `ord g ≥ p`.
The point `x` is the origin of `z^p + g`, with the divisor `E = V(∏_{i ∈ Δ} x_i)`. Let the
`x_j`-chart of the blowup of the origin, with translations `t`, send `g` to `x_j^p g'`. The point
`x'` is the origin of this chart. Its invariants are computed from the clean part `g'_c` of `g'`
and the new divisor `Δ' = blowupDivisor Δ j t`. We write `ε = ord G` for the residual order.

* `cpIota_cleanPart_pointChart_le`: `ι(x') ≤ ι(x)`.
* `exists_ord_eq_mul_of_lt`: if `ε(x') > ε(x)`, then `ord g = p n` for some `n : ℕ`, that is,
  `δ(x) = ord g / p ∈ ℕ`.
* `cpOmega_eq_of_lt_pointChart`: if `ε(x') > ε(x)`, then `ω(x) = ε(x)`, `ω(x') = ω(x)` and
  `ε(x') = ε(x) + 1`.
* `cpIota_cleanPart_pointChart`: the two claims of Corollary 4.3.2 together.
* `ord_residualFactor_cleanPart_le_add_one`: Moh's bound `ε(x') ≤ ε(x) + 1` in this notation.

The handbook deduces the corollary from Theorem 3.2.6, which it cites. The proof here does not
use Theorem 3.2.6. It uses three results of the repo: `ω` does not go up under a point blowup
(`cpOmega_cleanPart_le`, Volume 7, Corollary 3.6.2), Moh's bound
(`residualOrderAlong_pointChart_le`), and the fact that `ε` does not go up if `p ∤ ord g`
(`residualOrderAlong_pointChart_le_of_not_dvd`). So the hypotheses "condition (E)" and
"`ω(x) > 0`" of the corollary are not needed in this setting.

What is missing. The polynomial `g` stands for the series `F` of Section 4.3, and the strict
transform at `x'` is the polynomial `g'`. The invariants at `x'` are read off from the clean part
`g'_c`. This uses that cleaning gives well adapted coordinates (Proposition 3.2.4 and Volume 7,
Proposition 1.2.7). This step is not formalized here, as in `cpIota_originTransform_le`. The
cleaning is a translation of `Z` only when `k` is perfect, as for `k = 𝔽_p` in Section 4.3.
Only the points of the charts with coordinates `t ∈ k^σ` are covered. Closed points of the
exceptional divisor with a larger residue field are not covered. The value of `κ` is only `1` or
`≥ 2`, as in Definition 3.2.5.

## A core of Theorem 3.2.6 (Volume 6, Section 3.2)

* `eq_of_le_add_one_of_lt`, `cpOmega_eq_of_lt`: if `ω(x') ≤ ω(x)` and `ε(x') > ε(x)`, then
  `ω(x) = ε(x)` and `ω(x') = ω(x)`. This is the step from the first claim of Theorem 3.2.6 to the
  part `ε(x) = ω(x)` of the second claim, for the point center `Y = {x}`. It only uses
  `ε - 1 ≤ ω ≤ ε` (Lemma 3.2.14(1)), and it holds for each center.

Theorem 3.2.6 itself is not proved. For centers of positive dimension, the bound `ω(x') ≤ ω(x)`
is in the repo only under the conditions (H1) and (H2) (`cpOmega_cleanPart_le_center`), not under
condition (E). The claims on `i_0 = p`, on `ε(y)` and on `δ(y) ∈ ℕ` for such centers are not
proved.

## A core of Theorem 3.2.7 (Volume 6, Section 3.2)

* `not_strictAnti_of_mul_mem_nat`, `not_strictAnti_of_factorial_mul`: a sequence of rational
  numbers in `(1/N) ℕ` cannot strictly decrease forever. With `N = p!` this is the reason why
  `δ ∈ (1/p!) ℕ` cannot drop forever in the proof of Theorem 3.2.7.

Theorem 3.2.7 itself is not proved: the choice of the centers along a valuation, the chart
formulas and the drop of `δ` in the general case are missing. The step for `ε(x) = 0` is in
`Singularity/Invariant/IotaInduction.lean`, in part.

## Theorem 3.2.11 (Volume 6, Section 3.2)

The Projection Theorem is not proved, and this file adds nothing to it. Its use in the induction
of Proposition 3.2.12 is in `Singularity/Invariant/IotaInduction.lean`, with the theorem as a
hypothesis.

## References

* [CP19] V. Cossart, O. Piltant, *Resolution of singularities of arithmetical threefolds*,
  J. Algebra 529 (2019), Theorems 2.81, 3.13 and 5.5.
* Volume 6, Sections 3.2 and 4.3 of the handbook.
* Volume 7, Sections 1.4 and 3.6 of the handbook.
-/

open MvPolynomial Finsupp

namespace Singularity

/-! ### A core of Theorem 3.2.6 -/

section Core

/-- The order argument behind Theorem 3.2.6. Let `ω ≤ ε`, `ε' ≤ ω' + 1` and `ω' ≤ ω` in `ℕ∞`.
If `ε < ε'`, then `ω = ε` and `ω' = ω`. -/
theorem eq_of_le_add_one_of_lt {ω ε ω' ε' : ℕ∞} (hω : ω ≤ ε) (hε' : ε' ≤ ω' + 1)
    (hle : ω' ≤ ω) (hlt : ε < ε') : ω = ε ∧ ω' = ω := by
  have hω_top : ω ≠ ⊤ := ne_top_of_le_ne_top (ne_top_of_lt hlt) hω
  have h1 : ε < ω + 1 := lt_of_lt_of_le hlt (hε'.trans (by gcongr))
  have h2 : ε ≤ ω := (ENat.lt_add_one_iff hω_top).mp h1
  have h3 : ω = ε := le_antisymm hω h2
  have h4 : ω < ω' + 1 := by rw [h3]; exact lt_of_lt_of_le hlt hε'
  have hω'_top : ω' ≠ ⊤ := ne_top_of_le_ne_top hω_top hle
  exact ⟨h3, le_antisymm hle ((ENat.lt_add_one_iff hω'_top).mp h4)⟩

variable {σ k : Type*} [CommSemiring k]

/-- **A core of Theorem 3.2.6** (Volume 6, Section 3.2 of the handbook). Let `x` and `x'` have the
invariants `ω = cpOmega Δ g`, `ε = ord (residualFactor Δ g)` and `ω'`, `ε'` for `(Δ', g')`.
If `ω(x') ≤ ω(x)` and `ε(x') > ε(x)`, then `ω(x) = ε(x)` and `ω(x') = ω(x)`. The proof uses only
`ε - 1 ≤ ω ≤ ε` (Lemma 3.2.14(1)). -/
theorem cpOmega_eq_of_lt {Δ Δ' : Finset σ} {g g' : MvPolynomial σ k}
    (hle : cpOmega Δ' g' ≤ cpOmega Δ g)
    (hlt : ord (residualFactor Δ g) < ord (residualFactor Δ' g')) :
    cpOmega Δ g = ord (residualFactor Δ g) ∧ cpOmega Δ' g' = cpOmega Δ g :=
  eq_of_le_add_one_of_lt (cpOmega_le_ord_residualFactor Δ g)
    (ord_residualFactor_le_cpOmega_add_one Δ' g') hle hlt

end Core

/-! ### Corollary 4.3.2 for point blowups -/

section PointBlowup

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ]
variable (p : ℕ) [CharP k p] {Δ : Finset σ} {j : σ} {t : σ → k} {g g' : MvPolynomial σ k}

/-- **Corollary 4.3.2, `ι(x') ≤ ι(x)`** (Volume 6, Section 4.3 of the handbook). Let `k` have
characteristic `p`, and let `g ≠ 0` be clean with `ord g ≥ p`. Let `π(g) = x_j^p g'` in the chart
`π = pointChart j t`. Then `ι(x') ≤ ι(x)`, with `ι(x')` computed from the clean part `g'_c` of `g'`
and the new divisor `Δ' = blowupDivisor Δ j t`. The translations `t` are arbitrary. -/
theorem cpIota_cleanPart_pointChart_le (hg : g ≠ 0) (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g') :
    cpIota p (blowupDivisor Δ j t) (cleanPart p g') ≤ cpIota p Δ g := by
  have hnot : ¬ cpMult p g < p := by
    rw [cpMult_of_le hord]
    exact lt_irrefl _
  by_cases hm : cpMult p (cleanPart p g') < p
  · unfold cpIota
    apply le_of_lt
    apply toLex_lt_toLex_of_lt
    rw [cpMult_of_le hord]
    exact hm
  · have hm' : cpMult p (cleanPart p g') = cpMult p g := by
      rw [cpMult_of_le hord]
      exact le_antisymm (cpMult_le _ _) (not_lt.mp hm)
    exact cpIota_le_of_cpOmega_le hm' hnot (cpOmega_cleanPart_le p hg hc hord h)

variable [Fact p.Prime]

omit [Fintype σ] in
/-- **Moh's bound in the notation of Corollary 4.3.2** (Volume 6, Section 3.2 of the handbook,
and Volume 7, Theorem 1.4.1 with `q = p`). Let `g` be clean with `ord g ≥ p`, and let
`π(g) = x_j^p g'`. Then `ε(x') ≤ ε(x) + 1`, with `ε(x') = ord (residualFactor Δ' g'_c)`. -/
theorem ord_residualFactor_cleanPart_le_add_one (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g') :
    ord (residualFactor (blowupDivisor Δ j t) (cleanPart p g')) ≤
      ord (residualFactor Δ g) + 1 := by
  have hb := residualOrderAlong_pointChart_le p Δ j t (e := 1) (by rwa [pow_one])
    (by rwa [pow_one]) (by rwa [pow_one])
  simp only [pow_one, Nat.sub_self, pow_zero, Nat.cast_one, residualOrderAlong,
    cleanPart_eq_self hc] at hb
  exact hb

omit [Fintype σ] in
/-- **Corollary 4.3.2, `δ(x) ∈ ℕ`** (Volume 6, Section 4.3 of the handbook). Let `g` be clean with
`ord g ≥ p`, and let `π(g) = x_j^p g'`. If `ε(x') > ε(x)`, then `ord g = p n` for some `n : ℕ`.
So `δ(x) = ord g / p` is an integer. The reason: if `p ∤ ord g`, then `ε` does not go up
(`residualOrderAlong_pointChart_le_of_not_dvd`). -/
theorem exists_ord_eq_mul_of_lt (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g')
    (hlt : ord (residualFactor Δ g) < ord (residualFactor (blowupDivisor Δ j t) (cleanPart p g'))) :
    ∃ n : ℕ, ord g = ((p * n : ℕ) : ℕ∞) := by
  have hg : g ≠ 0 := by
    rintro rfl
    simp [residualFactor] at hlt
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ord_ne_top hg)
  by_cases hdvd : p ∣ m
  · obtain ⟨n, rfl⟩ := hdvd
    exact ⟨n, hm.symm⟩
  · exfalso
    have hb := residualOrderAlong_pointChart_le_of_not_dvd p Δ j t (e := 1) (m := m)
      (by rwa [pow_one]) (by rwa [pow_one]) hm.symm (by rwa [pow_one]) (by rwa [pow_one])
    simp only [pow_one, residualOrderAlong, cleanPart_eq_self hc] at hb
    exact absurd hlt (not_lt.mpr hb)

/-- **Corollary 4.3.2, `ω(x) = ε(x)`** (Volume 6, Section 4.3 of the handbook). Let `g ≠ 0` be
clean with `ord g ≥ p`, and let `π(g) = x_j^p g'`. If `ε(x') > ε(x)`, then `ω(x) = ε(x)`,
`ω(x') = ω(x)` and `ε(x') = ε(x) + 1`. -/
theorem cpOmega_eq_of_lt_pointChart (hg : g ≠ 0) (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g')
    (hlt : ord (residualFactor Δ g) < ord (residualFactor (blowupDivisor Δ j t) (cleanPart p g'))) :
    cpOmega Δ g = ord (residualFactor Δ g) ∧
      cpOmega (blowupDivisor Δ j t) (cleanPart p g') = cpOmega Δ g ∧
      ord (residualFactor (blowupDivisor Δ j t) (cleanPart p g')) =
        ord (residualFactor Δ g) + 1 := by
  obtain ⟨h1, h2⟩ := cpOmega_eq_of_lt (cpOmega_cleanPart_le p hg hc hord h) hlt
  refine ⟨h1, h2, le_antisymm (ord_residualFactor_cleanPart_le_add_one p hc hord h) ?_⟩
  exact (ENat.add_one_le_iff (ne_top_of_lt hlt)).mpr hlt

/-- **Corollary 4.3.2** (Volume 6, Section 4.3 of the handbook). Let `k` have characteristic `p`,
let `g ≠ 0` be clean with `ord g ≥ p`, and let `π(g) = x_j^p g'` in the chart `π = pointChart j t`
of the blowup of the closed point. Then `ι(x') ≤ ι(x)`. If also `ε(x') > ε(x)`, then
`ε(x) = ω(x)` and `δ(x) = ord g / p` is an integer. Here `x'` is computed from the clean part of
`g'` and the divisor `Δ' = blowupDivisor Δ j t`. Condition (E) and `ω(x) > 0` are not needed. -/
theorem cpIota_cleanPart_pointChart (hg : g ≠ 0) (hc : IsClean p g) (hord : (p : ℕ∞) ≤ ord g)
    (h : pointChart j t g = X j ^ p * g') :
    cpIota p (blowupDivisor Δ j t) (cleanPart p g') ≤ cpIota p Δ g ∧
      (ord (residualFactor Δ g) < ord (residualFactor (blowupDivisor Δ j t) (cleanPart p g')) →
        cpOmega Δ g = ord (residualFactor Δ g) ∧ ∃ n : ℕ, ord g = ((p * n : ℕ) : ℕ∞)) :=
  ⟨cpIota_cleanPart_pointChart_le p hg hc hord h, fun hlt =>
    ⟨(cpOmega_eq_of_lt_pointChart p hg hc hord h hlt).1, exists_ord_eq_mul_of_lt p hc hord h hlt⟩⟩

end PointBlowup

/-! ### A core of Theorem 3.2.7 -/

section Termination

/-- A strictly decreasing sequence of natural numbers does not exist. -/
private theorem not_strictAnti_nat (m : ℕ → ℕ) : ¬ StrictAnti m := by
  intro hm
  have key : ∀ n, m n + n ≤ m 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hm (Nat.lt_add_one n)
      omega
  have := key (m 0 + 1)
  omega

/-- **A core of Theorem 3.2.7** (Volume 6, Section 3.2 of the handbook). Let `N > 0`. A sequence
of rational numbers in `(1/N) ℕ` is not strictly decreasing. -/
theorem not_strictAnti_of_mul_mem_nat {N : ℕ} (hN : 0 < N) (f : ℕ → ℚ)
    (hf : ∀ n, ∃ m : ℕ, f n = m / N) : ¬ StrictAnti f := by
  choose m hm using hf
  intro hanti
  apply not_strictAnti_nat m
  intro a b hab
  have h := hanti hab
  rw [hm a, hm b] at h
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have h' : (m b : ℚ) < m a := (div_lt_div_iff_of_pos_right hN').mp h
  exact_mod_cast h'

/-- **A core of Theorem 3.2.7** (Volume 6, Section 3.2 of the handbook). The invariant `δ` takes
values in `(1/p!) ℕ`. So `δ` cannot drop forever: a sequence in `(1/p!) ℕ` is not strictly
decreasing. -/
theorem not_strictAnti_of_factorial_mul (p : ℕ) (f : ℕ → ℚ)
    (hf : ∀ n, ∃ m : ℕ, f n = m / p.factorial) : ¬ StrictAnti f :=
  not_strictAnti_of_mul_mem_nat (Nat.factorial_pos p) f hf

end Termination

end Singularity
