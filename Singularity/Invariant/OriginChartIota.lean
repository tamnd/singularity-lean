/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.OriginChartResidualOrder
import Singularity.Invariant.CharacteristicPolyhedronClean

/-!
# The invariant `ι` at the origin of a chart

This file proves the rest of Proposition 4.3.4 of Volume 6, Section 4.3 of the handbook: the bound
`ι(x') ≤ ι(x)` of part 4, and the claim of part 2 that `(x; Z')` is well adapted.

Let `k` be a field, let `g ∈ k[x_i : i ∈ σ]`, and let `Δ` give the divisor
`E = V(∏_{i ∈ Δ} x_i)`. The point `x` is the origin of `z^p + g`.

## The invariant `ι`

Volume 6, Definition 3.2.5 of the handbook defines `ι(x) = (m(x), ω(x), κ(x))`, ordered
lexicographically, with `κ` taking only the values `1` and `≥ 2`.

* `cpMult p g = min p (ord g)` is the multiplicity `m(x)` of `z^p + g` at the origin. This is the
  formula `min_i (d_i + m - i)` of the proof of Proposition 3.2.2(3) of Volume 6, in which only
  `i = p` has a nonzero coefficient `f_{i, Z}`, with `d_p = ord g`.
* `cpOmegaAt p Δ g` is `ω(x)`: it is `0` if `m(x) < p`, and `cpOmega Δ g` otherwise.
* `cpKappa p Δ g` is `κ(x)`: it is `1` if `ω(x) = 0`, and `2` otherwise. The value `2` stands for
  the case `κ(x) ≥ 2`, in which Definition 3.2.5 does not distinguish the values. If `m(x) < p`,
  then `ω(x) = 0` and so `κ(x) = 1`, as the definition asks (`cpKappa_of_lt`).
* `cpIota p Δ g = (m(x), ω(x), κ(x))` in `ℕ∞ ×ₗ ℕ∞ ×ₗ ℕ`, with the lexicographic order.

## Part 4, the bound on `ι`

Let `g ≠ 0` be clean in characteristic `p` with `ord g ≥ p`, so `m(x) = p`. Let `g'` be the
polynomial at the origin of the `x_j`-chart, with the new divisor `Δ ∪ {j}`. If `m(x') < p`, then
`ι(x') < ι(x)` (`cpIota_originTransform_lt_of_lt`). In all cases `ι(x') ≤ ι(x)`
(`cpIota_originTransform_le`). The proof is the one of the handbook. The first coordinates are
`p` and `p`, the second ones satisfy `ω(x') ≤ ω(x)` (`cpOmega_originTransform_le`), and if
`ω(x') = ω(x)`, then `κ(x') = κ(x)`.

## Part 2, well adapted coordinates

Let `k` have exponential characteristic `p`, let `g` be clean with `ord g ≥ p`, and let
`h' = Z'^p + g'`. The coordinates `(x; Z')` are well adapted, that is, the projected polyhedron
`Δ(h'; x; Z')` is the characteristic polyhedron `Δ(h'; x)`
(`charPolyhedron_originTransform_eq_projPolyhedron`). It is `(1/p) N(g')`
(`charPolyhedron_originTransform`). The proof is the one of the handbook: `g'` is clean
(`OriginRuns.isClean_originTransform`), and Volume 7, Proposition 1.2.7 applies to it. The
polyhedra are the ones of `Singularity/Invariant/CharacteristicPolyhedron.lean`, for `h'` as a
polynomial in `Z'` over the power series ring.

## Main definitions

* `cpMult`, `cpOmegaAt`, `cpKappa`, `cpIota`: the invariants `m`, `ω`, `κ` and `ι` of Volume 6,
  Definition 3.2.5.

## Main results

* `cpIota_originTransform_le`: part 4, `ι(x') ≤ ι(x)`.
* `cpIota_originTransform_lt_of_lt`: part 4, `ι(x') < ι(x)` if `m(x') < p`.
* `charPolyhedron_originTransform_eq_projPolyhedron`, `charPolyhedron_originTransform`: part 2,
  `(x; Z')` is well adapted.

## References

* Volume 6, Section 3.2 of the handbook: Definition 3.2.5 and Proposition 3.2.2.
* Volume 6, Section 4.3 of the handbook: Proposition 4.3.4.
* Volume 7, Section 1.2 of the handbook: Proposition 1.2.7.
-/

open MvPolynomial Finsupp

namespace Singularity

open OriginRuns

/-! ### The lexicographic order -/

section Lex

variable {α β : Type*} [Preorder α] [Preorder β]

/-- A criterion for `≤` in the lexicographic order on a product. -/
theorem toLex_le_toLex_of_or {a a' : α} {b b' : β} (h : a < a' ∨ a = a' ∧ b ≤ b') :
    toLex (a, b) ≤ toLex (a', b') := by
  rcases h with h | ⟨rfl, h⟩
  · first
      | exact Prod.Lex.left _ _ h
      | exact Prod.Lex.toLex_le_toLex.mpr (Or.inl h)
  · first
      | exact Prod.Lex.right _ h
      | exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, h⟩)

/-- If the first coordinates satisfy `a < a'`, then `(a, b) < (a', b')` in the lexicographic
order. -/
theorem toLex_lt_toLex_of_lt {a a' : α} (b b' : β) (h : a < a') :
    toLex (a, b) < toLex (a', b') := by
  first
    | exact Prod.Lex.left _ _ h
    | exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

end Lex

/-! ### The definitions -/

section Def

variable {σ k : Type*} [CommSemiring k]

/-- The multiplicity `m(x)` of `z^p + g` at the origin (Volume 6, Definition 3.2.5 of the
handbook): `min p (ord g)`. By the proof of Proposition 3.2.2(3) of Volume 6, the order of
`h = Z^p + F` at `(x, Z)` is `min(p, ord F)`. -/
noncomputable def cpMult (p : ℕ) (g : MvPolynomial σ k) : ℕ∞ :=
  min (p : ℕ∞) (ord g)

open Classical in
/-- The invariant `ω(x)` of Volume 6, Definition 3.2.5 of the handbook, with the convention
`ω(x) = 0` if `m(x) < p`. Otherwise it is `cpOmega Δ g`. -/
noncomputable def cpOmegaAt (p : ℕ) (Δ : Finset σ) (g : MvPolynomial σ k) : ℕ∞ :=
  if cpMult p g < p then 0 else cpOmega Δ g

open Classical in
/-- The invariant `κ(x)` of Volume 6, Definition 3.2.5 of the handbook, with only the values `1`
and `≥ 2`: it is `1` if `ω(x) = 0`, and `2` otherwise. The value `2` stands for `κ(x) ≥ 2`. -/
noncomputable def cpKappa (p : ℕ) (Δ : Finset σ) (g : MvPolynomial σ k) : ℕ :=
  if cpOmegaAt p Δ g = 0 then 1 else 2

/-- The invariant `ι(x) = (m(x), ω(x), κ(x))` of Volume 6, Definition 3.2.5 of the handbook,
ordered lexicographically. -/
noncomputable def cpIota (p : ℕ) (Δ : Finset σ) (g : MvPolynomial σ k) : ℕ∞ ×ₗ ℕ∞ ×ₗ ℕ :=
  toLex (cpMult p g, toLex (cpOmegaAt p Δ g, cpKappa p Δ g))

/-- The multiplicity is at most `p`. -/
theorem cpMult_le (p : ℕ) (g : MvPolynomial σ k) : cpMult p g ≤ p :=
  min_le_left _ _

/-- If `ord g ≥ p`, then `m(x) = p`. -/
theorem cpMult_of_le {p : ℕ} {g : MvPolynomial σ k} (h : (p : ℕ∞) ≤ ord g) : cpMult p g = p :=
  min_eq_left h

/-- If `m(x) < p`, then `ω(x) = 0`. -/
theorem cpOmegaAt_of_lt {p : ℕ} (Δ : Finset σ) {g : MvPolynomial σ k} (h : cpMult p g < p) :
    cpOmegaAt p Δ g = 0 := by
  unfold cpOmegaAt
  exact if_pos h

/-- If `m(x) = p`, then `ω(x)` is `cpOmega Δ g`. -/
theorem cpOmegaAt_of_not_lt {p : ℕ} (Δ : Finset σ) {g : MvPolynomial σ k}
    (h : ¬ cpMult p g < p) : cpOmegaAt p Δ g = cpOmega Δ g := by
  unfold cpOmegaAt
  exact if_neg h

/-- If `ord g ≥ p`, then `ω(x)` is `cpOmega Δ g`. -/
theorem cpOmegaAt_of_le {p : ℕ} (Δ : Finset σ) {g : MvPolynomial σ k} (h : (p : ℕ∞) ≤ ord g) :
    cpOmegaAt p Δ g = cpOmega Δ g :=
  cpOmegaAt_of_not_lt Δ (by rw [cpMult_of_le h]; exact lt_irrefl _)

/-- `κ(x) = 1` if and only if `ω(x) = 0`. -/
theorem cpKappa_eq_one_iff {p : ℕ} {Δ : Finset σ} {g : MvPolynomial σ k} :
    cpKappa p Δ g = 1 ↔ cpOmegaAt p Δ g = 0 := by
  unfold cpKappa
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h2 => absurd h2 (by decide), fun h0 => absurd h0 h⟩

/-- If `m(x) < p`, then `κ(x) = 1`. -/
theorem cpKappa_of_lt {p : ℕ} (Δ : Finset σ) {g : MvPolynomial σ k} (h : cpMult p g < p) :
    cpKappa p Δ g = 1 :=
  cpKappa_eq_one_iff.mpr (cpOmegaAt_of_lt Δ h)

/-- The comparison of `ι` for two points with `m = p`: if `m(x') = m(x)`, `m(x) = p` and
`ω(x') ≤ ω(x)`, then `ι(x') ≤ ι(x)`. The reason: `κ(x') = κ(x)` when `ω(x') = ω(x)`. -/
theorem cpIota_le_of_cpOmega_le {p : ℕ} {Δ Δ' : Finset σ} {g g' : MvPolynomial σ k}
    (hm : cpMult p g' = cpMult p g) (hnot : ¬ cpMult p g < p)
    (hω : cpOmega Δ' g' ≤ cpOmega Δ g) : cpIota p Δ' g' ≤ cpIota p Δ g := by
  have hnot' : ¬ cpMult p g' < p := by rwa [hm]
  have hω' : cpOmegaAt p Δ' g' ≤ cpOmegaAt p Δ g := by
    rw [cpOmegaAt_of_not_lt Δ' hnot', cpOmegaAt_of_not_lt Δ hnot]
    exact hω
  unfold cpIota
  refine toLex_le_toLex_of_or (Or.inr ⟨hm, toLex_le_toLex_of_or ?_⟩)
  rcases lt_or_eq_of_le hω' with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    have hκ : cpKappa p Δ' g' = cpKappa p Δ g := by
      unfold cpKappa
      rw [heq]
    exact hκ.le

end Def

/-! ### Part 4: `ι(x') ≤ ι(x)` -/

section Iota

variable {σ k : Type*} [Fintype σ] [DecidableEq σ] [Field k] {p : ℕ} {Δ : Finset σ} {j : σ}
  {g : MvPolynomial σ k}

omit [Fintype σ] in
/-- **Proposition 4.3.4, part 4, the case `m(x') < p`** (Volume 6, Section 4.3 of the handbook).
Let `ord g ≥ p`. If the multiplicity at the origin of the `x_j`-chart is `m(x') < p`, then
`ι(x') < ι(x)`. -/
theorem cpIota_originTransform_lt_of_lt (hp : (p : ℕ∞) ≤ ord g)
    (h : cpMult p (originTransform p j g) < p) :
    cpIota p (insert j Δ) (originTransform p j g) < cpIota p Δ g := by
  unfold cpIota
  apply toLex_lt_toLex_of_lt
  rw [cpMult_of_le hp]
  exact h

/-- **Proposition 4.3.4, part 4, the bound on `ι`** (Volume 6, Section 4.3 of the handbook). Let
`k` have characteristic `p`, and let `g ≠ 0` be clean with `ord g ≥ p`. At the origin of the
`x_j`-chart, with the new divisor `Δ ∪ {j}`, `ι(x') ≤ ι(x)` for the invariant
`ι = (m, ω, κ)` of Volume 6, Definition 3.2.5, in which `κ` takes only the values `1` and
`≥ 2`. -/
theorem cpIota_originTransform_le [DecidableEq k] [CharP k p] (hg : g ≠ 0) (hc : IsClean p g)
    (hp : (p : ℕ∞) ≤ ord g) :
    cpIota p (insert j Δ) (originTransform p j g) ≤ cpIota p Δ g := by
  by_cases hm : cpMult p (originTransform p j g) < p
  · exact (cpIota_originTransform_lt_of_lt hp hm).le
  · have hm' : cpMult p (originTransform p j g) = cpMult p g := by
      rw [cpMult_of_le hp]
      exact le_antisymm (cpMult_le _ _) (not_lt.mp hm)
    have hnot : ¬ cpMult p g < p := by
      rw [cpMult_of_le hp]
      exact lt_irrefl _
    exact cpIota_le_of_cpOmega_le hm' hnot (cpOmega_originTransform_le hg hc hp)

end Iota

/-! ### Part 2: `(x; Z')` is well adapted -/

section WellAdapted

variable {σ k : Type*} [Fintype σ] [DecidableEq σ] [Field k] {p : ℕ} [ExpChar k p] {j : σ}
  {g : MvPolynomial σ k}

/-- **Proposition 4.3.4, part 2, the polyhedron** (Volume 6, Section 4.3 of the handbook). Let
`k` have exponential characteristic `p`, and let `g` be clean with `ord g ≥ p`. At the origin of
the `x_j`-chart, the characteristic polyhedron of `h' = Z'^p + g'` is `(1/p) N(g')`. -/
theorem charPolyhedron_originTransform (hc : IsClean p g) (hp : (p : ℕ∞) ≤ ord g) :
    charPolyhedron (Polynomial.X ^ p +
        Polynomial.C (originTransform p j g : MvPowerSeries σ k)) =
      ((p : ℕ) : ℝ)⁻¹ • newtonPolyhedron (originTransform p j g) := by
  have h1 : p ^ 1 = p := pow_one p
  have hc' : IsClean (p ^ 1) (originTransform p j g) := by
    rw [h1]
    exact isClean_originTransform j (degreeGe_of_le_ord hp) hc
  have h := charPolyhedron_X_pow_add_C_eq_smul_newtonPolyhedron p 1 hc'
  rw [h1] at h
  exact h

/-- **Proposition 4.3.4, part 2, `(x; Z')` is well adapted** (Volume 6, Section 4.3 of the
handbook). Let `k` have exponential characteristic `p`, and let `g` be clean with `ord g ≥ p`. At
the origin of the `x_j`-chart, the projected polyhedron `Δ(h'; x; Z')` of `h' = Z'^p + g'` is
the characteristic polyhedron `Δ(h'; x)`. So the coordinate `Z'` attains the characteristic
polyhedron, which is the definition of well adapted coordinates in Volume 6, Section 3.2. -/
theorem charPolyhedron_originTransform_eq_projPolyhedron (hc : IsClean p g)
    (hp : (p : ℕ∞) ≤ ord g) :
    charPolyhedron (Polynomial.X ^ p +
        Polynomial.C (originTransform p j g : MvPowerSeries σ k)) =
      projPolyhedron (Polynomial.X ^ p +
        Polynomial.C (originTransform p j g : MvPowerSeries σ k)) := by
  rw [charPolyhedron_originTransform hc hp,
    projPolyhedron_X_pow_add_C_coe (Nat.one_le_iff_ne_zero.mpr (expChar_ne_zero k p))]

end WellAdapted

end Singularity
