/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.LogJacobianFullDirectrix

/-!
# The kangaroo path: `τ_ρ` along a run of points of case B

Let `k` be a field of characteristic `p`. A point is a pair `(Δ, g)`, with `g` a polynomial in
`k[x_i : i ∈ σ]` and `Δ` the set of the components of the divisor `E = V(∏_{i ∈ Δ} x_i)`. A
step from `(Δ, g)` to `(Δ', g'')` is a chart of a point blowup: `g ≠ 0` is clean with
`ord g ≥ p`, the chart sends `g` to `x_j^p g'`, `Δ' = blowupDivisor Δ j t` and
`g'' = cleanPart p g'`. The step keeps `ρ = m` if `ρ = m` at both points (`RhoStep`). A component
of `Δ` can leave at a step.

A kangaroo path is a sequence of points `P_0, P_1, …, P_m` with steps that keep `ρ`, with
`P_1, …, P_{m-1}` of case B (`IsLogJacobianCaseB`). The handbook takes `P_0` and `P_m` of case A,
but the results of this file do not need this hypothesis.

This file proves Proposition 3.11.1 of Volume 7, Section 3.11 of the handbook.

* `τ_ρ` does not go down along a run of steps into points of case B:
  `τ_ρ(P_0) ≤ τ_ρ(P_{m-1})` (`logJacobianDirectrixCodim_le_of_reflTransGen`).
* At the last step, `τ_ρ(P_0) ≤ τ̃(P_m)`, with `τ̃` the full form of Section 3.8
  (`logJacobianDirectrixCodim_le_fullDirectrixCodim_of_reflTransGen`).

The proof. Proposition 3.8.2 (`logJacobianDirectrixCodim_le_cleanPart`) has the hypotheses that
`ρ` stays and that the new point is of case B. It has no hypothesis on the case of the old point,
and a component can leave. So it applies at each step into a point of case B, and an induction
gives the first result. At the last step, `logJacobianDirectrixCodim_le_fullDirectrixCodim_cleanPart`
gives `τ_ρ(P_{m-1}) ≤ τ̃(P_m)` with no hypothesis on the cases.

Conjecture 3.11.3 of the handbook is the bound `τ_ρ(P_0) ≤ τ_ρ(P_m)` if `P_m` is of case A.
Since `τ_ρ(P_m) ≤ τ̃(P_m)`, this file does not prove it. Example 3.11.2 of the handbook shows that
`T_ρ(P_m)` and `T_ρ(P_0)` can be different subspaces of the same dimension. The computation of this
example is `KangarooExample.kangarooExample`.

## Main definitions

* `RhoStep p m P Q`: a step of a point blowup from `P` to `Q` where `ρ` is `m` at both points.
* `IsLogJacobianCaseA P` and `IsLogJacobianCaseB P`: the point `P` is of case A or of case B,
  that is the order of `Θ₀(g)` is `|r| + ρ` or `|r| + ρ + 1`.
* `KangarooPathConjecture p`: the statement of Conjecture 3.11.3. It is false for `p = 2`
  (`KangarooCounterexample.not_kangarooPathConjecture`).

## Main results

* `logJacobianDirectrixCodim_le_of_rhoStep`: one step into a point of case B.
* `logJacobianDirectrixCodim_le_of_reflTransGen`: a run of steps into points of case B.
* `logJacobianDirectrixCodim_le_fullDirectrixCodim_of_reflTransGen`: Proposition 3.11.1.

## References

* Volume 7, Section 3.11 of the handbook: Proposition 3.11.1, Example 3.11.2 and Conjecture 3.11.3.
* Volume 7, Section 3.8 of the handbook: Proposition 3.8.2 and Theorem 3.8.4.
-/

open MvPolynomial Finsupp

namespace Singularity

section Kangaroo

variable {σ k : Type*} [Field k] [DecidableEq σ] [DecidableEq k] [Fintype σ] (p : ℕ) [CharP k p]

/-- **A step of a point blowup where `ρ` stays `m`.** The polynomial `g ≠ 0` of `P = (Δ, g)` is
clean with `ord g ≥ p`, the chart sends `g` to `x_j^p g'`, the new point is
`Q = (blowupDivisor Δ j t, cleanPart p g')`, and `ρ = m` at `P` and at `Q`. -/
def RhoStep (m : ℕ) (P Q : Finset σ × MvPolynomial σ k) : Prop :=
  ∃ (j : σ) (t : σ → k) (g' : MvPolynomial σ k), P.2 ≠ 0 ∧ IsClean p P.2 ∧
    (p : ℕ∞) ≤ ord P.2 ∧ pointChart j t P.2 = X j ^ p * g' ∧
    Q = (blowupDivisor P.1 j t, cleanPart p g') ∧
    logJacobianOrder P.1 P.2 = m ∧ logJacobianOrder Q.1 Q.2 = m

/-- **A point of case B**: the order of `Θ₀(g)` is `|r| + ρ + 1`. -/
def IsLogJacobianCaseB (P : Finset σ × MvPolynomial σ k) : Prop :=
  idealOrd (logJacobianTangent P.1 P.2) =
    ((degree (divisorExponent P.1 P.2) : ℕ) : ℕ∞) + logJacobianOrder P.1 P.2 + 1

/-- **A point of case A**: the order of `Θ₀(g)` is `|r| + ρ`. -/
def IsLogJacobianCaseA (P : Finset σ × MvPolynomial σ k) : Prop :=
  idealOrd (logJacobianTangent P.1 P.2) =
    ((degree (divisorExponent P.1 P.2) : ℕ) : ℕ∞) + logJacobianOrder P.1 P.2

/-- **The kangaroo path conjecture** (Volume 7, Section 3.11 of the handbook, Conjecture 3.11.3).
Let `P_0, …, P_l` be a sequence of steps that keep `ρ = m`, with `l ≥ 2`, with `P_0` and `P_l` of
case A, and with `P_1, …, P_{l-1}` of case B. Then `τ_ρ(P_0) ≤ τ_ρ(P_l)`. This is a statement,
and it is false. Example 3.11.6 of the handbook is a counterexample with `p = 2`, three variables
and the divisor `{y, z}`: from `g_0 = x^2 y^3 z + x^2 y z^3 + x^4 y z^2`, the `y`-chart at `z = 1`
and then the `y`-chart at the origin give a kangaroo path where `τ_ρ` goes `2, 2, 1`. The statement
holds if `τ_ρ(P_0) ≤ 1` (`kangarooPath_of_codim_le_one`). The negation for `p = 2`, `Fin 3` and
`ZMod 2` is `KangarooCounterexample.not_kangarooPathConjecture`. -/
def KangarooPathConjecture : Prop :=
  ∀ (m : ℕ) (P Q R : Finset σ × MvPolynomial σ k), IsLogJacobianCaseA P →
    Relation.TransGen (fun A B => RhoStep p m A B ∧ IsLogJacobianCaseB B) P Q →
    RhoStep p m Q R → IsLogJacobianCaseA R →
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianDirectrixCodim R.1 R.2

variable {p}

/-- **One step into a point of case B** (Proposition 3.8.2). If `ρ` stays and the new point is of
case B, then `τ_ρ` does not go down. There is no hypothesis on the old point, and a component of
the divisor can leave. -/
theorem logJacobianDirectrixCodim_le_of_rhoStep {m : ℕ} {P Q : Finset σ × MvPolynomial σ k}
    (hs : RhoStep p m P Q) (hB : IsLogJacobianCaseB Q) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianDirectrixCodim Q.1 Q.2 := by
  obtain ⟨j, t, g', hg, hc, hord, h, rfl, hρ, hρ'⟩ := hs
  dsimp only at hρ' hB ⊢
  unfold IsLogJacobianCaseB at hB
  rw [hρ'] at hB
  exact logJacobianDirectrixCodim_le_cleanPart p hg hc hord h hρ hρ' (by exact_mod_cast hB)

/-- **The last step of a kangaroo path.** If `ρ` stays, then `τ_ρ(P) ≤ τ̃(Q)`, with no hypothesis
on the cases. -/
theorem logJacobianDirectrixCodim_le_fullDirectrixCodim_of_rhoStep {m : ℕ}
    {P Q : Finset σ × MvPolynomial σ k} (hs : RhoStep p m P Q) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianFullDirectrixCodim Q.1 Q.2 := by
  obtain ⟨j, t, g', hg, hc, hord, h, rfl, hρ, hρ'⟩ := hs
  dsimp only at hρ' ⊢
  exact logJacobianDirectrixCodim_le_fullDirectrixCodim_cleanPart p hg hc hord h hρ hρ'

/-- **`τ_ρ` along a run of points of case B** (Volume 7, Section 3.11 of the handbook,
Proposition 3.11.1). Let `P_0, …, P_l` be a sequence of steps that keep `ρ = m`, with each of
`P_1, …, P_l` of case B. Then `τ_ρ(P_0) ≤ τ_ρ(P_l)`. -/
theorem logJacobianDirectrixCodim_le_of_reflTransGen {m : ℕ}
    {P Q : Finset σ × MvPolynomial σ k}
    (h : Relation.ReflTransGen (fun A B => RhoStep p m A B ∧ IsLogJacobianCaseB B) P Q) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianDirectrixCodim Q.1 Q.2 := by
  induction h with
  | refl => exact le_rfl
  | tail _ hBC ih => exact ih.trans (logJacobianDirectrixCodim_le_of_rhoStep hBC.1 hBC.2)

/-- **The kangaroo path** (Volume 7, Section 3.11 of the handbook, Proposition 3.11.1). Let
`P_0, …, P_m` be a sequence of steps that keep `ρ`, with `P_1, …, P_{m-1}` of case B. Then
`τ_ρ(P_0) ≤ τ̃(P_m)`. -/
theorem logJacobianDirectrixCodim_le_fullDirectrixCodim_of_reflTransGen {m : ℕ}
    {P Q R : Finset σ × MvPolynomial σ k}
    (h : Relation.ReflTransGen (fun A B => RhoStep p m A B ∧ IsLogJacobianCaseB B) P Q)
    (hQR : RhoStep p m Q R) :
    logJacobianDirectrixCodim P.1 P.2 ≤ logJacobianFullDirectrixCodim R.1 R.2 :=
  (logJacobianDirectrixCodim_le_of_reflTransGen h).trans
    (logJacobianDirectrixCodim_le_fullDirectrixCodim_of_rhoStep hQR)

end Kangaroo

end Singularity
