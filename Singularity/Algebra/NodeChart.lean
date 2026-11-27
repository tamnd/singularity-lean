/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span

/-!
# The first chart of the blowup of a node family

This file gives an algebraic part of Proposition 2.1.5 of Volume 8, Section 2.1 of the handbook.

Let `k` be a commutative ring. Let `σ` be a type of variables `t i`. There is one more variable
`t₁`. Let `g` be a polynomial in `t₁` and the `t i`. We use `Option σ` for these variables:
`none` is `t₁` and `some i` is `t i`. The ring `P` is `k[u, v, t₁, t] / (u v - t₁ g)`.

The first chart of the blowup of `(u, t₁)` adds the variable `s = t₁ / u`. In this chart we have
`t₁ = u s`, and the strict transform of `u v - t₁ g` is `v - s g(u s, t)`. Thus we use the ring
`k[u, v, s, t₁, t] / J` with `J = (t₁ - u s, v - s g)`.

## Main declarations

* `NodeChartVar σ`: the variables `u, v, s, t₁, t i`.
* `NodeChartSmallVar σ`: the variables `u, s, t i`.
* `nodeChartIdeal g`: the ideal `J = (t₁ - u s, v - s g)`.
* `nodeChart_relation_mem`: the node relation `u v - t₁ g` is in `J`.
* `nodeChartFromNode g`: the algebra map from `P[s]` to `k[u, v, s, t₁, t] / J`.
* `nodeChartEquiv g`: the algebra isomorphism from `k[u, v, s, t₁, t] / J` to the polynomial
  ring `k[u, s, t]`. It sends `t₁` to `u s` and `v` to `s g(u s, t)`.

## Gaps

We do not prove that `k[u, v, s, t₁, t] / J` is the chart `P[t₁ / u]` of the blowup. For this
step, we must show that `J` is the ideal of `P[s] / (t₁ - u s)` modulo the `u`-torsion. The
handbook uses a dimension argument for this step. We also do not treat the second chart.
-/

namespace Singularity.Algebra

open MvPolynomial

/-- The variables `u, v, s, t₁, t i` of the first chart. -/
inductive NodeChartVar (σ : Type*)
  | u
  | v
  | s
  | t₁
  | t (i : σ)

/-- The variables `u, s, t i` of the polynomial ring of the first chart. -/
inductive NodeChartSmallVar (σ : Type*)
  | u
  | s
  | t (i : σ)

variable {k : Type*} [CommRing k] {σ : Type*}

/-- The variables `t₁, t i` in the big ring. -/
noncomputable def nodeChartT : Option σ → MvPolynomial (NodeChartVar σ) k
  | none => X .t₁
  | some i => X (.t i)

/-- The variables `t₁, t i` in the small ring, with `t₁ = u s`. -/
noncomputable def nodeChartSmallT : Option σ → MvPolynomial (NodeChartSmallVar σ) k
  | none => X .u * X .s
  | some i => X (.t i)

/-- The ideal `J = (t₁ - u s, v - s g)`. -/
noncomputable def nodeChartIdeal (g : MvPolynomial (Option σ) k) :
    Ideal (MvPolynomial (NodeChartVar σ) k) :=
  Ideal.span {X .t₁ - X .u * X .s, X .v - X .s * aeval nodeChartT g}

/-- The ideal of the node relation `u v - t₁ g`. -/
noncomputable def nodeChartNodeIdeal (g : MvPolynomial (Option σ) k) :
    Ideal (MvPolynomial (NodeChartVar σ) k) :=
  Ideal.span {X .u * X .v - X .t₁ * aeval nodeChartT g}

/-- The node relation is in `J`: `u v - t₁ g = u (v - s g) - g (t₁ - u s)`. -/
theorem nodeChart_relation_mem (g : MvPolynomial (Option σ) k) :
    X .u * X .v - X .t₁ * aeval nodeChartT g ∈ nodeChartIdeal g := by
  rw [nodeChartIdeal, Ideal.mem_span_pair]
  exact ⟨-aeval nodeChartT g, X .u, by ring⟩

theorem nodeChartNodeIdeal_le (g : MvPolynomial (Option σ) k) :
    nodeChartNodeIdeal g ≤ nodeChartIdeal g := by
  rw [nodeChartNodeIdeal, Ideal.span_le, Set.singleton_subset_iff]
  exact nodeChart_relation_mem g

/-- The algebra map from `P[s] = k[u, v, s, t₁, t] / (u v - t₁ g)` to the chart ring. -/
noncomputable def nodeChartFromNode (g : MvPolynomial (Option σ) k) :
    MvPolynomial (NodeChartVar σ) k ⧸ nodeChartNodeIdeal g →ₐ[k]
      MvPolynomial (NodeChartVar σ) k ⧸ nodeChartIdeal g :=
  Ideal.Quotient.factorₐ k (nodeChartNodeIdeal_le g)

/-- The images of the variables in the small ring. -/
noncomputable def nodeChartImage (g : MvPolynomial (Option σ) k) :
    NodeChartVar σ → MvPolynomial (NodeChartSmallVar σ) k
  | .u => X .u
  | .v => X .s * aeval nodeChartSmallT g
  | .s => X .s
  | .t₁ => X .u * X .s
  | .t i => X (.t i)

theorem nodeChartImage_comp_T (g : MvPolynomial (Option σ) k) :
    (fun i => aeval (nodeChartImage g) (nodeChartT (k := k) i)) = nodeChartSmallT := by
  funext i
  cases i <;> simp [nodeChartT, nodeChartSmallT, nodeChartImage]

theorem aeval_nodeChartImage_g (g : MvPolynomial (Option σ) k) :
    aeval (nodeChartImage g) (aeval (nodeChartT (k := k)) g) = aeval nodeChartSmallT g := by
  rw [← AlgHom.comp_apply, comp_aeval, nodeChartImage_comp_T]

/-- The map from `k[u, v, s, t₁, t] / J` to `k[u, s, t]`. -/
noncomputable def nodeChartToPoly (g : MvPolynomial (Option σ) k) :
    MvPolynomial (NodeChartVar σ) k ⧸ nodeChartIdeal g →ₐ[k]
      MvPolynomial (NodeChartSmallVar σ) k :=
  Ideal.Quotient.liftₐ (nodeChartIdeal g) (aeval (nodeChartImage g)) (by
    intro a ha
    rw [nodeChartIdeal] at ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro x (rfl | rfl)
      · simp [nodeChartImage]
      · simp [nodeChartImage, aeval_nodeChartImage_g]
    · simp
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro c x _ hx
      simp [hx])

theorem nodeChartToPoly_mk (g : MvPolynomial (Option σ) k) (a : MvPolynomial (NodeChartVar σ) k) :
    nodeChartToPoly g (Ideal.Quotient.mk _ a) = aeval (nodeChartImage g) a :=
  rfl

/-- The images of the small variables in the chart ring. -/
noncomputable def nodeChartBack (g : MvPolynomial (Option σ) k) :
    NodeChartSmallVar σ → MvPolynomial (NodeChartVar σ) k ⧸ nodeChartIdeal g
  | .u => Ideal.Quotient.mk _ (X .u)
  | .s => Ideal.Quotient.mk _ (X .s)
  | .t i => Ideal.Quotient.mk _ (X (.t i))

/-- The map from `k[u, s, t]` to `k[u, v, s, t₁, t] / J`. -/
noncomputable def nodeChartOfPoly (g : MvPolynomial (Option σ) k) :
    MvPolynomial (NodeChartSmallVar σ) k →ₐ[k]
      MvPolynomial (NodeChartVar σ) k ⧸ nodeChartIdeal g :=
  aeval (nodeChartBack g)

theorem nodeChart_mk_t₁ (g : MvPolynomial (Option σ) k) :
    (Ideal.Quotient.mk (nodeChartIdeal g) (X .t₁) : _) =
      Ideal.Quotient.mk (nodeChartIdeal g) (X .u * X .s) := by
  rw [Ideal.Quotient.eq]
  exact Ideal.subset_span (Set.mem_insert _ _)

theorem nodeChart_mk_v (g : MvPolynomial (Option σ) k) :
    (Ideal.Quotient.mk (nodeChartIdeal g) (X .v) : _) =
      Ideal.Quotient.mk (nodeChartIdeal g) (X .s * aeval nodeChartT g) := by
  rw [Ideal.Quotient.eq]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem nodeChartOfPoly_g (g : MvPolynomial (Option σ) k) :
    nodeChartOfPoly g (aeval nodeChartSmallT g) =
      Ideal.Quotient.mk (nodeChartIdeal g) (aeval nodeChartT g) := by
  rw [nodeChartOfPoly, ← AlgHom.comp_apply, comp_aeval, ← Ideal.Quotient.mkₐ_eq_mk k,
    ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  cases i with
  | none =>
    simp [nodeChartSmallT, nodeChartT, nodeChartBack, nodeChart_mk_t₁]
  | some i => simp [nodeChartSmallT, nodeChartT, nodeChartBack]

/-- Proposition 2.1.5, first chart, algebraic part: the ring `k[u, v, s, t₁, t] / J` with
`J = (t₁ - u s, v - s g)` is isomorphic to the polynomial ring `k[u, s, t]`. -/
noncomputable def nodeChartEquiv (g : MvPolynomial (Option σ) k) :
    (MvPolynomial (NodeChartVar σ) k ⧸ nodeChartIdeal g) ≃ₐ[k]
      MvPolynomial (NodeChartSmallVar σ) k :=
  AlgEquiv.ofAlgHom (nodeChartToPoly g) (nodeChartOfPoly g)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      cases i <;> simp [nodeChartOfPoly, nodeChartBack, nodeChartToPoly_mk, nodeChartImage])
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply,
        nodeChartToPoly_mk, aeval_X]
      cases i with
      | u => simp [nodeChartImage, nodeChartOfPoly, nodeChartBack]
      | v =>
        rw [nodeChartImage, map_mul, nodeChartOfPoly_g, nodeChart_mk_v, map_mul]
        simp [nodeChartOfPoly, nodeChartBack]
      | s => simp [nodeChartImage, nodeChartOfPoly, nodeChartBack]
      | t₁ =>
        rw [nodeChart_mk_t₁]
        simp [nodeChartImage, nodeChartOfPoly, nodeChartBack]
      | t i => simp [nodeChartImage, nodeChartOfPoly, nodeChartBack])

theorem nodeChartEquiv_t₁ (g : MvPolynomial (Option σ) k) :
    nodeChartEquiv g (Ideal.Quotient.mk _ (X .t₁)) = X .u * X .s := by
  simp [nodeChartEquiv, nodeChartToPoly_mk, nodeChartImage]

theorem nodeChartEquiv_v (g : MvPolynomial (Option σ) k) :
    nodeChartEquiv g (Ideal.Quotient.mk _ (X .v)) = X .s * aeval nodeChartSmallT g := by
  simp [nodeChartEquiv, nodeChartToPoly_mk, nodeChartImage]

end Singularity.Algebra
