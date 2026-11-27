/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Algebra.NodeChart

/-!
# The second chart of the blowup of a node family

This file gives an algebraic part of Proposition 2.1.5 of Volume 8, Section 2.1 of the handbook.
We use the notation of `Singularity.Algebra.NodeChart`. The ring `P` is
`k[u, v, t₁, t] / (u v - t₁ g)`.

The second chart of the blowup of `(u, t₁)` adds the variable `s = u / t₁`. The handbook calls
this variable `u'`. In this chart we have `u = t₁ s`, and the strict transform of `u v - t₁ g` is
`s v - g`. Thus we use the ring `k[u, v, s, t₁, t] / J₂` with `J₂ = (u - t₁ s, s v - g)`. We have

  `u v - t₁ g = v (u - t₁ s) + t₁ (s v - g)`,

so the node relation is in `J₂`.

## Main declarations

* `NodeChartTwoSmallVar σ`: the variables `s, v, t₁, t i` of the ring `C₂`.
* `nodeChartTwoSmallIdeal g`: the ideal `(s v - g)` of `k[s, v, t₁, t]`.
* `nodeChartTwoIdeal g`: the ideal `J₂ = (u - t₁ s, s v - g)`.
* `nodeChartTwo_relation_mem`: the node relation `u v - t₁ g` is in `J₂`.
* `nodeChartTwoFromNode g`: the algebra map from `P[s]` to `k[u, v, s, t₁, t] / J₂`.
* `nodeChartTwoEquiv g`: the algebra isomorphism from `k[u, v, s, t₁, t] / J₂` to
  `C₂ = k[s, v, t₁, t] / (s v - g)`. It sends `u` to `t₁ s`.
* `nodeChartTwoNodeMap g`: the composite algebra map from `P[s]` to `C₂`.

## Gaps

We do not prove that `k[u, v, s, t₁, t] / J₂` is the chart `P[u / t₁]` of the blowup. For this
step, we must show that `J₂` is the ideal of `P[s] / (u - t₁ s)` modulo the `t₁`-torsion. The
handbook uses a dimension argument for this step. We do not prove that `C₂` is a domain, and we do
not prove that the two charts cover the blowup.
-/

namespace Singularity.Algebra

open MvPolynomial

/-- The variables `s, v, t₁, t i` of the ring `C₂` of the second chart. Here `s = u / t₁`. -/
inductive NodeChartTwoSmallVar (σ : Type*)
  | s
  | v
  | t₁
  | t (i : σ)

variable {k : Type*} [CommRing k] {σ : Type*}

/-- The variables `t₁, t i` in the ring `k[s, v, t₁, t]`. -/
noncomputable def nodeChartTwoSmallT : Option σ → MvPolynomial (NodeChartTwoSmallVar σ) k
  | none => X .t₁
  | some i => X (.t i)

/-- The ideal `(s v - g)` of `k[s, v, t₁, t]`. -/
noncomputable def nodeChartTwoSmallIdeal (g : MvPolynomial (Option σ) k) :
    Ideal (MvPolynomial (NodeChartTwoSmallVar σ) k) :=
  Ideal.span {X .s * X .v - aeval nodeChartTwoSmallT g}

/-- The ideal `J₂ = (u - t₁ s, s v - g)`. -/
noncomputable def nodeChartTwoIdeal (g : MvPolynomial (Option σ) k) :
    Ideal (MvPolynomial (NodeChartVar σ) k) :=
  Ideal.span {X .u - X .t₁ * X .s, X .s * X .v - aeval nodeChartT g}

/-- The node relation is in `J₂`: `u v - t₁ g = v (u - t₁ s) + t₁ (s v - g)`. -/
theorem nodeChartTwo_relation_mem (g : MvPolynomial (Option σ) k) :
    X .u * X .v - X .t₁ * aeval nodeChartT g ∈ nodeChartTwoIdeal g := by
  rw [nodeChartTwoIdeal, Ideal.mem_span_pair]
  exact ⟨X .v, X .t₁, by ring⟩

theorem nodeChartNodeIdeal_le_two (g : MvPolynomial (Option σ) k) :
    nodeChartNodeIdeal g ≤ nodeChartTwoIdeal g := by
  rw [nodeChartNodeIdeal, Ideal.span_le, Set.singleton_subset_iff]
  exact nodeChartTwo_relation_mem g

/-- The algebra map from `P[s] = k[u, v, s, t₁, t] / (u v - t₁ g)` to the second chart ring. -/
noncomputable def nodeChartTwoFromNode (g : MvPolynomial (Option σ) k) :
    MvPolynomial (NodeChartVar σ) k ⧸ nodeChartNodeIdeal g →ₐ[k]
      MvPolynomial (NodeChartVar σ) k ⧸ nodeChartTwoIdeal g :=
  Ideal.Quotient.factorₐ k (nodeChartNodeIdeal_le_two g)

/-- The images of the variables in `k[s, v, t₁, t]`, with `u = t₁ s`. -/
noncomputable def nodeChartTwoImage : NodeChartVar σ → MvPolynomial (NodeChartTwoSmallVar σ) k
  | .u => X .t₁ * X .s
  | .v => X .v
  | .s => X .s
  | .t₁ => X .t₁
  | .t i => X (.t i)

theorem nodeChartTwoImage_comp_T :
    (fun i => aeval (nodeChartTwoImage (k := k) (σ := σ)) (nodeChartT (k := k) i)) =
      nodeChartTwoSmallT := by
  funext i
  cases i <;> simp [nodeChartT, nodeChartTwoSmallT, nodeChartTwoImage]

theorem aeval_nodeChartTwoImage_g (g : MvPolynomial (Option σ) k) :
    aeval (nodeChartTwoImage (k := k)) (aeval (nodeChartT (k := k)) g) =
      aeval nodeChartTwoSmallT g := by
  rw [← AlgHom.comp_apply, comp_aeval, nodeChartTwoImage_comp_T]

/-- The map from `k[u, v, s, t₁, t] / J₂` to `C₂ = k[s, v, t₁, t] / (s v - g)`. -/
noncomputable def nodeChartTwoToSmall (g : MvPolynomial (Option σ) k) :
    MvPolynomial (NodeChartVar σ) k ⧸ nodeChartTwoIdeal g →ₐ[k]
      MvPolynomial (NodeChartTwoSmallVar σ) k ⧸ nodeChartTwoSmallIdeal g :=
  Ideal.Quotient.liftₐ (nodeChartTwoIdeal g)
    ((Ideal.Quotient.mkₐ k (nodeChartTwoSmallIdeal g)).comp (aeval nodeChartTwoImage)) (by
    intro a ha
    rw [nodeChartTwoIdeal] at ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro x (rfl | rfl)
      · simp [nodeChartTwoImage]
      · rw [AlgHom.comp_apply, map_sub, map_mul, aeval_X, aeval_X, aeval_nodeChartTwoImage_g,
          Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
    · simp
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro c x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero])

theorem nodeChartTwoToSmall_mk (g : MvPolynomial (Option σ) k)
    (a : MvPolynomial (NodeChartVar σ) k) :
    nodeChartTwoToSmall g (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (aeval nodeChartTwoImage a) :=
  rfl

/-- The images of the variables `s, v, t₁, t i` in the second chart ring. -/
noncomputable def nodeChartTwoBack (g : MvPolynomial (Option σ) k) :
    NodeChartTwoSmallVar σ → MvPolynomial (NodeChartVar σ) k ⧸ nodeChartTwoIdeal g
  | .s => Ideal.Quotient.mk _ (X .s)
  | .v => Ideal.Quotient.mk _ (X .v)
  | .t₁ => Ideal.Quotient.mk _ (X .t₁)
  | .t i => Ideal.Quotient.mk _ (X (.t i))

theorem nodeChartTwoBack_s (g : MvPolynomial (Option σ) k) :
    nodeChartTwoBack g .s = Ideal.Quotient.mk (nodeChartTwoIdeal g) (X .s) :=
  rfl

theorem nodeChartTwoBack_v (g : MvPolynomial (Option σ) k) :
    nodeChartTwoBack g .v = Ideal.Quotient.mk (nodeChartTwoIdeal g) (X .v) :=
  rfl

theorem aeval_nodeChartTwoBack_g (g : MvPolynomial (Option σ) k) :
    aeval (nodeChartTwoBack g) (aeval (nodeChartTwoSmallT (k := k)) g) =
      Ideal.Quotient.mk (nodeChartTwoIdeal g) (aeval nodeChartT g) := by
  rw [← AlgHom.comp_apply, comp_aeval, ← Ideal.Quotient.mkₐ_eq_mk k,
    ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  cases i <;> simp [nodeChartTwoSmallT, nodeChartT, nodeChartTwoBack]

/-- The map from `C₂ = k[s, v, t₁, t] / (s v - g)` to `k[u, v, s, t₁, t] / J₂`. -/
noncomputable def nodeChartTwoOfSmall (g : MvPolynomial (Option σ) k) :
    MvPolynomial (NodeChartTwoSmallVar σ) k ⧸ nodeChartTwoSmallIdeal g →ₐ[k]
      MvPolynomial (NodeChartVar σ) k ⧸ nodeChartTwoIdeal g :=
  Ideal.Quotient.liftₐ (nodeChartTwoSmallIdeal g) (aeval (nodeChartTwoBack g)) (by
    intro a ha
    rw [nodeChartTwoSmallIdeal] at ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro x rfl
      rw [map_sub, map_mul, aeval_X, aeval_X, aeval_nodeChartTwoBack_g, nodeChartTwoBack_s,
        nodeChartTwoBack_v, ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    · exact map_zero _
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro c x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero])

theorem nodeChartTwoOfSmall_mk (g : MvPolynomial (Option σ) k)
    (a : MvPolynomial (NodeChartTwoSmallVar σ) k) :
    nodeChartTwoOfSmall g (Ideal.Quotient.mk _ a) = aeval (nodeChartTwoBack g) a :=
  rfl

theorem nodeChartTwo_mk_u (g : MvPolynomial (Option σ) k) :
    (Ideal.Quotient.mk (nodeChartTwoIdeal g) (X .u) : _) =
      Ideal.Quotient.mk (nodeChartTwoIdeal g) (X .t₁ * X .s) := by
  rw [Ideal.Quotient.eq]
  exact Ideal.subset_span (Set.mem_insert _ _)

/-- Proposition 2.1.5, second chart, algebraic part: the ring `k[u, v, s, t₁, t] / J₂` with
`J₂ = (u - t₁ s, s v - g)` is isomorphic to `C₂ = k[s, v, t₁, t] / (s v - g)`. -/
noncomputable def nodeChartTwoEquiv (g : MvPolynomial (Option σ) k) :
    (MvPolynomial (NodeChartVar σ) k ⧸ nodeChartTwoIdeal g) ≃ₐ[k]
      (MvPolynomial (NodeChartTwoSmallVar σ) k ⧸ nodeChartTwoSmallIdeal g) :=
  AlgEquiv.ofAlgHom (nodeChartTwoToSmall g) (nodeChartTwoOfSmall g)
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply,
        nodeChartTwoOfSmall_mk, aeval_X]
      cases i <;> simp [nodeChartTwoBack, nodeChartTwoToSmall_mk, nodeChartTwoImage])
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply,
        nodeChartTwoToSmall_mk, aeval_X]
      cases i with
      | u =>
        rw [nodeChartTwo_mk_u]
        simp [nodeChartTwoImage, nodeChartTwoOfSmall_mk, nodeChartTwoBack]
      | v => simp [nodeChartTwoImage, nodeChartTwoOfSmall_mk, nodeChartTwoBack]
      | s => simp [nodeChartTwoImage, nodeChartTwoOfSmall_mk, nodeChartTwoBack]
      | t₁ => simp [nodeChartTwoImage, nodeChartTwoOfSmall_mk, nodeChartTwoBack]
      | t i => simp [nodeChartTwoImage, nodeChartTwoOfSmall_mk, nodeChartTwoBack])

theorem nodeChartTwoEquiv_u (g : MvPolynomial (Option σ) k) :
    nodeChartTwoEquiv g (Ideal.Quotient.mk _ (X .u)) =
      Ideal.Quotient.mk _ (X .t₁ * X .s) := by
  simp [nodeChartTwoEquiv, nodeChartTwoToSmall_mk, nodeChartTwoImage]

/-- The composite algebra map from `P[s]` to `C₂ = k[s, v, t₁, t] / (s v - g)`. It sends `u`
to `t₁ s`. -/
noncomputable def nodeChartTwoNodeMap (g : MvPolynomial (Option σ) k) :
    MvPolynomial (NodeChartVar σ) k ⧸ nodeChartNodeIdeal g →ₐ[k]
      MvPolynomial (NodeChartTwoSmallVar σ) k ⧸ nodeChartTwoSmallIdeal g :=
  (nodeChartTwoEquiv g).toAlgHom.comp (nodeChartTwoFromNode g)

theorem nodeChartTwoNodeMap_u (g : MvPolynomial (Option σ) k) :
    nodeChartTwoNodeMap g (Ideal.Quotient.mk _ (X .u)) =
      Ideal.Quotient.mk _ (X .t₁ * X .s) := by
  simp [nodeChartTwoNodeMap, nodeChartTwoFromNode, nodeChartTwoEquiv, nodeChartTwoToSmall_mk,
    nodeChartTwoImage]

end Singularity.Algebra
