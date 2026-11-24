/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Newton
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Convex.Extreme
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# The characteristic polyhedron of Hironaka

Let `k` be a commutative ring, let `A = k[[x_i : i ∈ σ]]` be the ring of formal power series, and let `f = z^m + a_1 z^(m-1) + ... + a_m` be a polynomial in `z` over `A`. In the application `f` is a Weierstrass polynomial: it is monic and each `a_i` lies in the maximal ideal. This file defines the polyhedra of Hironaka [Hir67] for such an `f` and proves their first properties. The results do not use that `f` is monic or that the `a_i` lie in the maximal ideal, unless the statement says so. The ring `A` is the power series ring over `k`, and not a general regular local ring.

The projected Newton polyhedron `Δ(f; x; z)` is the convex hull in `σ → ℝ` of the points `α / i` for `1 ≤ i ≤ m` and `x^α` a monomial of `a_i`, plus the positive orthant (`projPolyhedron`). Here `m` is `f.natDegree` and `a_i` is the coefficient `f.coeff (m - i)` of `z^(m-i)`. The change of coordinates `z ↦ z + φ` with `φ ∈ A` is the Taylor shift `Polynomial.taylor φ f = f(z + φ)`. The characteristic polyhedron `Δ(f; x)` is the intersection of the polyhedra `Δ(f(z + φ); x; z)` over all `φ` with constant term `0` (`charPolyhedron`). This is the definition of Hironaka for the fixed coordinates `x`.

Let `v ∈ ℕ^σ`. The initial polynomial of `f` at `v` is `∑_d c_d Z^d` in `k[Z]`, where `c_d` is the coefficient of `x^((m-d) v)` in the coefficient of `z^d` of `f` (`vertexPoly`). It is the initial form `in_v(f)` of Hironaka at the point `v`, after the substitution `z = Z x^v` and the division by `x^(m v)`. The vertex `v` is solvable with the constant `c` if this polynomial is `(Z + c)^m`, that is, if `in_v(f) = (z + c x^v)^m` (`IsSolvableVertex`).

## Main results

* `coeff_taylor_eq_sum`, `coeff_taylor_monomial`: the translation formula. The coefficient of `z^d` in `f(z + h)` is `∑_e (e choose d) a'_e h^(e-d)`, where `a'_e` is the coefficient of `z^e` in `f`. For `h = c x^β` the power `h^(e-d)` is the monomial `c^(e-d) x^((e-d) β)`.
* `convex_projPolyhedron`, `projPolyhedron_add_orthant`: `Δ(f; x; z)` is convex and is stable under the addition of the orthant.
* `projPolyhedron_taylor_monomial_subset`: `Δ(f(z + c x^β); x; z)` lies in the convex hull of `Δ(f; x; z)` and `β + ℝ_{≥0}^σ`. So `Δ(f(z + c x^β); x; z) ⊆ Δ(f; x; z)` if `β ∈ Δ(f; x; z)` (`projPolyhedron_taylor_monomial_subset_self`).
* `extremePoints_projPolyhedron_subset`: each vertex of `Δ(f; x; z)` is one of the points `α / i`.
* `vertexPoly_taylor_monomial`: the initial polynomial at `v` of `f(z + c x^v)` is the initial polynomial of `f` at `v`, shifted by `c`.
* `vertexPoly_ne_X_pow`: at a vertex `v` of `Δ(f; x; z)`, the initial polynomial is not `Z^m`.
* `notMem_projPolyhedron_taylor_of_isSolvable`, `projPolyhedron_taylor_ssubset_of_isSolvable`: if the vertex `v` is solvable with the constant `c`, then the translation `z ↦ z - c x^v` removes `v`, and the new polyhedron is a proper subset of the old one.
* `charPolyhedron_subset_projPolyhedron_taylor`, `convex_charPolyhedron`, `charPolyhedron_add_orthant`, `charPolyhedron_taylor`: `Δ(f; x)` lies in each `Δ(f(z + φ); x; z)`, it is convex and stable under the orthant, and it does not change under a translation `z ↦ z + ψ`.
* `not_isSolvableVertex_of_charPolyhedron_eq`: one direction of the vertex criterion of Hironaka. If `Δ(f; x; z) = Δ(f; x)`, then no vertex `v ≠ 0` of `Δ(f; x; z)` is solvable.

The other direction of the criterion of Hironaka is not proved here. It says that if no vertex is solvable, then `Δ(f; x; z) = Δ(f; x)`. Its proof needs the convergence of an infinite sequence of translations in the complete ring `A`.

## References

* [Hir67] H. Hironaka, *Characteristic polyhedra of singularities*, J. Math. Kyoto Univ. 7 (1967).
-/

open Polynomial Pointwise

namespace Singularity

/-! ### The translation formula -/

section Translation

variable {A : Type*} [CommSemiring A]

/-- The translation formula for a polynomial in `z`. The coefficient of `z^d` in `f(z + h)` is `∑_e (e choose d) b_e h^(e-d)`, where `b_e` is the coefficient of `z^e` in `f`. -/
theorem coeff_taylor_eq_sum (f : A[X]) (h : A) (d : ℕ) :
    (taylor h f).coeff d =
      ∑ e ∈ Finset.range (f.natDegree + 1), (e.choose d : A) * f.coeff e * h ^ (e - d) := by
  conv_lhs => rw [f.as_sum_range' (f.natDegree + 1) (Nat.lt_succ_self _)]
  simp only [map_sum, taylor_monomial, finsetSum_coeff, coeff_C_mul, coeff_X_add_C_pow]
  exact Finset.sum_congr rfl fun e _ => by ring

end Translation

/-! ### Sets of the form `conv(S) + ℝ_{≥0}^σ` -/

section Hull

variable {σ : Type*}

theorem convex_convexHull_add_orthant (S : Set (σ → ℝ)) :
    Convex ℝ (convexHull ℝ S + orthant σ) :=
  (convex_convexHull ℝ S).add convex_orthant

theorem convexHull_add_orthant_add_orthant (S : Set (σ → ℝ)) :
    convexHull ℝ S + orthant σ + orthant σ = convexHull ℝ S + orthant σ := by
  rw [add_assoc, orthant_add_orthant]

theorem subset_convexHull_add_orthant (S : Set (σ → ℝ)) : S ⊆ convexHull ℝ S + orthant σ :=
  fun u hu => ⟨u, subset_convexHull ℝ S hu, 0, zero_mem_orthant, add_zero u⟩

/-- If `S ⊆ P`, where `P` is convex and stable under the orthant, then `conv(S) + ℝ_{≥0}^σ ⊆ P`. -/
theorem convexHull_add_orthant_subset {S P : Set (σ → ℝ)} (hS : S ⊆ P) (hP : Convex ℝ P)
    (hPO : P + orthant σ ⊆ P) : convexHull ℝ S + orthant σ ⊆ P := by
  rintro _ ⟨a, ha, o, ho, rfl⟩
  exact hPO ⟨a, convexHull_min hS hP ha, o, ho, rfl⟩

/-- The convex hull of a union of two sets that are stable under the orthant is stable under the orthant. -/
theorem convexHull_union_add_orthant {P Q : Set (σ → ℝ)} (hP : P + orthant σ = P)
    (hQ : Q + orthant σ = Q) : convexHull ℝ (P ∪ Q) + orthant σ = convexHull ℝ (P ∪ Q) := by
  rw [← convexHull_orthant, ← convexHull_add, Set.union_add, hP, hQ]

/-- The extreme points of `conv(S) + ℝ_{≥0}^σ` lie in `S`: each vertex of the polyhedron is one of the generating points. -/
theorem extremePoints_convexHull_add_orthant_subset (S : Set (σ → ℝ)) :
    (convexHull ℝ S + orthant σ).extremePoints ℝ ⊆ S := by
  rintro _ ⟨⟨a, ha, o, ho, rfl⟩, hext⟩
  have hsub : convexHull ℝ S ⊆ convexHull ℝ S + orthant σ :=
    fun u hu => ⟨u, hu, 0, zero_mem_orthant, add_zero u⟩
  have ho0 : o = 0 := by
    have h2 : a + (2 : ℝ) • o ∈ convexHull ℝ S + orthant σ :=
      ⟨a, ha, (2 : ℝ) • o, fun i => by
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by norm_num) (ho i), rfl⟩
    have hseg : a + o ∈ openSegment ℝ a (a + (2 : ℝ) • o) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h := hext (hsub ha) h2 hseg
    exact (add_left_cancel (h.symm.trans (add_zero a).symm))
  subst ho0
  simp only [add_zero] at hext ⊢
  exact extremePoints_convexHull_subset ⟨ha, fun x₁ h₁ x₂ h₂ hs => hext (hsub h₁) (hsub h₂) hs⟩

end Hull

/-! ### The projected Newton polyhedron -/

variable {σ k : Type*}

section Semiring

variable [CommSemiring k]

/-- The coefficient of `x^α` in `n * φ`, for a natural number `n` and a power series `φ`. -/
theorem MvPowerSeries.coeff_natCast_mul (n : ℕ) (φ : MvPowerSeries σ k) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α ((n : MvPowerSeries σ k) * φ) = n * MvPowerSeries.coeff α φ := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

/-- The translation formula for the change `z ↦ z + c x^β`. The coefficient of `z^d` in `f(z + c x^β)` is `∑_e (e choose d) b_e c^(e-d) x^((e-d) β)`, where `b_e` is the coefficient of `z^e` in `f`. -/
theorem coeff_taylor_monomial (f : (MvPowerSeries σ k)[X]) (β : σ →₀ ℕ) (c : k) (d : ℕ) :
    (taylor (MvPowerSeries.monomial β c) f).coeff d =
      ∑ e ∈ Finset.range (f.natDegree + 1),
        (e.choose d : MvPowerSeries σ k) * f.coeff e *
          MvPowerSeries.monomial ((e - d) • β) (c ^ (e - d)) := by
  simp only [coeff_taylor_eq_sum, MvPowerSeries.monomial_pow]

/-- The generating points of the projected Newton polyhedron: the points `α / i` for `1 ≤ i ≤ m` and `x^α` a monomial of `a_i`, the coefficient of `z^(m-i)` in `f`. Here `m = f.natDegree`. -/
def projPoints (f : (MvPowerSeries σ k)[X]) : Set (σ → ℝ) :=
  {u | ∃ i : ℕ, 1 ≤ i ∧ i ≤ f.natDegree ∧ ∃ α : σ →₀ ℕ,
    MvPowerSeries.coeff α (f.coeff (f.natDegree - i)) ≠ 0 ∧ u = (i : ℝ)⁻¹ • expToReal α}

/-- The projected Newton polyhedron `Δ(f; x; z)` of Hironaka [Hir67]: the convex hull of the points `α / i` of `projPoints f`, plus the positive orthant. -/
noncomputable def projPolyhedron (f : (MvPowerSeries σ k)[X]) : Set (σ → ℝ) :=
  convexHull ℝ (projPoints f) + orthant σ

theorem convex_projPolyhedron (f : (MvPowerSeries σ k)[X]) : Convex ℝ (projPolyhedron f) :=
  convex_convexHull_add_orthant _

theorem projPolyhedron_add_orthant (f : (MvPowerSeries σ k)[X]) :
    projPolyhedron f + orthant σ = projPolyhedron f :=
  convexHull_add_orthant_add_orthant _

theorem projPoints_subset_projPolyhedron (f : (MvPowerSeries σ k)[X]) :
    projPoints f ⊆ projPolyhedron f :=
  subset_convexHull_add_orthant _

/-- Each vertex of `Δ(f; x; z)` is one of the points `α / i`. -/
theorem extremePoints_projPolyhedron_subset (f : (MvPowerSeries σ k)[X]) :
    (projPolyhedron f).extremePoints ℝ ⊆ projPoints f :=
  extremePoints_convexHull_add_orthant_subset _

/-- The points of `Δ(f(z + c x^β); x; z)` lie in the convex hull of `Δ(f; x; z)` and `β + ℝ_{≥0}^σ`. A monomial `x^α` of the new coefficient `a'_i` has the form `α = (i - j) β + α'` with `x^α'` a monomial of `a_j` and `j ≤ i`. So `α / i` is a convex combination of `β` and `α' / j`, or lies in `β + ℝ_{≥0}^σ` when `j = 0`. -/
theorem projPoints_taylor_monomial_subset (f : (MvPowerSeries σ k)[X]) (β : σ →₀ ℕ) (c : k) :
    projPoints (taylor (MvPowerSeries.monomial β c) f) ⊆
      convexHull ℝ (projPolyhedron f ∪ ({expToReal β} + orthant σ)) := by
  rintro _ ⟨i, hi1, him, α, hα, rfl⟩
  rw [natDegree_taylor] at him hα
  rw [coeff_taylor_monomial, map_sum] at hα
  obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
  have he' : e ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
  rw [MvPowerSeries.coeff_mul_monomial] at hne
  split_ifs at hne with hle
  swap
  · exact absurd rfl hne
  rw [MvPowerSeries.coeff_natCast_mul] at hne
  have hch : e.choose (f.natDegree - i) ≠ 0 := by
    intro h0
    rw [h0] at hne
    simp at hne
  have hei : f.natDegree - i ≤ e := by
    by_contra h
    exact hch (Nat.choose_eq_zero_of_lt (by omega))
  have hf : MvPowerSeries.coeff (α - (e - (f.natDegree - i)) • β) (f.coeff e) ≠ 0 :=
    fun h0 => hne (by rw [h0]; simp)
  obtain ⟨n, hn⟩ : ∃ n, n = e - (f.natDegree - i) := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, j = f.natDegree - e := ⟨_, rfl⟩
  rw [← hn] at hf hle
  obtain ⟨α', hα'⟩ : ∃ α', α' = α - n • β := ⟨_, rfl⟩
  rw [← hα'] at hf
  have hreal : expToReal α = n • expToReal β + expToReal α' := by
    rw [hα', ← map_nsmul, ← map_add, add_tsub_cancel_of_le hle]
  have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · have hni : n = i := by omega
    apply subset_convexHull
    right
    refine ⟨expToReal β, rfl, (i : ℝ)⁻¹ • expToReal α', fun l => ?_, ?_⟩
    · simp only [Pi.smul_apply, expToReal_apply, smul_eq_mul]
      positivity
    · rw [hreal, hni, smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hi0,
        one_smul]
  · have hP : ((j : ℝ)⁻¹ • expToReal α') ∈ projPolyhedron f := by
      refine projPoints_subset_projPolyhedron f ⟨j, hpos, by omega, α', ?_, rfl⟩
      rwa [hj, Nat.sub_sub_self he']
    have hQ : expToReal β ∈ ({expToReal β} + orthant σ : Set (σ → ℝ)) :=
      ⟨_, rfl, 0, zero_mem_orthant, add_zero _⟩
    have hsum : (n : ℝ) / i + (j : ℝ) / i = 1 := by
      rw [← add_div, ← Nat.cast_add, show n + j = i by omega, div_self hi0]
    have key := convex_convexHull ℝ (projPolyhedron f ∪ ({expToReal β} + orthant σ))
      (subset_convexHull ℝ _ (Or.inr hQ)) (subset_convexHull ℝ _ (Or.inl hP))
      (by positivity) (by positivity) hsum
    convert key using 1
    have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hreal]
    funext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
      expToReal_apply]
    field_simp

/-- The translation `z ↦ z + c x^β` moves `Δ(f; x; z)` into the convex hull of `Δ(f; x; z)` and `β + ℝ_{≥0}^σ`. -/
theorem projPolyhedron_taylor_monomial_subset (f : (MvPowerSeries σ k)[X]) (β : σ →₀ ℕ) (c : k) :
    projPolyhedron (taylor (MvPowerSeries.monomial β c) f) ⊆
      convexHull ℝ (projPolyhedron f ∪ ({expToReal β} + orthant σ)) := by
  refine convexHull_add_orthant_subset (projPoints_taylor_monomial_subset f β c)
    (convex_convexHull ℝ _) ?_
  rw [convexHull_union_add_orthant (projPolyhedron_add_orthant f)]
  rw [add_assoc, orthant_add_orthant]

/-- If `β ∈ Δ(f; x; z)`, then the translation `z ↦ z + c x^β` does not make the polyhedron larger. -/
theorem projPolyhedron_taylor_monomial_subset_self {f : (MvPowerSeries σ k)[X]} {β : σ →₀ ℕ}
    (hβ : expToReal β ∈ projPolyhedron f) (c : k) :
    projPolyhedron (taylor (MvPowerSeries.monomial β c) f) ⊆ projPolyhedron f := by
  refine (projPolyhedron_taylor_monomial_subset f β c).trans
    (convexHull_min (Set.union_subset le_rfl ?_) (convex_projPolyhedron f))
  rintro _ ⟨_, rfl, o, ho, rfl⟩
  rw [← projPolyhedron_add_orthant f]
  exact ⟨_, hβ, o, ho, rfl⟩

/-! ### The initial polynomial at a point -/

/-- The initial polynomial of `f` at `v ∈ ℕ^σ`: the polynomial `∑_d c_d Z^d` in `k[Z]`, where `c_d` is the coefficient of `x^((m-d) v)` in the coefficient of `z^d` of `f`, and `m = f.natDegree`. The initial form of Hironaka at `v` is `in_v(f) = ∑_d c_d x^((m-d) v) z^d`, and `in_v(f)(x, Z x^v) = x^(m v) ∑_d c_d Z^d`. -/
noncomputable def vertexPoly (f : (MvPowerSeries σ k)[X]) (v : σ →₀ ℕ) : k[X] :=
  ∑ d ∈ Finset.range (f.natDegree + 1),
    Polynomial.monomial d (MvPowerSeries.coeff ((f.natDegree - d) • v) (f.coeff d))

theorem coeff_vertexPoly (f : (MvPowerSeries σ k)[X]) (v : σ →₀ ℕ) (d : ℕ) :
    (vertexPoly f v).coeff d =
      if d ≤ f.natDegree then MvPowerSeries.coeff ((f.natDegree - d) • v) (f.coeff d) else 0 := by
  simp [vertexPoly, finsetSum_coeff, coeff_monomial]

/-- The initial polynomial at `v` of `f(z + c x^v)` is the initial polynomial of `f` at `v`, shifted by `c`. This is the translation formula on the face `{v}`. -/
theorem vertexPoly_taylor_monomial (f : (MvPowerSeries σ k)[X]) (v : σ →₀ ℕ) (c : k) :
    vertexPoly (taylor (MvPowerSeries.monomial v c) f) v = taylor c (vertexPoly f v) := by
  ext d
  rw [coeff_vertexPoly, natDegree_taylor]
  simp only [vertexPoly, map_sum, taylor_monomial, finsetSum_coeff, coeff_C_mul,
    coeff_X_add_C_pow]
  split_ifs with hd
  · rw [coeff_taylor_monomial, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have he' : e ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
    rw [MvPowerSeries.coeff_mul_monomial]
    rcases lt_or_ge e d with hed | hde
    · rw [Nat.choose_eq_zero_of_lt hed]
      simp
    · have hsplit : f.natDegree - d = (f.natDegree - e) + (e - d) := by omega
      rw [ite_eq_left (by rw [hsplit, add_nsmul]; exact le_add_self), hsplit, add_nsmul,
        add_tsub_cancel_right, MvPowerSeries.coeff_natCast_mul]
      ring
  · symm
    refine Finset.sum_eq_zero fun e he => ?_
    have he' : e ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- At a vertex `v` of `Δ(f; x; z)`, the initial polynomial of `f` is not `Z^m`: the vertex is a point `α / i` with `α = i v`, so the coefficient of `Z^(m-i)` is not `0`. -/
theorem vertexPoly_ne_X_pow {f : (MvPowerSeries σ k)[X]} {v : σ →₀ ℕ}
    (hv : expToReal v ∈ (projPolyhedron f).extremePoints ℝ) :
    vertexPoly f v ≠ X ^ f.natDegree := by
  intro h
  obtain ⟨i, hi1, him, α, hα, hu⟩ := extremePoints_projPolyhedron_subset f hv
  have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hαv : α = i • v := by
    ext l
    have hl := congrFun hu l
    simp only [expToReal_apply, Pi.smul_apply, smul_eq_mul] at hl
    rw [Finsupp.smul_apply, smul_eq_mul]
    have : (α l : ℝ) = i * v l := by
      rw [hl]
      field_simp
    exact_mod_cast this
  have hc := congrArg (fun P => P.coeff (f.natDegree - i)) h
  simp only [coeff_vertexPoly, coeff_X_pow] at hc
  rw [ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self him, ite_eq_right (by omega)] at hc
  rw [hαv] at hα
  exact hα hc

/-! ### The characteristic polyhedron -/

/-- The characteristic polyhedron `Δ(f; x)` of Hironaka [Hir67]: the intersection of the polyhedra `Δ(f(z + φ); x; z)` over all power series `φ` with constant term `0`. -/
noncomputable def charPolyhedron (f : (MvPowerSeries σ k)[X]) : Set (σ → ℝ) :=
  ⋂ φ : MvPowerSeries σ k, ⋂ (_ : MvPowerSeries.constantCoeff φ = 0),
    projPolyhedron (taylor φ f)

/-- The characteristic polyhedron lies in `Δ(f(z + φ); x; z)` for each `φ` with constant term `0`. -/
theorem charPolyhedron_subset_projPolyhedron_taylor (f : (MvPowerSeries σ k)[X])
    {φ : MvPowerSeries σ k} (hφ : MvPowerSeries.constantCoeff φ = 0) :
    charPolyhedron f ⊆ projPolyhedron (taylor φ f) :=
  Set.iInter₂_subset φ hφ

theorem charPolyhedron_subset_projPolyhedron (f : (MvPowerSeries σ k)[X]) :
    charPolyhedron f ⊆ projPolyhedron f := by
  simpa using charPolyhedron_subset_projPolyhedron_taylor f (map_zero _)

theorem convex_charPolyhedron (f : (MvPowerSeries σ k)[X]) : Convex ℝ (charPolyhedron f) :=
  convex_iInter₂ fun _ _ => convex_projPolyhedron _

theorem charPolyhedron_add_orthant (f : (MvPowerSeries σ k)[X]) :
    charPolyhedron f + orthant σ = charPolyhedron f := by
  refine subset_antisymm ?_ fun u hu => ⟨u, hu, 0, zero_mem_orthant, add_zero u⟩
  rintro _ ⟨a, ha, o, ho, rfl⟩
  refine Set.mem_iInter₂.mpr fun φ hφ => ?_
  rw [← projPolyhedron_add_orthant]
  exact ⟨a, Set.mem_iInter₂.mp ha φ hφ, o, ho, rfl⟩

/-- If `0 ≠ v`, then the constant term of `c x^v` is `0`. -/
theorem constantCoeff_monomial_of_ne {v : σ →₀ ℕ} (hv : v ≠ 0) (c : k) :
    MvPowerSeries.constantCoeff (MvPowerSeries.monomial v c) = 0 := by
  classical
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_monomial,
    ite_eq_right (Ne.symm hv)]

end Semiring

section Ring

variable [CommRing k]

/-- The characteristic polyhedron does not change under a translation `z ↦ z + ψ` with `ψ` in the maximal ideal. -/
theorem charPolyhedron_taylor (f : (MvPowerSeries σ k)[X]) {ψ : MvPowerSeries σ k}
    (hψ : MvPowerSeries.constantCoeff ψ = 0) : charPolyhedron (taylor ψ f) = charPolyhedron f := by
  refine subset_antisymm (Set.subset_iInter₂ fun φ hφ => ?_)
    (Set.subset_iInter₂ fun φ hφ => ?_)
  · have h := charPolyhedron_subset_projPolyhedron_taylor (taylor ψ f)
      (φ := φ - ψ) (by rw [map_sub, hφ, hψ, sub_zero])
    rwa [taylor_taylor, sub_add_cancel] at h
  · rw [taylor_taylor]
    exact charPolyhedron_subset_projPolyhedron_taylor f (by rw [map_add, hφ, hψ, add_zero])

/-- The vertex `v` of `Δ(f; x; z)` is solvable with the constant `c` if the initial polynomial of `f` at `v` is `(Z + c)^m`, that is, if the initial form of `f` at `v` is `(z + c x^v)^m`. -/
def IsSolvableVertex (f : (MvPowerSeries σ k)[X]) (v : σ →₀ ℕ) (c : k) : Prop :=
  vertexPoly f v = (X + C c) ^ f.natDegree

/-- If `v` is solvable with the constant `c`, then the initial polynomial at `v` of `f(z - c x^v)` is `Z^m`. -/
theorem vertexPoly_taylor_of_isSolvable {f : (MvPowerSeries σ k)[X]} {v : σ →₀ ℕ} {c : k}
    (hs : IsSolvableVertex f v c) :
    vertexPoly (taylor (MvPowerSeries.monomial v (-c)) f) v = X ^ f.natDegree := by
  rw [vertexPoly_taylor_monomial, hs, taylor_pow, map_add, taylor_X, taylor_C, add_assoc, ← C_add,
    neg_add_cancel, C_0, add_zero]

/-- One direction of the vertex criterion of Hironaka [Hir67]. Let `v` be a vertex of `Δ(f; x; z)` that is solvable with the constant `c`. Then the translation `z ↦ z - c x^v` removes `v`: the point `v` is not in `Δ(f(z - c x^v); x; z)`. -/
theorem notMem_projPolyhedron_taylor_of_isSolvable {f : (MvPowerSeries σ k)[X]} {v : σ →₀ ℕ}
    {c : k} (hv : expToReal v ∈ (projPolyhedron f).extremePoints ℝ)
    (hs : IsSolvableVertex f v c) :
    expToReal v ∉ projPolyhedron (taylor (MvPowerSeries.monomial v (-c)) f) := by
  intro hmem
  have hsub := projPolyhedron_taylor_monomial_subset_self hv.1 (-c)
  have hext := inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hmem, hv⟩
  apply vertexPoly_ne_X_pow hext
  rw [natDegree_taylor]
  exact vertexPoly_taylor_of_isSolvable hs

/-- If a vertex `v` of `Δ(f; x; z)` is solvable with the constant `c`, then `Δ(f(z - c x^v); x; z)` is a proper subset of `Δ(f; x; z)`. -/
theorem projPolyhedron_taylor_ssubset_of_isSolvable {f : (MvPowerSeries σ k)[X]} {v : σ →₀ ℕ}
    {c : k} (hv : expToReal v ∈ (projPolyhedron f).extremePoints ℝ)
    (hs : IsSolvableVertex f v c) :
    projPolyhedron (taylor (MvPowerSeries.monomial v (-c)) f) ⊂ projPolyhedron f :=
  (Set.ssubset_iff_of_subset (projPolyhedron_taylor_monomial_subset_self hv.1 (-c))).mpr
    ⟨expToReal v, hv.1, notMem_projPolyhedron_taylor_of_isSolvable hv hs⟩

/-- A solvable vertex `v ≠ 0` of `Δ(f; x; z)` is not in the characteristic polyhedron. -/
theorem notMem_charPolyhedron_of_isSolvable {f : (MvPowerSeries σ k)[X]} {v : σ →₀ ℕ} {c : k}
    (hv0 : v ≠ 0) (hv : expToReal v ∈ (projPolyhedron f).extremePoints ℝ)
    (hs : IsSolvableVertex f v c) : expToReal v ∉ charPolyhedron f := fun h =>
  notMem_projPolyhedron_taylor_of_isSolvable hv hs
    (charPolyhedron_subset_projPolyhedron_taylor f (constantCoeff_monomial_of_ne hv0 (-c)) h)

/-- One direction of the vertex criterion of Hironaka [Hir67]. If the coordinate `z` attains the characteristic polyhedron, that is `Δ(f; x; z) = Δ(f; x)`, then no vertex `v ≠ 0` of `Δ(f; x; z)` is solvable. -/
theorem not_isSolvableVertex_of_charPolyhedron_eq {f : (MvPowerSeries σ k)[X]} {v : σ →₀ ℕ}
    (h : charPolyhedron f = projPolyhedron f) (hv0 : v ≠ 0)
    (hv : expToReal v ∈ (projPolyhedron f).extremePoints ℝ) (c : k) :
    ¬ IsSolvableVertex f v c := fun hs =>
  notMem_charPolyhedron_of_isSolvable hv0 hv hs (h ▸ hv.1)

end Ring

end Singularity
