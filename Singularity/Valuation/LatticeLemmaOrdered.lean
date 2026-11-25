/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Basic.Real.Embedding
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Free
import Singularity.Valuation.LatticeLemma

/-!
# The lattice lemma for an ordered free abelian group

Let `Γ` be a free abelian group of finite rank with a total order that is compatible with addition, and let `D` be a finite set of elements `d ≥ 0` of `Γ`. The lattice lemma (Volume 5, Lemma 2.1.4 of the handbook) says: there is a basis `m_1, ..., m_r` of `Γ` with `m_i > 0` for each `i`, such that each `d ∈ D` is a combination of the `m_i` with coefficients in `ℕ`. This file proves it for each rank, with no condition on the rank of the order. The file `Singularity/Valuation/LatticeLemma.lean` proves the case of an ordered subgroup of `ℝ`, and this file uses that case.

In the application to valuations, `Γ` is the group of Laurent monomials `x^a` in a system `x_1, ..., x_n`, with the order given by the valuation. The basis `m_i` gives new monomials `u_i` with `ν(u_i) > 0`, and each monomial in `D` is a monomial in the `u_i` with exponents in `ℕ`.

## The proof

The proof is by induction on the rank `r` of `Γ`. For `r = 0` there is nothing to prove. Let `r > 0`, and let `b` be a basis of `Γ`.

1. A convex subgroup. Let `t = |b_1| + ... + |b_r|`. Then `t > 0`, and each `a ∈ Γ` has `|a| ≤ M t` for some `M ∈ ℕ`. Let `H` be the set of `a` with `N |a| < t` for each `N ∈ ℕ`. This is a convex subgroup of `Γ`, and `t ∉ H`. If `n a ∈ H` with `n ≠ 0`, then `a ∈ H`. So `Γ / H` is torsion free, thus free, and `H` has a complement `W` in `Γ`.
2. The complement is archimedean. Let `w, y ∈ W` with `w > 0`. Then `w ∉ H`, so `t ≤ N w` for some `N`, and `y ≤ |y| ≤ M t ≤ M N w`. By the theorem of Hölder, `W` is an ordered subgroup of `ℝ`, and the case of rank 1 (`Singularity.latticeLemma_real`) gives a good basis `q_1, ..., q_s` of `W` for the components in `W` of the elements of `D`. These components are `≥ 0`: if `d ∉ H`, then the component is `d - h` with `h ∈ H`, and it is `> 0` because `H` is convex.
3. The induction. The rank of `H` is `r - s < r`. The induction hypothesis gives a good basis `m_1, ..., m_k` of `H` for the elements of `D` that lie in `H`.
4. A shear. Let `S = m_1 + ... + m_k` and let `N` be a bound for the absolute values of the coordinates in the basis `m` of the components in `H` of the elements of `D`. The new basis is `m_1, ..., m_k, q_1 - N S, ..., q_s - N S`. The elements `q_i - N S` are `> 0` because `q_i ∉ H` and `H` is convex. Let `d ∈ D` with `d ∉ H`, and let `μ_i ≥ 0` be its coordinates in the basis `q`. Then `μ = ∑ μ_i ≥ 1`, and the coordinate of `d` at `m_j` in the new basis is `c_j + N μ ≥ 0`, where `c_j ≥ -N` is the coordinate of the component in `H`. The coordinates at `q_i - N S` are the `μ_i`.

The handbook proves the lemma with the cone lemma (Lemma 2.1.3) and a reduction of the index. The proof here goes by induction on convex subgroups instead, and it uses the case of rank 1 for the archimedean steps.

## Main results

* `Singularity.LatticeLemma.infinitesimal`: the convex subgroup of the elements that are infinitely small with respect to `t > 0`.
* `Singularity.LatticeLemma.exists_basis_pos_of_archimedean`: the lattice lemma for an archimedean group.
* `Singularity.LatticeLemma.exists_basis_of_split`: the induction step.
* `Singularity.latticeLemma`: the lattice lemma, for a free abelian group of finite rank with a total order compatible with addition.
* `Singularity.latticeLemma_of_injective`: the same result for `ℤ^n` with an order given by an injective map to an ordered group, in the form of two integer matrices `B` and `C` that are inverse to each other.
-/

open Module Matrix

universe u

namespace Singularity

namespace LatticeLemma

section Order

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- `|n • a| = |n| • |a|`, with the absolute value of `n` as a natural number. -/
theorem abs_int_smul (n : ℤ) (a : Γ) : |n • a| = n.natAbs • |a| := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [natCast_zsmul, abs_nsmul, Int.natAbs_natCast]
  · rw [neg_zsmul, abs_neg, natCast_zsmul, abs_nsmul, Int.natAbs_neg, Int.natAbs_natCast]

/-- The elements of `Γ` that are infinitely small with respect to `t > 0`: `N • |a| < t` for each `N ∈ ℕ`. They form a convex subgroup. -/
def infinitesimal (t : Γ) (ht : 0 < t) : Submodule ℤ Γ where
  carrier := {a | ∀ N : ℕ, N • |a| < t}
  zero_mem' := fun N => by simpa using ht
  add_mem' := by
    intro a b ha hb N
    have h1 : N • |a + b| ≤ N • (|a| + |b|) := nsmul_le_nsmul_right (abs_add_le a b) N
    rcases le_total |a| |b| with h | h
    · have h2 : N • (|a| + |b|) ≤ (N * 2) • |b| := by
        rw [mul_two, add_nsmul, ← nsmul_add]
        exact nsmul_le_nsmul_right (add_le_add_left h _) N
      exact h1.trans_lt (h2.trans_lt (hb _))
    · have h2 : N • (|a| + |b|) ≤ (N * 2) • |a| := by
        rw [mul_two, add_nsmul, ← nsmul_add]
        exact nsmul_le_nsmul_right (add_le_add_right h _) N
      exact h1.trans_lt (h2.trans_lt (ha _))
  smul_mem' := by
    intro n a ha N
    change N • |n • a| < t
    rw [abs_int_smul, ← mul_nsmul]
    exact ha _

variable {t : Γ} {ht : 0 < t}

theorem mem_infinitesimal {a : Γ} : a ∈ infinitesimal t ht ↔ ∀ N : ℕ, N • |a| < t := Iff.rfl

theorem exists_le_nsmul_of_not_mem {a : Γ} (ha : a ∉ infinitesimal t ht) : ∃ N : ℕ, t ≤ N • |a| := by
  rw [mem_infinitesimal] at ha
  push Not at ha
  exact ha

/-- An infinitely small element is smaller in absolute value than each element that is not infinitely small. -/
theorem abs_lt_abs_of_mem {a h : Γ} (hh : h ∈ infinitesimal t ht) (ha : a ∉ infinitesimal t ht) :
    |h| < |a| := by
  obtain ⟨N, hN⟩ := exists_le_nsmul_of_not_mem ha
  by_contra hle
  push Not at hle
  exact (lt_irrefl t) (hN.trans_lt ((nsmul_le_nsmul_right hle N).trans_lt (hh N)))

/-- Adding an infinitely small element does not change the sign of an element that is not infinitely small. -/
theorem pos_add_of_mem {a h : Γ} (ha : a ∉ infinitesimal t ht) (ha0 : 0 < a)
    (hh : h ∈ infinitesimal t ht) : 0 < a + h := by
  have h1 := abs_lt_abs_of_mem hh ha
  rw [abs_of_pos ha0] at h1
  have h2 : -|h| ≤ h := neg_abs_le h
  have h3 : 0 < a + -|h| := by
    rw [← sub_eq_add_neg]
    exact sub_pos.mpr h1
  exact h3.trans_le (add_le_add_right h2 a)

theorem not_mem_infinitesimal_self : t ∉ infinitesimal t ht := by
  intro h
  have := h 1
  rw [one_nsmul, abs_of_pos ht] at this
  exact lt_irrefl t this

end Order

section Archimedean

variable {W : Type*} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The lattice lemma for an archimedean group: rank 1. -/
theorem exists_basis_pos_of_archimedean [Archimedean W] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℤ W) (D : Finset W) (hD : ∀ d ∈ D, 0 ≤ d) :
    ∃ q : Basis κ ℤ W, (∀ l, 0 < q l) ∧ ∀ d ∈ D, ∀ l, 0 ≤ q.repr d l := by
  obtain ⟨ψ, hψ⟩ := Archimedean.exists_orderAddMonoidHom_real_injective W
  have hψb : ∀ n : κ → ℤ, ψ (∑ i, n i • b i) = ∑ i, (n i : ℝ) * ψ (b i) := by
    intro n
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
  have hind : ∀ a : κ → ℤ, ∑ i, (a i : ℝ) * ψ (b i) = 0 → a = 0 := by
    intro a ha
    rw [← hψb, ← map_zero ψ] at ha
    exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent a (hψ ha))
  have hpos : ∀ w : W, 0 < ψ w → 0 < w := by
    intro w hw
    by_contra h
    push Not at h
    have : ψ w ≤ ψ 0 := ψ.monotone' h
    rw [map_zero] at this
    linarith
  obtain ⟨B, C, hBC, hCB, hBpos, hEC⟩ := latticeLemma_real (fun i => ψ (b i)) hind
    (D.image fun d => b.equivFun d) (by
      intro a ha
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
      have h2 : ψ d = ∑ i, ((b.equivFun d i : ℤ) : ℝ) * ψ (b i) := by
        rw [← hψb, b.sum_equivFun d]
      rw [← h2]
      have : ψ 0 ≤ ψ d := ψ.monotone' (hD d hd)
      rwa [map_zero] at this)
  let L : (κ → ℤ) ≃ₗ[ℤ] (κ → ℤ) := LinearEquiv.ofLinearMap (vecMulLinear C) (vecMulLinear B)
    (LinearMap.ext fun v => by simp [vecMul_vecMul, hBC])
    (LinearMap.ext fun v => by simp [vecMul_vecMul, hCB])
  let q := Basis.ofEquivFun (b.equivFun.trans L)
  refine ⟨q, fun l => hpos _ ?_, fun d hd l => ?_⟩
  · have hq : q l = ∑ i, B l i • b i := by
      simp [q, L, Basis.coe_ofEquivFun, Basis.equivFun_symm_apply]
    rw [hq, hψb]
    exact hBpos l
  · have hq : q.repr d l = (b.equivFun d ᵥ* C) l := by
      rw [← q.equivFun_apply, Basis.equivFun_ofEquivFun]
      rfl
    rw [hq]
    exact hEC _ (Finset.mem_image_of_mem _ hd) l

end Archimedean

section Saturated

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] {t : Γ} {ht : 0 < t}

theorem mem_of_zsmul_mem {n : ℤ} (hn : n ≠ 0) {a : Γ} (h : n • a ∈ infinitesimal t ht) :
    a ∈ infinitesimal t ht := by
  intro N
  have h1 : |a| ≤ n.natAbs • |a| := by
    have := nsmul_le_nsmul_left (abs_nonneg a) (Int.natAbs_pos.mpr hn)
    rwa [one_nsmul] at this
  refine (nsmul_le_nsmul_right h1 N).trans_lt ?_
  have := h N
  rwa [abs_int_smul] at this

end Saturated

section Split

variable {Γ : Type*} [AddCommGroup Γ] {H : Submodule ℤ Γ} {f : Γ →ₗ[ℤ] H}

/-- The projection of `Γ` onto the kernel of a projection `f : Γ → H`, along `H`. -/
def kerProj (hf : ∀ x : H, f x = x) : Γ →ₗ[ℤ] LinearMap.ker f :=
  LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - H.subtype ∘ₗ f) fun x => by
    simp [LinearMap.mem_ker, hf]

theorem coe_kerProj (hf : ∀ x : H, f x = x) (x : Γ) : (kerProj hf x : Γ) = x - f x := rfl

/-- The splitting `Γ ≃ H × ker f` given by a projection `f : Γ → H`. -/
def splitEquiv (hf : ∀ x : H, f x = x) : Γ ≃ₗ[ℤ] H × LinearMap.ker f :=
  LinearEquiv.ofLinearMap (f.prod (kerProj hf)) (H.subtype.coprod (LinearMap.ker f).subtype)
    (by
      refine LinearMap.ext fun x => Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · have h := x.2.2
        rw [LinearMap.mem_ker] at h
        simp [hf, h]
      · have h := x.2.2
        rw [LinearMap.mem_ker] at h
        simp [coe_kerProj, hf, h])
    (by
      refine LinearMap.ext fun x => ?_
      simp [coe_kerProj])

theorem splitEquiv_apply (hf : ∀ x : H, f x = x) (x : Γ) :
    splitEquiv hf x = (f x, kerProj hf x) := rfl

theorem splitEquiv_symm_apply (hf : ∀ x : H, f x = x) (x : H × LinearMap.ker f) :
    (splitEquiv hf).symm x = (x.1 : Γ) + x.2 := rfl

theorem kerProj_of_mem (hf : ∀ x : H, f x = x) {x : Γ} (hx : x ∈ H) : kerProj hf x = 0 := by
  ext
  simp [coe_kerProj, hf ⟨x, hx⟩]

theorem kerProj_coe (hf : ∀ x : H, f x = x) (w : LinearMap.ker f) : kerProj hf w = w := by
  have h := w.2
  rw [LinearMap.mem_ker] at h
  ext
  simp [coe_kerProj, h]

theorem eq_zero_of_coe_mem (hf : ∀ x : H, f x = x) (w : LinearMap.ker f) (hw : (w : Γ) ∈ H) :
    w = 0 := by
  have h := w.2
  rw [LinearMap.mem_ker, hf ⟨w, hw⟩] at h
  ext
  simpa using congrArg Subtype.val h

end Split

section Step

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] {H : Submodule ℤ Γ} {f : Γ →ₗ[ℤ] H}

/-- The induction step of the lattice lemma. A good basis of a convex subgroup `H` and a good
basis of a complement give a good basis of `Γ`, after a shear of the second basis by `H`. -/
theorem exists_basis_of_split (hf : ∀ x : H, f x = x) {κ ν : Type*} [Fintype κ] [Fintype ν]
    [DecidableEq κ] [DecidableEq ν]
    (hconv : ∀ a h : Γ, a ∉ H → 0 < a → h ∈ H → 0 < a + h) (D : Finset Γ)
    (m : Basis κ ℤ H) (hm : ∀ j, (0 : Γ) < m j)
    (hmD : ∀ d ∈ D, ∀ hd : d ∈ H, ∀ j, 0 ≤ m.repr ⟨d, hd⟩ j)
    (q : Basis ν ℤ (LinearMap.ker f)) (hq : ∀ i, (0 : Γ) < q i)
    (hqD : ∀ d ∈ D, ∀ i, 0 ≤ q.repr (kerProj hf d) i) :
    ∃ F : Basis (κ ⊕ ν) ℤ Γ, (∀ s, 0 < F s) ∧ ∀ d ∈ D, ∀ s, 0 ≤ F.repr d s := by
  classical
  have hfH : ∀ x (hx : x ∈ H), f x = ⟨x, hx⟩ := fun x hx => hf ⟨x, hx⟩
  have hpH : ∀ x ∈ H, kerProj hf x = 0 := by
    intro x hx
    ext
    simp [coe_kerProj, hfH x hx]
  have hpW : ∀ w : LinearMap.ker f, kerProj hf w = w := by
    intro w
    have h := w.2
    rw [LinearMap.mem_ker] at h
    ext
    simp [coe_kerProj, h]
  have hWH : ∀ w : LinearMap.ker f, (w : Γ) ∈ H → w = 0 := by
    intro w hw
    have h := w.2
    rw [LinearMap.mem_ker, hfH _ hw] at h
    ext
    simpa using congrArg Subtype.val h
  let ℓ : Γ →ₗ[ℤ] ℤ := ∑ i, (q.coord i) ∘ₗ kerProj hf
  have hℓ : ∀ x, ℓ x = ∑ i, q.repr (kerProj hf x) i := by
    intro x
    simp [ℓ]
  let S : H := ∑ j, m j
  have hSrepr : ∀ j, m.repr S j = 1 := by
    intro j
    simp [S, map_sum, Finsupp.single_apply]
  have hℓH : ∀ x ∈ H, ℓ x = 0 := by
    intro x hx
    rw [hℓ, hpH x hx]
    simp
  let N : ℕ := ∑ d ∈ D, ∑ j, (m.repr (f d) j).natAbs
  have hN : ∀ d ∈ D, ∀ j, -(N : ℤ) ≤ m.repr (f d) j := by
    intro d hd j
    have h1 : (m.repr (f d) j).natAbs ≤ N :=
      (Finset.single_le_sum (f := fun j => (m.repr (f d) j).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun d => ∑ j, (m.repr (f d) j).natAbs)
          (fun _ _ => Nat.zero_le _) hd)
    have h2 := neg_abs_le (m.repr (f d) j)
    rw [← Int.natCast_natAbs] at h2
    have h3 : ((m.repr (f d) j).natAbs : ℤ) ≤ N := by exact_mod_cast h1
    linarith
  let φ : Γ →ₗ[ℤ] Γ := ((N : ℤ) • ℓ).smulRight (S : Γ)
  have hφ : ∀ x, φ x = ((N : ℤ) * ℓ x) • (S : Γ) := by
    intro x
    simp [φ]
  have hφH : ∀ x, φ x ∈ H := by
    intro x
    rw [hφ]
    exact H.smul_mem _ S.2
  have hφφ : ∀ x, φ (φ x) = 0 := by
    intro x
    rw [hφ (φ x), hℓH _ (hφH x)]
    simp
  let T : Γ ≃ₗ[ℤ] Γ := LinearEquiv.ofLinearMap (LinearMap.id - φ) (LinearMap.id + φ)
    (LinearMap.ext fun x => by simp [hφφ]) (LinearMap.ext fun x => by simp [hφφ])
  let F : Basis (κ ⊕ ν) ℤ Γ := ((m.prod q).map (splitEquiv hf).symm).map T
  have hFrepr : ∀ x s, F.repr x s = (m.prod q).repr (splitEquiv hf (x + φ x)) s := by
    intro x s
    rfl
  have hFinl : ∀ j, F (Sum.inl j) = m j := by
    intro j
    simp only [F, T, Basis.map_apply, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
      LinearMap.inl_apply, splitEquiv_symm_apply, LinearEquiv.coe_ofLinearMap]
    simp [hφ, hℓH _ (m j).2]
  have hℓq : ∀ i, ℓ (q i) = 1 := by
    intro i
    rw [hℓ, hpW]
    simp [Finsupp.single_apply]
  have hFinr : ∀ i, F (Sum.inr i) = (q i : Γ) + -(((N : ℤ)) • (S : Γ)) := by
    intro i
    simp only [F, T, Basis.map_apply, Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
      LinearMap.inr_apply, splitEquiv_symm_apply, LinearEquiv.coe_ofLinearMap]
    simp [hφ, hℓq, sub_eq_add_neg]
  have hqH : ∀ i, (q i : Γ) ∉ H := by
    intro i hi
    exact q.ne_zero i (hWH _ hi)
  refine ⟨F, ?_, ?_⟩
  · rintro (j | i)
    · rw [hFinl]
      exact hm j
    · rw [hFinr]
      exact hconv _ _ (hqH i) (hq i) (H.neg_mem (H.smul_mem _ S.2))
  · intro d hd s
    by_cases hdH : d ∈ H
    · rw [hFrepr, hφ, hℓH d hdH]
      rcases s with j | i
      · simp only [mul_zero, zero_smul, add_zero, splitEquiv_apply, Basis.prod_repr_inl]
        rw [hfH d hdH]
        exact hmD d hd hdH j
      · simp [splitEquiv_apply, Basis.prod_repr_inr, hpH d hdH]
    · have hpd : kerProj hf d ≠ 0 := by
        intro h0
        apply hdH
        have h1 := congrArg Subtype.val h0
        rw [coe_kerProj] at h1
        rw [sub_eq_zero.mp h1]
        exact (f d).2
      have hℓd : 1 ≤ ℓ d := by
        rw [hℓ]
        by_contra hlt
        push Not at hlt
        have hs0 : ∑ i, q.repr (kerProj hf d) i = 0 :=
          le_antisymm (by omega) (Finset.sum_nonneg fun i _ => hqD d hd i)
        rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => hqD d hd i] at hs0
        apply hpd
        rw [← q.repr.injective.eq_iff, map_zero]
        ext i
        exact hs0 i (Finset.mem_univ i)
      rw [hFrepr]
      rcases s with j | i
      · simp only [splitEquiv_apply, Basis.prod_repr_inl, hφ, map_add, map_zsmul, hf S,
          Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hSrepr,
          mul_one]
        have h1 := hN d hd j
        have h2 : (N : ℤ) ≤ N * ℓ d := le_mul_of_one_le_right (Int.natCast_nonneg N) hℓd
        linarith
      · rw [splitEquiv_apply, Basis.prod_repr_inr, map_add (kerProj hf), hpH _ (hφH d), add_zero]
        exact hqD d hd i

end Step

section Induction

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

theorem abs_le_nsmul_sum_abs {κ : Type*} [Fintype κ] (b : Basis κ ℤ Γ) (a : Γ) :
    ∃ M : ℕ, |a| ≤ M • ∑ i, |b i| := by
  refine ⟨∑ i, (b.repr a i).natAbs, ?_⟩
  conv_lhs => rw [← b.sum_repr a]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.smul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_int_smul]
  exact nsmul_le_nsmul_left (abs_nonneg _)
    (Finset.single_le_sum (f := fun i => (b.repr a i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))

theorem isTorsionFree_quotient_infinitesimal {t : Γ} (ht : 0 < t) :
    Module.IsTorsionFree ℤ (Γ ⧸ infinitesimal t ht) := by
  refine Module.IsTorsionFree.mk fun r hr x y hxy => ?_
  induction x using Submodule.Quotient.induction_on with | _ x => ?_
  induction y using Submodule.Quotient.induction_on with | _ y => ?_
  have hxy' : Submodule.Quotient.mk (r • x) = (Submodule.Quotient.mk (r • y) :
      Γ ⧸ infinitesimal t ht) := hxy
  rw [Submodule.Quotient.eq, ← smul_sub] at hxy'
  exact (Submodule.Quotient.eq _).mpr (mem_of_zsmul_mem hr.ne_zero hxy')

theorem exists_basis_fin (n : ℕ) : ∀ {Γ : Type u} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ], Basis (Fin n) ℤ Γ → ∀ D : Finset Γ, (∀ d ∈ D, 0 ≤ d) →
    ∃ q : Basis (Fin n) ℤ Γ, (∀ l, 0 < q l) ∧ ∀ d ∈ D, ∀ l, 0 ≤ q.repr d l := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Γ _ _ _ b D hD
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨b, fun l => l.elim0, fun _ _ l => l.elim0⟩
  set t := ∑ i, |b i| with ht_def
  have ht : 0 < t := by
    have h0 : 0 < |b ⟨0, hn⟩| := abs_pos.mpr (b.ne_zero _)
    exact h0.trans_le (Finset.single_le_sum (f := fun i => |b i|) (fun i _ => abs_nonneg (b i))
      (Finset.mem_univ _))
  set H := infinitesimal t ht with hH_def
  have := Module.Finite.of_basis b
  have := isTorsionFree_quotient_infinitesimal ht
  have : Module.Free ℤ (Γ ⧸ H) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property H.mkQ LinearMap.id H.mkQ_surjective
  have hs' : ∀ y, H.mkQ (s y) = y := fun y => LinearMap.congr_fun hs y
  have hmem : ∀ x, ((LinearMap.id : Γ →ₗ[ℤ] Γ) - s ∘ₗ H.mkQ) x ∈ H := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, LinearMap.sub_apply, LinearMap.id_apply,
      Submodule.Quotient.mk_sub]
    have := hs' (Submodule.Quotient.mk x)
    rw [Submodule.mkQ_apply] at this
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, this, sub_self]
  let f : Γ →ₗ[ℤ] H := LinearMap.codRestrict H ((LinearMap.id : Γ →ₗ[ℤ] Γ) - s ∘ₗ H.mkQ) hmem
  have hf : ∀ x : H, f x = x := by
    intro x
    ext
    simp [f, (Submodule.Quotient.mk_eq_zero H).mpr x.2]
  obtain ⟨k, m0⟩ := Submodule.basisOfPid b H
  obtain ⟨l, q0⟩ := Submodule.basisOfPid b (LinearMap.ker f)
  have hcard : n = k + l := by
    have := Fintype.card_congr (b.indexEquiv ((m0.prod q0).map (splitEquiv hf).symm))
    simpa using this
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · exfalso
      have h0 : kerProj hf t = 0 := by
        rw [← q0.sum_repr (kerProj hf t)]
        simp
      have h1 := congrArg Subtype.val h0
      rw [coe_kerProj, ZeroMemClass.coe_zero, sub_eq_zero] at h1
      have h2 : (f t : Γ) ∈ H := (f t).2
      rw [← h1] at h2
      exact not_mem_infinitesimal_self h2
    · exact hl
  obtain ⟨m, hm, hmD⟩ := ih k (by omega) m0 (D.subtype (· ∈ H)) (fun d hd =>
    hD _ (Finset.mem_subtype.mp hd))
  have : Archimedean (LinearMap.ker f) := ⟨fun y w hw => by
    have hw' : (0 : Γ) < w := hw
    have hw0 : (w : Γ) ∉ H := fun h => hw.ne' (eq_zero_of_coe_mem hf w h)
    obtain ⟨N, hN⟩ := exists_le_nsmul_of_not_mem hw0
    obtain ⟨M, hM⟩ := abs_le_nsmul_sum_abs b (y : Γ)
    refine ⟨M * N, ?_⟩
    have hc : (((M * N) • w : LinearMap.ker f) : Γ) = (M * N) • (w : Γ) := by simp
    change (y : Γ) ≤ (((M * N) • w : LinearMap.ker f) : Γ)
    rw [hc, ← smul_smul, ← abs_of_pos hw']
    exact (le_abs_self _).trans (hM.trans (nsmul_le_nsmul_right hN M))⟩
  have hDW : ∀ d ∈ D, (0 : LinearMap.ker f) ≤ kerProj hf d := by
    intro d hd
    by_cases hdH : d ∈ H
    · rw [kerProj_of_mem hf hdH]
    · have hd0 : 0 < d := lt_of_le_of_ne (hD d hd) fun h => hdH (h ▸ H.zero_mem)
      change (0 : Γ) ≤ (kerProj hf d : Γ)
      rw [coe_kerProj, sub_eq_add_neg]
      exact (pos_add_of_mem hdH hd0 (H.neg_mem (f d).2)).le
  obtain ⟨q, hq, hqD⟩ := exists_basis_pos_of_archimedean q0 (D.image (kerProj hf)) (by
    intro w hw
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
    exact hDW d hd)
  obtain ⟨F, hF, hFD⟩ := exists_basis_of_split hf
    (fun a h ha ha0 hh => pos_add_of_mem ha ha0 hh) D m (fun j => hm j)
    (fun d hd hdH j => hmD ⟨d, hdH⟩ (Finset.mem_subtype.mpr hd) j) q (fun i => hq i)
    (fun d hd => hqD _ (Finset.mem_image_of_mem _ hd))
  refine ⟨F.reindex (F.indexEquiv b), fun l => ?_, fun d hd l => ?_⟩
  · rw [Basis.reindex_apply]
    exact hF _
  · rw [Basis.repr_reindex_apply]
    exact hFD d hd _

end Induction

end LatticeLemma

open LatticeLemma

section Lattice

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {ι : Type*} [Fintype ι]

/-- The lattice lemma (Volume 5, Lemma 2.1.4). -/
theorem latticeLemma (b : Basis ι ℤ Γ) (D : Finset Γ) (hD : ∀ d ∈ D, 0 ≤ d) :
    ∃ m : Basis ι ℤ Γ, (∀ i, 0 < m i) ∧ ∀ d ∈ D, ∀ i, 0 ≤ m.repr d i := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨q, hq, hqD⟩ := exists_basis_fin _ (b.reindex e) D hD
  refine ⟨q.reindex e.symm, fun i => ?_, fun d hd i => ?_⟩
  · rw [Basis.reindex_apply]
    exact hq _
  · rw [Basis.repr_reindex_apply]
    exact hqD d hd _

/-- The lattice lemma in matrix form. -/
theorem latticeLemma_of_injective [DecidableEq ι] {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] (w : (ι → ℤ) →+ G) (hw : Function.Injective w)
    (E : Finset (ι → ℤ)) (hE : ∀ a ∈ E, 0 ≤ w a) :
    ∃ B C : Matrix ι ι ℤ, B * C = 1 ∧ C * B = 1 ∧ (∀ l, 0 < w (B l)) ∧
      ∀ a ∈ E, ∀ l, 0 ≤ (a ᵥ* C) l := by
  classical
  let e : (ι → ℤ) ≃ₗ[ℤ] w.range := (AddMonoidHom.ofInjective hw).toIntLinearEquiv
  have he : ∀ a, (e a : G) = w a := fun a => rfl
  obtain ⟨m, hm, hmE⟩ := latticeLemma ((Pi.basisFun ℤ ι).map e) (E.image e) (by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    change (0 : G) ≤ e a
    rw [he]
    exact hE a ha)
  let m' := m.map e.symm
  have hrepr : ∀ v : ι → ℤ, ∀ l, ∑ i, v i * m'.repr (Pi.single i 1) l = m'.repr v l := by
    intro v l
    have hv : v = ∑ i, v i • Pi.single i 1 := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv, map_sum]
    simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine ⟨Matrix.of fun l => m' l, Matrix.of fun i l => m'.repr (Pi.single i 1) l, ?_, ?_,
    fun l => ?_, fun a ha l => ?_⟩
  · ext l l'
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [hrepr (m' l) l', Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  · ext i i'
    have h := congrFun (m'.sum_repr (Pi.single i 1)) i'
    rw [Finset.sum_apply] at h
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [h, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  · change 0 < w (m' l)
    rw [← he]
    simp only [m', Basis.map_apply, LinearEquiv.apply_symm_apply]
    exact hm l
  · have h1 : (a ᵥ* Matrix.of fun i l => m'.repr (Pi.single i 1) l) l = m'.repr a l := by
      rw [← hrepr a l]
      rfl
    rw [h1]
    simp only [m', Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
    exact hmE _ (Finset.mem_image_of_mem _ ha) l

end Lattice

end Singularity
