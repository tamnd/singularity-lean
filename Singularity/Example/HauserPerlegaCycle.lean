/-
Copyright (c) 2026 The singularity authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Singularity.Invariant.Residual
import Mathlib.Algebra.CharP.Two

/-!
# One cycle of the first example of Hauser and Perlega

This file certifies one full cycle of the first example of Hauser and Perlega [HP19a, Section 4].
The field `K` has characteristic 2.
The equation is `f = z^8 + F` in `n = 5` variables `x, y, u, v, w`, which are `X 0, ..., X 4`.

The paper starts from

  `F = x^(8a+4) y^(8b+4) u^(8r) w^(8s-d) (w^d (λ + u^(2d+6) Q) + x^(d+1) u^(2d+6) A)`.

This file uses the instance `d = 2`, `a = b = r = 0`, `s = 1`, `λ = 1`, `A = 1` and `Q = 0`, so

  `F = x^4 y^4 w^6 (w^2 + x^3 u^10)`.

The start divisor is `x y u w = 0`, and the residual order along it is `d = 2`.
The cycle has the 7 steps of the paper, with 20 point blowups:

1. the `x`-chart with `y ↦ y + 1`, `u ↦ u + 1`, and then cleaning with `z ↦ z + x w`,
2. the `x`-chart,
3. the `u`-chart,
4. the `v`-chart, `d / 2 = 1` times,
5. the `w`-chart with `y ↦ y + 1`, `v ↦ v + 1`,
6. the `u`-chart,
7. the `y`-chart, `2d + 10 = 14` times.

For each blowup the file proves five facts.
These are the chart equation `π(F) = x_j^8 F'`, the weak transform `z^8 + F'` of `f`, the bound `8 ≤ ord F'`, the new divisor (`blowupDivisor`) and the residual order along the new divisor.
The residual orders are 6 after step (1), 5 after steps (2), (3), (4) and (5), 4 after step (6), and 4 after each of the 14 charts of step (7).
These are the values `d + 4`, `d + 3` and `d + 2` of the paper.
The paper does not give the values after steps (3), (4) and (5).
The final equation has the shape of the start, with `y` and `u` exchanged and with `d + 2 = 4` in place of `d` (`cycleF7_shape`).
The main theorem is `hauserPerlegaCycle`.

## Method

The file uses the method of `Singularity/Example/HauserPerlega.lean`, with one change.
Each polynomial is the sum of the monomials in a list of exponent vectors (`poly5`).
A monomial that occurs twice cancels, because the characteristic is 2.
A chart without translation acts on each exponent vector (`chartStep5`).
A translation `x_i ↦ x_i + 1` expands `(x_i + 1)^n` by the binary digits of `n` (`binom2`, `shift5_poly5`).
The lists for the steps are computed from the start list.
The checks on the lists (cleanness, order, the factor of the divisor, the witnesses for the residual order) use `decide +kernel`, so the kernel computes them.

## Where the instance differs from the paper

* The paper writes the factors `(y + 1)^(8b+4)`, `(u + 1)^(8r)` and `(u + 1)^(2d+6)` in step (1) and `(v + 1)^((8a+8r+8s+6)d/2)` in step (5) as units, and it puts them into the series `A`, `B` and `Q`.
  Here the polynomials keep the full expansions.
  In step (5) the exponent of `v + 1` is 30.
  After step (5) the right side has 136 monomials.
* In step (1) the paper removes the term `λ (u + 1)^(8r) w^d` by cleaning.
  Here this term is `x^8 w^8`, and `z ↦ z + x w` removes it.
  The polynomial before cleaning also has residual order 6, because `residualOrderAlong` uses the clean part.
  Steps (2) to (7) need no cleaning.
* After step (7) the series `Q` and `A` of the final equation are not 0 and 1.
  They are explicit polynomials, and `A(0) = 1`.
-/

open MvPolynomial Finsupp

namespace Singularity.Examples

/-! ### Exponent vectors in five variables -/

/-- An exponent vector `(a, b, c, d, e)` of the monomial `x^a y^b u^c v^d w^e`. -/
abbrev Exp5 := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The entries of an exponent vector as a function on `Fin 5`. -/
def ev5 (e : Exp5) : Fin 5 → ℕ := ![e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2]

/-- The exponent vector with the entries `f 0, ..., f 4`. -/
def ofFun5 (f : Fin 5 → ℕ) : Exp5 := (f 0, f 1, f 2, f 3, f 4)

/-- The total degree of an exponent vector. -/
def deg5 (e : Exp5) : ℕ := e.1 + e.2.1 + e.2.2.1 + e.2.2.2.1 + e.2.2.2.2

/-- The exponent vector `e` with the entry `i` replaced by `n`. -/
def set5 (e : Exp5) (i : Fin 5) (n : ℕ) : Exp5 := ofFun5 (Function.update (ev5 e) i n)

/-- `true` if each entry of `e` is a multiple of `q`, that is, if `x^e` is a `q`-th power. -/
def allDvd5 (q : ℕ) (e : Exp5) : Bool :=
  e.1 % q == 0 && e.2.1 % q == 0 && e.2.2.1 % q == 0 && e.2.2.2.1 % q == 0 &&
    e.2.2.2.2 % q == 0

/-- `true` if each entry of `r` is at most the entry of `e`. -/
def le5 (r e : Exp5) : Bool :=
  r.1 ≤ e.1 && r.2.1 ≤ e.2.1 && r.2.2.1 ≤ e.2.2.1 && r.2.2.2.1 ≤ e.2.2.2.1 &&
    r.2.2.2.2 ≤ e.2.2.2.2

@[simp]
theorem ev5_ofFun5 (f : Fin 5 → ℕ) : ev5 (ofFun5 f) = f := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem ofFun5_ev5 (e : Exp5) : ofFun5 (ev5 e) = e := rfl

theorem ev5_injective : Function.Injective ev5 := fun e e' h => by
  rw [← ofFun5_ev5 e, h, ofFun5_ev5]

theorem set5_ev5_self (e : Exp5) (i : Fin 5) : set5 e i (ev5 e i) = e := by
  rw [set5, Function.update_eq_self, ofFun5_ev5]

theorem allDvd5_iff (q : ℕ) (f : Fin 5 → ℕ) : allDvd5 q (ofFun5 f) = true ↔ ∀ i, q ∣ f i := by
  simp only [allDvd5, ofFun5, Bool.and_eq_true, beq_iff_eq, ← Nat.dvd_iff_mod_eq_zero]
  refine ⟨fun h i => ?_, fun h => ⟨⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩, h 4⟩⟩
  fin_cases i
  exacts [h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2]

/-! ### Polynomials as lists of exponent vectors -/

/-- The finitely supported function of an exponent vector. -/
noncomputable def toF5 (e : Exp5) : Fin 5 →₀ ℕ := Finsupp.equivFunOnFinite.symm (ev5 e)

@[simp]
theorem toF5_apply (e : Exp5) (i : Fin 5) : toF5 e i = ev5 e i := rfl

theorem coe_toF5 (e : Exp5) : ⇑(toF5 e) = ev5 e := rfl

theorem toF5_injective : Function.Injective toF5 := fun e e' h =>
  ev5_injective (by rw [← coe_toF5, h, coe_toF5])

@[simp]
theorem toF5_ofFun5 (d : Fin 5 →₀ ℕ) : toF5 (ofFun5 d) = d := by
  ext i
  simp

@[simp]
theorem ofFun5_toF5 (e : Exp5) : ofFun5 (toF5 e) = e := by
  rw [coe_toF5, ofFun5_ev5]

theorem toF5_add (a b : Exp5) : toF5 (a + b) = toF5 a + toF5 b := by
  ext i
  fin_cases i <;> rfl

theorem degree_toF5 (e : Exp5) : Finsupp.degree (toF5 e) = deg5 e := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_five]
  rfl

variable {R : Type*} [CommRing R]

theorem monomial_toF5 (e : Exp5) : monomial (toF5 e) (1 : R) =
    X 0 ^ e.1 * X 1 ^ e.2.1 * X 2 ^ e.2.2.1 * X 3 ^ e.2.2.2.1 * X 4 ^ e.2.2.2.2 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_five]
  rfl

/-- The polynomial `∑_{e ∈ L} x^e`.
An exponent vector that appears twice in `L` cancels in characteristic 2. -/
noncomputable def poly5 (L : List Exp5) : MvPolynomial (Fin 5) R :=
  (L.map fun e => monomial (toF5 e) 1).sum

@[simp]
theorem poly5_nil : (poly5 [] : MvPolynomial (Fin 5) R) = 0 := rfl

@[simp]
theorem poly5_cons (e : Exp5) (L : List Exp5) :
    (poly5 (e :: L) : MvPolynomial (Fin 5) R) = monomial (toF5 e) 1 + poly5 L := by
  simp [poly5]

theorem poly5_append (L L' : List Exp5) :
    (poly5 (L ++ L') : MvPolynomial (Fin 5) R) = poly5 L + poly5 L' := by
  simp [poly5]

theorem poly5_flatMap (L : List Exp5) (g : Exp5 → List Exp5) :
    (poly5 (L.flatMap g) : MvPolynomial (Fin 5) R) = (L.map fun e => poly5 (g e)).sum := by
  induction L with
  | nil => rfl
  | cons e L ih => rw [List.flatMap_cons, poly5_append, ih, List.map_cons, List.sum_cons]

theorem poly5_filter_add (p : Exp5 → Bool) (L : List Exp5) :
    (poly5 (L.filter p) : MvPolynomial (Fin 5) R) + poly5 (L.filter fun e => !p e) =
      poly5 L := by
  induction L with
  | nil => simp
  | cons e L ih =>
    by_cases h : p e
    · simp only [List.filter_cons, h, ite_true, Bool.not_true, poly5_cons, ← ih]
      simp
      ring
    · simp only [List.filter_cons, h, Bool.not_false, poly5_cons, ← ih]
      simp
      ring

/-- Multiplication by a monomial adds its exponent vector to each exponent vector. -/
theorem monomial_mul_poly5 (r : Exp5) (L : List Exp5) :
    monomial (toF5 r) (1 : R) * poly5 L = poly5 (L.map (r + ·)) := by
  induction L with
  | nil => simp
  | cons e L ih =>
    rw [poly5_cons, mul_add, ih, List.map_cons, poly5_cons, monomial_mul_monomial, mul_one, toF5_add]

/-- The coefficient of `x^d` in `∑_{e ∈ L} x^e` is the number of times that `d` appears in `L`. -/
theorem coeff_poly5 (L : List Exp5) (d : Fin 5 →₀ ℕ) :
    (poly5 L : MvPolynomial (Fin 5) R).coeff d = (L.count (ofFun5 d) : R) := by
  induction L with
  | nil => simp
  | cons e L ih =>
    rw [poly5_cons, coeff_add_apply, ih, coeff_monomial, List.count_cons]
    by_cases h : e = ofFun5 d
    · subst h
      simp only [toF5_ofFun5, ite_true, beq_self_eq_true]
      push_cast
      ring
    · have h' : toF5 e ≠ d := fun h'' =>
        h (toF5_injective (h''.trans (toF5_ofFun5 d).symm))
      simp [h, h']

theorem mem_of_mem_support_poly5 {L : List Exp5} {d : Fin 5 →₀ ℕ}
    (hd : d ∈ (poly5 L : MvPolynomial (Fin 5) R).support) : ofFun5 d ∈ L := by
  rw [MvPolynomial.mem_support_iff, coeff_poly5] at hd
  refine List.count_pos_iff.mp (Nat.pos_of_ne_zero fun h => hd ?_)
  rw [h, Nat.cast_zero]

theorem toF5_mem_support_poly5 [CharP R 2] {L : List Exp5} {e : Exp5} (h : L.count e % 2 = 1) :
    toF5 e ∈ (poly5 L : MvPolynomial (Fin 5) R).support := by
  rw [MvPolynomial.mem_support_iff, coeff_poly5, ofFun5_toF5, Ne, CharP.cast_eq_zero_iff R 2]
  omega

/-- A list of exponent vectors, none of them in `q ℕ^5`, gives a clean polynomial. -/
theorem isClean_poly5 {q : ℕ} {L : List Exp5} (h : L.all (fun e => !allDvd5 q e) = true) :
    IsClean q (poly5 L : MvPolynomial (Fin 5) R) := by
  intro d hd hall
  have hmem := mem_of_mem_support_poly5 hd
  have := List.all_eq_true.mp h _ hmem
  rw [(allDvd5_iff q d).mpr hall] at this
  exact Bool.false_ne_true this

theorem le_ord_poly5 {n : ℕ} {L : List Exp5} (h : L.all (fun e => n ≤ deg5 e) = true) :
    (n : ℕ∞) ≤ ord (poly5 L : MvPolynomial (Fin 5) R) := by
  refine le_ord_iff.mpr fun d hd => ?_
  by_contra hc
  have hmem := mem_of_mem_support_poly5 (MvPolynomial.mem_support_iff.mpr hc)
  have := List.all_eq_true.mp h _ hmem
  rw [decide_eq_true_eq, ← degree_toF5, toF5_ofFun5] at this
  omega

theorem ord_poly5 [CharP R 2] {n : ℕ} {L : List Exp5} (h : L.all (fun e => n ≤ deg5 e) = true)
    (e : Exp5) (he : deg5 e = n) (hc : L.count e % 2 = 1) :
    ord (poly5 L : MvPolynomial (Fin 5) R) = n := by
  refine le_antisymm ?_ (le_ord_poly5 h)
  have := ord_le (MvPolynomial.mem_support_iff.mp (toF5_mem_support_poly5 (R := R) hc))
  rwa [degree_toF5, he] at this

/-- The residual order along `Δ` of `x^r ∑_{e ∈ G} x^e`, computed from the list `G`. -/
theorem residualOrderAlong_poly5 [CharP R 2] (Δ : Finset (Fin 5)) (q n : ℕ) (r : Exp5)
    (G : List Exp5) (hclean : (G.map (r + ·)).all (fun e => !allDvd5 q e) = true)
    (hr : ∀ i, i ∉ Δ → ev5 r i = 0)
    (hG : ∀ i ∈ Δ, (G.any fun e => ev5 e i == 0 && G.count e % 2 == 1) = true)
    (hlow : G.all (fun e => n ≤ deg5 e) = true) (e : Exp5) (he : deg5 e = n)
    (hc : G.count e % 2 = 1) :
    residualOrderAlong Δ q (poly5 (G.map (r + ·)) : MvPolynomial (Fin 5) R) = n := by
  have hclean' : IsClean q (monomial (toF5 r) (1 : R) * poly5 G) := by
    rw [monomial_mul_poly5]
    exact isClean_poly5 hclean
  rw [← monomial_mul_poly5 r G,
    residualOrderAlong_eq hclean' (fun i hi => hr i hi), ord_poly5 hlow e he hc]
  intro i hi
  obtain ⟨e', -, he'⟩ := List.any_eq_true.mp (hG i hi)
  simp only [Bool.and_eq_true, beq_iff_eq] at he'
  exact ⟨toF5 e', toF5_mem_support_poly5 he'.2, he'.1⟩

/-- `L` is `x^r` times the list of the differences `e - r`, if `r ≤ e` for each `e ∈ L`. -/
theorem map_sub_add {r : Exp5} {L : List Exp5} (h : L.all (le5 r) = true) :
    (L.map fun e => e - r).map (r + ·) = L := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  refine List.map_congr_left fun e he => ?_
  have := List.all_eq_true.mp h e he
  obtain ⟨a, b, c, d, w⟩ := e
  obtain ⟨a', b', c', d', w'⟩ := r
  simp only [le5, Bool.and_eq_true, decide_eq_true_eq] at this
  simp only [Function.comp_apply, id, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk.injEq]
  omega

/-! ### Charts and translations on lists -/

/-- The exponent vector of the `x_j`-chart, divided by `x_j^q`: the entry `j` becomes the total degree minus `q`. -/
def chartStep5 (q : ℕ) (j : Fin 5) (e : Exp5) : Exp5 := set5 e j (deg5 e - q)

theorem monomial_set5 (e : Exp5) (i : Fin 5) (k : ℕ) :
    monomial (toF5 (set5 e i k)) (1 : R) = monomial (toF5 (set5 e i 0)) 1 * X i ^ k := by
  obtain ⟨a, b, c, d, w⟩ := e
  fin_cases i <;> simp [monomial_toF5, set5, ofFun5, ev5] <;> ring

theorem pointChart_zero_X (j i : Fin 5) :
    pointChart j (0 : Fin 5 → R) (X i) = if i = j then X j else X j * X i := by
  split_ifs with h
  · subst h
    exact pointChart_X_self _ _
  · rw [pointChart_X_of_ne _ h]
    simp

theorem pointChart_monomial_toF5 (j : Fin 5) (e : Exp5) :
    pointChart j (0 : Fin 5 → R) (monomial (toF5 e) 1) =
      monomial (toF5 (set5 e j (deg5 e))) 1 := by
  obtain ⟨a, b, c, d, w⟩ := e
  rw [monomial_toF5, monomial_toF5]
  simp only [map_mul, map_pow, pointChart_zero_X]
  fin_cases j <;> simp [set5, ofFun5, ev5, deg5] <;> ring

/-- The `x_j`-chart without translations sends `∑_{e ∈ L} x^e` to `x_j^q` times the polynomial of the list `chartStep5 q j e`, if each monomial of `L` has degree at least `q`. -/
theorem pointChart_poly5 (q : ℕ) (j : Fin 5) (L : List Exp5)
    (h : L.all (fun e => q ≤ deg5 e) = true) :
    pointChart j (0 : Fin 5 → R) (poly5 L) = X j ^ q * poly5 (L.map (chartStep5 q j)) := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [poly5_cons, map_add, ih h.2, List.map_cons, poly5_cons, mul_add,
      pointChart_monomial_toF5]
    congr 1
    obtain ⟨m, hm⟩ : ∃ m, deg5 e = m + q := ⟨deg5 e - q, by omega⟩
    rw [chartStep5, hm, Nat.add_sub_cancel, monomial_set5 e j (m + q), monomial_set5 e j m,
      pow_add]
    ring

/-- The translation `x_i ↦ x_i + 1`. -/
noncomputable def shift5 (i : Fin 5) : MvPolynomial (Fin 5) R →ₐ[R] MvPolynomial (Fin 5) R :=
  aeval fun k => if k = i then X k + 1 else X k

theorem shift5_X (i k : Fin 5) :
    shift5 i (X k : MvPolynomial (Fin 5) R) = if k = i then X k + 1 else X k := by
  simp [shift5]

theorem shift5_monomial_set5_zero (i : Fin 5) (e : Exp5) :
    shift5 i (monomial (toF5 (set5 e i 0)) (1 : R)) = monomial (toF5 (set5 e i 0)) 1 := by
  obtain ⟨a, b, c, d, w⟩ := e
  rw [monomial_toF5]
  simp only [map_mul, map_pow, shift5_X]
  fin_cases i <;> simp [set5, ofFun5, ev5]

/-- The exponents `k` with `binom n k` odd, computed with the binary digits of `n`.
The first argument is a bound for the recursion. -/
def binom2Aux : ℕ → ℕ → List ℕ
  | 0, _ => [0]
  | f + 1, n =>
    if n = 0 then [0] else
      (binom2Aux f (n / 2)).flatMap fun k => if n % 2 = 0 then [2 * k] else [2 * k, 2 * k + 1]

/-- The exponents `k` with `binom n k` odd. -/
def binom2 (n : ℕ) : List ℕ := binom2Aux n n

theorem add_one_pow_eq_sum_aux {A : Type*} [CommRing A] [CharP A 2] (f : ℕ) :
    ∀ (n : ℕ) (a : A), n ≤ f → (a + 1) ^ n = ((binom2Aux f n).map (a ^ ·)).sum := by
  induction f with
  | zero =>
    intro n a hn
    obtain rfl : n = 0 := by omega
    simp [binom2Aux]
  | succ f ih =>
    intro n a hn
    by_cases h0 : n = 0
    · subst h0
      simp [binom2Aux]
    · rw [binom2Aux]
      simp only [h0, ↓reduceIte]
      have hsq : (a + 1) ^ 2 = a ^ 2 + 1 := by rw [CharTwo.add_sq, one_pow]
      have hn2 : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
      have key : ∀ B : List ℕ, ((B.flatMap fun k =>
          if n % 2 = 0 then [2 * k] else [2 * k, 2 * k + 1]).map (a ^ ·)).sum =
            (B.map ((a ^ 2) ^ ·)).sum * (a + 1) ^ (n % 2) := by
        intro B
        induction B with
        | nil => simp
        | cons k B ihB =>
          rw [List.flatMap_cons, List.map_append, List.sum_append, ihB, List.map_cons,
            List.sum_cons, add_mul]
          congr 1
          rcases Nat.mod_two_eq_zero_or_one n with h | h
          · simp [h, ← pow_mul]
          · simp [h, ← pow_mul]
            ring
      rw [key, ← ih (n / 2) (a ^ 2) (by omega), ← hsq, ← pow_mul, ← pow_add, hn2]

/-- In characteristic 2, `(a + 1)^n` is the sum of the `a^k` with `binom n k` odd. -/
theorem add_one_pow_eq_sum {A : Type*} [CommRing A] [CharP A 2] (a : A) (n : ℕ) :
    (a + 1) ^ n = ((binom2 n).map (a ^ ·)).sum :=
  add_one_pow_eq_sum_aux n n a le_rfl

theorem poly5_map_set5 (e : Exp5) (i : Fin 5) (B : List ℕ) :
    (poly5 (B.map (set5 e i)) : MvPolynomial (Fin 5) R) =
      monomial (toF5 (set5 e i 0)) 1 * (B.map (X i ^ ·)).sum := by
  induction B with
  | nil => simp
  | cons k B ih =>
    rw [List.map_cons, poly5_cons, ih, monomial_set5 e i k, List.map_cons, List.sum_cons, mul_add]

theorem shift5_monomial [CharP R 2] (i : Fin 5) (e : Exp5) :
    shift5 i (monomial (toF5 e) (1 : R)) = poly5 ((binom2 (ev5 e i)).map (set5 e i)) := by
  conv_lhs => rw [← set5_ev5_self e i, monomial_set5]
  rw [map_mul, map_pow, shift5_monomial_set5_zero, shift5_X]
  simp only [↓reduceIte]
  rw [poly5_map_set5, add_one_pow_eq_sum]

/-- The translation `x_i ↦ x_i + 1` on lists of exponent vectors. -/
def transl5 (i : Fin 5) (L : List Exp5) : List Exp5 :=
  L.flatMap fun e => (binom2 (ev5 e i)).map (set5 e i)

theorem shift5_poly5 [CharP R 2] (i : Fin 5) (L : List Exp5) :
    shift5 i (poly5 L : MvPolynomial (Fin 5) R) = poly5 (transl5 i L) := by
  rw [transl5, poly5_flatMap]
  induction L with
  | nil => simp
  | cons e L ih => rw [poly5_cons, map_add, ih, shift5_monomial, List.map_cons, List.sum_cons]

theorem shift5_X_pow_of_ne {i j : Fin 5} (h : j ≠ i) (n : ℕ) :
    shift5 i (X j ^ n : MvPolynomial (Fin 5) R) = X j ^ n := by
  simp only [map_pow, shift5_X, h, ↓reduceIte]

/-! ### The stages of the cycle -/

/-- The exponent vectors of the starting equation `z^8 + x^4 y^4 w^6 (w^2 + x^3 u^10)`. -/
def cycleL0 : List Exp5 := [(4, 4, 0, 0, 8), (7, 4, 10, 0, 6)]

/-- Step (1): the `x`-chart with the translations `y ↦ y + 1`, `u ↦ u + 1`, before cleaning. -/
def cycleL1' : List Exp5 := transl5 1 (transl5 2 (cycleL0.map (chartStep5 8 0)))

/-- Step (1) after cleaning: the monomial `x^8 w^8` is removed. -/
def cycleL1 : List Exp5 := cycleL1'.filter fun e => !allDvd5 8 e

/-- Step (2): the `x`-chart. -/
def cycleL2 : List Exp5 := cycleL1.map (chartStep5 8 0)

/-- Step (3): the `u`-chart. -/
def cycleL3 : List Exp5 := cycleL2.map (chartStep5 8 2)

/-- Step (4): the `v`-chart, `d / 2 = 1` times. -/
def cycleL4 : List Exp5 := cycleL3.map (chartStep5 8 3)

/-- Step (5): the `w`-chart with the translations `y ↦ y + 1`, `v ↦ v + 1`. -/
def cycleL5 : List Exp5 := transl5 1 (transl5 3 (cycleL4.map (chartStep5 8 4)))

/-- Step (6): the `u`-chart. -/
def cycleL6 : List Exp5 := cycleL5.map (chartStep5 8 2)

/-- Step (7): the `y`-chart, `k` times.
The step uses `k = 2d + 10 = 14`. -/
def cycleL7 : ℕ → List Exp5
  | 0 => cycleL6
  | k + 1 => (cycleL7 k).map (chartStep5 8 1)

variable {K : Type*} [Field K]

/-- The right side `F = x^4 y^4 w^6 (w^2 + x^3 u^10)` of the starting equation `f = z^8 + F`.
It is the equation of [HP19a, Section 4, (0)] with `d = 2`, `a = b = r = 0`, `s = 1`, `λ = 1`, `A = 1` and `Q = 0`. -/
noncomputable def cycleF0 : MvPolynomial (Fin 5) K :=
  X 0 ^ 4 * X 1 ^ 4 * X 4 ^ 6 * (X 4 ^ 2 + X 0 ^ 3 * X 2 ^ 10)

/-- The right side of the equation after step (1), before cleaning. -/
noncomputable def cycleF1' : MvPolynomial (Fin 5) K := poly5 cycleL1'

/-- The right side of the equation after step (1). -/
noncomputable def cycleF1 : MvPolynomial (Fin 5) K := poly5 cycleL1

/-- The right side of the equation after step (2). -/
noncomputable def cycleF2 : MvPolynomial (Fin 5) K := poly5 cycleL2

/-- The right side of the equation after step (3). -/
noncomputable def cycleF3 : MvPolynomial (Fin 5) K := poly5 cycleL3

/-- The right side of the equation after step (4). -/
noncomputable def cycleF4 : MvPolynomial (Fin 5) K := poly5 cycleL4

/-- The right side of the equation after step (5). -/
noncomputable def cycleF5 : MvPolynomial (Fin 5) K := poly5 cycleL5

/-- The right side of the equation after step (6). -/
noncomputable def cycleF6 : MvPolynomial (Fin 5) K := poly5 cycleL6

/-- The right side of the equation after `k` of the `y`-charts of step (7). -/
noncomputable def cycleF7 (k : ℕ) : MvPolynomial (Fin 5) K := poly5 (cycleL7 k)

/-- The translations `y ↦ y + 1`, `u ↦ u + 1` of step (1). -/
def cycleT1 : Fin 5 → K := ![0, 1, 1, 0, 0]

/-- The translations `y ↦ y + 1`, `v ↦ v + 1` of step (5). -/
def cycleT5 : Fin 5 → K := ![0, 1, 0, 1, 0]

/-- The coordinate change `z_1 = z + x w` that cleans the equation in step (1). -/
noncomputable def cycleH1 : MvPolynomial (Fin 5) K := X 0 * X 4

theorem cycleF0_eq : (cycleF0 : MvPolynomial (Fin 5) K) = poly5 cycleL0 := by
  simp only [cycleF0, cycleL0, poly5_cons, poly5_nil, monomial_toF5]
  ring

theorem pointChart_cycleT1 :
    pointChart 0 (cycleT1 : Fin 5 → K) =
      (shift5 1).comp ((shift5 2).comp (pointChart 0 (0 : Fin 5 → K))) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [pointChart, shift5, cycleT1]

theorem pointChart_cycleT5 :
    pointChart 4 (cycleT5 : Fin 5 → K) =
      (shift5 1).comp ((shift5 3).comp (pointChart 4 (0 : Fin 5 → K))) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [pointChart, shift5, cycleT5]

variable [CharP K 2]

theorem two_eq_zero_five : (2 : MvPolynomial (Fin 5) K) = 0 := by
  rw [show (2 : MvPolynomial (Fin 5) K) = C 2 from (map_ofNat C 2).symm, CharTwo.two_eq_zero,
    map_zero]

/-- The residual order along `Δ` of `∑_{e ∈ L} x^e`, with the factor `x^r` and the residual factor read off from the list. -/
theorem residualOrderAlong_poly5' (Δ : Finset (Fin 5)) (n : ℕ) (r : Exp5) (L : List Exp5)
    (hle : L.all (le5 r) = true) (hclean : L.all (fun e => !allDvd5 8 e) = true)
    (hr : ∀ i, i ∉ Δ → ev5 r i = 0)
    (hG : ∀ i ∈ Δ, ((L.map fun e => e - r).any fun e =>
      ev5 e i == 0 && (L.map fun e => e - r).count e % 2 == 1) = true)
    (hlow : (L.map fun e => e - r).all (fun e => n ≤ deg5 e) = true) (e : Exp5) (he : deg5 e = n)
    (hc : (L.map fun e => e - r).count e % 2 = 1) :
    residualOrderAlong Δ 8 (poly5 L : MvPolynomial (Fin 5) K) = n := by
  rw [← map_sub_add hle] at hclean ⊢
  exact residualOrderAlong_poly5 Δ 8 n r _ hclean hr hG hlow e he hc

/-! ### The start -/

omit [CharP K 2] in
theorem isClean_cycleF0 : IsClean 8 (cycleF0 : MvPolynomial (Fin 5) K) := by
  rw [cycleF0_eq]
  exact isClean_poly5 (by decide +kernel)

omit [CharP K 2] in
theorem ord_cycleF0 : 8 ≤ ord (cycleF0 : MvPolynomial (Fin 5) K) := by
  rw [cycleF0_eq]
  exact_mod_cast le_ord_poly5 (n := 8) (by decide +kernel)

/-- The starting residual order is `d = 2`. -/
theorem residualOrderAlong_cycleF0 :
    residualOrderAlong {0, 1, 2, 4} 8 (cycleF0 : MvPolynomial (Fin 5) K) = 2 := by
  rw [cycleF0_eq]
  exact residualOrderAlong_poly5' _ 2 (4, 4, 0, 0, 6) _ (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel) (by decide +kernel) (0, 0, 0, 0, 2) rfl (by decide +kernel)

/-! ### Step (1) -/

/-- Step (1): the `x`-chart with `y ↦ y + 1`, `u ↦ u + 1` sends `F` to `x^8 F_1'`. -/
theorem pointChart_cycleF0 :
    pointChart 0 cycleT1 (cycleF0 : MvPolynomial (Fin 5) K) = X 0 ^ 8 * cycleF1' := by
  rw [pointChart_cycleT1, AlgHom.comp_apply, AlgHom.comp_apply, cycleF0_eq,
    pointChart_poly5 8 0 _ (by decide +kernel), map_mul, map_mul,
    shift5_X_pow_of_ne (i := 2) (j := 0) (by decide),
    shift5_X_pow_of_ne (i := 1) (j := 0) (by decide), shift5_poly5, shift5_poly5]
  rfl

/-- Step (1), cleaning: `z ↦ z + x w` removes the monomial `x^8 w^8`. -/
theorem cycleF1'_add_pow : (cycleF1' : MvPolynomial (Fin 5) K) + cycleH1 ^ 8 = cycleF1 := by
  have hfil : cycleL1'.filter (allDvd5 8) = [(8, 0, 0, 0, 8)] := by decide +kernel
  have h := poly5_filter_add (R := K) (allDvd5 8) cycleL1'
  rw [hfil] at h
  rw [cycleF1', cycleF1, cycleL1, ← h, cycleH1]
  simp only [poly5_cons, poly5_nil, monomial_toF5]
  linear_combination (X 0 ^ 8 * X 4 ^ 8) * two_eq_zero_five (K := K)

omit [CharP K 2] in
theorem ord_cycleF1' : 8 ≤ ord (cycleF1' : MvPolynomial (Fin 5) K) := by
  exact_mod_cast le_ord_poly5 (n := 8) (by decide +kernel)

omit [CharP K 2] in
theorem ord_cycleF1 : 8 ≤ ord (cycleF1 : MvPolynomial (Fin 5) K) := by
  exact_mod_cast le_ord_poly5 (n := 8) (by decide +kernel)

/-- After step (1) the residual order is `d + 4 = 6`. -/
theorem residualOrderAlong_cycleF1 :
    residualOrderAlong {0, 4} 8 (cycleF1 : MvPolynomial (Fin 5) K) = 6 :=
  residualOrderAlong_poly5' _ 6 (8, 0, 0, 0, 6) _ (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel) (by decide +kernel) (0, 4, 0, 0, 2) rfl (by decide +kernel)

/-! ### Steps (2) to (6) -/

omit [CharP K 2] in
theorem pointChart_cycleF1 :
    pointChart 0 0 (cycleF1 : MvPolynomial (Fin 5) K) = X 0 ^ 8 * cycleF2 :=
  pointChart_poly5 8 0 _ (by decide +kernel)

omit [CharP K 2] in
theorem ord_cycleF2 : 8 ≤ ord (cycleF2 : MvPolynomial (Fin 5) K) := by
  exact_mod_cast le_ord_poly5 (n := 8) (by decide +kernel)

/-- After step (2) the residual order is `d + 3 = 5`. -/
theorem residualOrderAlong_cycleF2 :
    residualOrderAlong {0, 4} 8 (cycleF2 : MvPolynomial (Fin 5) K) = 5 :=
  residualOrderAlong_poly5' _ 5 (12, 0, 0, 0, 6) _ (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel) (by decide +kernel) (5, 0, 0, 0, 0) rfl (by decide +kernel)

omit [CharP K 2] in
theorem pointChart_cycleF2 :
    pointChart 2 0 (cycleF2 : MvPolynomial (Fin 5) K) = X 2 ^ 8 * cycleF3 :=
  pointChart_poly5 8 2 _ (by decide +kernel)

omit [CharP K 2] in
theorem ord_cycleF3 : 8 ≤ ord (cycleF3 : MvPolynomial (Fin 5) K) := by
  exact_mod_cast le_ord_poly5 (n := 8) (by decide +kernel)

theorem residualOrderAlong_cycleF3 :
    residualOrderAlong {0, 2, 4} 8 (cycleF3 : MvPolynomial (Fin 5) K) = 5 :=
  residualOrderAlong_poly5' _ 5 (12, 0, 15, 0, 6) _ (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel) (by decide +kernel) (5, 0, 0, 0, 0) rfl (by decide +kernel)

omit [CharP K 2] in
theorem pointChart_cycleF3 :
    pointChart 3 0 (cycleF3 : MvPolynomial (Fin 5) K) = X 3 ^ 8 * cycleF4 :=
  pointChart_poly5 8 3 _ (by decide +kernel)

omit [CharP K 2] in
theorem ord_cycleF4 : 8 ≤ ord (cycleF4 : MvPolynomial (Fin 5) K) := by
  exact_mod_cast le_ord_poly5 (n := 8) (by decide +kernel)

theorem residualOrderAlong_cycleF4 :
    residualOrderAlong {0, 2, 3, 4} 8 (cycleF4 : MvPolynomial (Fin 5) K) = 5 :=
  residualOrderAlong_poly5' _ 5 (12, 0, 15, 30, 6) _ (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel) (by decide +kernel) (5, 0, 0, 0, 0) rfl (by decide +kernel)

theorem pointChart_cycleF4 :
    pointChart 4 cycleT5 (cycleF4 : MvPolynomial (Fin 5) K) = X 4 ^ 8 * cycleF5 := by
  rw [pointChart_cycleT5, AlgHom.comp_apply, AlgHom.comp_apply, cycleF4,
    pointChart_poly5 8 4 _ (by decide +kernel), map_mul, map_mul,
    shift5_X_pow_of_ne (i := 3) (j := 4) (by decide),
    shift5_X_pow_of_ne (i := 1) (j := 4) (by decide), shift5_poly5, shift5_poly5]
  rfl

omit [CharP K 2] in
theorem ord_cycleF5 : 8 ≤ ord (cycleF5 : MvPolynomial (Fin 5) K) := by
  exact_mod_cast le_ord_poly5 (n := 8) (by decide +kernel)

theorem residualOrderAlong_cycleF5 :
    residualOrderAlong {0, 2, 4} 8 (cycleF5 : MvPolynomial (Fin 5) K) = 5 :=
  residualOrderAlong_poly5' _ 5 (12, 0, 15, 0, 60) _ (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel) (by decide +kernel) (0, 0, 1, 0, 4) rfl (by decide +kernel)

omit [CharP K 2] in
theorem pointChart_cycleF5 :
    pointChart 2 0 (cycleF5 : MvPolynomial (Fin 5) K) = X 2 ^ 8 * cycleF6 :=
  pointChart_poly5 8 2 _ (by decide +kernel)

omit [CharP K 2] in
theorem ord_cycleF6 : 8 ≤ ord (cycleF6 : MvPolynomial (Fin 5) K) := by
  exact_mod_cast le_ord_poly5 (n := 8) (by decide +kernel)

/-- After step (6) the residual order is `d + 2 = 4`. -/
theorem residualOrderAlong_cycleF6 :
    residualOrderAlong {0, 2, 4} 8 (cycleF6 : MvPolynomial (Fin 5) K) = 4 :=
  residualOrderAlong_poly5' _ 4 (12, 0, 84, 0, 60) _ (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel) (by decide +kernel) (0, 0, 0, 0, 4) rfl (by decide +kernel)

/-! ### Step (7) -/

/-- The checks of step (7) for `k` charts: the factor `x^12 y^(152 k) u^84 w^60`, cleanness, the residual factor along `x y u w = 0`, the order `4` of the residual factor and the witness `w^4`. -/
def cycleCheck7 (k : ℕ) : Bool :=
  (cycleL7 k).all (le5 (12, 152 * k, 84, 0, 60)) &&
  (cycleL7 k).all (fun e => !allDvd5 8 e) &&
  ([0, 1, 2, 4] : List (Fin 5)).all (fun i =>
    ((cycleL7 k).map fun e => e - (12, 152 * k, 84, 0, 60)).any fun e =>
      ev5 e i == 0 && ((cycleL7 k).map fun e => e - (12, 152 * k, 84, 0, 60)).count e % 2 == 1) &&
  ((cycleL7 k).map fun e => e - (12, 152 * k, 84, 0, 60)).all (fun e => 4 ≤ deg5 e) &&
  ((cycleL7 k).map fun e => e - (12, 152 * k, 84, 0, 60)).count (0, 0, 0, 0, 4) % 2 == 1

theorem cycleL7_deg : (List.range 15).all
    (fun k => (cycleL7 k).all fun e => 8 ≤ deg5 e) = true := by
  decide +kernel

theorem cycleCheck7_range : (List.range' 1 14).all cycleCheck7 = true := by
  decide +kernel

theorem cycleL7_deg_of_le {k : ℕ} (hk : k ≤ 14) : (cycleL7 k).all (fun e => 8 ≤ deg5 e) = true :=
  List.all_eq_true.mp cycleL7_deg k (List.mem_range.mpr (by omega))

omit [CharP K 2] in
theorem cycleF7_zero : (cycleF7 0 : MvPolynomial (Fin 5) K) = cycleF6 := rfl

omit [CharP K 2] in
/-- Step (7): the `y`-chart sends `F_7(k)` to `y^8 F_7(k + 1)`. -/
theorem pointChart_cycleF7 (k : ℕ) (hk : k < 14) :
    pointChart 1 0 (cycleF7 k : MvPolynomial (Fin 5) K) = X 1 ^ 8 * cycleF7 (k + 1) :=
  pointChart_poly5 8 1 _ (cycleL7_deg_of_le (by omega))

omit [CharP K 2] in
theorem ord_cycleF7 (k : ℕ) (hk : k ≤ 14) : 8 ≤ ord (cycleF7 k : MvPolynomial (Fin 5) K) := by
  exact_mod_cast le_ord_poly5 (n := 8) (cycleL7_deg_of_le hk)

/-- During step (7) the residual order stays `d + 2 = 4`. -/
theorem residualOrderAlong_cycleF7 (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 14) :
    residualOrderAlong {0, 1, 2, 4} 8 (cycleF7 k : MvPolynomial (Fin 5) K) = 4 := by
  have h := List.all_eq_true.mp cycleCheck7_range k (List.mem_range'_1.mpr ⟨h1, by omega⟩)
  simp only [cycleCheck7, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hle, hclean⟩, hG⟩, hlow⟩, hc⟩ := h
  refine residualOrderAlong_poly5' _ 4 (12, 152 * k, 84, 0, 60) _ hle hclean ?_ ?_ hlow
    (0, 0, 0, 0, 4) rfl hc
  · intro i hi
    fin_cases i <;> simp_all [ev5]
  · intro i hi
    refine List.all_eq_true.mp hG i ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hi

/-! ### The divisors -/

section Divisor

variable [DecidableEq K]

omit [CharP K 2] in
theorem blowupDivisor_step1 :
    blowupDivisor {0, 1, 2, 4} 0 (cycleT1 : Fin 5 → K) = {0, 4} := by
  ext i
  rw [blowupDivisor, Finset.mem_insert, Finset.mem_filter]
  fin_cases i <;> simp [cycleT1]

omit [CharP K 2] in
theorem blowupDivisor_step2 : blowupDivisor {0, 4} 0 (0 : Fin 5 → K) = {0, 4} := by
  ext i
  rw [blowupDivisor, Finset.mem_insert, Finset.mem_filter]
  fin_cases i <;> simp

omit [CharP K 2] in
theorem blowupDivisor_step3 : blowupDivisor {0, 4} 2 (0 : Fin 5 → K) = {0, 2, 4} := by
  ext i
  rw [blowupDivisor, Finset.mem_insert, Finset.mem_filter]
  fin_cases i <;> simp

omit [CharP K 2] in
theorem blowupDivisor_step4 : blowupDivisor {0, 2, 4} 3 (0 : Fin 5 → K) = {0, 2, 3, 4} := by
  ext i
  rw [blowupDivisor, Finset.mem_insert, Finset.mem_filter]
  fin_cases i <;> simp

omit [CharP K 2] in
theorem blowupDivisor_step5 :
    blowupDivisor {0, 2, 3, 4} 4 (cycleT5 : Fin 5 → K) = {0, 2, 4} := by
  ext i
  rw [blowupDivisor, Finset.mem_insert, Finset.mem_filter]
  fin_cases i <;> simp [cycleT5]

omit [CharP K 2] in
theorem blowupDivisor_step6 : blowupDivisor {0, 2, 4} 2 (0 : Fin 5 → K) = {0, 2, 4} := by
  ext i
  rw [blowupDivisor, Finset.mem_insert, Finset.mem_filter]
  fin_cases i <;> simp

omit [CharP K 2] in
theorem blowupDivisor_step7_first :
    blowupDivisor {0, 2, 4} 1 (0 : Fin 5 → K) = {0, 1, 2, 4} := by
  ext i
  rw [blowupDivisor, Finset.mem_insert, Finset.mem_filter]
  fin_cases i <;> simp

omit [CharP K 2] in
theorem blowupDivisor_step7 : blowupDivisor {0, 1, 2, 4} 1 (0 : Fin 5 → K) = {0, 1, 2, 4} := by
  ext i
  rw [blowupDivisor, Finset.mem_insert, Finset.mem_filter]
  fin_cases i <;> simp

end Divisor

/-! ### The cleaning in step (1) -/

/-- Before the cleaning, the residual order after step (1) is also `d + 4 = 6`. -/
theorem residualOrderAlong_cycleF1' :
    residualOrderAlong {0, 4} 8 (cycleF1' : MvPolynomial (Fin 5) K) = 6 := by
  have hadd := residualOrderAlong_add_pow 2 ({0, 4} : Finset (Fin 5)) 3
    (cycleF1' : MvPolynomial (Fin 5) K) cycleH1
  change residualOrderAlong {0, 4} 8 (cycleF1' + cycleH1 ^ 8) =
    residualOrderAlong {0, 4} 8 cycleF1' at hadd
  rw [← hadd, cycleF1'_add_pow, residualOrderAlong_cycleF1]

/-- The coordinate change `z ↦ z + x w` takes `z^8 + F_1'` to `z^8 + F_1`. -/
theorem zShift_cycleF1' :
    zShift cycleH1 (purelyInseparable 8 (cycleF1' : MvPolynomial (Fin 5) K)) =
      purelyInseparable 8 cycleF1 := by
  have h := zShift_purelyInseparable 2 3 (cycleH1 : MvPolynomial (Fin 5) K) cycleF1'
  change zShift cycleH1 (purelyInseparable 8 cycleF1') =
    purelyInseparable 8 (cycleF1' + cycleH1 ^ 8) at h
  rw [h, cycleF1'_add_pow]

omit [CharP K 2] in
theorem isClean_cycleF1 : IsClean 8 (cycleF1 : MvPolynomial (Fin 5) K) :=
  isClean_poly5 (by decide +kernel)

/-- The polynomial `F_1'` is not clean: it has the monomial `x^8 w^8`. -/
theorem not_isClean_cycleF1' : ¬ IsClean 8 (cycleF1' : MvPolynomial (Fin 5) K) := by
  intro h
  refine h (toF5 (8, 0, 0, 0, 8)) (toF5_mem_support_poly5 (by decide +kernel)) fun i => ?_
  fin_cases i <;> simp [toF5_apply, ev5]

/-! ### The shape of the final equation -/

omit [CharP K 2] in
/-- The start has the shape of [HP19a, Section 4, (0)] with `d = 2`, `a = b = r = 0`, `s = 1`, `λ = 1`, `Q = 0` and `A = 1`. -/
theorem cycleF0_shape : (cycleF0 : MvPolynomial (Fin 5) K) =
    X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 0 * X 4 ^ 6 *
      (X 4 ^ 2 * (1 + X 2 ^ 10 * 0) + X 0 ^ 3 * X 2 ^ 10 * 1) := by
  rw [cycleF0]
  ring

/-- The exponents of `F_7` after the `14` charts of step (7), divided by `x^12 y^2128 u^84 w^60`. -/
def cycleG : List Exp5 := (cycleL7 14).map fun e => e - (12, 2128, 84, 0, 60)

/-- The exponents of `cycleG` with `w`-degree at least `4`, divided by `w^4`. -/
def cycleW : List Exp5 := (cycleG.filter fun e => decide (4 ≤ e.2.2.2.2)).map
  fun e => e - (0, 0, 0, 0, 4)

/-- The exponents of `cycleG` with `w`-degree less than `4`. -/
def cycleN : List Exp5 := cycleG.filter fun e => !decide (4 ≤ e.2.2.2.2)

omit [CharP K 2] in
theorem constantCoeff_poly5 (L : List Exp5) :
    constantCoeff (poly5 L : MvPolynomial (Fin 5) K) = (L.count (0, 0, 0, 0, 0) : K) := by
  rw [constantCoeff_eq, coeff_poly5]
  rfl

omit [CharP K 2] in
theorem poly5_eq_mul {r : Exp5} {L : List Exp5} (h : L.all (le5 r) = true) :
    (poly5 L : MvPolynomial (Fin 5) K) = monomial (toF5 r) 1 * poly5 (L.map fun e => e - r) := by
  rw [monomial_mul_poly5, map_sub_add h]

omit [CharP K 2] in
/-- **The final equation.** After the `2d + 10 = 14` charts of step (7), the right side is `x^12 y^2128 u^84 w^60 (w^4 (1 + y^14 Q) + x^5 y^14 A)` with `A(0) = 1`.
This is the shape of the start [HP19a, Section 4, (0)] with `y` and `u` exchanged and with `d + 2 = 4` in place of `d`.
The exponents are `12 = 8 + 4`, `2128 = 8 · 266`, `84 = 8 · 10 + 4` and `60 = 8 · 8 - 4`. -/
theorem cycleF7_shape : ∃ Q A : MvPolynomial (Fin 5) K, constantCoeff A = 1 ∧
    cycleF7 14 = X 0 ^ 12 * X 1 ^ 2128 * X 2 ^ 84 * X 4 ^ 60 *
      (X 4 ^ 4 * (1 + X 1 ^ 14 * Q) + X 0 ^ 5 * X 1 ^ 14 * A) := by
  refine ⟨poly5 ((cycleW.filter fun e => e != (0, 0, 0, 0, 0)).map fun e => e - (0, 14, 0, 0, 0)),
    poly5 (cycleN.map fun e => e - (5, 14, 0, 0, 0)), ?_, ?_⟩
  · rw [constantCoeff_poly5, show (cycleN.map fun e => e - (5, 14, 0, 0, 0)).count
      (0, 0, 0, 0, 0) = 1 by decide +kernel, Nat.cast_one]
  have hW : poly5 cycleW = (1 : MvPolynomial (Fin 5) K) +
      poly5 (cycleW.filter fun e => e != (0, 0, 0, 0, 0)) := by
    have h := poly5_filter_add (R := K) (fun e => e != (0, 0, 0, 0, 0)) cycleW
    rw [show cycleW.filter (fun e => !(e != (0, 0, 0, 0, 0))) = [(0, 0, 0, 0, 0)] by
      decide +kernel] at h
    rw [← h, poly5_cons, poly5_nil, add_zero, monomial_toF5]
    simp only [pow_zero, mul_one]
    ring
  have hG : poly5 cycleG = (X 4 ^ 4 * poly5 cycleW : MvPolynomial (Fin 5) K) +
      poly5 cycleN := by
    have h := poly5_filter_add (R := K) (fun e => decide (4 ≤ e.2.2.2.2)) cycleG
    rw [poly5_eq_mul (L := cycleG.filter fun e => decide (4 ≤ e.2.2.2.2)) (r := (0, 0, 0, 0, 4))
      (by decide +kernel), monomial_toF5] at h
    simp only [pow_zero, one_mul] at h
    rw [← h]
    rfl
  rw [cycleF7, poly5_eq_mul (L := cycleL7 14) (r := (12, 2128, 84, 0, 60)) (by decide +kernel),
    monomial_toF5]
  change _ * poly5 cycleG = _
  rw [hG, hW, poly5_eq_mul (L := cycleW.filter fun e => e != (0, 0, 0, 0, 0))
      (r := (0, 14, 0, 0, 0)) (by decide +kernel),
    poly5_eq_mul (L := cycleN) (r := (5, 14, 0, 0, 0)) (by decide +kernel), monomial_toF5,
    monomial_toF5]
  ring

/-! ### The cycle -/

/-- **One cycle of the first example of Hauser and Perlega** [HP19a, Section 4], with `d = 2`, `a = b = r = 0`, `s = 1`, `λ = 1`, `A = 1` and `Q = 0`, over a field of characteristic 2.

The variables `x, y, u, v, w` are `X 0, ..., X 4`.
The start is `f = z^8 + F` with `F = x^4 y^4 w^6 (w^2 + x^3 u^10)` and the divisor `x y u w = 0`.
The cycle has 20 point blowups in the 7 steps of the paper.
For each blowup the statement gives the chart equation `π(F) = x_j^8 F'`, the weak transform of `f`, the bound `8 ≤ ord F'`, the new divisor and the residual order along it.
The residual order is `d = 2` at the start, `d + 4 = 6` after step (1), `d + 3 = 5` after steps (2) to (5), and `d + 2 = 4` after step (6) and after each chart of step (7). -/
theorem hauserPerlegaCycle [DecidableEq K] :
    -- the start
    IsClean 8 (cycleF0 : MvPolynomial (Fin 5) K) ∧
    8 ≤ ord (cycleF0 : MvPolynomial (Fin 5) K) ∧
    residualOrderAlong {0, 1, 2, 4} 8 (cycleF0 : MvPolynomial (Fin 5) K) = 2 ∧
    -- step (1): `x`-chart, `y ↦ y + 1`, `u ↦ u + 1`, then cleaning
    pointChart 0 cycleT1 (cycleF0 : MvPolynomial (Fin 5) K) = X 0 ^ 8 * cycleF1' ∧
    pointChartZ 0 cycleT1 (purelyInseparable 8 (cycleF0 : MvPolynomial (Fin 5) K)) =
      X (some 0) ^ 8 * purelyInseparable 8 cycleF1' ∧
    zShift cycleH1 (purelyInseparable 8 (cycleF1' : MvPolynomial (Fin 5) K)) =
      purelyInseparable 8 cycleF1 ∧
    8 ≤ ord (cycleF1 : MvPolynomial (Fin 5) K) ∧
    blowupDivisor {0, 1, 2, 4} 0 (cycleT1 : Fin 5 → K) = {0, 4} ∧
    residualOrderAlong {0, 4} 8 (cycleF1 : MvPolynomial (Fin 5) K) = 6 ∧
    -- step (2): `x`-chart
    pointChart 0 0 (cycleF1 : MvPolynomial (Fin 5) K) = X 0 ^ 8 * cycleF2 ∧
    pointChartZ 0 0 (purelyInseparable 8 (cycleF1 : MvPolynomial (Fin 5) K)) =
      X (some 0) ^ 8 * purelyInseparable 8 cycleF2 ∧
    8 ≤ ord (cycleF2 : MvPolynomial (Fin 5) K) ∧
    blowupDivisor {0, 4} 0 (0 : Fin 5 → K) = {0, 4} ∧
    residualOrderAlong {0, 4} 8 (cycleF2 : MvPolynomial (Fin 5) K) = 5 ∧
    -- step (3): `u`-chart
    pointChart 2 0 (cycleF2 : MvPolynomial (Fin 5) K) = X 2 ^ 8 * cycleF3 ∧
    pointChartZ 2 0 (purelyInseparable 8 (cycleF2 : MvPolynomial (Fin 5) K)) =
      X (some 2) ^ 8 * purelyInseparable 8 cycleF3 ∧
    8 ≤ ord (cycleF3 : MvPolynomial (Fin 5) K) ∧
    blowupDivisor {0, 4} 2 (0 : Fin 5 → K) = {0, 2, 4} ∧
    residualOrderAlong {0, 2, 4} 8 (cycleF3 : MvPolynomial (Fin 5) K) = 5 ∧
    -- step (4): `v`-chart, `d / 2 = 1` times
    pointChart 3 0 (cycleF3 : MvPolynomial (Fin 5) K) = X 3 ^ 8 * cycleF4 ∧
    pointChartZ 3 0 (purelyInseparable 8 (cycleF3 : MvPolynomial (Fin 5) K)) =
      X (some 3) ^ 8 * purelyInseparable 8 cycleF4 ∧
    8 ≤ ord (cycleF4 : MvPolynomial (Fin 5) K) ∧
    blowupDivisor {0, 2, 4} 3 (0 : Fin 5 → K) = {0, 2, 3, 4} ∧
    residualOrderAlong {0, 2, 3, 4} 8 (cycleF4 : MvPolynomial (Fin 5) K) = 5 ∧
    -- step (5): `w`-chart, `y ↦ y + 1`, `v ↦ v + 1`
    pointChart 4 cycleT5 (cycleF4 : MvPolynomial (Fin 5) K) = X 4 ^ 8 * cycleF5 ∧
    pointChartZ 4 cycleT5 (purelyInseparable 8 (cycleF4 : MvPolynomial (Fin 5) K)) =
      X (some 4) ^ 8 * purelyInseparable 8 cycleF5 ∧
    8 ≤ ord (cycleF5 : MvPolynomial (Fin 5) K) ∧
    blowupDivisor {0, 2, 3, 4} 4 (cycleT5 : Fin 5 → K) = {0, 2, 4} ∧
    residualOrderAlong {0, 2, 4} 8 (cycleF5 : MvPolynomial (Fin 5) K) = 5 ∧
    -- step (6): `u`-chart
    pointChart 2 0 (cycleF5 : MvPolynomial (Fin 5) K) = X 2 ^ 8 * cycleF6 ∧
    pointChartZ 2 0 (purelyInseparable 8 (cycleF5 : MvPolynomial (Fin 5) K)) =
      X (some 2) ^ 8 * purelyInseparable 8 cycleF6 ∧
    8 ≤ ord (cycleF6 : MvPolynomial (Fin 5) K) ∧
    blowupDivisor {0, 2, 4} 2 (0 : Fin 5 → K) = {0, 2, 4} ∧
    residualOrderAlong {0, 2, 4} 8 (cycleF6 : MvPolynomial (Fin 5) K) = 4 ∧
    -- step (7): `y`-chart, `2d + 10 = 14` times, from `F_6 = F_7(0)` to `F_7(14)`
    (∀ k < 14, pointChart 1 0 (cycleF7 k : MvPolynomial (Fin 5) K) = X 1 ^ 8 * cycleF7 (k + 1) ∧
      pointChartZ 1 0 (purelyInseparable 8 (cycleF7 k : MvPolynomial (Fin 5) K)) =
        X (some 1) ^ 8 * purelyInseparable 8 (cycleF7 (k + 1)) ∧
      8 ≤ ord (cycleF7 (k + 1) : MvPolynomial (Fin 5) K) ∧
      residualOrderAlong {0, 1, 2, 4} 8 (cycleF7 (k + 1) : MvPolynomial (Fin 5) K) = 4) ∧
    blowupDivisor {0, 2, 4} 1 (0 : Fin 5 → K) = {0, 1, 2, 4} ∧
    blowupDivisor {0, 1, 2, 4} 1 (0 : Fin 5 → K) = {0, 1, 2, 4} ∧
    -- the final equation
    (∃ Q A : MvPolynomial (Fin 5) K, constantCoeff A = 1 ∧
      cycleF7 14 = X 0 ^ 12 * X 1 ^ 2128 * X 2 ^ 84 * X 4 ^ 60 *
        (X 4 ^ 4 * (1 + X 1 ^ 14 * Q) + X 0 ^ 5 * X 1 ^ 14 * A)) := by
  refine ⟨isClean_cycleF0, ord_cycleF0, residualOrderAlong_cycleF0,
    pointChart_cycleF0, pointChartZ_purelyInseparable pointChart_cycleF0, zShift_cycleF1',
    ord_cycleF1, blowupDivisor_step1, residualOrderAlong_cycleF1,
    pointChart_cycleF1, pointChartZ_purelyInseparable pointChart_cycleF1, ord_cycleF2,
    blowupDivisor_step2, residualOrderAlong_cycleF2,
    pointChart_cycleF2, pointChartZ_purelyInseparable pointChart_cycleF2, ord_cycleF3,
    blowupDivisor_step3, residualOrderAlong_cycleF3,
    pointChart_cycleF3, pointChartZ_purelyInseparable pointChart_cycleF3, ord_cycleF4,
    blowupDivisor_step4, residualOrderAlong_cycleF4,
    pointChart_cycleF4, pointChartZ_purelyInseparable pointChart_cycleF4, ord_cycleF5,
    blowupDivisor_step5, residualOrderAlong_cycleF5,
    pointChart_cycleF5, pointChartZ_purelyInseparable pointChart_cycleF5, ord_cycleF6,
    blowupDivisor_step6, residualOrderAlong_cycleF6,
    fun k hk => ⟨pointChart_cycleF7 k hk, pointChartZ_purelyInseparable (pointChart_cycleF7 k hk),
      ord_cycleF7 (k + 1) hk, residualOrderAlong_cycleF7 (k + 1) (by omega) hk⟩,
    blowupDivisor_step7_first, blowupDivisor_step7, cycleF7_shape⟩

end Singularity.Examples
