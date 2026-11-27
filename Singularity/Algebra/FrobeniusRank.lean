/-
Volume 1, Corollary 6.1.6, rank part. For a perfect field K of characteristic p and
S = K[[x_σ]] with σ finite, the module F^e_* S is free over S of rank q^n, q = p^e.

S already acts on itself by multiplication, so F^e_* S is the type synonym
`FrobeniusPush σ K p e` with the action c • f = c^(p^e) * f.
-/
import Singularity.Algebra.FrobeniusFlat

namespace Singularity.Algebra

open MvPowerSeries

/-- `F^e_* S`: the underlying group of `S = K[[x_σ]]`; `S` acts through `F^e` below. -/
def FrobeniusPush (σ K : Type*) (_p _e : ℕ) : Type _ := MvPowerSeries σ K

variable (σ K : Type*) [Field K] (p : ℕ) [CharP K p]

attribute [local instance] charP_mvPowerSeries

variable [Fact p.Prime]


noncomputable instance (e : ℕ) : AddCommGroup (FrobeniusPush σ K p e) :=
  inferInstanceAs (AddCommGroup (MvPowerSeries σ K))

noncomputable instance (e : ℕ) : Module (MvPowerSeries σ K) (FrobeniusPush σ K p e) :=
  letI : Module (MvPowerSeries σ K) (FrobeniusPush σ K p e) :=
    inferInstanceAs (Module (MvPowerSeries σ K) (MvPowerSeries σ K))
  Module.compHom _ (iterateFrobenius (MvPowerSeries σ K) p e)

/-- The action on `F^e_* S` is `c • f = c ^ p ^ e * f`. -/
theorem frobeniusPush_smul_def (e : ℕ) (c : MvPowerSeries σ K) (f : FrobeniusPush σ K p e) :
    (show MvPowerSeries σ K from c • f) = c ^ p ^ e * (show MvPowerSeries σ K from f) :=
  rfl

/-- The ring isomorphism `S ≃+* S_e` given by `f ↦ f ^ p ^ e`. -/
noncomputable def frobeniusPowEquiv [PerfectRing K p] (e : ℕ) :
    MvPowerSeries σ K ≃+* powSubalgebra σ K (p ^ e) :=
  RingEquiv.ofBijective _ (bijective_frobeniusToPowSubalgebra σ K p e)

/-- Auxiliary: the plain action of `S_e` on the underlying group of `F^e_* S`.
Not an instance; it is used only to transport `boxBasis`. -/
@[instance_reducible]
noncomputable def frobeniusPushPowModule (e : ℕ) :
    Module (powSubalgebra σ K (p ^ e)) (FrobeniusPush σ K p e) :=
  inferInstanceAs (Module (powSubalgebra σ K (p ^ e)) (MvPowerSeries σ K))

variable [Fintype σ] [DecidableEq σ]

/-- The monomial basis of `F^e_* S` over `S`, from `boxBasis` along `S ≃+* S_e`. -/
noncomputable def frobeniusPushBasis [PerfectRing K p] (e : ℕ) :
    Module.Basis (σ → Fin (p ^ e)) (MvPowerSeries σ K) (FrobeniusPush σ K p e) :=
  letI := frobeniusPushPowModule σ K p e
  let b : Module.Basis (σ → Fin (p ^ e)) (powSubalgebra σ K (p ^ e))
      (FrobeniusPush σ K p e) := boxBasis σ K (pow_pos (Fact.out : p.Prime).pos e)
  b.mapCoeffs (frobeniusPowEquiv σ K p e).symm fun c x => by
    change ((frobeniusToPowSubalgebra σ K p e ((frobeniusPowEquiv σ K p e).symm c) :
        powSubalgebra σ K (p ^ e)) : MvPowerSeries σ K) * (show MvPowerSeries σ K from x) =
      (c : MvPowerSeries σ K) * (show MvPowerSeries σ K from x)
    exact congrArg (fun y : powSubalgebra σ K (p ^ e) =>
      (y : MvPowerSeries σ K) * (show MvPowerSeries σ K from x))
      ((frobeniusPowEquiv σ K p e).apply_symm_apply c)

theorem frobeniusPushBasis_apply [PerfectRing K p] (e : ℕ) (α : σ → Fin (p ^ e)) :
    frobeniusPushBasis σ K p e α =
      (show FrobeniusPush σ K p e from (monomial (boxExp α) 1 : MvPowerSeries σ K)) := by
  let := frobeniusPushPowModule σ K p e
  unfold frobeniusPushBasis
  exact (Module.Basis.mapCoeffs_apply _ _ _ α).trans (boxBasis_apply _ α)

/-- Corollary 6.1.6 (rank part): `F^e_* S` is free over `S` of rank `q ^ n`, `q = p ^ e`. -/
theorem free_and_finrank_frobeniusPush [PerfectRing K p] (e : ℕ) :
    Module.Free (MvPowerSeries σ K) (FrobeniusPush σ K p e) ∧
      Module.finrank (MvPowerSeries σ K) (FrobeniusPush σ K p e) =
        (p ^ e) ^ Fintype.card σ := by
  refine ⟨Module.Free.of_basis (frobeniusPushBasis σ K p e), ?_⟩
  rw [Module.finrank_eq_card_basis (frobeniusPushBasis σ K p e), Fintype.card_fun,
    Fintype.card_fin]

end Singularity.Algebra
