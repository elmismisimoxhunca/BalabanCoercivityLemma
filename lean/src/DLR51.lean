import DLR50

/-!
# DL51 -- the statement carrier `E₀ = ↥(bondSupp G)` on the full tower is ALL fine bonds: `data.G`, `data.H` in fine-bond form

* `iE_pE_full`, `pE_iE_full` : `ι P = 1`, `P ι = 1` (every fine bond lies in `E₀` on the full tower).
* `ring_inverse_eq_of` : a two-sided inverse is `Ring.inverse`.
* `dataGinv_eq` : `data.Ginv = P ∘ GinvFull ∘ ι`;  `dataG_eq` : `data.G = P ∘ GinvFull⁻¹ ∘ ι` (at M0, `GinvFull` a unit);
* **`dataH_eq`** : `ι (data.H w) = GinvFull⁻¹ Q_U* (Q_U GinvFull⁻¹ Q_U*)⁻¹ w` — the genuine `H` of (3.126) in fine-bond form.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU PlaqFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 Mc KhatM0 phiC ThetaM0)
open AdalyFormal.M0Finish (PU)

theorem ring_inverse_eq_of {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M X : E →L[ℝ] E}
    (h1 : M * X = 1) (h2 : X * M = 1) : Ring.inverse M = X := by
  have hu : IsUnit M := ⟨⟨M, X, h1, h2⟩, rfl⟩
  calc Ring.inverse M = Ring.inverse M * (M * X) := by rw [h1, mul_one]
    _ = (Ring.inverse M * M) * X := by rw [mul_assoc]
    _ = X := by rw [Ring.inverse_mul_cancel _ hu, one_mul]

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

theorem iE_pE_full (x : BondFnL2 (scaleUp ell k Lu)) : iE (GF ell k Lu) (pE (GF ell k Lu) x) = x := by
  refine ext_inner_right ℝ (fun y => ?_)
  set y' : ↥(bondSupp (GF ell k Lu)) := ⟨y, mem_bondSupp_full ell k Lu y⟩
  have hy : iE (GF ell k Lu) y' = y := rfl
  rw [← hy]
  have h1 : ⟪iE (GF ell k Lu) (pE (GF ell k Lu) x), iE (GF ell k Lu) y'⟫ = ⟪pE (GF ell k Lu) x, y'⟫ := rfl
  rw [h1, pE_inner_left]

theorem pE_iE_full (z : ↥(bondSupp (GF ell k Lu))) : pE (GF ell k Lu) (iE (GF ell k Lu) z) = z := by
  refine ext_inner_right ℝ (fun w => ?_)
  rw [pE_inner_left]
  rfl

theorem iE_pE_op : iE (GF ell k Lu) ∘L pE (GF ell k Lu) = ContinuousLinearMap.id ℝ _ := by
  ext1 x; exact iE_pE_full ell k Lu x

variable (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

theorem dataGinv_eq :
    (PU ell k Lu hell U a Lam).data.Ginv = pE (GF ell k Lu) ∘L GinvFull ell k Lu U a ∘L iE (GF ell k Lu) := by
  ext1 z
  show pE (GF ell k Lu) (DpiFull (GF ell k Lu) U a (iE (GF ell k Lu) z))
      + ContinuousLinearMap.adjoint ((Tfull (GF ell k Lu) U).comp (iE (GF ell k Lu)))
          ((Tfull (GF ell k Lu) U).comp (iE (GF ell k Lu)) z)
      + pE (GF ell k Lu) (MassFull (GF ell k Lu) a (bondSectorOf (GF ell k Lu) U) (iE (GF ell k Lu) z))
      = pE (GF ell k Lu) (GinvFull ell k Lu U a (iE (GF ell k Lu) z))
  rw [ContinuousLinearMap.adjoint_comp]
  simp only [GinvFull, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, map_add]
  rfl

theorem dataQs_eq : (PU ell k Lu hell U a Lam).data.Qs
    = pE (GF ell k Lu) ∘L ContinuousLinearMap.adjoint (bondSectorOf (GF ell k Lu) U).Qfull := by
  show ContinuousLinearMap.adjoint ((bondSectorOf (GF ell k Lu) U).Qfull.comp (iE (GF ell k Lu))) = _
  rw [ContinuousLinearMap.adjoint_comp]
  rfl

theorem dataQ_eq : (PU ell k Lu hell U a Lam).data.Q = (bondSectorOf (GF ell k Lu) U).Qfull ∘L iE (GF ell k Lu) := rfl

/-- `data.G` in fine-bond form, given that `GinvFull` is a unit -/
theorem dataG_eq (hu : IsUnit (GinvFull ell k Lu U a)) :
    (PU ell k Lu hell U a Lam).data.G
      = pE (GF ell k Lu) ∘L Ring.inverse (GinvFull ell k Lu U a) ∘L iE (GF ell k Lu) := by
  unfold BaseDataS.G
  rw [dataGinv_eq]
  apply ring_inverse_eq_of
  · ext1 z
    show pE (GF ell k Lu) (GinvFull ell k Lu U a (iE (GF ell k Lu) (pE (GF ell k Lu)
        (Ring.inverse (GinvFull ell k Lu U a) (iE (GF ell k Lu) z))))) = z
    rw [iE_pE_full, ← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu, ContinuousLinearMap.one_apply,
      pE_iE_full]
  · ext1 z
    show pE (GF ell k Lu) (Ring.inverse (GinvFull ell k Lu U a) (iE (GF ell k Lu) (pE (GF ell k Lu)
        (GinvFull ell k Lu U a (iE (GF ell k Lu) z))))) = z
    rw [iE_pE_full, ← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hu, ContinuousLinearMap.one_apply,
      pE_iE_full]

/-- the fine-bond Schur complement `N_f = Q_U GinvFull⁻¹ Q_U*` -/
noncomputable def Nf : FSp (GF ell k Lu) →L[ℝ] FSp (GF ell k Lu) :=
  (bondSectorOf (GF ell k Lu) U).Qfull ∘L Ring.inverse (GinvFull ell k Lu U a)
    ∘L ContinuousLinearMap.adjoint (bondSectorOf (GF ell k Lu) U).Qfull

theorem dataN_eq (hu : IsUnit (GinvFull ell k Lu U a)) :
    ((PU ell k Lu hell U a Lam).data.Q.comp (PU ell k Lu hell U a Lam).data.G).comp (PU ell k Lu hell U a Lam).data.Qs
      = Nf ell k Lu U a := by
  rw [dataG_eq ell k Lu hell U a Lam hu, dataQs_eq, dataQ_eq]
  ext1 w
  simp only [Nf, ContinuousLinearMap.comp_apply]
  rw [iE_pE_full, iE_pE_full]

/-- **the genuine `H` in fine-bond form** -/
theorem dataH_eq (hu : IsUnit (GinvFull ell k Lu U a)) (w : FSp (GF ell k Lu)) :
    iE (GF ell k Lu) ((PU ell k Lu hell U a Lam).data.H w)
      = Ring.inverse (GinvFull ell k Lu U a)
          (ContinuousLinearMap.adjoint (bondSectorOf (GF ell k Lu) U).Qfull (Ring.inverse (Nf ell k Lu U a) w)) := by
  unfold BaseDataS.H
  rw [dataN_eq ell k Lu hell U a Lam hu, dataG_eq ell k Lu hell U a Lam hu, dataQs_eq]
  simp only [ContinuousLinearMap.comp_apply]
  rw [iE_pE_full, iE_pE_full]

end

#print axioms ring_inverse_eq_of
#print axioms iE_pE_full
#print axioms pE_iE_full
#print axioms dataGinv_eq
#print axioms dataQs_eq
#print axioms dataG_eq
#print axioms dataN_eq
#print axioms dataH_eq

end AdalyFormal.DLayer
