import MI17

/-!
# MI18 -- the mass square, its row partition, `MassComm`, and the genuine `Ginv` form (M1 lane E, 2026-10-13)

* `Ymass`, `inner_MassFull_eq` : `⟪A, Q* w Q A⟫ = ‖√w Q A‖²`;  `rowMul`, `rowBase` (`rowBase_mem`), `hrow`, `row_partition`
  (every constraint row has a base site in `Ω₀`);
* **`MassComm CM`** : the mass commutator bound (a definition; it is DISCHARGED on proper towers in MI32 `massComm_proper`
  under the M0-chain tower hypotheses);
* `siteMask_norm_le`, `Wop_eq` (`W B = B − Dm(G'(T B))`);
* `ginv_form` : `⟪A, Ginv A⟫ = ‖χ_P C(B − Dm λ)‖² + Δ'(B − Dm λ) + ‖T B‖² + ‖√w Q B‖²`, `B = ι A`, `λ = G'(T B)`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply deltaPrimeBilL2NormLoc inner_deltaKLocCLM)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

variable {L : PeriodicLatticeExtent}

/-! ## 1. the mass square and its row partition -/

/-- `√w Q` -/
noncomputable def Ymass (G : TowerGeom L) (U : Cfg L) (a : ℝ) : BondFnL2 L →L[ℝ] FSp G :=
  diagW G (fun p => Real.sqrt (massW G a p)) ∘L QfullOf G U

theorem inner_MassFull_eq (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a) (A : BondFnL2 L) :
    ⟪A, MassFull G a (bondSectorOf G U) A⟫ = ‖Ymass G U a A‖ ^ 2 := by
  rw [inner_MassFull, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  show _ = ‖Real.sqrt (massW G a p) • (QfullOf G U A) p‖ ^ 2
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by unfold massW; positivity)]
  rfl

/-- multiplication on constraint rows. -/
noncomputable def rowMul (G : TowerGeom L) (h : BIdx G → ℝ) : FSp G →L[ℝ] FSp G := diagW G h

/-- the base site of a constraint row: its endpoint in `Ω₀`. -/
noncomputable def rowBase (G : TowerGeom L) (p : BIdx G) : PeriodicLatticeSite L :=
  open Classical in
  if p.2.1.1 ∈ G.Om0 then p.2.1.1 else coarseShift p.2.1.1 (G.ell ^ (p.1 : ℕ)) p.2.1.2

theorem rowBase_mem {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} (hS : Admissible ell M R k S)
    (p : BIdx (geomOf ell k S)) : rowBase (geomOf ell k S) p ∈ S.Om 0 := by
  classical
  unfold rowBase
  split_ifs with h
  · exact h
  · have hb := p.2.2.1
    rcases hb with h1 | h1
    · exact absurd (AdalyFormal.M1.om_anti hS (Nat.zero_le _) h1.2.1) h
    · exact AdalyFormal.M1.om_anti hS (Nat.zero_le _) h1.2.1

/-- the row partition. -/
noncomputable def hrow {Lf : PeriodicLatticeExtent} (ell M k κ c : ℕ) (S : Tower Lf) (i : Fin (k + 1) × PeriodicLatticeSite Lf)
    (p : BIdx (geomOf ell k S)) : ℝ :=
  AdalyFormal.M1.hpart ell M k κ c S i (rowBase (geomOf ell k S) p)

theorem row_partition {Lf : PeriodicLatticeExtent} {ell M R k κ c : ℕ} {S : Tower Lf} (hS : Admissible ell M R k S)
    (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell) (y : FSp (geomOf ell k S)) :
    ∑ i, ‖rowMul (geomOf ell k S) (hrow ell M k κ c S i) y‖ ^ 2 = ‖y‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  show ∑ i, ‖hrow ell M k κ c S i p • y p‖ ^ 2 = _
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.sum_mul]
  unfold hrow
  rw [AdalyFormal.M1.sum_hpart_sq hc hκ hM hell (rowBase_mem hS p), one_mul]

/-- **the mass commutator** (W1 input stated here; proved on proper towers in MI32 `massComm_proper` from the row
locality / row norm of `QfullOf` (MI29), the partition oscillation over a footprint (MI30) and the footprint
multiplicity (MI32)). -/
def MassComm {Lf : PeriodicLatticeExtent} (ell M k κ c : ℕ) (S : Tower Lf) (U : Cfg Lf) (a CM : ℝ) : Prop :=
  ∀ A : BondFnL2 Lf, ∑ i, ‖rowMul (geomOf ell k S) (hrow ell M k κ c S i) (Ymass (geomOf ell k S) U a A)
      - Ymass (geomOf ell k S) U a (bondMul (hbond ell M k κ c S i) A)‖ ^ 2
    ≤ CM * ‖bondWt (-sigG (geomOf ell k S)) A‖ ^ 2

/-! ## 2. the `Ginv` form of the genuine object -/

theorem siteMask_norm_le (Sset : Set (PeriodicLatticeSite L)) (f : SiteL2 L) : ‖siteMask Sset f‖ ≤ ‖f‖ := by
  classical
  have hsq : ‖siteMask Sset f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [siteMask_apply]; split_ifs
    · exact le_rfl
    · rw [norm_zero, sq, mul_zero]; exact sq_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

section form
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
  (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

/-- `W B = B − Dm(G'(T B))` when `LP` is invertible. -/
theorem Wop_eq (hu : IsUnit (LP (geomOf ell k S) U a)) (B : BondFnL2 (scaleUp ell k Lu)) :
    Wop (geomOf ell k S) U a B = B - Dm (geomOf ell k S) U (Gp (geomOf ell k S) U a (Tfull (geomOf ell k S) U B)) := by
  have hspec := (Gp_spec (geomOf ell k S) U a hu (Tfull (geomOf ell k S) U B)).1
  simp only [Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  congr 1
  show gradL2 U (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U B)))
    = gradL2 U (siteMask (geomOf ell k S).Om0 (Gp (geomOf ell k S) U a (Tfull (geomOf ell k S) U B)))
  rw [hspec]; rfl

/-- **the genuine `Ginv` form**. -/
theorem ginv_form (ha : 0 ≤ a) (hu : IsUnit (LP (geomOf ell k S) U a))
    (A : ↥(bondSupp (gparams ell k Lu hell0 S U a Lam).G)) :
    ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Ginv A⟫
      = ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U ((A : BondFnL2 _) - Dm (geomOf ell k S) U
            (Gp (geomOf ell k S) U a (Tfull (geomOf ell k S) U A))))‖ ^ 2
        + deltaPrimeBilL2NormLoc U (plaqIn (S.Om 0))
            ((A : BondFnL2 _) - Dm (geomOf ell k S) U (Gp (geomOf ell k S) U a (Tfull (geomOf ell k S) U A)))
            ((A : BondFnL2 _) - Dm (geomOf ell k S) U (Gp (geomOf ell k S) U a (Tfull (geomOf ell k S) U A)))
        + ‖Tfull (geomOf ell k S) U A‖ ^ 2 + ‖Ymass (geomOf ell k S) U a A‖ ^ 2 := by
  rw [(gparams ell k Lu hell0 S U a Lam).data.inner_Ginv A]
  have h1 : ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Dpi A⟫
      = ⟪(A : BondFnL2 _), DpiFull (geomOf ell k S) U a A⟫ := by
    show ⟪A, pE _ (DpiFull (geomOf ell k S) U a (iE _ A))⟫ = _
    rw [pE_inner_right]; rfl
  have h3 : ⟪A, (gparams ell k Lu hell0 S U a Lam).data.Mass A⟫
      = ⟪(A : BondFnL2 _), MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) U) A⟫ := by
    show ⟪A, pE _ (MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) U) (iE _ A))⟫ = _
    rw [pE_inner_right]; rfl
  have h2 : (gparams ell k Lu hell0 S U a Lam).data.T A = Tfull (geomOf ell k S) U A := rfl
  rw [h1, h2, h3, inner_MassFull_eq _ U a ha]
  have hspec := (Gp_spec (geomOf ell k S) U a hu (Tfull (geomOf ell k S) U A)).1
  have hv : (A : BondFnL2 _) - gradL2 U (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U A)))
      = (A : BondFnL2 _) - Dm (geomOf ell k S) U (Gp (geomOf ell k S) U a (Tfull (geomOf ell k S) U A)) := by
    show _ = (A : BondFnL2 _) - gradL2 U (siteMask (geomOf ell k S).Om0 (Gp (geomOf ell k S) U a (Tfull (geomOf ell k S) U A)))
    rw [hspec]; rfl
  rw [inner_DpiFull, hv]
  rw [show Delta (geomOf ell k S) U = AdalyFormal.StatementLaneR6.deltaKLocCLM U (plaqIn (S.Om 0)) from rfl]
  rw [inner_deltaKLocCLM, real_inner_self_eq_norm_sq]

end form

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.inner_MassFull_eq
#print axioms AdalyFormal.M1IMS.rowBase_mem
#print axioms AdalyFormal.M1IMS.row_partition
#print axioms AdalyFormal.M1IMS.siteMask_norm_le
#print axioms AdalyFormal.M1IMS.Wop_eq
#print axioms AdalyFormal.M1IMS.ginv_form
#print axioms AdalyFormal.M1IMS.Ymass
#print axioms AdalyFormal.M1IMS.rowMul
#print axioms AdalyFormal.M1IMS.rowBase
#print axioms AdalyFormal.M1IMS.hrow
#print axioms AdalyFormal.M1IMS.MassComm
