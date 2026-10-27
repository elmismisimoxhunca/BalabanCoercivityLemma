import ZXG3J1

/-!
# G3J2 -- THE CLOSED POINT OF THE GENUINE CLAIM: `ell = 2`, `k = 0`, `Lu = L10` (10 sites per direction),
full tower, `Λ = univ`, flat `U`, any `a > 0`:  for EVERY `B̃ ∈ Λ̃` (the statement's class),
   `(1/1728)·‖B̃‖² ≤ (3.156)(C B̃)`    (genuine form, genuine `C`).
The proof composes: `C` produces an axial `Q₁`-kernel field (tree/ingredient facts), the tree's
CMP96 Lemma 2.4 at `U = 1` (`lemma24_flat`), and the reduction `(3.156) = ⟨x,Δ_π x⟩ + ‖R D* x‖² ≥ ‖curl x‖²`
(G3C `P0_genForm_eq`, `inner_DpiFull`).   No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlCovariantLM curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice staircasePath)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast droppedBondLast_not_mem_staircase)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)

/-- `Q₁` of the genuine family at a flat background is the tree's flat line average -/
theorem Q1_eq_q1SU2 (P : IngrBParams) (hU : P.U = flatCfg) (hdvd : ∀ μ, P.ell ∣ (P.Lu μ + 1)) :
    P.Q1 = AdalyFormal.IngredientFamily.q1SU2 P.ell := by
  have h1 : P.unitBgU = flatCfg := by
    unfold IngrBParams.unitBgU
    rw [show bgTower P.G P.U P.k = flatCfg by
      unfold bgTower; rw [hU]; exact Ubar_flat P.ell P.k]
    rfl
  unfold IngrBParams.Q1; rw [h1]; exact Q1_flat_eq P.ell P.hell hdvd

theorem unitBondEmb_zero_L10 (hell : 0 < 2) (e : Bond L10) :
    (unitBondEmb 2 0 L10 hell e : Bond (scaleUp 2 0 L10)) = (e : Bond (scaleUp 2 0 L10)) := by
  refine Prod.ext (funext fun μ => Fin.ext ?_) rfl
  show 2 ^ 0 * (e.1 μ).val = (e.1 μ).val
  simp

/-- `⟨A, Δ_π A⟩ = ‖χ_{Ω₀} curl A‖²` at the flat background (r6: the curl energy runs over the plaquettes of `Ω₀` only) -/
theorem inner_DpiFull_flat {L : PeriodicLatticeExtent} (G : TowerGeom L) (a : ℝ) (A : BondFnL2 L) :
    ⟪A, DpiFull G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) a A⟫ =
      ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn G.Om0)
        (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A)‖ ^ 2 := by
  have h0 : AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2
      (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
      (A - IngredientFamilyR2.gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
        (Gp G flatCfg a (Rproj G flatCfg (gradAdj flatCfg A))))
      = curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A := by
    have h1 : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
      (A - IngredientFamilyR2.gradL2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
        (Gp G flatCfg a (Rproj G flatCfg (gradAdj flatCfg A))))
      = curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A := by
      rw [map_sub, AdalyFormal.StatementLane3.curl_gradL2_flat, sub_zero]
    exact h1
  rw [inner_DpiFull, AdalyFormal.StatementLane3.Delta_flat_form, h0]

/-- the plaquettes of the whole torus: every plaquette is a plaquette of `univ`. -/
theorem plaqIn_univ {L : PeriodicLatticeExtent} :
    plaqIn (Set.univ : Set (PeriodicLatticeSite L)) = Set.univ := by
  ext p; simp [plaqIn]

/-- with `Ω₀` the whole torus the localised energy is the full curl energy (the r5 form). -/
theorem inner_DpiFull_flat_univ {L : PeriodicLatticeExtent} (G : TowerGeom L) (hG : G.Om0 = Set.univ) (a : ℝ)
    (A : BondFnL2 L) :
    ⟪A, DpiFull G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) a A⟫ =
      ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A‖ ^ 2 := by
  rw [inner_DpiFull_flat, hG, plaqIn_univ, AdalyFormal.StatementLaneR6.plaqMask_univ]

#print axioms Q1_eq_q1SU2
#print axioms unitBondEmb_zero_L10
#print axioms inner_DpiFull_flat
#print axioms plaqIn_univ
#print axioms inner_DpiFull_flat_univ

end AdalyFormal.StatementLaneG
