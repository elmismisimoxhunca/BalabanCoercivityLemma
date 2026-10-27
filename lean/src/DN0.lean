import DH1

/-!
# DN0 -- numeric twins of the Combes–Thomas constants (M1 D-layer lane, 2026-10-14)

Every constant of the D2 chain at a `CTData` (`EX`, `cG`, `dTc`, `kZc`, `kWc`, the split constant `κ`, the Schur
constants `EN`, `CHw`) is a function of the REAL numbers `ℓ, a, cs, Θ, Δ, γ, θχ, θ', ρ, cw, S*, bN` only.  This module
names those functions (`…N`, `…F`) and proves, by `rfl`, that the structure-valued constants ARE these functions.
Consequence: a numeric condition on the twins does not mention `k`, `S`, `Lu`, `U`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.TowerLoc (RegData)

/-! ## 1. the twins -/

noncomputable def qN (a : ℝ) : ℝ := Real.sqrt (max a 1)
noncomputable def dDN (Θ : ℝ) : ℝ := Real.sqrt 3 * (Real.exp Θ - 1)
noncomputable def dQN (a Δ : ℝ) : ℝ := Real.sqrt a * (Real.exp Δ - 1)
noncomputable def nXN (a cs Δ : ℝ) : ℝ := (4 / cs) * (qN a + dQN a Δ)
noncomputable def K3N (a cs Θ Δ : ℝ) : ℝ := (Real.sqrt (12 / cs) + dDN Θ * (4 / cs)) * (qN a + dQN a Δ)
noncomputable def EXN (a cs Θ Δ : ℝ) : ℝ :=
  (4 / cs) * dQN a Δ + (4 / cs) * dDN Θ * (qN a / Real.sqrt cs)
    + (Real.sqrt (48 / cs) * dDN Θ + (8 / cs) * dDN Θ ^ 2 + (4 / cs) * 1 * (2 * qN a * dQN a Δ + dQN a Δ ^ 2))
      * (qN a / cs)
noncomputable def EDXN (a cs Θ Δ : ℝ) : ℝ :=
  Real.sqrt (12 / cs) * dQN a Δ + Real.sqrt (12 / cs) * dDN Θ * (qN a / Real.sqrt cs)
    + (Real.sqrt 24 * dDN Θ + 2 * Real.sqrt (12 / cs) * dDN Θ ^ 2
      + Real.sqrt (12 / cs) * 1 * (2 * qN a * dQN a Δ + dQN a Δ ^ 2)) * (qN a / cs)
noncomputable def EDX'N (a cs Θ Δ : ℝ) : ℝ := dDN Θ * nXN a cs Δ + EDXN a cs Θ Δ
noncomputable def epsGN (ell : ℕ) (a cs Θ Δ : ℝ) : ℝ := 2 * (ell : ℝ) * EXN a cs Θ Δ
noncomputable def cGN (ell : ℕ) (a cs Θ Δ γ : ℝ) : ℝ :=
  1 / γ ^ 2 - 2 * epsGN ell a cs Θ Δ / γ - epsGN ell a cs Θ Δ ^ 2
noncomputable def dGN (ell : ℕ) (a cs Θ Δ : ℝ) : ℝ :=
  2 * ((ell : ℝ) * nXN a cs Δ) * epsGN ell a cs Θ Δ + epsGN ell a cs Θ Δ ^ 2
noncomputable def dTcN (ell : ℕ) (a cs Θ Δ γ θξ : ℝ) : ℝ :=
  Real.sqrt 3 * (ell : ℝ) * (Real.exp θξ - 1)
    + 2 * (ell : ℝ) * EXN a cs Θ Δ * ((ell : ℝ) * K3N a cs Θ Δ / cGN ell a cs Θ Δ γ)
    + (ell : ℝ) * nXN a cs Δ * (dGN ell a cs Θ Δ * γ ^ 2 * ((ell : ℝ) * K3N a cs Θ Δ) / cGN ell a cs Θ Δ γ
      + γ ^ 2 * (2 * (ell : ℝ) * EDX'N a cs Θ Δ))
noncomputable def kZcN (ell : ℕ) (a cs Θ Δ γ : ℝ) : ℝ :=
  (ell : ℝ) * Real.sqrt (48 / cs)
    + (4 / cs) * ((ell : ℝ) * ((ell : ℝ) * nXN a cs Δ * ((ell : ℝ) * K3N a cs Θ Δ / cGN ell a cs Θ Δ γ)))
noncomputable def kWcN (ell : ℕ) (a cs Θ Δ γ : ℝ) : ℝ :=
  1 + (ell : ℝ) * (Real.sqrt 24 + dDN Θ * Real.sqrt (48 / cs))
    + (Real.sqrt (12 / cs) + dDN Θ * (4 / cs))
      * ((ell : ℝ) * ((ell : ℝ) * nXN a cs Δ * ((ell : ℝ) * K3N a cs Θ Δ / cGN ell a cs Θ Δ γ)))

/-- the split constant of `GSplit` as a function of its six numbers -/
noncomputable def kapF (d1 d2 d3 cΔ cΔ' cw : ℝ) : ℝ :=
  (2 * d1 * Real.sqrt (1 + cΔ) * (1 / Real.sqrt cw) + d1 ^ 2 * (1 / Real.sqrt cw) ^ 2)
    + (2 * d2 * Real.sqrt (1 + cΔ) * (1 / Real.sqrt cw) + d2 ^ 2 * (1 / Real.sqrt cw) ^ 2)
    + (2 * d3 * Real.sqrt (1 + cΔ) * (1 / Real.sqrt cw) + d3 ^ 2 * (1 / Real.sqrt cw) ^ 2) + (cΔ + cΔ')

/-- the D2 split constant -/
noncomputable def kapN (ell : ℕ) (a cs Θ Δ γ θχ θ' ρ cw Sstar : ℝ) : ℝ :=
  kapF (d1c ell θ') (dTcN ell a cs Θ Δ γ θχ) (d3c ell a Sstar θ')
    (cDc ell ρ cw (kZcN ell a cs Θ Δ γ) (kWcN ell a cs Θ Δ γ))
    (cDc' ell ρ cw (kZcN ell a cs Θ Δ γ) (kWcN ell a cs Θ Δ γ) θ' (d1c ell θ')) cw

/-- the Schur constants as functions of `κ, CQ, dB, cw, bN` -/
noncomputable def CyF (κ CQ dB cw : ℝ) : ℝ := (CQ + dB / Real.sqrt cw) / (1 - κ)
noncomputable def ENF (κ CQ dB cw : ℝ) : ℝ :=
  dB * (CyF κ CQ dB cw / Real.sqrt cw) + dB * (CQ / Real.sqrt cw) + κ * (CQ * CyF κ CQ dB cw)
noncomputable def CHwF (κ CQ dB cw bN : ℝ) : ℝ := CyF κ CQ dB cw / Real.sqrt cw * (1 / (1 / bN - ENF κ CQ dB cw))

/-- the D2 `CQ` (`= ss`) -/
noncomputable def CQN (ell : ℕ) (a cs Θ Δ γ ρ cw : ℝ) : ℝ :=
  Real.sqrt (1 + cDc ell ρ cw (kZcN ell a cs Θ Δ γ) (kWcN ell a cs Θ Δ γ))

/-! ## 2. the `rfl` bridges -/

namespace CTData

section basic
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {W : ℕ} (D : CTData ell M R k S W)

theorem EX_eqN : D.EX = EXN D.a D.cs D.Θ D.Δ := rfl
theorem epsG_eqN : D.epsG = epsGN ell D.a D.cs D.Θ D.Δ := rfl
theorem cG_eqN : D.cG = cGN ell D.a D.cs D.Θ D.Δ D.γ := rfl
theorem dTc_eqN (θξ : ℝ) : D.dTc θξ = dTcN ell D.a D.cs D.Θ D.Δ D.γ θξ := rfl
theorem kZc_eqN : D.kZc = kZcN ell D.a D.cs D.Θ D.Δ D.γ := rfl
theorem kWc_eqN : D.kWc = kWcN ell D.a D.cs D.Θ D.Δ D.γ := rfl

end basic

variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (D : CTData ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
  (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k D.U ρ)
  (hεγ : D.epsG * D.γ ≤ 1) (hcG : 0 < D.cG)
  (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv A⟫)
  (θ' : ℝ) (hθ' : 0 ≤ θ')
  (hL : ∀ (x : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3),
    |D.χ (periodicLatticeShift x μ) - D.χ x| ≤ θ' / (ell : ℝ) ^ AdalyFormal.M1.strat S k x)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : RegData ell k Lu S D.U Sstar)
  (bN : ℝ) (hbN : 0 < bN)
  (hext : ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
    (gparams ell k Lu hell0 S D.U D.a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu hell0 S D.U D.a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) D.a p)) v‖ ^ 2)
  (hQs : Function.Injective (gparams ell k Lu hell0 S D.U D.a Lam).data.Qs)

/-- **`κ` is its numeric twin** -/
theorem kap_eqN :
    (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap
      = kapN ell D.a D.cs D.Θ D.Δ D.γ D.θχ θ' ρ cw Sstar := rfl

/-- `CQ = ss` is its numeric twin -/
theorem ss_eqN :
    (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).ss
      = CQN ell D.a D.cs D.Θ D.Δ D.γ ρ cw := rfl

/-- **`EN` is its numeric twin** -/
theorem EN_eqN (hκ1 : (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap < 1) :
    (D.wschur hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).EN
      = ENF (kapN ell D.a D.cs D.Θ D.Δ D.γ D.θχ θ' ρ cw Sstar) (CQN ell D.a D.cs D.Θ D.Δ D.γ ρ cw)
          (d3c ell D.a Sstar θ') cw := rfl

/-- `bN` of the Schur instance -/
theorem bN_eqN (hκ1 : (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap < 1) :
    (D.wschur hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).bN = bN := rfl

/-- **`CHw` is its numeric twin** -/
theorem CHw_eqN (hκ1 : (D.gsplit hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr).kap < 1) :
    (D.wschur hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs hκ1).CHw
      = CHwF (kapN ell D.a D.cs D.Θ D.Δ D.γ D.θχ θ' ρ cw Sstar) (CQN ell D.a D.cs D.Θ D.Δ D.γ ρ cw)
          (d3c ell D.a Sstar θ') cw bN := rfl

end CTData

#print axioms qN
#print axioms EXN
#print axioms dTcN
#print axioms kapF
#print axioms kapN
#print axioms ENF
#print axioms CHwF
#print axioms CQN
#print axioms CTData.EX_eqN
#print axioms CTData.epsG_eqN
#print axioms CTData.cG_eqN
#print axioms CTData.dTc_eqN
#print axioms CTData.kZc_eqN
#print axioms CTData.kWc_eqN
#print axioms CTData.kap_eqN
#print axioms CTData.ss_eqN
#print axioms CTData.EN_eqN
#print axioms CTData.bN_eqN
#print axioms CTData.CHw_eqN

end AdalyFormal.M1DStrat
