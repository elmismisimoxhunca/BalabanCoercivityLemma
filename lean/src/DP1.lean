import DH1
import DW2
import DS3
import DQ6

/-!
# DP1 -- the FIRST clause of `DLayerStrat` (the stratified `Δ⁽²⁾` form bound `hD2`, the input of W5 `wellDef_strat`) at
one configuration, from the hatted chain, W4, the energy right inverse and explicit smallness (M1 D-layer lane, 2026-10-14)

* `CTBase` : the χ-free part of `CTData` (hatted chain, `Gi`, `γ`, the CT rate `θ`, the common pair `(Θ, Δ)`);
  `CTBase.toCT B c` : the `CTData` at the D2 weight `χ = phiC θ c` (DW1/DW2; `θχ = 3θℓ²`, `δχ = 6θ`).
* **`dlayer_clause1`** : `|⟪A, Δ⁽²⁾A⟫| ≤ 2 (CΨ SJ) K2 CW · wnormSq A` for every `A ∈ E₀`, with
  `CΨ = √(3ℓ⁷ a Cg) · CH` (`Cg = ℓ⁴(64 + 8ℓ³/θ³)`, `CH` any common bound of DC2's `CHw`), `SJ = 400ℓ³·12Mα₀` (DS3),
  `K2 = K2strat ℓ (12Mα₀)` (DQ5), `CW = ℓ² CWc²` (DC1).
Inputs NOT discharged here (named hypotheses): W4 (`hW4`, constant `cw`), the energy right inverse of the bond `Q`
(`hext`, constant `bN`), `Q*` injective (`hQs`), the numeric smallness `κ < 1`, `EN < 1/bN`, `εγ ≤ 1`, `cΓ > 0`.
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
open AdalyFormal.TowerLoc (RegData Estar)
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.M1 (M1Regular strat bstrat wnormSq)
open AdalyFormal.M1DStrat.DQ

/-- the χ-free part of the CT data -/
structure CTBase {Lf : PeriodicLatticeExtent} (ell M R k : ℕ) (S : Tower Lf) (W : ℕ) where
  hS : Admissible ell M R k S
  hW : 1 ≤ W
  hell : 2 ≤ ell
  hR : 1 ≤ R
  hM : 1 ≤ M
  hWR : W ≤ R * M * ell
  U : Cfg Lf
  a : ℝ
  cs : ℝ
  hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs
  θ : ℝ
  hθ : 0 < θ
  Θ : ℝ
  Δ : ℝ
  hΘ : 3 * θ * (ell : ℝ) ^ 2 + 2 * (ell : ℝ) ^ 2 * Real.log ell / W ≤ Θ
  hΔ : 6 * θ + 3 * (ell : ℝ) * Real.log ell / W ≤ Δ
  hsm : 24 * ((Real.sqrt 3 * (Real.exp Θ - 1)) ^ 2 + 1 * (Real.sqrt a * (Real.exp Δ - 1)) ^ 2) ≤ cs
  hsmD : 4 * (Real.sqrt 3 * (Real.exp Θ - 1)) ^ 2 ≤ cs
  Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S)
  hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) (Gi u) = u
  hG2 : ∀ u, Gi ((ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) u) = u
  γ : ℝ
  hγ0 : 0 < γ
  hγ : ∀ u, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ γ * ‖Xop (geomOf ell k S) U a u‖

namespace CTBase
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {W : ℕ} (B : CTBase ell M R k S W)

/-- the `CTData` at the D2 weight centred at `c` -/
noncomputable def toCT (c : PeriodicLatticeSite Lf) : CTData ell M R k S W where
  hS := B.hS
  hW := B.hW
  hell := B.hell
  hR := B.hR
  hM := B.hM
  hWR := B.hWR
  U := B.U
  a := B.a
  cs := B.cs
  hp := B.hp
  χ := phiC S ell M R k B.θ c
  θχ := 3 * B.θ * (ell : ℝ) ^ 2
  δχ := 6 * B.θ
  hθχ := by have := B.hθ; positivity
  hδχ := by have := B.hθ; positivity
  hχ := phiC_WtOK B.hS B.hR B.hM B.hell B.hθ.le c
  Θ := B.Θ
  Δ := B.Δ
  hΘ := B.hΘ
  hΔ := B.hΔ
  hsm := B.hsm
  hsmD := B.hsmD
  Gi := B.Gi
  hG1 := B.hG1
  hG2 := B.hG2
  γ := B.γ
  hγ0 := B.hγ0
  hγ := B.hγ

theorem toCT_U (c : PeriodicLatticeSite Lf) : (B.toCT c).U = B.U := rfl
theorem toCT_a (c : PeriodicLatticeSite Lf) : (B.toCT c).a = B.a := rfl
theorem toCT_χ (c : PeriodicLatticeSite Lf) : (B.toCT c).χ = phiC S ell M R k B.θ c := rfl

end CTBase

/-- the constant `Cg` of the column sum -/
noncomputable def Cgeo (ell : ℕ) (θ : ℝ) : ℝ := (ell : ℝ) ^ 4 * (64 + 8 * (ell : ℝ) ^ 3 / θ ^ 3)

section clause
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (B : CTBase ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
  (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k B.U ρ)
  (hεγ : ∀ c, (B.toCT c).epsG * B.γ ≤ 1) (hcG : ∀ c, 0 < (B.toCT c).cG)
  (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S B.U B.a Lam).data.Ginv A⟫)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : RegData ell k Lu S B.U Sstar)
  (bN : ℝ) (hbN : 0 < bN)
  (hext : ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
    (gparams ell k Lu hell0 S B.U B.a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu hell0 S B.U B.a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) B.a p)) v‖ ^ 2)
  (hQs : Function.Injective (gparams ell k Lu hell0 S B.U B.a Lam).data.Qs)

theorem θ'_nonneg : 0 ≤ 3 * B.θ * ell := by have := B.hθ; positivity

/-- the split constant `κ` at the column centre `c` -/
noncomputable def kapB (c : PeriodicLatticeSite (scaleUp ell k Lu)) : ℝ :=
  ((B.toCT c).gsplit hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
    (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr).kap

/-- the Schur instance at the column centre `c` -/
noncomputable def wsB (hκ1 : ∀ c, kapB B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr c < 1)
    (c : PeriodicLatticeSite (scaleUp ell k Lu)) :
    WSchur ↥(bondSupp (geomOf ell k S)) (FSp (geomOf ell k S)) :=
  (B.toCT c).wschur hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
    (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs (hκ1 c)

include hR8 in
/-- the weighted columns of `H`, uniform in the row -/
theorem hcol_B (hκ1 : ∀ c, kapB B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr c < 1)
    (hcN : ∀ c, 0 < 1 / (wsB B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr bN hbN hext hQs hκ1 c).bN
      - (wsB B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr bN hbN hext hQs hκ1 c).EN)
    (CH : ℝ) (hCH : ∀ c, (wsB B hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 hR8 Sstar Dr bN hbN hext hQs hκ1 c).CHw ≤ CH)
    (hq : (ell : ℝ) ^ 3 * Real.exp (-(B.θ * (R * M))) ≤ 1 / 2)
    (p : BIdx (geomOf ell k S)) (v : SuTwo) :
    ∑ b, omJ S ell k b * ‖(iE (geomOf ell k S) ((gparams ell k Lu hell0 S B.U B.a Lam).data.H
        (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S)))) b‖
      ≤ (Real.sqrt (3 * (ell : ℝ) ^ 7 * B.a * Cgeo ell B.θ) * CH) * ‖v‖ := by
  have hell1 : 1 ≤ ell := by omega
  have hCg0 : 0 ≤ Cgeo ell B.θ := by unfold Cgeo; have := B.hθ; positivity
  have hc0 : (B.toCT (rowBase (geomOf ell k S) p)).χ (rowBase (geomOf ell k S) p) = 0 :=
    phiC_self B.hS B.θ (rowBase (geomOf ell k S) p)
  have hCg := phiC_colsum B.hS B.hR B.hM hell1 B.hθ hq (rowBase (geomOf ell k S) p)
  have hlev := rowBase_strat B.hS B.hR B.hM B.hell
    (le_trans (by omega : ell ≤ R) (Nat.le_mul_of_pos_right R (by have := B.hM; omega))) p
  have h := (B.toCT (rowBase (geomOf ell k S) p)).H_col hell0 Lam ρ hρ hreg (hεγ _) (hcG _) cw hcw hW4
    (3 * B.θ * ell) (θ'_nonneg B) (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le _) hR8 Sstar Dr bN hbN hext hQs (hκ1 _)
    (hcN _) p v hc0 (Cgeo ell B.θ) hCg0 (by unfold Cgeo; exact hCg) hlev
  refine h.trans ?_
  have h2 := hCH (rowBase (geomOf ell k S) p)
  have hs0 : 0 ≤ Real.sqrt (3 * (ell : ℝ) ^ 7 * B.a * Cgeo ell B.θ) := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hs0) (norm_nonneg _)

end clause

/-- **the first clause of `DLayerStrat` at one configuration**, from the weighted columns -/
theorem dlayer_clause1 {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
    (B : CTBase ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu)) (CΨ : ℝ) (hCΨ0 : 0 ≤ CΨ)
    (hcol : ∀ (p : BIdx (geomOf ell k S)) (v : SuTwo),
      ∑ b, omJ S ell k b * ‖(iE (geomOf ell k S) ((gparams ell k Lu hell0 S B.U B.a Lam).data.H
        (WithLp.toLp 2 (Pi.single p v) : FSp (geomOf ell k S)))) b‖ ≤ CΨ * ‖v‖)
    (α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hU : M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ B.U)
    (hRM4 : 4 ≤ R * M) (hsmJ : 4 * ((12 : ℝ) * M * α₀) ≤ 1) (hroom : 18 * ell ≤ R * M)
    (hLu : ∀ μ, ell < Lu μ + 1) (hDQ : DQSmall ell (12 * M * α₀))
    (A : ↥(bondSupp (gparams ell k Lu hell0 S B.U B.a Lam).G)) :
    |⟪A, (gparams ell k Lu hell0 S B.U B.a Lam).data.Delta2 (gparams ell k Lu hell0 S B.U B.a Lam).data_laws A⟫|
      ≤ 2 * (CΨ * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2strat ell (12 * M * α₀)
          * ((ell : ℝ) ^ 2 * CWc B.hS B.hW B.hell B.hR B.hM B.hWR B.U B.a B.cs B.hp (Real.sqrt (max B.a 1)) B.γ ^ 2)
        * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) := by
  have hSJ0 : 0 ≤ 400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀) := by positivity
  have hJ : ∀ b, ‖(gparams ell k Lu hell0 S B.U B.a Lam).Jf b‖
      ≤ (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀)) * omJ S ell k b := fun b =>
    Jf_strat ell M R k Lu hell0 S B.U B.a Lam α₀ B.hS hRM4 hU hsmJ b
  have hψ := psi_le_of_wcol (gparams ell k Lu hell0 S B.U B.a Lam) (omJ S ell k) CΨ _ hCΨ0 hSJ0 hcol hJ
  have hC := hC2_strat ell M R k Lu hell0 S B.U B.a Lam α₀ B.hS B.hell hroom hLu hα₀ hU hDQ
  have hW : ∀ A : ↥(bondSupp (geomOf ell k S)),
      wnormSq S ell k (Wop (geomOf ell k S) B.U B.a (iE (geomOf ell k S) A))
        ≤ ((ell : ℝ) ^ 2 * CWc B.hS B.hW B.hell B.hR B.hM B.hWR B.U B.a B.cs B.hp (Real.sqrt (max B.a 1)) B.γ ^ 2)
          * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) := fun A =>
    W_wnormSq B.hS B.hW B.hell B.hR B.hM B.hWR B.U B.a B.cs B.hp B.Gi B.hG1 B.γ B.hγ0.le B.hγ (iE (geomOf ell k S) A)
  have hK2 : 0 ≤ K2strat ell (12 * M * α₀) := by
    unfold K2strat
    have := K2free_nonneg ell ((1 + 3 * Real.pi) * alphaQ ell (12 * M * α₀)) (thetaK2_lt_of ell _ hDQ.hK2c)
    positivity
  exact delta2_strat (gparams ell k Lu hell0 S B.U B.a Lam) _ (K2strat ell (12 * M * α₀)) _
    (mul_nonneg hCΨ0 hSJ0) hK2 hψ hC hW A

#print axioms CTBase
#print axioms CTBase.toCT
#print axioms CTBase.toCT_U
#print axioms CTBase.toCT_a
#print axioms CTBase.toCT_χ
#print axioms Cgeo
#print axioms θ'_nonneg
#print axioms kapB
#print axioms wsB
#print axioms hcol_B
#print axioms dlayer_clause1

end AdalyFormal.M1DStrat
