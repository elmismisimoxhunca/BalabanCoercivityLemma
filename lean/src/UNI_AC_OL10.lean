import OL10
import UNI_Base
import UNI_AC_OL8
import AC_OL10

/-! AC copy of OL10: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 8000

namespace UNI.M2OpLayer
open UNI.AllC (CF CubeFamOK)
open AdalyFormal.M2OpLayer

open AdalyFormal.AllC UNI.AllC
variable {Fm : CF} [CubeFamOK Fm]

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer (bondWt psiD)
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.M1DStrat
open AdalyFormal.M2DLayer (Ageo)

section cfg
variable {ell M R k W : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (B : CTBase ell M R k S W) (hell0 : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
  (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k B.U ρ)
  (hεγ : ∀ c, (B.toCT c).epsG * B.γ ≤ 1) (hcG : ∀ c, 0 < (B.toCT c).cG)
  (cw : ℝ) (hcw : 0 < cw)
  (hW4 : ∀ A : ↥(bondSupp (geomOf ell k S)),
    cw * AdalyFormal.M1.wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell0 S B.U B.a Lam).data.Ginv A⟫)
  (hR8 : 8 * ell ≤ R) (Sstar : ℝ) (Dr : ∀ p : BIdx (geomOf ell k S), AdalyFormal.M2F123.RowQ ell k Lu S B.U Sstar p)
  (bN : ℝ) (hbN : 0 < bN)
  (hext : ∀ v : FSp (geomOf ell k S), ∃ g : ↥(bondSupp (geomOf ell k S)),
    (gparams ell k Lu hell0 S B.U B.a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu hell0 S B.U B.a Lam).data.Ginv g⟫
        ≤ bN * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) B.a p)) v‖ ^ 2)


include hρ hreg hεγ hcG hcw hW4 hR8 Dr hbN hext in
/-- the `hH1L2` field at the configuration -/
theorem hH1L2_cfgACΦ (hell2 : 2 ≤ ell) (hroom : 18 * ell ≤ R * M) {α₀ : ℝ}
    (hU : ClassCoupledHQ ell M Fm 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ B.U) (hα : 0 ≤ α₀) (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1)
    (hq : (ell : ℝ) ^ 3 * Real.exp (-(B.θ * (R * M))) ≤ 1 / 2)
    (KH : ℝ) (hKH : 0 ≤ KH)
    (hHL2 : ∀ (p : BIdx (gparams ell k Lu hell0 S B.U B.a Lam).G) (v : SuTwo), ∃ c : PeriodicLatticeSite (scaleUp ell k Lu),
      ∑ b : Bond (scaleUp ell k Lu), ((((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹) * Real.exp (phiC S ell M R k B.θ c b.1)
        * ‖(iE (gparams ell k Lu hell0 S B.U B.a Lam).G ((gparams ell k Lu hell0 S B.U B.a Lam).data.H
            (WithLp.toLp 2 (Pi.single p v) : FSp (gparams ell k Lu hell0 S B.U B.a Lam).G))) b‖) ^ 2
        ≤ KH ^ 2 * (ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2)
    (K2 : ℝ) (hK2 : 0 ≤ K2)
    (hC : ∀ z, ∑ q, ‖C2fullOf (geomOf ell k S) B.U z q‖ ≤ K2 * AdalyFormal.M1.wnormSq S ell k z)
    (CH1 : ℝ) (hCH10 : 0 ≤ CH1)
    (hlt2 : 2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * Real.exp (2 * 0)
          * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2 < cw)
    (hκ1N : kap1N ell B.a B.cs B.Θ B.Δ B.γ (3 * B.θ * (ell : ℝ) ^ 2) (3 * B.θ * ell) ρ cw Sstar
      (2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * Real.exp (2 * 0)
          * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2)
      (2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2
          * Real.exp (2 * (32 * B.θ * ell)) * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2) < 1)
    (hcN1N : ENF (kap1N ell B.a B.cs B.Θ B.Δ B.γ (3 * B.θ * (ell : ℝ) ^ 2) (3 * B.θ * ell) ρ cw Sstar
      (2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * Real.exp (2 * 0)
          * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2)
      (2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2
          * Real.exp (2 * (32 * B.θ * ell)) * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2))
      (CQ1N ell B.a B.cs B.Θ B.Δ B.γ ρ cw
        (2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * Real.exp (2 * 0)
          * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2))
      (d3c ell B.a Sstar (3 * B.θ * ell))
      (cw - 2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * Real.exp (2 * 0)
          * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2)
      < 1 / ((1 + 2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2
          * Real.exp (2 * 0) * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2 / cw) * bN))
    (hCH1 : CHwF (kap1N ell B.a B.cs B.Θ B.Δ B.γ (3 * B.θ * (ell : ℝ) ^ 2) (3 * B.θ * ell) ρ cw Sstar
      (2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * Real.exp (2 * 0)
          * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2)
      (2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2
          * Real.exp (2 * (32 * B.θ * ell)) * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2))
      (CQ1N ell B.a B.cs B.Θ B.Δ B.γ ρ cw
        (2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * Real.exp (2 * 0)
          * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2))
      (d3c ell B.a Sstar (3 * B.θ * ell))
      (cw - 2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * Real.exp (2 * 0)
          * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2)
      ((1 + 2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2
          * Real.exp (2 * 0) * 44217 * ((ell : ℝ) * kWcN ell B.a B.cs B.Θ B.Δ B.γ) ^ 2 / cw) * bN) ≤ CH1) :
    ∀ (e : Bond Lu) (v : SuTwo), ∃ c : PeriodicLatticeSite (scaleUp ell k Lu),
      ∑ b : Bond (scaleUp ell k Lu), ((((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹)
        * Real.exp (phiC S ell M R k B.θ c b.1)
        * ‖((gparams ell k Lu hell0 S B.U B.a Lam).H1in (WithLp.toLp 2 (Pi.single e v) : BondFnL2 Lu)) b‖) ^ 2
        ≤ (CH1 * Real.sqrt (B.a * ell)) ^ 2 * (ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2 := by
  classical
  have hQs := qs_inj_of_hext hell0 S B.U B.a Lam bN hext
  have hR1 : 1 ≤ R := B.hR
  have hM1 : 1 ≤ M := B.hM
  set kW : ℝ := kWcN ell B.a B.cs B.Θ B.Δ B.γ with hkWdef
  set c0 : PeriodicLatticeSite (scaleUp ell k Lu) := fun _ => 0 with hc0
  have hkW : ∀ c, (B.toCT c).kWc = kW := fun c => rfl
  have hkW0 : 0 ≤ kW := by rw [← hkW c0]; exact (B.toCT c0).kWc_nonneg (hcG c0)
  set δ0 : ℝ := 2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2
      * Real.exp (2 * 0) * 44217 * ((ell : ℝ) * kW) ^ 2 with hδ0def
  set δ1 : ℝ := 2 * ((Real.sqrt (Ageo ell B.θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2
      * Real.exp (2 * (32 * B.θ * ell)) * 44217 * ((ell : ℝ) * kW) ^ 2 with hδ1def
  have hδ0 : 0 ≤ δ0 := by rw [hδ0def]; positivity
  have hδ1 : 0 ≤ δ1 := by rw [hδ1def]; positivity
  have eW0 : ∀ x : ↥(bondSupp (geomOf ell k S)), eW (geomOf ell k S) (fun _ => (0 : ℝ)) x = x := fun x => by
    apply Subtype.ext
    show iE (geomOf ell k S) (eW (geomOf ell k S) (fun _ => (0 : ℝ)) x) = iE (geomOf ell k S) x
    rw [iE_eW, bondWt_zero_fn]
  have eW0' : ∀ x : ↥(bondSupp (geomOf ell k S)), eW (geomOf ell k S) (-(fun _ => (0 : ℝ))) x = x := fun x => by
    rw [show (-(fun _ : PeriodicLatticeSite (scaleUp ell k Lu) => (0 : ℝ))) = fun _ => (0 : ℝ) from by funext; simp]
    exact eW0 x
  have hD0 : ∀ x y : ↥(bondSupp (geomOf ell k S)), |⟪x, (gparams ell k Lu hell0 S B.U B.a Lam).data.Delta2
      (gparams ell k Lu hell0 S B.U B.a Lam).data_laws y⟫|
      ≤ δ0 * (nq S ell k (geomOf ell k S) x * nq S ell k (geomOf ell k S) y) := by
    intro x y
    have hWp : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt (-(fun _ => (0 : ℝ))) (Wop (geomOf ell k S) B.U B.a
        (bondWt (fun _ => (0 : ℝ)) z)))‖ ≤ kW * ‖bondWt (-sigG (geomOf ell k S)) z‖ := by
      intro z
      rw [show (-(fun _ : PeriodicLatticeSite (scaleUp ell k Lu) => (0 : ℝ))) = fun _ => (0 : ℝ) from by funext; simp,
        bondWt_zero_fn, bondWt_zero_fn]
      have h := (B.toCT c0).WC_bound (fun _ => (0 : ℝ)) (B.toCT c0).ok0P (B.toCT c0).ok0M (B.toCT c0).ok0N
        (hεγ c0) (hcG c0) z
      rw [(B.toCT c0).WC_zero] at h
      rw [← hkW c0]; exact h
    have hWm : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt (fun _ => (0 : ℝ)) (Wop (geomOf ell k S) B.U B.a
        (bondWt (-(fun _ => (0 : ℝ))) z)))‖ ≤ kW * ‖bondWt (-sigG (geomOf ell k S)) z‖ := by
      intro z
      rw [show (-(fun _ : PeriodicLatticeSite (scaleUp ell k Lu) => (0 : ℝ))) = fun _ => (0 : ℝ) from by funext; simp,
        bondWt_zero_fn, bondWt_zero_fn]
      have h := (B.toCT c0).WC_bound (fun _ => (0 : ℝ)) (B.toCT c0).ok0P (B.toCT c0).ok0M (B.toCT c0).ok0N
        (hεγ c0) (hcG c0) z
      rw [(B.toCT c0).WC_zero] at h
      rw [← hkW c0]; exact h
    have h := delta2_classACΦ hell0 hell2 B.hS hR1 hM1 hroom hU hα hsm B.hθ hq B.a Lam KH hKH hHL2 K2 hK2 hC
      (fun _ => (0 : ℝ)) kW hkW0 hWp hWm 0 le_rfl (fun p _ e _ => by simp) x y
    rw [eW0, eW0'] at h
    refine h.trans (le_of_eq ?_)
    unfold nq; ring
  have hD1 : ∀ (c : PeriodicLatticeSite (scaleUp ell k Lu)) (x y : ↥(bondSupp (geomOf ell k S))),
      |⟪(EWP (geomOf ell k S) (B.toCT c).χ).w x, (gparams ell k Lu hell0 S B.U B.a Lam).data.Delta2
        (gparams ell k Lu hell0 S B.U B.a Lam).data_laws ((EWP (geomOf ell k S) (B.toCT c).χ).wi y)⟫|
      ≤ δ1 * (nq S ell k (geomOf ell k S) x * nq S ell k (geomOf ell k S) y) := by
    intro c x y
    have hWp : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt (-(B.toCT c).χ) (Wop (geomOf ell k S) B.U B.a
        (bondWt (B.toCT c).χ z)))‖ ≤ kW * ‖bondWt (-sigG (geomOf ell k S)) z‖ := by
      intro z
      have h := (B.toCT c).WC_bound (-(B.toCT c).χ) (B.toCT c).okM (B.toCT c).okMM (B.toCT c).okN2 (hεγ c) (hcG c) z
      rw [← hkW c]
      unfold CTData.WC at h
      rw [neg_neg] at h
      exact h
    have hWm : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt (B.toCT c).χ (Wop (geomOf ell k S) B.U B.a
        (bondWt (-(B.toCT c).χ) z)))‖ ≤ kW * ‖bondWt (-sigG (geomOf ell k S)) z‖ := by
      intro z
      have h := (B.toCT c).WC_bound (B.toCT c).χ (B.toCT c).okP (B.toCT c).okM (B.toCT c).okN1 (hεγ c) (hcG c) z
      rw [← hkW c]
      exact h
    have hosc : ∀ (p : BIdx (geomOf ell k S)), 1 ≤ (p.1 : ℕ) →
        ∀ e : Bond (scaleUp ell k Lu), e.1 ∈ AdalyFormal.StatementLaneR8.Ball p.2.1.1 (AdalyFormal.StatementLaneR8.rhoT ell p.1) →
        |(B.toCT c).χ e.1 - (B.toCT c).χ p.2.1.1| ≤ 32 * B.θ * ell :=
      fun p hp e he => ball_osc B.hS hell2 hroom hR1 hM1 B.hθ.le c p hp e he
    have h := delta2_classACΦ hell0 hell2 B.hS hR1 hM1 hroom hU hα hsm B.hθ hq B.a Lam KH hKH hHL2 K2 hK2 hC
      (B.toCT c).χ kW hkW0 hWp hWm (32 * B.θ * ell) (by have := B.hθ; positivity) hosc x y
    refine h.trans (le_of_eq ?_)
    unfold nq; ring
  intro e v
  have hH : (gparams ell k Lu hell0 S B.U B.a Lam).H1in (WithLp.toLp 2 (Pi.single e v) : BondFnL2 Lu)
      = iE (geomOf ell k S) ((gparams ell k Lu hell0 S B.U B.a Lam).data.H1 (gparams ell k Lu hell0 S B.U B.a Lam).G1inv
        (ContinuousLinearMap.adjoint (tauExt ell k Lu hell0 S) (WithLp.toLp 2 (Pi.single e v) : BondFnL2 Lu))) := rfl
  rw [hH, tau_adj_single ell k Lu hell0 S e v]
  split_ifs with hb
  · set p : BIdx (geomOf ell k S) := ⟨Fin.last k, ⟨unitBondEmb ell k Lu hell0 e, hb⟩⟩ with hp
    set c := rowBase (geomOf ell k S) p with hc
    refine ⟨c, ?_⟩
    have hc0 : (B.toCT c).χ c = 0 := phiC_self B.hS B.θ c
    have hlev := rowBase_strat B.hS B.hR B.hM B.hell
      (le_trans (by omega : ell ≤ R) (Nat.le_mul_of_pos_right R (by have := B.hM; omega))) p
    have hκ1 : (gsplit1R (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
        (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt2 hD0 (hD1 c)).kap < 1 := hκ1N
    have hcN : 0 < 1 / (wschur1R (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
        (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt2 hD0 (hD1 c) hκ1).bN
        - (wschur1R (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
        (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt2 hD0 (hD1 c) hκ1).EN :=
      sub_pos.mpr hcN1N
    have heq : (gparams ell k Lu hell0 S B.U B.a Lam).data.H1 (gparams ell k Lu hell0 S B.U B.a Lam).G1inv
        = (wschur1R (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
          (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt2 hD0 (hD1 c) hκ1).H :=
      H1_eqR (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
        (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt2 hD0 (hD1 c) hκ1
    rw [heq]
    have h := H1_l2_colR (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
        (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt2 hD0 (hD1 c) hκ1 hcN
        p v hc0 hlev
    refine h.trans ?_
    set J := wschur1R (B.toCT c) hell0 Lam ρ hρ hreg (hεγ c) (hcG c) cw hcw hW4 (3 * B.θ * ell) (θ'_nonneg B)
        (phiC_lip B.hS B.hR B.hM B.hell B.hθ.le c) hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt2 hD0 (hD1 c) hκ1 with hJ
    have hCHw : 0 ≤ J.CHw := by
      unfold WSchur.CHw; have := J.Cy_nonneg; have := J.hcw; positivity
    have hle : J.CHw ≤ CH1 := hCH1
    have ha := B.hp.ha
    have hal : 0 ≤ B.a * (ell : ℝ) := by positivity
    have hsq : (CH1 * Real.sqrt (B.a * ell)) ^ 2 = CH1 ^ 2 * (B.a * ell) := by
      rw [mul_pow, Real.sq_sqrt hal]
    rw [hsq]
    have h2 : J.CHw ^ 2 ≤ CH1 ^ 2 := pow_le_pow_left₀ hCHw hle 2
    have hp0 : (0 : ℝ) ≤ (ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2 := by positivity
    calc J.CHw ^ 2 * (B.a * ell) * (ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2
        = J.CHw ^ 2 * ((B.a * ell) * ((ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2)) := by ring
      _ ≤ CH1 ^ 2 * ((B.a * ell) * ((ell : ℝ) ^ AdalyFormal.M1.strat S k c * ‖v‖ ^ 2)) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg hal hp0)
      _ = _ := by ring
  · refine ⟨c0, ?_⟩
    rw [map_zero, map_zero]
    simp only [PiLp.zero_apply, norm_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero]
    positivity

end cfg

end UNI.M2OpLayer

