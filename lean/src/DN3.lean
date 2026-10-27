import DN2
import DY4b

/-!
# DN3 -- numeric twins of the `H₁` constants and their ball (M1 D-layer lane, clause 2, 2026-10-14)

* `kap1N`, `CQ1N` : the constants of DY4b's perturbed split as functions of real numbers; `kap1_eqN`, `ss1_eqN`,
  `EN1_eqN`, `bN1_eqN`, `CHw1_eqN` : the `rfl` bridges;
* `NumOK2` : the clause-1 conditions at `z.1 = (θ, r, p, q)` and the clause-2 conditions at `z = ((θ,r,p,q),(δ₀,δ₁))`;
* **`num_ball2`** : for `ℓ ≥ 2`, `a > 0`, `cw > 0` there is a ball around `0` (sup distance) on which `NumOK2` holds.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open Filter Topology
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (RegData Estar rho1 SstarM delStar Ctheta)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.W6 (CwE CgE CEp)

/-! ## 1. twins -/

noncomputable def kap1N (ell : ℕ) (a cs Θ Δ γ θχ θ' ρ cw Sstar δ0 δ1 : ℝ) : ℝ :=
  kapF (d1c ell θ') (dTcN ell a cs Θ Δ γ θχ) (d3c ell a Sstar θ')
    (cw / (cw - δ0) * cDc ell ρ cw (kZcN ell a cs Θ Δ γ) (kWcN ell a cs Θ Δ γ) + δ0 / (cw - δ0))
    (cw / (cw - δ0) * cDc' ell ρ cw (kZcN ell a cs Θ Δ γ) (kWcN ell a cs Θ Δ γ) θ' (d1c ell θ') + δ1 / (cw - δ0))
    (cw - δ0)

noncomputable def CQ1N (ell : ℕ) (a cs Θ Δ γ ρ cw δ0 : ℝ) : ℝ :=
  Real.sqrt (1 + (cw / (cw - δ0) * cDc ell ρ cw (kZcN ell a cs Θ Δ γ) (kWcN ell a cs Θ Δ γ) + δ0 / (cw - δ0)))

namespace CTData

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
  (δ0 δ1 : ℝ) (hδ0 : 0 ≤ δ0) (hδ1 : 0 ≤ δ1) (hlt : δ0 < cw)
  (hD0 : ∀ x y : ↥(bondSupp (geomOf ell k S)), |⟪x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2
      (gparams ell k Lu hell0 S D.U D.a Lam).data_laws y⟫|
    ≤ δ0 * (nq S ell k (geomOf ell k S) x * nq S ell k (geomOf ell k S) y))
  (hD1 : ∀ x y : ↥(bondSupp (geomOf ell k S)),
    |⟪(EWP (geomOf ell k S) D.χ).w x, (gparams ell k Lu hell0 S D.U D.a Lam).data.Delta2
      (gparams ell k Lu hell0 S D.U D.a Lam).data_laws ((EWP (geomOf ell k S) D.χ).wi y)⟫|
      ≤ δ1 * (nq S ell k (geomOf ell k S) x * nq S ell k (geomOf ell k S) y))

theorem kap1_eqN :
    (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).kap
      = kap1N ell D.a D.cs D.Θ D.Δ D.γ D.θχ θ' ρ cw Sstar δ0 δ1 := rfl

theorem ss1_eqN :
    (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0 hD1).ss
      = CQ1N ell D.a D.cs D.Θ D.Δ D.γ ρ cw δ0 := rfl

theorem EN1_eqN (hκ1 : (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0
      hD1).kap < 1) :
    (D.wschur1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1
        hκ1).EN
      = ENF (kap1N ell D.a D.cs D.Θ D.Δ D.γ D.θχ θ' ρ cw Sstar δ0 δ1) (CQ1N ell D.a D.cs D.Θ D.Δ D.γ ρ cw δ0)
          (d3c ell D.a Sstar θ') (cw - δ0) := rfl

theorem bN1_eqN (hκ1 : (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0
      hD1).kap < 1) :
    (D.wschur1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1
        hκ1).bN = (1 + δ0 / cw) * bN := rfl

theorem CHw1_eqN (hκ1 : (D.gsplit1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr δ0 δ1 hδ0 hδ1 hlt hD0
      hD1).kap < 1) :
    (D.wschur1 hell0 Lam ρ hρ hreg hεγ hcG cw hcw hW4 θ' hθ' hL hR8 Sstar Dr bN hbN hext hQs δ0 δ1 hδ0 hδ1 hlt hD0 hD1
        hκ1).CHw
      = CHwF (kap1N ell D.a D.cs D.Θ D.Δ D.γ D.θχ θ' ρ cw Sstar δ0 δ1) (CQ1N ell D.a D.cs D.Θ D.Δ D.γ ρ cw δ0)
          (d3c ell D.a Sstar θ') (cw - δ0) ((1 + δ0 / cw) * bN) := rfl

end CTData

/-! ## 2. the functions of `z = ((θ,r,p,q),(δ₀,δ₁))` -/

section num2
variable (ell : ℕ) (a cw : ℝ)

noncomputable def kWF (x : ℝ × ℝ × ℝ × ℝ) : ℝ := kWcN ell a (csF ell a x) (ThF ell x) (DeF x) (gamF ell a x)

noncomputable def kap1F (z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  kap1N ell a (csF ell a z.1) (ThF ell z.1) (DeF z.1) (gamF ell a z.1) (3 * z.1.1 * (ell : ℝ) ^ 2) (3 * z.1.1 * ell)
    z.1.2.1 cw (SsF ell z.1.2.1) z.2.1 z.2.2

noncomputable def CQ1F (z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  CQ1N ell a (csF ell a z.1) (ThF ell z.1) (DeF z.1) (gamF ell a z.1) z.1.2.1 cw z.2.1

noncomputable def bN1F (z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)) : ℝ := (1 + z.2.1 / cw) * bNF ell a z.1

noncomputable def EN1F (z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  ENF (kap1F ell a cw z) (CQ1F ell a cw z) (d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) (cw - z.2.1)

noncomputable def CH1F (z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  CHwF (kap1F ell a cw z) (CQ1F ell a cw z) (d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) (cw - z.2.1)
    (bN1F ell a cw z)

/-- the clause-1 and clause-2 numeric conditions -/
def NumOK2 (CHb CWb KWb CH1b : ℝ) (z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)) : Prop :=
  NumOK ell a cw CHb CWb z.1 ∧ kWF ell a z.1 ^ 2 < KWb ∧ z.2.1 < cw / 2 ∧ kap1F ell a cw z < 1 ∧
  EN1F ell a cw z < 1 / bN1F ell a cw z ∧ CH1F ell a cw z < CH1b

end num2

section ball2
variable {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) {cw : ℝ} (hcw : 0 < cw)
include hell ha hcw

theorem kap1_0 : kap1F ell a cw 0 = 0 := by
  simp only [kap1F, kap1N, kapF, Prod.fst_zero, Prod.snd_zero]
  have h0 := dTc0 (ell := ell) (a := a)
  simp only [Prod.fst_zero] at h0
  rw [h0]
  simp only [d1c, d3c, cDc, cDc', cYc, kapK, nuD, SsF, Prod.fst_zero, Prod.snd_zero, Real.exp_zero, sub_self, mul_zero,
    zero_mul, add_zero, zero_add, zero_pow two_ne_zero, zero_div, Real.sqrt_zero, sub_zero]

theorem cont_kap1 : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => kap1F ell a cw z) 0 := by
  have hd : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => dTcN ell a (csF ell a z.1) (ThF ell z.1) (DeF z.1)
      (gamF ell a z.1) (3 * z.1.1 * (ell : ℝ) ^ 2)) 0 :=
    by have h := ContinuousAt.comp (f := Prod.fst) (x := (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ))) (cont_dTc hell ha) continuousAt_fst; exact h
  have hZ : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => kZcN ell a (csF ell a z.1) (ThF ell z.1) (DeF z.1)
      (gamF ell a z.1)) 0 := by have h := ContinuousAt.comp (f := Prod.fst) (x := (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ))) (cont_kZ hell ha) continuousAt_fst; exact h
  have hW : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => kWcN ell a (csF ell a z.1) (ThF ell z.1) (DeF z.1)
      (gamF ell a z.1)) 0 := by have h := ContinuousAt.comp (f := Prod.fst) (x := (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ))) (cont_kW hell ha) continuousAt_fst; exact h
  have h1 : Real.sqrt cw ≠ 0 := (Real.sqrt_pos.mpr hcw).ne'
  have h2 : cw - (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1 ≠ 0 := by simp only [Prod.snd_zero, Prod.fst_zero, sub_zero]; exact hcw.ne'
  have h3 : Real.sqrt (cw - (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1) ≠ 0 := by
    simp only [Prod.snd_zero, Prod.fst_zero, sub_zero]; exact h1
  simp only [kap1F, kap1N, kapF, d1c, d3c, cDc, cDc', cYc, kapK, nuD, SsF, Estar]
  fun_prop (disch := first | exact h1 | exact h2 | exact h3 | exact hcw.ne' | positivity)

theorem cont_CQ1 : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => CQ1F ell a cw z) 0 := by
  have hZ : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => kZcN ell a (csF ell a z.1) (ThF ell z.1) (DeF z.1)
      (gamF ell a z.1)) 0 := by have h := ContinuousAt.comp (f := Prod.fst) (x := (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ))) (cont_kZ hell ha) continuousAt_fst; exact h
  have hW : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => kWcN ell a (csF ell a z.1) (ThF ell z.1) (DeF z.1)
      (gamF ell a z.1)) 0 := by have h := ContinuousAt.comp (f := Prod.fst) (x := (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ))) (cont_kW hell ha) continuousAt_fst; exact h
  have h1 : Real.sqrt cw ≠ 0 := (Real.sqrt_pos.mpr hcw).ne'
  have h2 : cw - (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1 ≠ 0 := by simp only [Prod.snd_zero, Prod.fst_zero, sub_zero]; exact hcw.ne'
  simp only [CQ1F, CQ1N, cDc, cYc, kapK, nuD]
  fun_prop (disch := first | exact h1 | exact h2 | exact hcw.ne' | positivity)

theorem cont_d3z : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) =>
    d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) 0 :=
  by have h := ContinuousAt.comp (f := Prod.fst) (x := (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ))) (cont_d3 (ell := ell) hell ha (a := a)) continuousAt_fst; exact h

theorem cont_bN1 : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => bN1F ell a cw z) 0 := by
  have hb : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => bNF ell a z.1) 0 := by have h := ContinuousAt.comp (f := Prod.fst) (x := (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ))) (cont_bN hell ha) continuousAt_fst; exact h
  simp only [bN1F]
  fun_prop (disch := exact hcw.ne')

theorem EN1_0 : EN1F ell a cw 0 = 0 := by
  have hk := kap1_0 hell ha hcw
  have hd3 : d3c ell a (SsF ell (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1.2.1) (3 * (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1.1 * ell)
      = 0 := by
    simp only [d3c, SsF, Prod.fst_zero, Prod.snd_zero, mul_zero, zero_mul, Real.exp_zero, sub_self,
      zero_pow two_ne_zero, Real.sqrt_zero]
  unfold EN1F ENF
  rw [hk, hd3]
  simp

theorem bN1_0 : 0 < bN1F ell a cw 0 := by
  simp only [bN1F, Prod.snd_zero, Prod.fst_zero, zero_div, add_zero, one_mul]
  exact bN0 hell ha

theorem cont_EN1 : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => EN1F ell a cw z) 0 := by
  have hk := cont_kap1 hell ha hcw
  have hq := cont_CQ1 hell ha hcw
  have h3 := cont_d3z hell ha hcw
  have h1 : Real.sqrt (cw - (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1) ≠ 0 := by
    simp only [Prod.snd_zero, Prod.fst_zero, sub_zero]; exact (Real.sqrt_pos.mpr hcw).ne'
  have h2 : 1 - kap1F ell a cw 0 ≠ 0 := by rw [kap1_0 hell ha hcw]; norm_num
  simp only [EN1F, ENF, CyF]
  fun_prop (disch := first | exact h1 | exact h2 | positivity)

theorem cont_CH1 : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => CH1F ell a cw z) 0 := by
  have hk := cont_kap1 hell ha hcw
  have hq := cont_CQ1 hell ha hcw
  have h3 := cont_d3z hell ha hcw
  have hb := cont_bN1 hell ha hcw
  have hE : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => ENF (kap1F ell a cw z) (CQ1F ell a cw z)
      (d3c ell a (SsF ell z.1.2.1) (3 * z.1.1 * ell)) (cw - z.2.1)) 0 := cont_EN1 hell ha hcw
  have h1 : Real.sqrt (cw - (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1) ≠ 0 := by
    simp only [Prod.snd_zero, Prod.fst_zero, sub_zero]; exact (Real.sqrt_pos.mpr hcw).ne'
  have h2 : 1 - kap1F ell a cw 0 ≠ 0 := by rw [kap1_0 hell ha hcw]; norm_num
  have hb0 := (bN1_0 hell ha hcw).ne'
  have h4 : 1 / bN1F ell a cw 0 - ENF (kap1F ell a cw 0) (CQ1F ell a cw 0)
      (d3c ell a (SsF ell (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1.2.1) (3 * (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1.1 * ell))
      (cw - (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).2.1) ≠ 0 := by
    have e := EN1_0 hell ha hcw; simp only [EN1F] at e; rw [e, sub_zero]; have := bN1_0 hell ha hcw; positivity
  simp only [CH1F, CHwF, CyF]
  fun_prop (disch := first | exact h1 | exact h2 | exact hb0 | exact h4 | positivity)

/-- **the second ball** -/
theorem num_ball2 : ∃ CHb : ℝ, 0 ≤ CHb ∧ ∃ CWb : ℝ, 0 ≤ CWb ∧ ∃ KWb : ℝ, 0 ≤ KWb ∧ ∃ CH1b : ℝ, 0 ≤ CH1b ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ), dist z 0 < δ → NumOK2 ell a cw CHb CWb KWb CH1b z := by
  obtain ⟨CHb, hCHb, CWb, hCWb, δ1, hδ1, hb1⟩ := num_ball hell ha hcw
  have hkW : ContinuousAt (fun z : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ) => kWF ell a z.1) 0 :=
    by have h := ContinuousAt.comp (f := Prod.fst) (x := (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ))) (cont_kW hell ha) continuousAt_fst; exact h
  have e1 : ∀ᶠ z in 𝓝 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)), kWF ell a z.1 ^ 2 < (|kWF ell a 0| + 1) ^ 2 :=
    hkW.pow 2 |>.eventually_lt continuousAt_const (by
      have h1 := abs_nonneg (kWF ell a 0)
      have h2 : kWF ell a (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1 ^ 2 = |kWF ell a 0| ^ 2 := by
        rw [Prod.fst_zero]; exact (sq_abs _).symm
      rw [h2]; nlinarith)
  have e2 : ∀ᶠ z in 𝓝 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)), z.2.1 < cw / 2 :=
    (continuous_snd.fst.continuousAt).eventually_lt continuousAt_const (by simp; positivity)
  have e3 : ∀ᶠ z in 𝓝 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)), kap1F ell a cw z < 1 :=
    (cont_kap1 hell ha hcw).eventually_lt continuousAt_const (by rw [kap1_0 hell ha hcw]; norm_num)
  have e4 : ∀ᶠ z in 𝓝 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)), EN1F ell a cw z < 1 / bN1F ell a cw z :=
    (cont_EN1 hell ha hcw).eventually_lt (by
      have hb := cont_bN1 hell ha hcw
      fun_prop (disch := exact (bN1_0 hell ha hcw).ne'))
      (by rw [EN1_0 hell ha hcw]; have := bN1_0 hell ha hcw; positivity)
  have e5 : ∀ᶠ z in 𝓝 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)), CH1F ell a cw z < |CH1F ell a cw 0| + 1 :=
    (cont_CH1 hell ha hcw).eventually_lt continuousAt_const (by have := le_abs_self (CH1F ell a cw 0); linarith)
  obtain ⟨δ2, hδ2, hb2⟩ := Metric.eventually_nhds_iff.mp (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨CHb, hCHb, CWb, hCWb, (|kWF ell a 0| + 1) ^ 2, by positivity, |CH1F ell a cw 0| + 1, by positivity,
    min δ1 δ2, lt_min hδ1 hδ2, fun z hz => ?_⟩
  have hz1 : dist z.1 0 < δ1 := by
    have : dist z.1 (0 : (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ)).1 ≤ dist z 0 := by rw [Prod.dist_eq]; exact le_max_left _ _
    rw [Prod.fst_zero] at this
    exact lt_of_le_of_lt this (lt_of_lt_of_le hz (min_le_left _ _))
  obtain ⟨g1, g2, g3, g4, g5⟩ := hb2 (lt_of_lt_of_le hz (min_le_right _ _))
  exact ⟨hb1 z.1 hz1, g1, g2, g3, g4, g5⟩

end ball2

#print axioms kap1N
#print axioms CQ1N
#print axioms CTData.kap1_eqN
#print axioms CTData.ss1_eqN
#print axioms CTData.EN1_eqN
#print axioms CTData.bN1_eqN
#print axioms CTData.CHw1_eqN
#print axioms NumOK2
#print axioms kap1_0
#print axioms cont_kap1
#print axioms cont_CQ1
#print axioms cont_d3z
#print axioms cont_bN1
#print axioms EN1_0
#print axioms bN1_0
#print axioms cont_EN1
#print axioms cont_CH1
#print axioms num_ball2

end AdalyFormal.M1DStrat
