import R7Fork.ZXG3L

/-!
# G3M -- THE CLOSED-POINT COERCIVE INEQUALITY for the GENUINE family (statement in G3L header).
No sorry / native_decide / axiom.
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.IngredientFamily (q1SU2)

/-- `τ Q (fineOf B) = B` at the closed point -/
theorem P0_mem_bondSupp (Lu : PeriodicLatticeExtent) (hell : 0 < 2) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu))
    (y : BondFnL2 (scaleUp (P0 2 Lu hell a Lam).ell (P0 2 Lu hell a Lam).k (P0 2 Lu hell a Lam).Lu)) :
    y ∈ bondSupp (P0 2 Lu hell a Lam).G := by
  rw [P0_bondSupp_top]; exact Submodule.mem_top

theorem P0_tau_Q_fineOf (Lu : PeriodicLatticeExtent) (hell : 0 < 2) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (B : Bond Lu → SuTwo)
    (hx : fineOf 2 Lu hell B ∈ bondSupp (P0 2 Lu hell a Lam).G) :
    (P0 2 Lu hell a Lam).tau ((P0 2 Lu hell a Lam).data.Q ⟨fineOf 2 Lu hell B, hx⟩) =
      (WithLp.toLp 2 B : BondFnL2 (P0 2 Lu hell a Lam).Lu) := by
  refine PiLp.ext (fun e => ?_)
  have hFS := fullTower_fullSupp 2 0 Lu hell flatCfg a Lam
  rw [IngrBParams.tau_apply (P0 2 Lu hell a Lam) hFS, P0_Q_apply 2 Lu hell a Lam]
  show (WithLp.ofLp (fineOf 2 Lu hell B)) (unitBondEmb 2 0 Lu hell e) = B e
  exact fineOf_emb 2 Lu hell B e

theorem closed_point_coerc (Lu : PeriodicLatticeExtent) (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) (hell : 0 < 2) (a : ℝ) (ha : 0 < a) (Bt : Bond Lu → SuTwo)
    (hBt : OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite Lu)) 2 Bt) :
    (1 / 1728 : ℝ) * bondEnergy Bt ≤
      GenP.genForm (P0 2 Lu hell a Set.univ)
        (WithLp.toLp 2 (GenP.genC (P0 2 Lu hell a Set.univ) Bt)) := by
  have hN : ∀ μ, 1 ≤ Lu μ := fun μ => by have := hL μ; omega
  have hQ1 : (P0 2 Lu hell a Set.univ).Q1 = q1SU2 2 := Q1_eq_q1SU2 (P0 2 Lu hell a Set.univ) rfl hd
  have hb : Function.Bijective (H0 (Set.univ : Set (PeriodicLatticeSite Lu)) (q1SU2 2)) := by
    have := P0_hb 2 Lu hell a Set.univ hd
    rw [hQ1] at this
    exact this
  have hgen : GenP.genC (P0 2 Lu hell a Set.univ) Bt = Cop Set.univ (q1SU2 2) Bt := by
    unfold GenP.genC; rw [hQ1]; rfl
  obtain ⟨hax, hker, hen⟩ := Cop_props_univ Lu hd hb Bt hBt
  have h24 := lemma24_flat hL hd (Cop Set.univ (q1SU2 2) Bt) hax hker
  rw [hgen]
  set B := Cop (Set.univ : Set (PeriodicLatticeSite Lu)) (q1SU2 2) Bt with hBdef
  have hmem : fineOf 2 Lu hell B ∈ bondSupp (P0 2 Lu hell a Set.univ).G :=
    P0_mem_bondSupp Lu hell a Set.univ _
  have hτ := P0_tau_Q_fineOf Lu hell a Set.univ B hmem
  rw [← hτ, P0_genForm_eq 2 Lu hell a Set.univ hd ha ⟨fineOf 2 Lu hell B, hmem⟩]
  have hD : ⟪iE (P0 2 Lu hell a Set.univ).G ⟨fineOf 2 Lu hell B, hmem⟩,
      DpiFull (P0 2 Lu hell a Set.univ).G flatCfg a (iE (P0 2 Lu hell a Set.univ).G ⟨fineOf 2 Lu hell B, hmem⟩)⟫
      = ∑ p : PeriodicLatticePlaquette Lu, ‖curlValueCovariant (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lu) B p‖ ^ 2 := by
    rw [inner_DpiFull_flat_univ _ (P0_Om0 2 Lu hell a Set.univ)]
    show ‖curlCovariantCLM_L2 flatCfg (fineOf 2 Lu hell B)‖ ^ 2 = _
    have : fineOf 2 Lu hell B = WithLp.toLp 2 (WithLp.ofLp (fineOf 2 Lu hell B)) := rfl
    rw [this, curlCovariantCLM_L2_toLp, PiLp.norm_sq_eq_of_L2]
    exact curl_energy_fineOf 2 Lu hell hN B
  rw [hD]
  have h24' : (1 / 1728 : ℝ) * ∑ b : Bond Lu, ‖B b‖ ^ 2 ≤
      ∑ p : PeriodicLatticePlaquette Lu, ‖curlValueCovariant (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lu) B p‖ ^ 2 := h24
  have hT := sq_nonneg ‖Tfull (P0 2 Lu hell a Set.univ).G flatCfg (iE (P0 2 Lu hell a Set.univ).G ⟨fineOf 2 Lu hell B, hmem⟩)‖
  have hen' : (1 / 1728 : ℝ) * bondEnergy Bt ≤ (1 / 1728 : ℝ) * ∑ b : Bond Lu, ‖B b‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hen (by norm_num)
  linarith

#print axioms P0_tau_Q_fineOf
#print axioms closed_point_coerc

end AdalyFormal.StatementLaneG
