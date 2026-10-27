import R8UR1

/-!
# UR3 -- the junk-jet theorem of UR1 on EVERY torus with at least 4 sites per direction.

UR1 proved `QlinStepX 1 2 (cfg1 (−1)) = 0` on the concrete `120³` torus by kernel `decide`.  Here the same facts are
transported to a general extent `L` (`∀ μ, 4 ≤ L μ + 1`): every site touched by the computation is `sv v` with
`v ∈ {0,…,3}³`, `periodicLatticeShift (sv v) μ = sv (v + e_μ)` holds unconditionally (mod arithmetic), and the path
facts are decided in an abstract model on `ℕ³` (`apath`, `agpath`) that does not mention the torus.
Main theorem: `QlinStepX_bad_eq_zero_gen`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace AdalyFormal.URLocalityR8

open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath coarsePathEndpoint)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf inStepBlock)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)

/-! ## 1. the abstract model on `ℕ³` -/

def apath : (Fin 3 → ℕ) → List (Fin 3) → List ((Fin 3 → ℕ) × Fin 3)
  | _, [] => []
  | v, μ :: r => (v, μ) :: apath (Function.update v μ (v μ + 1)) r

def agpath (w v : Fin 3 → ℕ) : List (Fin 3) :=
  List.replicate (v 2 - w 2) 2 ++ (List.replicate (v 1 - w 1) 1 ++ List.replicate (v 0 - w 0) 0)

/-- the abstract "this path avoids `b1` and stays in `{0..3}³`" test -/
def avoids (v : Fin 3 → ℕ) (p : List (Fin 3)) : Prop :=
  ∀ q ∈ apath v p, (∀ μ, q.1 μ < 4) ∧ ¬ (q.1 = (fun _ => 0) ∧ q.2 = 0)

instance (v : Fin 3 → ℕ) (p : List (Fin 3)) : Decidable (avoids v p) := by unfold avoids; infer_instance

def dv (δ : Fin 3 → Fin 2) : Fin 3 → ℕ := fun μ => (δ μ : ℕ)
def v2 : Fin 3 → ℕ := fun μ => if μ = 0 then 2 else 0
def v2d (δ : Fin 3 → Fin 2) : Fin 3 → ℕ := fun μ => v2 μ + (δ μ : ℕ)

theorem A_paths_avoid : ∀ δ : Fin 3 → Fin 2, δ ≠ d000 → δ ≠ d100 →
    avoids (fun _ => 0) (agpath (fun _ => 0) (dv δ)) ∧ avoids (dv δ) [0, 0] ∧
    avoids v2 (agpath (fun _ => 0) (dv δ)) := by decide
theorem A_path000 : agpath (fun _ => 0) (dv d000) = [] := by decide
theorem A_path100 : agpath (fun _ => 0) (dv d100) = [0] := by decide
theorem A_tail : avoids (Function.update (fun _ => 0) 0 1) [0] := by decide
theorem A_e0 : avoids (dv d100) [0, 0] := by decide
theorem A_cP1 : avoids v2 [0] := by decide
theorem A_rprod : ∀ δ : Fin 3 → Fin 2, δ ≠ d100 → avoids (fun _ => 0) (agpath (fun _ => 0) (dv δ)) := by decide
theorem A_rprodP : ∀ δ : Fin 3 → Fin 2, avoids v2 (agpath v2 (v2d δ)) := by decide

/-! ## 2. transport to the torus -/

section transport
variable {L : PeriodicLatticeExtent}

def sv (v : Fin 3 → ℕ) : PeriodicLatticeSite L := fun μ => ⟨v μ % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem sv_val (v : Fin 3 → ℕ) (μ : Fin 3) : ((sv v : PeriodicLatticeSite L) μ).val = v μ % (L μ + 1) := rfl

theorem shift_sv (v : Fin 3 → ℕ) (μ : Fin 3) :
    periodicLatticeShift (sv v : PeriodicLatticeSite L) μ = sv (Function.update v μ (v μ + 1)) := by
  funext ν
  apply Fin.ext
  by_cases h : ν = μ
  · subst h
    simp only [periodicLatticeShift, Function.update_self, sv_val, Fin.val_add, Fin.val_one']
    exact (Nat.add_mod _ _ _).symm
  · simp only [periodicLatticeShift, Function.update_of_ne h, sv_val]

theorem coarseShift_one (y : PeriodicLatticeSite L) (μ : Fin 3) : coarseShift y 1 μ = periodicLatticeShift y μ := rfl

theorem pathBonds_sv (p : List (Fin 3)) :
    ∀ v : Fin 3 → ℕ, pathBonds (sv v : PeriodicLatticeSite L) p = (apath v p).map (fun q => (sv q.1, q.2)) := by
  induction p with
  | nil => intro v; rfl
  | cons μ r ih =>
    intro v
    show ((sv v : PeriodicLatticeSite L), μ) :: pathBonds (coarseShift (sv v : PeriodicLatticeSite L) 1 μ) r
        = List.map (fun q => ((sv q.1 : PeriodicLatticeSite L), q.2)) ((v, μ) :: apath (Function.update v μ (v μ + 1)) r)
    rw [coarseShift_one, shift_sv, ih]
    rfl

theorem o0_eq_sv : (o0 : PeriodicLatticeSite L) = sv (fun _ => 0) := by
  funext μ; apply Fin.ext; simp [o0, sv_val]

theorem sv_eq_zero_iff (hL : ∀ μ, 4 ≤ L μ + 1) (v : Fin 3 → ℕ) (hv : ∀ μ, v μ < 4) :
    (sv v : PeriodicLatticeSite L) = o0 ↔ v = fun _ => 0 := by
  constructor
  · intro h
    funext μ
    have := congrArg (fun x : PeriodicLatticeSite L => (x μ).val) h
    simp only [sv_val, o0] at this
    have := hL μ; have := hv μ
    rw [Nat.mod_eq_of_lt (by omega)] at *
    omega
  · rintro rfl; exact o0_eq_sv.symm

theorem not_mem_of_avoids (hL : ∀ μ, 4 ≤ L μ + 1) (v : Fin 3 → ℕ) (p : List (Fin 3)) (h : avoids v p) :
    (b1 : PeriodicLatticeEdge L) ∉ pathBonds (sv v) p := by
  rw [pathBonds_sv, List.mem_map]
  rintro ⟨q, hq, hq'⟩
  obtain ⟨hb, hn⟩ := h q hq
  have h1 : (sv q.1 : PeriodicLatticeSite L) = o0 := congrArg Prod.fst hq'
  have h2 : q.2 = 0 := congrArg Prod.snd hq'
  exact hn ⟨(sv_eq_zero_iff hL q.1 hb).mp h1, h2⟩

theorem gpath_sv (hL : ∀ μ, 4 ≤ L μ + 1) (w v : Fin 3 → ℕ) (hw : ∀ μ, w μ ≤ v μ) (hv : ∀ μ, v μ < 4) :
    coarseGammaPath 1 (sv w : PeriodicLatticeSite L) (sv v) = agpath w v := by
  have hs : ∀ μ, (((sv v : PeriodicLatticeSite L) μ) - ((sv w : PeriodicLatticeSite L) μ)).val = v μ - w μ := by
    intro μ
    have h4 := hL μ; have h1 := hv μ; have h2 := hw μ
    rw [Fin.sub_val_of_le]
    · simp only [sv_val]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    · show ((sv w : PeriodicLatticeSite L) μ).val ≤ ((sv v : PeriodicLatticeSite L) μ).val
      simp only [sv_val]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h2
  unfold coarseGammaPath AdalyFormal.Balaban.TowerLawCov.coarseStraightSegment
    AdalyFormal.Balaban.TowerLawCov.coarseCoordSteps agpath
  simp only [Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide), Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide), Nat.div_one, hs]

theorem stepBlock_sv (w : Fin 3 → ℕ) (hw : ∀ μ, w μ + 2 ≤ L μ + 1) :
    stepBlockOf (sv w : PeriodicLatticeSite L) 1 2 = Finset.univ.image (fun δ : Fin 3 → Fin 2 => sv (fun μ => w μ + δ μ)) := by
  ext x
  rw [mem_stepBlockOf, Finset.mem_image]
  have hwv : ∀ μ, ((sv w : PeriodicLatticeSite L) μ).val = w μ := fun μ => by
    rw [sv_val, Nat.mod_eq_of_lt (by have := hw μ; omega)]
  constructor
  · intro h
    have hb : ∀ μ, w μ ≤ (x μ).val ∧ (x μ).val < w μ + 2 := fun μ => by
      have h1 := (h μ).1; have h2 := (h μ).2.1; rw [hwv] at h1 h2; exact ⟨h1, by omega⟩
    refine ⟨fun μ => ⟨(x μ).val - w μ, by have := hb μ; omega⟩, Finset.mem_univ _, ?_⟩
    funext μ
    apply Fin.ext
    have h1 := hb μ; have h2 := (x μ).isLt
    rw [sv_val, Nat.mod_eq_of_lt (by simp only; omega)]
    simp only
    omega
  · rintro ⟨δ, -, rfl⟩ μ
    have h2 := (δ μ).isLt; have h3 := hw μ
    rw [hwv, sv_val, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, by omega, one_dvd _⟩

theorem sv_inj (w : Fin 3 → ℕ) (hw : ∀ μ, w μ + 2 ≤ L μ + 1) :
    Function.Injective (fun δ : Fin 3 → Fin 2 => (sv (fun μ => w μ + δ μ) : PeriodicLatticeSite L)) := by
  intro δ δ' h
  funext μ
  have := congrArg (fun x : PeriodicLatticeSite L => (x μ).val) h
  simp only [sv_val] at this
  have h1 := (δ μ).isLt; have h2 := (δ' μ).isLt; have h3 := hw μ
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact Fin.ext (by omega)

theorem cPlus_sv : cPlusS 1 2 ((o0, 0) : PeriodicLatticeEdge L) = sv v2 := by
  show coarsePathEndpoint 1 (o0 : PeriodicLatticeSite L) [0, 0] = sv v2
  rw [o0_eq_sv]
  show coarsePathEndpoint 1 (coarseShift (coarseShift (sv (fun _ => 0) : PeriodicLatticeSite L) 1 0) 1 0) [] = sv v2
  rw [coarseShift_one, coarseShift_one, shift_sv, shift_sv]
  show sv _ = sv v2
  congr 1
  funext μ; fin_cases μ <;> simp [v2, Function.update]

end transport

/-! ## 3. the loop computation at a general torus -/

theorem emb_eq {L : PeriodicLatticeExtent} (δ : Fin 3 → Fin 2) :
    (sv (fun μ => (fun _ : Fin 3 => 0) μ + (δ μ : ℕ)) : PeriodicLatticeSite L) = sv (dv δ) := by
  congr 1; funext μ; simp [dv]

theorem dv_le (δ : Fin 3 → Fin 2) : ∀ μ, (fun _ : Fin 3 => 0) μ ≤ dv δ μ := fun _ => Nat.zero_le _
theorem dv_lt (δ : Fin 3 → Fin 2) : ∀ μ, dv δ μ < 4 := fun μ => by have := (δ μ).isLt; simp [dv]; omega

section loops
variable {L : PeriodicLatticeExtent} (hL : ∀ μ, 4 ≤ L μ + 1)
include hL

theorem w0_ok : ∀ μ, (fun _ : Fin 3 => 0) μ + 2 ≤ L μ + 1 := fun μ => by have := hL μ; simp; omega
theorem v2_ok : ∀ μ, v2 μ + 2 ≤ L μ + 1 := fun μ => by
  by_cases h : μ = 0
  · subst h; have := hL 0; simp [v2]; omega
  · have := hL μ; simp [v2, h]; omega

theorem coarseBondVar_cfg1_gen (g : SU2) :
    coarseBondVar 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L) (o0, 0) = g := by
  show coarsePathHolonomy 1 (cfg1 g) (o0 : PeriodicLatticeSite L) [0, 0] = g
  refine hol_cfg1_cons_b1 g [0] ?_
  rw [coarseShift_one, o0_eq_sv, shift_sv]
  exact not_mem_of_avoids hL _ _ A_tail

theorem loopVar_cfg1_gen (g : SU2) (δ : Fin 3 → Fin 2) :
    loopVar 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L) (o0, 0) (sv (dv δ))
      = if δ = d000 ∨ δ = d100 then 1 else g⁻¹ := by
  unfold loopVar gammaVarStrided
  rw [coarseBondVar_cfg1_gen hL, cPlus_sv]
  dsimp only [List.replicate]
  have hg : coarseGammaPath 1 (o0 : PeriodicLatticeSite L) (sv (dv δ)) = agpath (fun _ => 0) (dv δ) := by
    rw [o0_eq_sv]; exact gpath_sv hL _ _ (dv_le δ) (dv_lt δ)
  rw [hg]
  have htail : (b1 : PeriodicLatticeEdge L) ∉ pathBonds (coarseShift (o0 : PeriodicLatticeSite L) 1 0) [] := by
    simp [pathBonds]
  split_ifs with h
  · rcases h with rfl | rfl
    · rw [A_path000, show (sv (dv d000) : PeriodicLatticeSite L) = o0 by
          rw [o0_eq_sv]; congr 1; funext μ; fin_cases μ <;> rfl]
      rw [hol_cfg1_cons_b1 g [0] (by rw [coarseShift_one, o0_eq_sv, shift_sv]; exact not_mem_of_avoids hL _ _ A_tail)]
      show 1 * g * (1 : SU2)⁻¹ * g⁻¹ = 1
      group
    · rw [A_path100, hol_cfg1_cons_b1 g [] htail, hol_cfg1_of_not_mem g _ _ (not_mem_of_avoids hL _ _ A_e0),
        hol_cfg1_of_not_mem g _ _ (not_mem_of_avoids hL _ _ A_cP1)]
      group
  · have h' : δ ≠ d000 ∧ δ ≠ d100 := ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
    obtain ⟨h1, h2, h3⟩ := A_paths_avoid δ h'.1 h'.2
    have e1 := not_mem_of_avoids (L := L) hL _ _ h1
    rw [← o0_eq_sv] at e1
    rw [hol_cfg1_of_not_mem g _ _ e1, hol_cfg1_of_not_mem g _ _ (not_mem_of_avoids hL _ _ h2),
      hol_cfg1_of_not_mem g _ _ (not_mem_of_avoids hL _ _ h3)]
    group

theorem avgSum_cfg1_gen (g : SU2) :
    (∑ x ∈ stepBlockOf (o0 : PeriodicLatticeSite L) 1 2,
        (((2 : ℕ) : ℚ) ^ 3)⁻¹ • su2Log (loopVar 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L) (o0, 0) x))
      = (6 : ℕ) • ((((2 : ℕ) : ℚ) ^ 3)⁻¹ • su2Log g⁻¹) := by
  rw [o0_eq_sv, stepBlock_sv _ (w0_ok hL), Finset.sum_image (fun δ _ δ' _ h => sv_inj _ (w0_ok hL) h)]
  rw [← o0_eq_sv]
  simp_rw [emb_eq, loopVar_cfg1_gen hL]
  rw [← card_bad, ← Finset.sum_const, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  split_ifs <;> simp_all

theorem ubar_cfg1_gen (g : SU2) :
    stridedBlockedGauge su2LogExp 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L) (o0, 0)
      = su2Exp ((6 : ℕ) • ((((2 : ℕ) : ℚ) ^ 3)⁻¹ • su2Log g⁻¹)) * g := by
  unfold stridedBlockedGauge
  rw [su2LogExp_exp, ← avgSum_cfg1_gen hL g, coarseBondVar_cfg1_gen hL]
  rfl

theorem sBlock_o_gen (h g : SU2) :
    sBlock 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L) (cfg1 h) (o0 : PeriodicLatticeSite L)
      = (((2 : ℕ) : ℚ) ^ 3)⁻¹ • su2Log ((h * g) * g⁻¹) := by
  have htail : (b1 : PeriodicLatticeEdge L) ∉ pathBonds (coarseShift (o0 : PeriodicLatticeSite L) 1 0) [] := by
    simp [pathBonds]
  unfold sBlock
  rw [o0_eq_sv, stepBlock_sv _ (w0_ok hL), Finset.sum_image (fun δ _ δ' _ hh => sv_inj _ (w0_ok hL) hh)]
  simp_rw [emb_eq]
  rw [Finset.sum_eq_single d100]
  · rw [rProd_eq, gpath_sv hL _ _ (dv_le d100) (dv_lt d100), A_path100, cfg1_mul, ← o0_eq_sv,
      hol_cfg1_cons_b1 _ [] htail, hol_cfg1_cons_b1 _ [] htail]
  · intro δ _ hδ
    have e := not_mem_of_avoids (L := L) hL _ _ (A_rprod δ hδ)
    rw [rProd_eq, gpath_sv hL _ _ (dv_le δ) (dv_lt δ), cfg1_mul, hol_cfg1_of_not_mem _ _ _ e,
      hol_cfg1_of_not_mem _ _ _ e]
    simp
  · intro hh; exact absurd (Finset.mem_univ _) hh

theorem sBlock_cP_gen (h g : SU2) :
    sBlock 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L) (cfg1 h) (sv v2) = 0 := by
  unfold sBlock
  rw [stepBlock_sv _ (v2_ok hL), Finset.sum_image (fun δ _ δ' _ hh => sv_inj _ (v2_ok hL) hh)]
  refine Finset.sum_eq_zero (fun δ _ => ?_)
  have hle : ∀ μ, v2 μ ≤ v2d δ μ := fun μ => by simp [v2d]
  have hlt : ∀ μ, v2d δ μ < 4 := fun μ => by have := (δ μ).isLt; fin_cases μ <;> simp [v2d, v2] <;> omega
  have hx : (sv (fun μ => v2 μ + (δ μ : ℕ)) : PeriodicLatticeSite L) = sv (v2d δ) := rfl
  have e := not_mem_of_avoids (L := L) hL _ _ (A_rprodP δ)
  rw [hx, rProd_eq, gpath_sv hL _ _ hle hlt, cfg1_mul, hol_cfg1_of_not_mem _ _ _ e, hol_cfg1_of_not_mem _ _ _ e]
  simp

theorem rawStep_aT_gen {t : ℝ} (ht0 : 0 < t) (htpi : t < Real.pi) :
    rawStep 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L) (expCfgX (aT t)) (o0, 0)
      = torus (3 * Real.pi / 4 + t / 8) := by
  have hn : su2NegOne⁻¹ = su2NegOne := negOne_inv
  have hlog1 : su2Log ((torus t * su2NegOne) * su2NegOne⁻¹) = psiR t := by
    rw [mul_assoc, mul_inv_cancel, mul_one, su2Log_torus ht0.le htpi]
  have hinv : (torus t * su2NegOne)⁻¹ = torus (Real.pi - t) := by
    rw [mul_inv_rev, hn, torus_inv, ← torus_pi, ← torus_add]; ring_nf
  have hlog2 : su2Log (torus t * su2NegOne)⁻¹ = psiR (Real.pi - t) := by
    rw [hinv, su2Log_torus (by linarith) (by linarith)]
  rw [rawStep_simp, expCfgX_aT, cfg1_mul]
  dsimp only
  rw [ubar_cfg1_gen hL, ubar_cfg1_gen hL, sBlock_o_gen hL, cPlus_sv, sBlock_cP_gen hL, hlog1, hlog2, hn, su2Log_center]
  simp only [smul_zero, su2Exp_zero, one_mul, mul_one, qsmul_psiR, nsmul_psiR, neg_psiR, su2Exp_psiR]
  rw [← torus_pi, torus_inv]
  simp only [← torus_add]
  congr 1
  push_cast
  ring

theorem qStepX_aT_val_gen {t : ℝ} (ht0 : 0 < t) (htpi : t < Real.pi) :
    qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L) (aT t) (o0, 0) 0 = 3 * Real.pi / 4 + t / 8 := by
  unfold qStepX
  rw [rawStep_aT_gen hL ht0 htpi, su2Log_torus (by positivity) (by linarith [Real.pi_pos]), fromM2_psiR]

theorem qStepX_not_differentiableAt_gen :
    ¬ DifferentiableAt ℝ (qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L)) 0 := by
  intro hd
  have hc := hd.continuousAt
  set F : ℝ → ℝ := fun t => qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L) (aT t) (o0, 0) 0 with hF
  have hcont_aT : Continuous (fun t : ℝ => (aT t : XS L)) := by
    have : (fun t : ℝ => (aT t : XS L)) = fun t => t • aT 1 := funext aT_eq_smul
    rw [this]; exact continuous_id.smul continuous_const
  have hFc : ContinuousAt F 0 := by
    have h1 : ContinuousAt (fun t : ℝ => qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L) (aT t)) 0 := by
      have : (aT 0 : XS L) = 0 := aT_zero
      refine ContinuousAt.comp (g := qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L)) ?_ hcont_aT.continuousAt
      rw [this]; exact hc
    exact ((continuous_apply 0).continuousAt.comp ((continuous_apply ((o0, 0) : PeriodicLatticeEdge L)).continuousAt.comp h1))
  have hF0 : F 0 = 0 := by
    simp only [hF, aT_zero, qStepX_zero]; rfl
  have hlim1 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have h := hFc.tendsto
    rw [hF0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : F =ᶠ[𝓝[>] 0] fun t => 3 * Real.pi / 4 + t / 8 := by
    have : Set.Ioo (0 : ℝ) Real.pi ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT Real.pi_pos
    filter_upwards [this] with t ht
    exact qStepX_aT_val_gen hL ht.1 ht.2
  have hlim2 : Tendsto F (𝓝[>] 0) (𝓝 (3 * Real.pi / 4 + 0 / 8)) := by
    refine Tendsto.congr' hev.symm ?_
    exact ((continuous_const.add (continuous_id.div_const 8)).tendsto 0).mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique hlim1 hlim2
  have hp := Real.pi_pos
  linarith

/-- **THE JUNK JET, any torus with ≥ 4 sites per direction.** -/
theorem QlinStepX_bad_eq_zero_gen : QlinStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L) = 0 :=
  fderiv_zero_of_not_differentiableAt (qStepX_not_differentiableAt_gen hL)

end loops

#print axioms qStepX_aT_val_gen
#print axioms qStepX_not_differentiableAt_gen
#print axioms QlinStepX_bad_eq_zero_gen

end AdalyFormal.URLocalityR8
