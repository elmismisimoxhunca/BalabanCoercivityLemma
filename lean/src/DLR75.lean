import DLR72
import DLR71
import MF6d
import ZXR2Unit3

/-!
# DL75 -- the UNIT-level pieces of `D̃⁽²⁾ = L⁻¹ h C̃⁽²⁾` in `ℓ¹`, at a curved unit background

* `Q1jet_row_congr` : the row `c` of `Q₁(V)` (`= ℓ⁻¹ D qStepX(0)`) reads only `VisStep 1 ℓ c` (DL28);
* `Q1_drift_local` : `‖(Q₁(V) − Q₁(1))B(c)‖ ≤ (8ℓε₀ + 8κ)·Σ_{e∈Vis(c)} ‖B e‖`  (MF6b `Q1jet_sub_flat_le` on the restricted field);
* `iotaD_l1` : `Σ_b ‖ι_D w b‖ ≤ Σ_d ‖w d‖`;
* **`H0_drift_l1`** : `Σ_d ‖(H₀(V) − H₀(1))w d‖ ≤ 192(8ℓε₀ + 8κ) Σ_d ‖w d‖`  (`H₀(1) = ℓ⁻³ id`, ZXR2Unit3);
* **`H0inv_l1`** : if `H₀(V)` is bijective and `δ := 192(8ℓε₀+8κ) < ℓ⁻³`, `Σ‖H₀(V)⁻¹ v‖ ≤ Σ‖v‖/(ℓ⁻³ − δ)`;
* **`hLift_l1`** : `Σ_b ‖h f b‖ ≤ Σ_c ‖f c‖/(ℓ⁻³ − δ)`  (`h = ι_D H₀⁻¹ ρ`);
* **`C2tilde_l1`** : `Σ_c ‖C̃⁽²⁾(B)(c)‖ ≤ K2s ℓ · Σ_b ‖B b‖²`  (DL69 at stride 1; loops from `loop_dev`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.IngredientFamilyR2 (QlinStepX C2StepX RegBg XS toM2 toM2_mem fromM2 suCoordF suCoordFInv Q1jet
  C2tilde flatCfg Dset rhoD iotaD H0 H0inv hLift H0_H0inv H0_q1SU2_apply Q1jet_flat)
open AdalyFormal.NonflatJet (suOf rhoOf)
open AdalyFormal.BondComposite (sum_le_of_injective sum_edge_eq_coarse1)
open EstimatesLayer.E1E3 (e2Majorant e2Majorant_nonneg)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

theorem Q1jet_row_congr (ell : ℕ) (V : PeriodicLinkConfiguration SU2 L) (hreg : RegBg 1 ell V)
    (B B' : Bond L → SuTwo) (c : CoarseBond L ell) (h : ∀ e, VisStep 1 ell (c.1.1, c.2) e → B e = B' e) :
    Q1jet ell V B c = Q1jet ell V B' c := by
  rw [AdalyFormal.IngredientFamilyR2.Q1jet_eq_r7 ell V hreg B c, AdalyFormal.IngredientFamilyR2.Q1jet_eq_r7 ell V hreg B' c]
  have h0 := QlinStepX_row_local 1 ell V hreg (c.1.1, c.2) (suCoordF B - suCoordF B') (fun e he => by
    show fromM2 ((B e : SuTwo) : M2) - fromM2 ((B' e : SuTwo) : M2) = 0
    rw [h e he, sub_self])
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  congr 1
  apply Subtype.ext
  show toM2 (QlinStepX 1 ell V (suCoordF B) (c.1.1, c.2)) = toM2 (QlinStepX 1 ell V (suCoordF B') (c.1.1, c.2))
  rw [h0]

open Classical in
theorem Q1_drift_local {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (hreg : RegBg 1 ell V) (B : Bond L → SuTwo) (c : CoarseBond L ell) :
    ‖Q1jet ell V B c - Q1jet ell flatCfg B c‖
      ≤ (8 * ell * ε0 + 8 * e2Majorant (rhoOf ell ε0)) *
          ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖B e‖ := by
  set B' : Bond L → SuTwo := fun e => if VisStep 1 ell (c.1.1, c.2) e then B e else 0 with hB'
  have h1 := Q1jet_row_congr ell V hreg B B' c (fun e he => by simp [hB', he])
  have h2 := Q1jet_row_congr ell flatCfg (AdalyFormal.NonflatJet.regBg_flat ell) B B' c (fun e he => by simp [hB', he])
  rw [h1, h2]
  set M := ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖B e‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun e _ => norm_nonneg _)
  refine AdalyFormal.M0Finish.R7.Q1jet_sub_flat_le hell hdvd V ε0 hε0 hV hsmall hreg B' M hM0 (fun b => ?_) c
  by_cases hb : VisStep 1 ell (c.1.1, c.2) b
  · simp only [hB', if_pos hb]
    exact Finset.single_le_sum (f := fun e => ‖B e‖) (fun e _ => norm_nonneg _)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  · simp only [hB', if_neg hb, norm_zero]; exact hM0

theorem iotaD_l1 {ell : ℕ} (Lam : Set (PeriodicLatticeSite L)) (w : Dset L ell Lam → SuTwo) :
    ∑ b : Bond L, ‖iotaD ell Lam w b‖ ≤ ∑ d : Dset L ell Lam, ‖w d‖ := by
  classical
  have h1 : ∀ b : Bond L, ‖iotaD ell Lam w b‖
      ≤ ∑ d : Dset L ell Lam, if b = AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell d.1 then ‖w d‖ else 0 := by
    intro b
    show ‖∑ d : Dset L ell Lam, if b = AdalyFormal.Balaban.ReparamCDisjoint.droppedBondLast ell d.1 then w d else 0‖ ≤ _
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    split_ifs <;> simp
  refine (Finset.sum_le_sum fun b _ => h1 b).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_ite_eq']
  simp

open Classical in
theorem H0_drift_l1 {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2) (hreg : RegBg 1 ell V)
    (w : Dset L ell Lam → SuTwo) :
    ∑ d : Dset L ell Lam, ‖H0 Lam (Q1jet ell V) w d - H0 Lam (AdalyFormal.IngredientFamily.q1SU2 ell) w d‖
      ≤ 192 * (8 * ell * ε0 + 8 * e2Majorant (rhoOf ell ε0)) * ∑ d : Dset L ell Lam, ‖w d‖ := by
  set κ := 8 * ell * ε0 + 8 * e2Majorant (rhoOf ell ε0) with hκ
  have hκ0 : 0 ≤ κ := by
    have : 0 ≤ e2Majorant (rhoOf ell ε0) := e2Majorant_nonneg (by unfold rhoOf; positivity)
    rw [hκ]; positivity
  set ι := iotaD ell Lam w with hι
  have hflat : ∀ c : CoarseBond L ell, AdalyFormal.IngredientFamily.q1SU2 ell ι c = Q1jet ell flatCfg ι c :=
    fun c => (Q1jet_flat ell hell hdvd ι c).symm
  have hd : ∀ d : Dset L ell Lam, H0 Lam (Q1jet ell V) w d - H0 Lam (AdalyFormal.IngredientFamily.q1SU2 ell) w d
      = Q1jet ell V ι d.1 - Q1jet ell flatCfg ι d.1 := by
    intro d
    show Q1jet ell V ι d.1 - AdalyFormal.IngredientFamily.q1SU2 ell ι d.1 = _
    rw [hflat]
  simp_rw [hd]
  set F : CoarseBond L ell → ℝ := fun c => ‖Q1jet ell V ι c - Q1jet ell flatCfg ι c‖ with hF
  have hF0 : ∀ c, 0 ≤ F c := fun c => norm_nonneg _
  have h1 : ∑ d : Dset L ell Lam, F d.1 ≤ ∑ c : CoarseBond L ell, F c :=
    sum_le_of_injective (fun d : Dset L ell Lam => d.1) Subtype.val_injective F hF0
  refine h1.trans ?_
  have h2 : ∀ c : CoarseBond L ell, F c ≤ κ * ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖ι e‖ :=
    fun c => Q1_drift_local hell hdvd V ε0 hε0 hV hsmall hreg ι c
  refine (Finset.sum_le_sum fun c _ => h2 c).trans ?_
  rw [← Finset.mul_sum]
  have hn : ∀ ν, 1 * ell ∣ L ν + 1 := fun ν => by rw [one_mul]; exact hdvd ν
  have h3 := sum_vis_le 1 ell Nat.one_pos hell hn (fun e => ‖ι e‖) (fun e => norm_nonneg _)
  have h4 := sum_one_mul (Lq := L) ell (fun y μ => ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (y, μ) e), ‖ι e‖)
  have h5 : ∑ e : CoarseBond L 1, ‖ι (e.1.1, e.2)‖ = ∑ e : Bond L, ‖ι e‖ :=
    (sum_edge_eq_coarse1 (fun e => ‖ι e‖)).symm
  have h6 := iotaD_l1 Lam w
  rw [h4]
  have h7 : ∑ c : CoarseBond L (1 * ell), ∑ e ∈ Finset.univ.filter (fun e => VisStep 1 ell (c.1.1, c.2) e), ‖ι e‖
      ≤ 192 * ∑ d : Dset L ell Lam, ‖w d‖ := by
    refine h3.trans ?_
    rw [h5]
    exact mul_le_mul_of_nonneg_left h6 (by norm_num)
  have := mul_le_mul_of_nonneg_left h7 hκ0
  linarith

/-- the inverse in `ℓ¹` -/
theorem H0inv_l1 {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (V : PeriodicLinkConfiguration SU2 L) (δ : ℝ)
    (hb : Function.Bijective (H0 Lam (Q1jet ell V))) (hδ : δ < 1 / (ell : ℝ) ^ 3)
    (hdrift : ∀ w : Dset L ell Lam → SuTwo, ∑ d, ‖H0 Lam (Q1jet ell V) w d - H0 Lam (AdalyFormal.IngredientFamily.q1SU2 ell) w d‖
      ≤ δ * ∑ d, ‖w d‖)
    (v : Dset L ell Lam → SuTwo) :
    ∑ d, ‖H0inv Lam (Q1jet ell V) v d‖ ≤ (∑ d, ‖v d‖) / (1 / (ell : ℝ) ^ 3 - δ) := by
  set u := H0inv Lam (Q1jet ell V) v with hu
  have hHu : H0 Lam (Q1jet ell V) u = v := H0_H0inv Lam _ hb v
  have hflat : ∀ d, H0 Lam (AdalyFormal.IngredientFamily.q1SU2 ell) u d = ((1 : ℝ) / (ell : ℝ) ^ 3) • u d :=
    fun d => H0_q1SU2_apply hell hdvd Lam u d
  have hpt : ∀ d, ((1 : ℝ) / (ell : ℝ) ^ 3) * ‖u d‖
      ≤ ‖v d‖ + ‖H0 Lam (Q1jet ell V) u d - H0 Lam (AdalyFormal.IngredientFamily.q1SU2 ell) u d‖ := by
    intro d
    have e1 : ((1 : ℝ) / (ell : ℝ) ^ 3) • u d
        = v d - (H0 Lam (Q1jet ell V) u d - H0 Lam (AdalyFormal.IngredientFamily.q1SU2 ell) u d) := by
      rw [← hflat d, ← hHu]; abel
    have e2 : ‖((1 : ℝ) / (ell : ℝ) ^ 3) • u d‖ = ((1 : ℝ) / (ell : ℝ) ^ 3) * ‖u d‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    rw [← e2, e1]
    exact norm_sub_le _ _
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => hpt d)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hdr := hdrift u
  have hpos : 0 < 1 / (ell : ℝ) ^ 3 - δ := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith

theorem hLift_l1 {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (V : PeriodicLinkConfiguration SU2 L) (δ : ℝ)
    (hb : Function.Bijective (H0 Lam (Q1jet ell V))) (hδ : δ < 1 / (ell : ℝ) ^ 3)
    (hdrift : ∀ w : Dset L ell Lam → SuTwo, ∑ d, ‖H0 Lam (Q1jet ell V) w d - H0 Lam (AdalyFormal.IngredientFamily.q1SU2 ell) w d‖
      ≤ δ * ∑ d, ‖w d‖)
    (f : CoarseBond L ell → SuTwo) :
    ∑ b : Bond L, ‖hLift Lam (Q1jet ell V) f b‖ ≤ (∑ c, ‖f c‖) / (1 / (ell : ℝ) ^ 3 - δ) := by
  have hpos : 0 < 1 / (ell : ℝ) ^ 3 - δ := by linarith
  have h1 := iotaD_l1 Lam (H0inv Lam (Q1jet ell V) (rhoD ell Lam f))
  have h2 := H0inv_l1 hell hdvd Lam V δ hb hδ hdrift (rhoD ell Lam f)
  have h3 : ∑ d : Dset L ell Lam, ‖rhoD ell Lam f d‖ ≤ ∑ c, ‖f c‖ :=
    sum_le_of_injective (fun d : Dset L ell Lam => d.1) Subtype.val_injective (fun c => ‖f c‖) (fun c => norm_nonneg _)
  calc ∑ b : Bond L, ‖hLift Lam (Q1jet ell V) f b‖
      = ∑ b : Bond L, ‖iotaD ell Lam (H0inv Lam (Q1jet ell V) (rhoD ell Lam f)) b‖ := rfl
    _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ (∑ c, ‖f c‖) / (1 / (ell : ℝ) ^ 3 - δ) := div_le_div_of_nonneg_right h3 hpos.le

theorem C2tilde_l1 {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L) (hreg : RegBg 1 ell V) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hloop : 8 * (ell : ℝ) * ε0 ≤ 1 / 16) (B : Bond L → SuTwo) :
    ∑ c : CoarseBond L ell, ‖C2tilde ell V B c‖ ≤ K2s ell * ∑ b : Bond L, ‖B b‖ ^ 2 := by
  have hn : ∀ ν, 1 * ell ∣ L ν + 1 := fun ν => by rw [one_mul]; exact hdvd ν
  have hL1 : ∀ ν, 1 ∣ L ν + 1 := fun ν => one_dvd _
  have hW : ∀ c : CoarseBond L (1 * ell), ∀ x ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1.1 1 ell,
      frobNorm (((AdalyFormal.Balaban.UbarTowerCov.loopVar 1 ell V (c.1.1, c.2) x : SU2) : Mt) - 1) ≤ 1 / 16 :=
    fun c x hx => (loop_dev 1 ell Nat.one_pos hL1 V ε0 hε0 (fun e _ => hV e) (c.1.1, c.2)
      (fun ν => one_dvd _) x hx hell).trans hloop
  have h1 := C2Step_l1 1 ell Nat.one_pos hell hn V hreg hW (suCoordF B)
  have e0 : ∑ c : CoarseBond L ell, ‖C2tilde ell V B c‖
      = ∑ c : CoarseBond L ell, ‖(suCoordFInv (C2StepX 1 ell V (suCoordF B))) (c.1.1, c.2)‖ :=
    Finset.sum_congr rfl (fun c _ => by rw [AdalyFormal.IngredientFamilyR2.C2tilde_eq_r7 ell V hreg B c])
  have e1 : ∑ c : CoarseBond L ell, ‖(suCoordFInv (C2StepX 1 ell V (suCoordF B))) (c.1.1, c.2)‖
      = ∑ c : CoarseBond L (1 * ell), ‖suOf (C2StepX 1 ell V (suCoordF B) (c.1.1, c.2))‖ :=
    sum_one_mul (Lq := L) ell (fun y μ => ‖suOf (C2StepX 1 ell V (suCoordF B) (y, μ))‖)
  have e2 : ∑ e : CoarseBond L 1, ‖suOf (suCoordF B (e.1.1, e.2))‖ ^ 2 = ∑ b : Bond L, ‖B b‖ ^ 2 := by
    rw [← sum_edge_eq_coarse1 (fun e => ‖suOf (suCoordF B e)‖ ^ 2)]
    refine Finset.sum_congr rfl fun b _ => ?_
    show ‖suOf (fromM2 ((B b : SuTwo) : M2))‖ ^ 2 = _
    rw [suOf_fromM2]
  rw [e0, e1]
  refine h1.trans (le_of_eq ?_)
  rw [e2]

#print axioms Q1jet_row_congr
#print axioms Q1_drift_local
#print axioms iotaD_l1
#print axioms H0_drift_l1
#print axioms H0inv_l1
#print axioms hLift_l1
#print axioms C2tilde_l1

end AdalyFormal.DLayer
