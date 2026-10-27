import MF6d
import MF6e
import ZXR2Unit3

/-!
# MF6f -- the unit-level perturbation of `C` (3.157): `C_V B̃` vs the flat `C₁ B̃`, in `L²`, volume-free.

With `u_V = H₀(V)⁻¹ ρ Q₁(V) B̃` (so `C_V B̃ = B̃ − ι_D u_V`) and the flat `H₀(1) = ℓ⁻³·id` (`H0_q1SU2_apply`):
`H₀(1)(u₁ − u_V) = ρ (Q₁(1) − Q₁(V)) (C_V B̃)`, hence
  `‖C_V B̃ − C₁ B̃‖² ≤ ℓ⁶ ω² ‖C_V B̃‖²`,  `ω² = 384 (ℓ ε₀)² + 480 e2Majorant(rhoOf ℓ ε₀)²`  (`Q1jet_sub_flat_l2`, ported),
for any unit background `V` with `‖V e − 1‖_F ≤ ε₀` (every link), `rhoOf ℓ ε₀ < π/2`, `RegBg 1 ℓ V`, `H₀(V)` bijective.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace AdalyFormal.M0Finish.R7

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.NonflatJet (rhoOf)
open EstimatesLayer.E1E3

variable {L : PeriodicLatticeExtent}

theorem Cop_apply' {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo)) (B : Bond L → SuTwo) :
    Cop Lam Q B = B - iotaD ell Lam (H0inv Lam Q (rhoD ell Lam (Q B))) := rfl

/-- **`C_V − C₁`, volume-free.** -/
theorem cop_pert {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (hreg : RegBg 1 ell V) (hbV : Function.Bijective (H0 Lam (Q1jet ell V))) (Bt : Bond L → SuTwo) :
    ∑ b : Bond L, ‖Cop Lam (Q1jet ell V) Bt b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2
      ≤ ((ell : ℝ) ^ 3) ^ 2 * (384 * (ell * ε0) ^ 2 + 480 * (e2Majorant (rhoOf ell ε0)) ^ 2)
        * ∑ b : Bond L, ‖Cop Lam (Q1jet ell V) Bt b‖ ^ 2 := by
  classical
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set QV := Q1jet ell V with hQV
  set Q1 := q1SU2 (Lu := L) ell with hQ1
  have hflat : Q1jet ell (flatCfg : PeriodicLinkConfiguration SU2 L) = Q1 := Q1_flat_eq ell hell hdvd
  have hb1 : Function.Bijective (H0 Lam Q1) := by
    refine ⟨?_, ?_⟩
    · intro w w' h
      funext c
      have e1 := congrFun h c
      rw [H0_q1SU2_apply hell hdvd Lam w c, H0_q1SU2_apply hell hdvd Lam w' c] at e1
      have hne : ((1 : ℝ) / (ell : ℝ) ^ 3) ≠ 0 := by positivity
      exact smul_right_injective SuTwo hne e1
    · intro w
      refine ⟨((ell : ℝ) ^ 3) • w, funext fun c => ?_⟩
      rw [map_smul, Pi.smul_apply, H0_q1SU2_apply hell hdvd Lam w c, smul_smul]
      have : (ell : ℝ) ^ 3 * (1 / (ell : ℝ) ^ 3) = 1 := by field_simp
      rw [this, one_smul]
  set uV := H0inv Lam QV (rhoD ell Lam (QV Bt)) with huV
  set u1 := H0inv Lam Q1 (rhoD ell Lam (Q1 Bt)) with hu1
  set X := Cop Lam QV Bt with hX
  have hXe : X = Bt - iotaD ell Lam uV := rfl
  have hdiff : Cop Lam QV Bt - Cop Lam Q1 Bt = iotaD ell Lam (u1 - uV) := by
    rw [Cop_apply', Cop_apply', map_sub]; abel
  -- H₀(1)(u₁ − u_V) = ρ (Q₁ − Q_V) X
  have hHV : H0 Lam QV uV = rhoD ell Lam (QV Bt) := H0_H0inv Lam QV hbV _
  have hH1 : H0 Lam Q1 u1 = rhoD ell Lam (Q1 Bt) := H0_H0inv Lam Q1 hb1 _
  have hkey : H0 Lam Q1 (u1 - uV) = rhoD ell Lam (Q1 X - QV X) := by
    have e1 : H0 Lam Q1 uV = rhoD ell Lam (Q1 (iotaD ell Lam uV)) := rfl
    have e2 : H0 Lam QV uV = rhoD ell Lam (QV (iotaD ell Lam uV)) := rfl
    have hz : rhoD ell Lam (QV Bt - QV (iotaD ell Lam uV)) = 0 := by
      rw [map_sub, ← hHV, ← e2, sub_self]
    calc H0 Lam Q1 (u1 - uV) = rhoD ell Lam (Q1 Bt) - rhoD ell Lam (Q1 (iotaD ell Lam uV)) := by
          rw [map_sub, hH1, e1]
      _ = rhoD ell Lam (Q1 (Bt - iotaD ell Lam uV)) - rhoD ell Lam (QV (Bt - iotaD ell Lam uV)) := by
          rw [map_sub QV, hz, sub_zero, map_sub Q1, map_sub (rhoD ell Lam)]
      _ = rhoD ell Lam (Q1 X - QV X) := by
          rw [hXe, map_sub (rhoD ell Lam)]
  -- pointwise: (u₁ − u_V) c = ℓ³ ((Q₁ − Q_V) X) c
  have hpt : ∀ c : Dset L ell Lam, (u1 - uV) c = ((ell : ℝ) ^ 3) • ((Q1 X - QV X) c.1) := by
    intro c
    have h := congrFun hkey c
    rw [H0_q1SU2_apply hell hdvd Lam (u1 - uV) c] at h
    have h' := congrArg (fun v => ((ell : ℝ) ^ 3) • v) h
    simp only [smul_smul] at h'
    have : (ell : ℝ) ^ 3 * (1 / (ell : ℝ) ^ 3) = 1 := by field_simp
    rw [this, one_smul] at h'
    rw [h']; rfl
  have hE := iotaD_energy hell hdvd Lam (u1 - uV)
  have hdl : ∑ b : Bond L, ‖Cop Lam QV Bt b - Cop Lam Q1 Bt b‖ ^ 2 = bondEnergy (iotaD ell Lam (u1 - uV)) := by
    unfold bondEnergy
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← hdiff]; rfl
  rw [hdl, hE]
  have hsum : ∑ c : Dset L ell Lam, ‖(u1 - uV) c‖ ^ 2
      = ((ell : ℝ) ^ 3) ^ 2 * ∑ c : Dset L ell Lam, ‖(Q1 X - QV X) c.1‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hpt c, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hsum]
  have hsub : ∑ c : Dset L ell Lam, ‖(Q1 X - QV X) c.1‖ ^ 2 ≤ ∑ c : CoarseBond L ell, ‖(Q1 X - QV X) c‖ ^ 2 := by
    have := Finset.sum_le_sum_of_subset_of_nonneg
      (s := (Finset.univ : Finset (Dset L ell Lam)).map (Function.Embedding.subtype _))
      (t := (Finset.univ : Finset (CoarseBond L ell))) (f := fun c => ‖(Q1 X - QV X) c‖ ^ 2)
      (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    rw [Finset.sum_map] at this
    exact this
  have hdr := Q1jet_sub_flat_l2 hell hdvd V ε0 hε0 hV hsmall hreg X
  rw [hflat] at hdr
  have hsym : ∑ c : CoarseBond L ell, ‖(Q1 X - QV X) c‖ ^ 2 = ∑ c : CoarseBond L ell, ‖QV X c - Q1 X c‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Pi.sub_apply, norm_sub_rev]
  have hX2 : bondEnergy X = ∑ b : Bond L, ‖Cop Lam QV Bt b‖ ^ 2 := rfl
  have hl6 : (0 : ℝ) ≤ ((ell : ℝ) ^ 3) ^ 2 := by positivity
  calc ((ell : ℝ) ^ 3) ^ 2 * ∑ c : Dset L ell Lam, ‖(Q1 X - QV X) c.1‖ ^ 2
      ≤ ((ell : ℝ) ^ 3) ^ 2 * ∑ c : CoarseBond L ell, ‖QV X c - Q1 X c‖ ^ 2 := by
        rw [← hsym]; exact mul_le_mul_of_nonneg_left hsub hl6
    _ ≤ ((ell : ℝ) ^ 3) ^ 2 * ((384 * (ell * ε0) ^ 2 + 480 * (e2Majorant (rhoOf ell ε0)) ^ 2) * bondEnergy X) :=
        mul_le_mul_of_nonneg_left hdr hl6
    _ = _ := by rw [hX2]; ring

/-- the flat `C₁` is bounded: `‖C₁ B̃‖ ≤ ‖B̃‖ + ℓ³ ‖Q₁(1) B̃‖` (pointwise in `L²` form). -/
theorem cop_flat_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (Lam : Set (PeriodicLatticeSite L)) (Bt : Bond L → SuTwo) :
    Real.sqrt (∑ b : Bond L, ‖Cop Lam (q1SU2 ell) Bt b‖ ^ 2)
      ≤ Real.sqrt (bondEnergy Bt) + (ell : ℝ) ^ 3 * Real.sqrt (∑ c : CoarseBond L ell, ‖q1SU2 ell Bt c‖ ^ 2) := by
  classical
  set Q1 := q1SU2 (Lu := L) ell
  have hb1 : ∀ w : Dset L ell Lam → SuTwo, H0 Lam Q1 (((ell : ℝ) ^ 3) • w) = w := by
    intro w; funext c
    rw [map_smul, Pi.smul_apply, H0_q1SU2_apply hell hdvd Lam w c, smul_smul]
    have : (ell : ℝ) ^ 3 * (1 / (ell : ℝ) ^ 3) = 1 := by
      have : (0:ℝ) < ell := by exact_mod_cast hell
      field_simp
    rw [this, one_smul]
  have hbij : Function.Bijective (H0 Lam Q1) := by
    refine ⟨?_, fun w => ⟨_, hb1 w⟩⟩
    intro w w' h
    have := congrArg (fun v => ((ell : ℝ) ^ 3) • v) h
    have e : ∀ v, ((ell : ℝ) ^ 3) • H0 Lam Q1 v = v := by
      intro v; funext c
      rw [Pi.smul_apply, H0_q1SU2_apply hell hdvd Lam v c, smul_smul]
      have : (ell : ℝ) ^ 3 * (1 / (ell : ℝ) ^ 3) = 1 := by
        have : (0:ℝ) < ell := by exact_mod_cast hell
        field_simp
      rw [this, one_smul]
    simp only [e w, e w'] at this; exact this
  have hinv : H0inv Lam Q1 (rhoD ell Lam (Q1 Bt)) = ((ell : ℝ) ^ 3) • rhoD ell Lam (Q1 Bt) := by
    apply hbij.1
    rw [H0_H0inv Lam Q1 hbij, hb1]
  have hC : Cop Lam Q1 Bt = Bt - ((ell : ℝ) ^ 3) • iotaD ell Lam (rhoD ell Lam (Q1 Bt)) := by
    rw [Cop_apply', hinv, map_smul]
  -- L² norms as EuclideanSpace norms
  have hnorm : ∀ f : Bond L → SuTwo, Real.sqrt (∑ b : Bond L, ‖f b‖ ^ 2) = ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : Bond L => SuTwo))‖ := by
    intro f; rw [PiLp.norm_eq_of_L2]
  rw [hnorm, hC]
  have hI : ‖(WithLp.toLp 2 (iotaD ell Lam (rhoD ell Lam (Q1 Bt))) : PiLp 2 (fun _ : Bond L => SuTwo))‖
      ≤ Real.sqrt (∑ c : CoarseBond L ell, ‖Q1 Bt c‖ ^ 2) := by
    rw [← hnorm]
    apply Real.sqrt_le_sqrt
    have hE := iotaD_energy hell hdvd Lam (rhoD ell Lam (Q1 Bt))
    unfold bondEnergy at hE
    rw [hE]
    have := Finset.sum_le_sum_of_subset_of_nonneg
      (s := (Finset.univ : Finset (Dset L ell Lam)).map (Function.Embedding.subtype _))
      (t := (Finset.univ : Finset (CoarseBond L ell))) (f := fun c => ‖Q1 Bt c‖ ^ 2)
      (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    rw [Finset.sum_map] at this
    exact this
  have htri := norm_sub_le (WithLp.toLp 2 Bt : PiLp 2 (fun _ : Bond L => SuTwo))
    (WithLp.toLp 2 (((ell : ℝ) ^ 3) • iotaD ell Lam (rhoD ell Lam (Q1 Bt))))
  have hsm : ‖(WithLp.toLp 2 (((ell : ℝ) ^ 3) • iotaD ell Lam (rhoD ell Lam (Q1 Bt))) : PiLp 2 (fun _ : Bond L => SuTwo))‖
      = (ell : ℝ) ^ 3 * ‖(WithLp.toLp 2 (iotaD ell Lam (rhoD ell Lam (Q1 Bt))) : PiLp 2 (fun _ : Bond L => SuTwo))‖ := by
    rw [show (WithLp.toLp 2 (((ell : ℝ) ^ 3) • iotaD ell Lam (rhoD ell Lam (Q1 Bt))) : PiLp 2 (fun _ : Bond L => SuTwo))
        = ((ell : ℝ) ^ 3) • (WithLp.toLp 2 (iotaD ell Lam (rhoD ell Lam (Q1 Bt)))) from rfl, norm_smul,
      Real.norm_eq_abs, abs_of_pos (pow_pos (by exact_mod_cast hell) 3)]
  have hBt : ‖(WithLp.toLp 2 Bt : PiLp 2 (fun _ : Bond L => SuTwo))‖ = Real.sqrt (bondEnergy Bt) := by
    rw [← hnorm]; rfl
  have hsub : (WithLp.toLp 2 (Bt - ((ell : ℝ) ^ 3) • iotaD ell Lam (rhoD ell Lam (Q1 Bt))) : PiLp 2 (fun _ : Bond L => SuTwo))
      = WithLp.toLp 2 Bt - WithLp.toLp 2 (((ell : ℝ) ^ 3) • iotaD ell Lam (rhoD ell Lam (Q1 Bt))) := rfl
  rw [hsub]
  have hl3 : (0 : ℝ) ≤ (ell : ℝ) ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hI hl3]

#print axioms Cop_apply'
#print axioms cop_pert
#print axioms cop_flat_le

end AdalyFormal.M0Finish.R7
