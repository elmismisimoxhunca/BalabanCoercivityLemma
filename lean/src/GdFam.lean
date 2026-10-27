import GdGeo
import GdGap

/-!
# GdFam -- on the boundary-twist family `U = Uth (Ω₀) θ` (interior flat) the second-order source term vanishes: `G1inv = Ginv`, hence the guard gap `GapAt`
reduces to `IsUnit Ginv → IsUnit (Q G Q*)`.  (So an IVT on `G1inv(θ)` along this family is the old IVT on `Ginv(θ)`; it cannot separate the two singular points.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLane2
open AdalyFormal.NonVac
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable (sD sJ : PlaqSel) (P : IngrBParams)

/-- **`G1inv = Ginv` on the twist family.** -/
theorem G1invS_eq_Ginv_theta {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h3 : 3 ≤ R * M) (θ : ℝ)
    (hU : P.U = Uth (P.S.Om 0) θ) : G1invS sD sJ P = (dataS sD sJ P).Ginv :=
  G1invS_eq_Ginv_of sD sJ P (fun b hb1 hb2 => JfS_vanish sJ P hS hell h3 θ hU b hb1 hb2)

/-- on the twist family the gap is `IsUnit Ginv → IsUnit (Q G Q*)`. -/
theorem GapAt_theta_iff {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h3 : 3 ≤ R * M) (θ : ℝ)
    (hU : P.U = Uth (P.S.Om 0) θ) :
    GapAt sD sJ P ↔ (IsUnit (dataS sD sJ P).Ginv →
      IsUnit (((dataS sD sJ P).Q.comp (dataS sD sJ P).G).comp (dataS sD sJ P).Qs)) := by
  have h := G1invS_eq_Ginv_theta sD sJ P hS hell h3 θ hU
  have hN : GenS.NmatS sD sJ P = ((dataS sD sJ P).Q.comp (dataS sD sJ P).G).comp (dataS sD sJ P).Qs := by
    unfold GenS.NmatS BaseDataS.G1 BaseDataS.G
    rw [h]
  unfold GapAt
  rw [h, hN]
  exact ⟨fun H hu => (H hu).2, fun H hu => ⟨hu, H hu⟩⟩

#print axioms G1invS_eq_Ginv_theta
#print axioms GapAt_theta_iff

/-- the `τ`-extraction does not read level 0, hence kills the level-0 part of any field (needs `1 ≤ k`). -/
theorem tau_level0 (hk : 1 ≤ P.k) (Jf : BondFnL2 P.Lf) : P.tau (level0 P.G Jf) = 0 := by
  classical
  refine PiLp.ext (fun e => ?_)
  unfold IngrBParams.tau tauExt
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  split_ifs with hb
  · simp [level0, Fin.last]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  · simp

/-- on the twist family the `J`-term of `genFormS` vanishes: `genFormS B = η⟨τ*B, N⁻¹ τ*B⟩ − a⟨B,B⟩` with `N = Q G Q*`. -/
theorem genFormS_theta {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h3 : 3 ≤ R * M) (θ : ℝ)
    (hU : P.U = Uth (P.S.Om 0) θ) (hk : 1 ≤ P.k) (B : BondFnL2 P.Lu) :
    GenS.genFormS sD sJ P B = GenS.firstTermS sD sJ P B - P.a * ⟪B, B⟫ := by
  have hJ := fun b hb1 hb2 => JfS_vanish sJ P hS hell h3 θ hU b hb1 hb2
  have hJe := dataS_J_eq_Qs sD sJ P hJ
  have hz : ⟪H1inS sD sJ P (P.D2in B), JfS sJ P⟫ = 0 := by
    unfold H1inS
    simp only [ContinuousLinearMap.comp_apply]
    have h1 : ⟪iE P.G ((dataS sD sJ P).H1 (G1invS sD sJ P) (ContinuousLinearMap.adjoint P.tau (P.D2in B))), JfS sJ P⟫
        = ⟪(dataS sD sJ P).J, (dataS sD sJ P).H1 (G1invS sD sJ P) (ContinuousLinearMap.adjoint P.tau (P.D2in B))⟫ := by
      rw [real_inner_comm]; exact (pE_inner_left P.G _ _).symm
    rw [h1, hJe, real_inner_comm]
    apply inner_H1_Qs
    rw [ContinuousLinearMap.adjoint_inner_left]
    rw [tau_level0 P hk]; simp
  unfold GenS.genFormS
  rw [hz]; ring

#print axioms genFormS_theta

/-- **consequence for the guarded statement on the twist family.**  `P428Target8SG selAll sJ` forces, at every twist angle `θ`
(NV slab, ell = 2, k = 2, a = 1, large `m`, `R ≥ 18`, any admissible `α₀`): `IsUnit Ginv(U_θ) → IsUnit (Q G Q*)`. -/
theorem SG_forces_NG_unit_theta (sJ : PlaqSel) (h : P428Target8SG selAll sJ) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 18 ≤ R →
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ α₀ : ℝ, 0 < α₀ → (12 : ℝ) * (2 ^ m : ℕ) * α₀ ≤ a₀ → ∀ θ : ℝ,
        IsUnit (dataS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
            (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R))).Ginv →
        IsUnit (((dataS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
            (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R))).Q.comp
          (dataS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
            (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R))).G).comp
          (dataS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
            (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) 1 (LamN (2 ^ m) R))).Qs) := by
  obtain ⟨m₀, hm₀, hm⟩ := SG_forces_gap_slab sJ h
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hm m hm'
  refine ⟨R₀, fun R hR hR18 => ?_⟩
  obtain ⟨a₀, ha₀, hall⟩ := hR₀ R hR hR18
  refine ⟨a₀, ha₀, fun α₀ hα hαS θ => ?_⟩
  have hM : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hM2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (le_trans hm₀ hm')
  have hdvd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hell : 2 ≤ 2 := le_rfl
  have hell0 : 0 < 2 := by norm_num
  have G := slabGeo_inst (ell := 2) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := 2) hell hM hR18
  have hN : ∀ μ, scaleUp 2 2 (nvLu (2 ^ m) R) μ + 1 = nvN 2 (2 ^ m) R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible 2 (2 ^ m) R 2 (SlabNv 2 (2 ^ m) R) := slab3_admissible G hN
  have hcov : CoversOm0p 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) := slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  have hcls : ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹ (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) :=
    ⟨hcov, perCubeRegular2_of_one_on_om0 _ hAdm.1 hα hM (by norm_num) hell0 (by positivity) _
      (fun e he _ => Uth_in _ _ e he)⟩
  have hgap := hall α₀ hα hαS _ hcls
  have h3 : 3 ≤ R * 2 ^ m := by nlinarith
  exact ((GapAt_theta_iff selAll sJ _ (M := 2 ^ m) (R := R) hAdm (by norm_num) h3 θ rfl).mp hgap)

#print axioms SG_forces_NG_unit_theta

#print axioms tau_level0

end AdalyFormal.D1Guarded
