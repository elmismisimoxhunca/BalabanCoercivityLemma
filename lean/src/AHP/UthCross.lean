import D1Main
import D1Final
import GdGap2
import GdFam
import GdR5b
import GdR6a
import GdR6b

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.FidelityGuarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.D1Guarded
open AdalyFormal.NonVac

/-- Audit wrapper for existing flat positivity. -/
theorem Ginv_lit_psd_at_zero
    {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (ha : 0 ≤ a) :
    PSD (dataS selAll selAll (Pth ell k Lu hell0 S a Lam 0)).Ginv := by
  exact Ginv_psd_flat hell0 a Lam selAll selAll ha

/-- This in-class crossing fails the guard; it does not refute the guarded headline. -/
theorem Uth_hits_nonunit
    {m R : ℕ} (hm : 1 ≤ m) (hR : 18 ≤ R)
    {α₀ : ℝ} (hα : 0 < α₀) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < Real.pi ∧
      ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R)
        α₀ (((2 : ℝ) ^ 2)⁻¹)
        (Uth ((SlabNv 2 (2 ^ m) R).Om 0) θ) ∧
      ¬ IsUnit
        (dataS selAll selAll
          (Pth 2 2 (nvLu (2 ^ m) R) (by norm_num)
            (SlabNv 2 (2 ^ m) R) 1 (LamN (2 ^ m) R) θ)).Ginv := by
  have hM : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hM2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hdvd : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hell : 2 ≤ 2 := le_rfl
  have hell0 : 0 < 2 := by norm_num
  have G := slabGeo_inst (ell := 2) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := 2) hell hM hR
  have hN : ∀ μ, scaleUp 2 2 (nvLu (2 ^ m) R) μ + 1 = nvN 2 (2 ^ m) R :=
    fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible 2 (2 ^ m) R 2 (SlabNv 2 (2 ^ m) R) := slab3_admissible G hN
  have hcov : CoversOm0p 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) :=
    slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  obtain ⟨x, hbd⟩ := SlabNv_bdpt hell hdvd hM hR
  have hroom : 17 * 2 ≤ R * 2 ^ m := by nlinarith
  obtain ⟨θ, h0, h1, hnu⟩ := exists_nonunit_Ginv selAll
    (ell := 2) (M := 2 ^ m) (R := R) (k := 2) (Lu := nvLu (2 ^ m) R)
    hell0 (S := SlabNv 2 (2 ^ m) R) 1 (LamN (2 ^ m) R)
    hAdm hell hroom hbd (by norm_num) (by norm_num)
  refine ⟨θ, h0, h1, ?_, hnu⟩
  exact ⟨hcov, perCubeRegular2_of_one_on_om0 _ hAdm.1 hα hM
    (by norm_num) hell0 (by positivity) _ (fun e he _ => Uth_in _ _ e he)⟩

/-- Equality of actual operators, including at singular points of the flat-interior path. -/
theorem Uth_singular_is_not_a_split
    {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (hS : Admissible ell M R k S) (h3 : 3 ≤ R * M)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (θ : ℝ) :
    let P := Pth ell k Lu hell0 S a Lam θ
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) = 0 ∧
    G1invS selAll selAll P = (dataS selAll selAll P).Ginv ∧
    (IsUnit (G1invS selAll selAll P) ↔
      IsUnit ((dataS selAll selAll P).Ginv -
        (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))) := by
  dsimp only
  let P := Pth ell k Lu hell0 S a Lam θ
  have hloc := G1invS_eq_Ginv_theta selIn selIn P hS hell0 h3 θ rfl
  have hspec := (dataS selIn selIn P).G1inv_unique (G1invS_spec selIn selIn P)
    ((dataS selIn selIn P).isG1inv_sub (dataS_laws selIn selIn P))
  have hz : (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) = 0 := by
    rw [hloc] at hspec
    exact sub_eq_self.mp hspec.symm
  have hall := G1invS_eq_Ginv_theta selAll selAll P hS hell0 h3 θ rfl
  refine ⟨hz, hall, ?_⟩
  change IsUnit (G1invS selAll selAll P) ↔ IsUnit ((dataS selAll selAll P).Ginv - _)
  rw [hz, sub_zero, hall]

end AdalyFormal.FidelityGuarded

