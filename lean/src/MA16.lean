import MA15

/-!
# MA16 -- the bridge `Psi <= cwW4` (lane m1_assembly_20261014)

`cwW4_ge_Psi`: the W4 constant `cwW4` of `w4_M1_*` (with `kappa = 1`, `c = 5`, `W = R M ell`, patch constant `cPnf`) is bounded below
by the real-parameter function `Psi` (MA13) at `s = 12 M alpha0`, `x = 1/W`, `K = KG ell M 1 5`, `m = min a (cW/2)`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.M1Assembly

open AdalyFormal.M1Num
open AdalyFormal.M1IMS AdalyFormal.M1GaugeW4 AdalyFormal.TowerLoc
open AdalyFormal.M1NonFlat (epsNF PkA thetaN)

theorem etaC_nonneg (ell W : ℕ) (cs ρ ε1 : ℝ) (hε1 : 0 < ε1) (hρ : 0 ≤ ρ) (hcs : 0 < cs) : 0 ≤ etaC ell W cs ρ ε1 := by
  unfold etaC nuC
  positivity

theorem cwR_mono (ell : ℕ) (x K a ρ ρh ε1 ε2 eX CM cP1 cP2 : ℝ) (hε2 : 0 < ε2)
    (hη0 : 0 ≤ etaR ell x (csOf a ρ) ρh ε1) (hη1 : etaR ell x (csOf a ρ) ρh ε1 < 1) (h : cP1 ≤ cP2) :
    cwR ell x K a ρ ρh ε1 ε2 cP1 eX CM ≤ cwR ell x K a ρ ρh ε1 ε2 cP2 eX CM := by
  unfold cwR
  generalize etaR ell x (csOf a ρ) ρh ε1 = η at hη0 hη1 ⊢
  have hd : 0 < 1 - η := by linarith
  have hDn : 0 < 1 + ((1 + η) * (1 + ε2) / (1 - η) - 1) := by
    have : 0 < (1 + η) * (1 + ε2) / (1 - η) := by apply div_pos <;> nlinarith
    have h1 : 1 ≤ (1 + η) * (1 + ε2) / (1 - η) := by
      rw [le_div_iff₀ hd]; nlinarith
    linarith
  exact div_le_div_of_nonneg_right (sub_le_sub_right h _) hDn.le

theorem cwW4_ge_Psi {ell M R d : ℕ} {a cW α₀ ε1 ε2 : ℝ} (hε2 : 0 < ε2)
    (hdD : epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2)
    (hη0 : 0 ≤ etaC ell (R * M * ell) (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1)
    (hη1 : etaC ell (R * M * ell) (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1 < 1) :
    Psi ell a ε1 ε2 (min a (cW / 2)) (((12 : ℕ) : ℝ) * M * α₀) (((R * M * ell : ℕ) : ℝ)⁻¹) (KG ell M 1 5)
      ≤ cwW4 ell M 1 5 (R * M * ell) a (rhoT ell 12 M α₀) (rho1 12 M α₀) ε1 ε2
          (cPnf ell (R * M * ell) d a cW α₀ ε1 12 M)
          (epsXnum ell (R * M * ell) a (rhoT ell 12 M α₀)) (CMcStar ell M 1 5 a (SstarM ell 12 M α₀)) := by
  have hρ1 : rho1 12 M α₀ = rhoH (((12 : ℕ) : ℝ) * M * α₀) := by unfold rho1 rhoH; rfl
  have hρT : rhoT ell 12 M α₀ = rhoTs ell (((12 : ℕ) : ℝ) * M * α₀) := by
    unfold AdalyFormal.M1GaugeW4.rhoT rhoTs; rw [hρ1]
  have hCM : CMcStar ell M 1 5 a (SstarM ell 12 M α₀)
      = a * Estar ell (Ssr ell (((12 : ℕ) : ℝ) * M * α₀)) ^ 2 * (49 * (ell : ℝ) ^ 2 * KG ell M 1 5) * (1944 * (ell : ℝ) ^ 2) := by
    unfold CMcStar SstarM Ssr; rw [hρ1]
  have hηe : etaC ell (R * M * ell) (csOf a (rhoT ell 12 M α₀)) (rho1 12 M α₀) ε1
      = etaR ell (((R * M * ell : ℕ) : ℝ)⁻¹) (csOf a (rhoTs ell (((12 : ℕ) : ℝ) * M * α₀))) (rhoH (((12 : ℕ) : ℝ) * M * α₀)) ε1 := by
    rw [etaC_eq, hρT, hρ1]
  rw [hηe] at hη0 hη1
  rw [cwW4_eq, epsXnum_eq, hCM, hρT, hρ1]
  unfold Psi
  refine cwR_mono ell _ _ a _ _ ε1 ε2 _ _ _ _ hε2 hη0 hη1 ?_
  unfold cPnf
  rw [etaC_eq, hρT, hρ1]
  have h1 : min a (cW / 2) ≤ min a (cW - epsNF ell (PkA a) (thetaN ell) d) := by
    apply min_le_min le_rfl; linarith
  have hd : 0 ≤ 1 - etaR ell (((R * M * ell : ℕ) : ℝ)⁻¹) (csOf a (rhoTs ell (((12 : ℕ) : ℝ) * M * α₀)))
      (rhoH (((12 : ℕ) : ℝ) * M * α₀)) ε1 := by linarith
  have := mul_le_mul_of_nonneg_left h1 hd
  linarith

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.etaC_nonneg
#print axioms AdalyFormal.M1Assembly.cwR_mono
#print axioms AdalyFormal.M1Assembly.cwW4_ge_Psi
