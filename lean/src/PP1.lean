import TL4
import DK1
import M1B
import OGP0

/-!
# TL5 -- the blocked link at level `l` over `Ω_{j0}` in the gauge of `M1Regular12` (generalises DK2 `tower_near` from `l = k`)

`m1_link_loc12` / `m1_plaq_loc12` are GW2 `m1_link12` / `m1_plaq12` (proofs copied; GW2 has no olean).
`tower_link_loc12` : cones of NB25 `link_tower_na_loc` inside `Ω_{j0}` (DK1 `goodBd_pd`, `goodL_pd`; pdist balls)
  ⟹ `dv(Ū^l(U^g)(z,μ)) ≤ ell^l e + 3π (ell²)^l q0`, `e = ρ1/ell^{j0}`, `q0 = ρ1/ell^{2 j0}`, `ρ1 = (4π+4) f M α₀`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.OneGap12

open AdalyFormal.TowerLoc
open AdalyFormal.OneGap12

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_self pdist_coarseShift_le)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.CurvBlock (dv pw PlaqT plaqIn CubeChart cube_link cube_plaq link_tower_na_loc GoodBd goodL)
open AdalyFormal.M1 (bstrat le_bstrat_of_mem)
open AdalyFormal.M1DK (goodBd_pd goodL_pd)

variable {L : PeriodicLatticeExtent}

theorem pdist_shift112 {L : PeriodicLatticeExtent} {x w : PeriodicLatticeSite L} {n : ℕ} (h : pdist x w ≤ n) (d : Fin 3) :
    pdist x (coarseShift w 1 d) ≤ n + 1 := by
  have h1 := pdist_coarseShift_le w 1 d
  have h2 := pdist_triangle x w (coarseShift w 1 d)
  omega

/-- bonds with both endpoints in `Ω_{j0}`. -/
def BInT12 (S : Tower L) (j0 : ℕ) (e : Bond L) : Prop :=
  e.1 ∈ S.Om j0 ∧ periodicLatticeShift e.1 e.2 ∈ S.Om j0

def m1ChartT12 {ell M f k : ℕ} (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds12 S ell M f k α₀ η A) (j0 : ℕ) (hj0 : j0 ≤ k) :
    CubeChart U (BInT12 S j0) η ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1))
      ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 2)) where
  g := g
  A := A
  hA := fun e he => ⟨hB.1 e, hU e, hB.2.1 e j0 (le_bstrat_of_mem hj0 e he.1 he.2)⟩
  hD := fun μ ν x h1 h2 =>
    hB.2.2.1 μ ν x j0 (le_bstrat_of_mem hj0 _ h1.1 h1.2) (le_bstrat_of_mem hj0 _ h2.1 h2.2)

section witness
variable {ell M f k : ℕ} (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
  (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
  (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
  (hB : M1Bounds12 S ell M f k α₀ η A)
include hU hB

theorem m1_link_loc12 (hη : 0 < η) (hell : 1 ≤ ell) (ha0 : 0 ≤ (f : ℝ) * M * α₀) (j0 : ℕ) (hj0 : j0 ≤ k) (b : Bond L)
    (h1 : b.1 ∈ S.Om j0) (h2 : periodicLatticeShift b.1 b.2 ∈ S.Om j0) :
    dv (periodicGaugeTransform g U b) ≤ (4 * Real.pi + 4) * ((f : ℝ) * M * α₀) / (ell : ℝ) ^ j0 := by
  have hK := cube_link hη (m1ChartT12 S U g A hU hB j0 hj0) b ⟨h1, h2⟩
  have hp : (0 : ℝ) < (ell : ℝ) ^ j0 := pow_pos (by exact_mod_cast hell) j0
  have e1 : η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1)) = (f : ℝ) * M * α₀ / (ell : ℝ) ^ j0 := by
    field_simp
  rw [e1] at hK
  refine hK.trans ?_
  apply div_le_div_of_nonneg_right _ hp.le
  have := Real.pi_pos
  nlinarith

theorem m1_plaq_loc12 (hη : 0 < η) (hell : 1 ≤ ell) (ha0 : 0 ≤ (f : ℝ) * M * α₀) (ha1 : (f : ℝ) * M * α₀ ≤ 1)
    (j0 : ℕ) (hj0 : j0 ≤ k) (y : PeriodicLatticeSite L) (ν μ : Fin 3)
    (h1 : y ∈ S.Om j0) (h2 : coarseShift y 1 ν ∈ S.Om j0) (h3 : coarseShift y 1 μ ∈ S.Om j0)
    (h4 : coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0) :
    dv (pw 1 (periodicGaugeTransform g U) y ν μ) ≤ (4 * Real.pi + 4) * ((f : ℝ) * M * α₀) / (ell : ℝ) ^ (2 * j0) := by
  set a1 := (f : ℝ) * M * α₀ with ha1d
  have hp : (0 : ℝ) < (ell : ℝ) ^ j0 := pow_pos (by exact_mod_cast hell) j0
  have hpow : (ell : ℝ) ^ (2 * j0) = ((ell : ℝ) ^ j0) ^ 2 := by rw [← pow_mul, mul_comm]
  have hp1 : (1 : ℝ) ≤ (ell : ℝ) ^ j0 := one_le_pow₀ (by exact_mod_cast hell)
  have hc : coarseShift (coarseShift y 1 μ) 1 ν = coarseShift (coarseShift y 1 ν) 1 μ :=
    AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen y 1 1 μ ν
  have hin : plaqIn (BInT12 S j0) (y, ν, μ) :=
    ⟨⟨h1, h2⟩, ⟨h2, h4⟩, ⟨h3, by show coarseShift (coarseShift y 1 μ) 1 ν ∈ S.Om j0; rw [hc]; exact h4⟩, ⟨h1, h3⟩⟩
  have e1 : η * (a1 * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1)) = a1 / (ell : ℝ) ^ j0 := by field_simp
  have hsmall : η * (a1 * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1)) ≤ 1 := by
    rw [e1, div_le_one hp]; linarith
  have hK0 := cube_plaq hη (m1ChartT12 S U g A hU hB j0 hj0) hsmall (y, ν, μ) hin
  have hK : dv (pw 1 (periodicGaugeTransform g U) y ν μ)
      ≤ 2 * (η ^ 2 * (a1 * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 2)))
        + (4 * Real.pi + 2) * (η * (a1 * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1))) ^ 2 := hK0
  have e2 : η ^ 2 * (a1 * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 2)) = a1 / (ell : ℝ) ^ (2 * j0) := by
    rw [hpow]; field_simp
  rw [e2, e1] at hK
  refine hK.trans ?_
  have hq : (0 : ℝ) < (ell : ℝ) ^ (2 * j0) := by positivity
  have e3 : (a1 / (ell : ℝ) ^ j0) ^ 2 = a1 ^ 2 / (ell : ℝ) ^ (2 * j0) := by rw [hpow]; field_simp
  rw [e3]
  have hpi := Real.pi_pos
  have : 2 * (a1 / (ell : ℝ) ^ (2 * j0)) + (4 * Real.pi + 2) * (a1 ^ 2 / (ell : ℝ) ^ (2 * j0))
      = (2 * a1 + (4 * Real.pi + 2) * a1 ^ 2) / (ell : ℝ) ^ (2 * j0) := by ring
  rw [this]
  apply div_le_div_of_nonneg_right _ hq.le
  nlinarith [mul_le_mul_of_nonneg_left ha1 ha0]

end witness

/-- **the level-`l` blocked link over `Ω_{j0}`** (cones inside `Ω_{j0}`; no wrap condition on the torus beyond `Lu+1 ≥ 3`). -/
theorem tower_link_loc12 {ell M k : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (hT3 : ∀ μ, 3 ≤ Lu μ + 1) {f : ℕ} {α₀ η : ℝ}
    (U : LinkCfg (scaleUp ell k Lu))
    (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (A : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds12 S ell M f k α₀ η A) (hη : 0 < η)
    (ha0 : 0 ≤ (f : ℝ) * M * α₀) (ha1 : (f : ℝ) * M * α₀ ≤ 1)
    (hsm : 4000000 * (ell : ℝ) ^ 2 * ((4 * Real.pi + 4) * ((f : ℝ) * M * α₀)) ≤ 1)
    (j0 l : ℕ) (hj0 : j0 ≤ k) (hl : l ≤ j0) (hlk : l < k)
    (z : PeriodicLatticeSite (scaleUp ell k Lu)) (hz : z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l)) (μ : Fin 3)
    (hcone : ∀ w, pdist z w ≤ 14 * ell ^ l → w ∈ S.Om j0) :
    dv (AdalyFormal.Balaban.BlockedBackground.ubarTowerSU2 ell (periodicGaugeTransform g U) l (z, μ))
      ≤ (ell : ℝ) ^ l * ((4 * Real.pi + 4) * ((f : ℝ) * M * α₀) / (ell : ℝ) ^ j0)
        + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * ((4 * Real.pi + 4) * ((f : ℝ) * M * α₀) / (ell : ℝ) ^ (2 * j0))) := by
  have hs1 : 1 ≤ ell ^ l := Nat.one_le_pow _ _ hell
  set V := periodicGaugeTransform g U with hV
  set ρ1 : ℝ := (4 * Real.pi + 4) * ((f : ℝ) * M * α₀) with hρ1
  set Rp : PeriodicLatticeSite (scaleUp ell k Lu) → Prop :=
    fun w => ∀ ν μ' : Fin 3, plaqIn (BInT12 S j0) (w, ν, μ') with hRp
  set Rl : PeriodicLatticeEdge (scaleUp ell k Lu) → Prop := fun b => BInT12 S j0 b with hRl
  have hpi := Real.pi_pos
  have hρ0 : 0 ≤ ρ1 := by rw [hρ1]; positivity
  set q0 : ℝ := ρ1 / (ell : ℝ) ^ (2 * j0) with hq0d
  set e : ℝ := ρ1 / (ell : ℝ) ^ j0 with hed
  have hq0 : 0 ≤ q0 := by positivity
  have h0 : ∀ w, Rp w → ∀ ν μ', dv (pw 1 V w ν μ') ≤ q0 := by
    intro w hw ν μ'
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩⟩ := hw ν μ'
    exact m1_plaq_loc12 S U g A hU hB hη (by omega) ha0 ha1 j0 hj0 w ν μ' a1 a2 c1 b2
  have he : ∀ b, Rl b → dv (V b) ≤ e := fun b hb =>
    m1_link_loc12 S U g A hU hB hη (by omega) ha0 j0 hj0 b hb.1 hb.2
  have hdvd : ∀ ρ, ell ^ l ∣ scaleUp ell k Lu ρ + 1 := fun ρ => by
    rw [AdalyFormal.GaugeCov.scaleUp_succ ell k Lu hell ρ]
    exact Dvd.dvd.mul_left (pow_dvd_pow ell hlk.le) _
  have hN : ∀ ρ, 2 * ell ^ l < scaleUp ell k Lu ρ + 1 := fun ρ => by
    rw [AdalyFormal.GaugeCov.scaleUp_succ ell k Lu hell ρ]
    have h1 : ell ^ l ≤ ell ^ k := Nat.pow_le_pow_right hell hlk.le
    have h2 := Nat.mul_le_mul (hT3 ρ) h1
    omega
  have hsm' : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) ≤ 1 := by
    have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    have hle : ((ell : ℝ) ^ 2) ^ l * q0 ≤ ρ1 := by
      rw [hq0d, ← pow_mul]
      have hp : (0 : ℝ) < (ell : ℝ) ^ (2 * j0) := by positivity
      rw [mul_div_assoc', div_le_iff₀ hp]
      have : (ell : ℝ) ^ (2 * l) ≤ (ell : ℝ) ^ (2 * j0) := pow_le_pow_right₀ hellR (by omega)
      nlinarith [mul_le_mul_of_nonneg_right this hρ0]
    have h4 : 0 ≤ 4000000 * (ell : ℝ) ^ 2 := by positivity
    calc 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) ≤ 4000000 * (ell : ℝ) ^ 2 * ρ1 :=
          mul_le_mul_of_nonneg_left hle h4
      _ ≤ 1 := hsm
  have hBK : ∀ w, pdist z w ≤ 13 * ell ^ l → ∀ d : Fin 3, BInT12 S j0 (w, d) := by
    intro w hw d
    refine ⟨hcone w (by omega), hcone _ ?_⟩
    have := pdist_shift112 hw d
    show pdist z (coarseShift w 1 d) ≤ 14 * ell ^ l
    omega
  have hgB : GoodBd ell Rp l (z, μ) := by
    refine goodBd_pd ell hell2 Rp l _ hz hdvd (fun w hw0 => fun ν μ' => ?_)
    have hw : pdist z w ≤ 12 * ell ^ l := hw0
    have hw1 : ∀ d, pdist z (coarseShift w 1 d) ≤ 13 * ell ^ l := fun d => by
      have := pdist_shift112 hw d; omega
    exact ⟨hBK w (by omega) ν, hBK _ (hw1 ν) μ', hBK _ (hw1 μ') ν, hBK w (by omega) μ'⟩
  have hgL : goodL ell Rl l (z, μ) := by
    refine goodL_pd ell hell2 Rl l _ (fun b _ hb => ?_)
    have hb' : pdist z b.1 ≤ 13 * ell ^ l := by
      have : pdist (z, μ).1 b.1 ≤ ell ^ l := hb
      simp only at this; omega
    exact hBK b.1 hb' b.2
  exact link_tower_na_loc ell hell2 V Rp Rl q0 e hq0 h0 he l hdvd hN hsm' l le_rfl _ hz hgB hgL

end AdalyFormal.OneGap12
#print axioms AdalyFormal.OneGap12.m1_link_loc12
#print axioms AdalyFormal.OneGap12.m1_plaq_loc12
#print axioms AdalyFormal.OneGap12.tower_link_loc12
