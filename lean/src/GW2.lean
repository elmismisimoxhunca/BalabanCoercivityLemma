import GW1
import MS13
import MS11
import M1B
import TL9

/-!
# GW2 -- the stratified link / holonomy regime at `U^g` from ONE `M1Regular` witness `(g, A)` (M1 gauge lane, 2026-10-13)

For a witness `(g, A)` of `M1Regular ell M f k S α₀ η U` (`U^g = exp(iηA)`, `M1Bounds`), and every `j0 ≤ k`, the bonds with both
endpoints in `Ω_{j0}` carry the curvature_blocking `CubeChart` with `c1 = fMα₀ (ell^{j0} η)⁻¹`, `c2 = fMα₀ (ell^{j0} η)⁻²`
(`m1Chart`; every such bond has `bstrat ≥ j0`).  CB9 then gives, with `a1 = fMα₀ ≤ 1` and `ρ = (4π+4)·a1`:
* `m1_link` : `dv((U^g)_b) ≤ ρ / ell^{j0}` on bonds with both endpoints in `Ω_{j0}`;
* `m1_plaq` : `dv(pw 1 (U^g) y ν μ) ≤ ρ / ell^{2 j0}` on plaquette words with all four corners in `Ω_{j0}`.
These are lane C's `hlink` / `hplaq` (MS9) at `U^g`; they transfer verbatim to ANY `U''` agreeing with `U^g` on the bonds with both
endpoints in `Ω₀` (`link_of_agree`, `plaq_of_agree`).  Consequences at such `U''`:
* `site_hU` / `site_hT` : lane C's `hU`, `hT` of MI33 with `ρ_T = (ell + 3πℓ²)ρ` (`hU_of_regime`, `hT_of_regime`);
* `holRegime_of_m1` : lane E's `HolRegime S ell k U'' ρ`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1GaugeW4

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible scaleUp HT)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.CurvBlock (dv CubeChart cube_link cube_plaq pw)
open AdalyFormal.M1 (M1Bounds M1Regular bstrat le_bstrat_of_mem)

variable {L : PeriodicLatticeExtent}

/-- bonds with both endpoints in `Ω_{j0}`. -/
def BIn (S : Tower L) (j0 : ℕ) (e : Bond L) : Prop :=
  e.1 ∈ S.Om j0 ∧ periodicLatticeShift e.1 e.2 ∈ S.Om j0

/-- the M1 witness, restricted to the bonds of `Ω_{j0}`, is a CB9 `CubeChart` with the printed stratum-`j0` scales. -/
def m1Chart {ell M f k : ℕ} (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A) (j0 : ℕ) (hj0 : j0 ≤ k) :
    CubeChart U (BIn S j0) η ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1))
      ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 2)) where
  g := g
  A := A
  hA := fun e he => ⟨hB.1 e, hU e, hB.2.1 e j0 (le_bstrat_of_mem hj0 e he.1 he.2)⟩
  hD := fun μ ν x h1 h2 =>
    hB.2.2.1 μ ν x j0 (le_bstrat_of_mem hj0 _ h1.1 h1.2) (le_bstrat_of_mem hj0 _ h2.1 h2.2)

section witness
variable {ell M f k : ℕ}

theorem m1_link (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A)
    (hη : 0 < η) (hell : 1 ≤ ell) (ha0 : 0 ≤ (f : ℝ) * M * α₀) (j0 : ℕ) (hj0 : j0 ≤ k) (b : Bond L)
    (h1 : b.1 ∈ S.Om j0) (h2 : periodicLatticeShift b.1 b.2 ∈ S.Om j0) :
    dv (periodicGaugeTransform g U b) ≤ (4 * Real.pi + 4) * ((f : ℝ) * M * α₀) / (ell : ℝ) ^ j0 := by
  have hK := cube_link hη (m1Chart S U g A hU hB j0 hj0) b ⟨h1, h2⟩
  have hp : (0 : ℝ) < (ell : ℝ) ^ j0 := pow_pos (by exact_mod_cast hell) j0
  have e1 : η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1)) = (f : ℝ) * M * α₀ / (ell : ℝ) ^ j0 := by
    field_simp
  rw [e1] at hK
  refine hK.trans ?_
  apply div_le_div_of_nonneg_right _ hp.le
  have := Real.pi_pos
  nlinarith

theorem m1_plaq (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A)
    (hη : 0 < η) (hell : 1 ≤ ell) (ha0 : 0 ≤ (f : ℝ) * M * α₀) (ha1 : (f : ℝ) * M * α₀ ≤ 1)
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
  have hin : AdalyFormal.CurvBlock.plaqIn (BIn S j0) (y, ν, μ) :=
    ⟨⟨h1, h2⟩, ⟨h2, h4⟩, ⟨h3, by show coarseShift (coarseShift y 1 μ) 1 ν ∈ S.Om j0; rw [hc]; exact h4⟩, ⟨h1, h3⟩⟩
  have e1 : η * (a1 * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1)) = a1 / (ell : ℝ) ^ j0 := by field_simp
  have hsmall : η * (a1 * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1)) ≤ 1 := by
    rw [e1, div_le_one hp]; linarith
  have hK0 := cube_plaq hη (m1Chart S U g A hU hB j0 hj0) hsmall (y, ν, μ) hin
  have hK : dv (pw 1 (periodicGaugeTransform g U) y ν μ) ≤ 2 * (η ^ 2 * (a1 * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 2)))
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

section agree
variable {ell M R k : ℕ} {S : Tower L}

theorem bIn_bothIn (hS : Admissible ell M R k S) {j0 : ℕ} {e : Bond L} (h : BIn S j0 e) : BothIn (S.Om 0) e := by
  have hsub : S.Om j0 ⊆ S.Om 0 := AdalyFormal.M1.om_anti hS (Nat.zero_le j0)
  exact ⟨hsub h.1, hsub h.2⟩

theorem link_of_agree (hS : Admissible ell M R k S) (V U'' : LinkCfg L)
    (hag : ∀ e : Bond L, BothIn (S.Om 0) e → V e = U'' e) (ρ : ℝ)
    (h : ∀ j0, j0 ≤ k → ∀ b : Bond L, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (V b) ≤ ρ / (ell : ℝ) ^ j0) :
    ∀ j0, j0 ≤ k → ∀ b : Bond L, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (U'' b) ≤ ρ / (ell : ℝ) ^ j0 := by
  intro j0 hj0 b h1 h2
  rw [← hag b (bIn_bothIn hS ⟨h1, h2⟩)]
  exact h j0 hj0 b h1 h2

theorem plaq_of_agree (hS : Admissible ell M R k S) (V U'' : LinkCfg L)
    (hag : ∀ e : Bond L, BothIn (S.Om 0) e → V e = U'' e) (ρ : ℝ)
    (h : ∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite L) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 → dv (pw 1 V y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * j0)) :
    ∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite L) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 → dv (pw 1 U'' y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * j0) := by
  intro j0 hj0 y ν μ h1 h2 h3 h4
  have hc : coarseShift (coarseShift y 1 μ) 1 ν = coarseShift (coarseShift y 1 ν) 1 μ :=
    AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_comm_gen y 1 1 μ ν
  have e1 := hag (y, ν) (bIn_bothIn hS (j0 := j0) ⟨h1, h2⟩)
  have e2 := hag (coarseShift y 1 ν, μ) (bIn_bothIn hS (j0 := j0) ⟨h2, h4⟩)
  have e3 := hag (coarseShift y 1 μ, ν) (bIn_bothIn hS (j0 := j0)
    ⟨h3, by show coarseShift (coarseShift y 1 μ) 1 ν ∈ S.Om j0; rw [hc]; exact h4⟩)
  have e4 := hag (y, μ) (bIn_bothIn hS (j0 := j0) ⟨h1, h3⟩)
  have hpw : pw 1 U'' y ν μ = pw 1 V y ν μ := by
    unfold pw; rw [e1, e2, e3, e4]
  rw [hpw]
  exact h j0 hj0 y ν μ h1 h2 h3 h4

theorem holRegime_of_plaq (hell : 0 < ell) (U'' : LinkCfg L) (ρ : ℝ)
    (h : ∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite L) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 → dv (pw 1 U'' y ν μ) ≤ ρ / (ell : ℝ) ^ (2 * j0)) :
    AdalyFormal.M1IMS.HolRegime S ell k U'' ρ := by
  intro j0 hj0 p h1 h2 h3 h4
  obtain ⟨y, ⟨⟨ν, μ⟩, hνμ⟩⟩ := p
  have e : periodicPlaquetteHolonomy U'' (y, ⟨(ν, μ), hνμ⟩) = pw 1 U'' y ν μ := rfl
  rw [e]
  exact h j0 hj0 y ν μ h1 h2 h3 h4

end agree

section regimeU
variable {ell M R f k : ℕ}

/-- `hlink` of lane C at `U^g`, in the form `rho1 / ell^j0`. -/
theorem hlink_M1 (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A) (hη : 0 < η) (hell : 1 ≤ ell) (ha0 : 0 ≤ (f : ℝ) * M * α₀) :
    ∀ j0, j0 ≤ k → ∀ b : Bond L, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (periodicGaugeTransform g U b) ≤ AdalyFormal.TowerLoc.rho1 f M α₀ / (ell : ℝ) ^ j0 :=
  fun j0 hj0 b h1 h2 => m1_link S U g A hU hB hη hell ha0 j0 hj0 b h1 h2

/-- `hplaq` of lane C at `U^g`, in the form `rho1 / ell^(2 j0)`. -/
theorem hplaq_M1 (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A) (hη : 0 < η) (hell : 1 ≤ ell) (ha0 : 0 ≤ (f : ℝ) * M * α₀)
    (ha1 : (f : ℝ) * M * α₀ ≤ 1) :
    ∀ j0, j0 ≤ k → ∀ (y : PeriodicLatticeSite L) (ν μ : Fin 3),
      y ∈ S.Om j0 → coarseShift y 1 ν ∈ S.Om j0 → coarseShift y 1 μ ∈ S.Om j0 →
      coarseShift (coarseShift y 1 ν) 1 μ ∈ S.Om j0 →
      dv (pw 1 (periodicGaugeTransform g U) y ν μ) ≤ AdalyFormal.TowerLoc.rho1 f M α₀ / (ell : ℝ) ^ (2 * j0) :=
  fun j0 hj0 y ν μ h1 h2 h3 h4 => m1_plaq S U g A hU hB hη hell ha0 ha1 j0 hj0 y ν μ h1 h2 h3 h4

/-- lane C's `hU` of MI33 at `U^g`, with `ρ_T = (ell + 3πℓ²)·rho1`. -/
theorem site_hU_M1 (hell2 : 2 ≤ ell) {S : Tower L} (hS : Admissible ell M R k S) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A) (hη : 0 < η) (hα0 : 0 ≤ α₀) :
    ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm (((periodicGaugeTransform g U b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * AdalyFormal.TowerLoc.rho1 f M α₀ / (ell : ℝ) ^ j :=
  hU_of_regime ell M R k hell2 hS (periodicGaugeTransform g U) _ (AdalyFormal.TowerLoc.rho1_nonneg f M α₀ hα0)
    (hlink_M1 S U g A hU hB hη (by omega) (by have := Real.pi_pos; positivity))

/-- lane C's `hT` of MI33 at `U^g`. -/
theorem site_hT_M1 (hell2 : 2 ≤ ell) {S : Tower L} (hS : Admissible ell M R k S) (hRM : 18 ≤ R * M)
    (hbig : ∀ σ, 4 * ell ^ k < L σ + 1) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A) (hη : 0 < η) (hα0 : 0 ≤ α₀) (ha1 : (f : ℝ) * M * α₀ ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * AdalyFormal.TowerLoc.rho1 f M α₀ ≤ 1) :
    ∀ j, j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j),
      z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower (geomOf ell k S) (periodicGaugeTransform g U) i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ ((ell : ℝ) + 3 * Real.pi * (ell : ℝ) ^ 2) * AdalyFormal.TowerLoc.rho1 f M α₀ * (ell : ℝ) ^ i / (ell : ℝ) ^ j :=
  hT_of_regime ell M R k hell2 hS hRM hbig (periodicGaugeTransform g U) _ (AdalyFormal.TowerLoc.rho1_nonneg f M α₀ hα0)
    hsm4 (hlink_M1 S U g A hU hB hη (by omega) (by have := Real.pi_pos; positivity))
    (hplaq_M1 S U g A hU hB hη (by omega) (by have := Real.pi_pos; positivity) ha1)

/-- lane E's `HolRegime` at `U^g` (constant `rho1`). -/
theorem holRegime_M1 (hell0 : 0 < ell) {S : Tower L} {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A) (hη : 0 < η) (ha0 : 0 ≤ (f : ℝ) * M * α₀) (ha1 : (f : ℝ) * M * α₀ ≤ 1) :
    AdalyFormal.M1IMS.HolRegime S ell k (periodicGaugeTransform g U) (AdalyFormal.TowerLoc.rho1 f M α₀) :=
  holRegime_of_plaq hell0 _ _ (hplaq_M1 S U g A hU hB hη hell0 ha0 ha1)

end regimeU

end AdalyFormal.M1GaugeW4

#print axioms AdalyFormal.M1GaugeW4.m1Chart
#print axioms AdalyFormal.M1GaugeW4.m1_link
#print axioms AdalyFormal.M1GaugeW4.m1_plaq
#print axioms AdalyFormal.M1GaugeW4.holRegime_of_plaq
#print axioms AdalyFormal.M1GaugeW4.site_hU_M1
#print axioms AdalyFormal.M1GaugeW4.site_hT_M1
#print axioms AdalyFormal.M1GaugeW4.holRegime_M1
