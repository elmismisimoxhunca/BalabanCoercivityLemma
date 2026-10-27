import CJ2
import ZR6A

/-!
# CJ3 -- block loops of `Ū^l` are bounded by FINE plaquettes (no gauge), and the class bounds fine plaquettes of `Ω_m`

1. `loop_small` (hypotheses: `2 ≤ ell`, `ell^l ∣ L ρ + 1`, `2 ell^l < L ρ + 1`, `4·10⁶ ell² (ell²)^l q0 ≤ 1`, `q0 ≥ 0`,
   `e₋ ∈ CoarseLattice (ell^l)`, and `hR` below):
   the block loop `loopVar (ell^l) ell (Ū^l) e x` of an `ell^l`-aligned row `e` is a strided ladder
   (`CurvBlock.loopVar_eq_ladS`), bounded by the stride-`ell^l` plaquettes of `Ū^l` it encloses (`CurvBlock.ladS_le`),
   each bounded by `2 (ell²)^l q0` (`CurvBlock.curv_tower_na_loc`) as soon as every FINE plaquette at a site of the
   ball `(e₋, 4 ell^(l+1) + 2 rhoT l)` has defect `≤ q0`.  Fine plaquette defects are gauge invariant: no gauge is chosen.
2. `plaq_small_class` (hypotheses: `1 ≤ ell`, `η > 0`, `Admissible`, `ClassCoupled`, `0 ≤ c M α₀ ≤ 1`, `hz : Ball z 2 ⊆ Ω_m`):
   inside `Ω_m` (a site whose `2`-ball lies in `Ω_m`), every fine plaquette defect is
   `≤ (4π+4) a / (ell²)^(m-1)`, `a = c M α₀`, from the class: the plaquette lies in ONE class cube (`CoversPlaqOm0c`),
   of index `i ≥ m - 1` (the cube sits in `B^i ∪ B^{i+1}`), whose chart bounds the plaquette (`CurvBlock.cube_plaq`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.ClassJets

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist pcd Tower Admissible towerBj DescribedAt IsClassCube CubeBond HT bigSide)
open AdalyFormal.StatementLane2 (ClassCoupled PerCubeRegular2 CoversPlaqOm0c)
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CurvBlock (dv pw ladS ladPlaqs pathBonds off Box GoodPl curv_tower_na_loc loopVar_eq_ladS ladS_le
  mem_ladPlaqs ladPlaqs_aligned dv_conj dv_inv dv_one dv_nonneg CubeChart cube_plaq HTm plaqIn)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

/-! ## 1. forward offsets dominate the circular distance -/

theorem pcd_le_off (y z : PeriodicLatticeSite L) (σ : Fin 3) : pcd (L σ + 1) (y σ).val (z σ).val ≤ off y z σ := by
  unfold off pcd
  have hy := (y σ).isLt
  have hz := (z σ).isLt
  rw [Fin.val_sub]
  split_ifs with h
  · have e : (L σ + 1 - (y σ).val + (z σ).val) % (L σ + 1) = (z σ).val - (y σ).val := by
      rw [show L σ + 1 - (y σ).val + (z σ).val = ((z σ).val - (y σ).val) + (L σ + 1) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e]; exact min_le_left _ _
  · have e : (L σ + 1 - (y σ).val + (z σ).val) % (L σ + 1) = L σ + 1 - (y σ).val + (z σ).val :=
      Nat.mod_eq_of_lt (by omega)
    rw [e]; exact le_trans (min_le_right _ _) (by omega)

theorem pdist_le_of_box {y z : PeriodicLatticeSite L} {s B : ℕ} (h : Box y s B z) : pdist y z ≤ 3 * B := by
  unfold pdist
  calc ∑ σ : Fin 3, pcd (L σ + 1) (y σ).val (z σ).val ≤ ∑ _σ : Fin 3, B :=
        Finset.sum_le_sum (fun σ _ => le_trans (pcd_le_off y z σ) (h σ).2)
    _ = 3 * B := by simp

/-- the plaquette cone of `CurvBlock` from a `pdist` ball (no wrap condition). -/
theorem goodPl_of_ball (ell : ℕ) (R : PeriodicLatticeSite L → Prop) :
    ∀ (l : ℕ) (y : PeriodicLatticeSite L), (∀ z ∈ Ball y (2 * rhoT ell l), R z) → GoodPl ell R l y := by
  intro l
  induction l with
  | zero => intro y h; exact h y (mem_Ball_self _ _)
  | succ k ih =>
      intro y h z _ hz
      refine ih z (fun z' hz' => h z' (Ball_sub (pdist_le_of_box hz) ?_ hz'))
      rw [rhoT_succ]
      have : 2 * (ell ^ k * ell) - ell ^ k ≤ 2 * (ell ^ k * ell) := Nat.sub_le _ _
      omega

theorem pdist_pathBonds_le (s : ℕ) : ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L),
    ∀ b ∈ pathBonds s y p, pdist y b.1 ≤ s * p.length := by
  intro p
  induction p with
  | nil => intro y b hb; simp [pathBonds] at hb
  | cons μ rest ih =>
      intro y b hb
      rcases List.mem_cons.mp hb with h | h
      · rw [h, pdist_self]; exact Nat.zero_le _
      · have h1 := ih _ b h
        have h2 := pdist_coarseShift_le y s μ
        have h3 := pdist_triangle y (coarseShift y s μ) b.1
        simp only [List.length_cons]; rw [Nat.mul_succ]; omega

/-! ## 2. the loop bound -/

/-- **gauge-free block-loop bound.** -/
theorem loop_small (ell : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L) (q0 : ℝ) (hq0 : 0 ≤ q0) (l : ℕ)
    (hdvd : ∀ ρ, ell ^ l ∣ L ρ + 1) (hN : ∀ ρ, 2 * ell ^ l < L ρ + 1)
    (hsmall : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) ≤ 1)
    (e : PeriodicLatticeEdge L) (he : e.1 ∈ CoarseLattice L (ell ^ l))
    (hR : ∀ z ∈ Ball e.1 (4 * (ell ^ l * ell) + 2 * rhoT ell l), ∀ ν μ : Fin 3, dv (pw 1 U z ν μ) ≤ q0) :
    ∀ x ∈ stepBlockOf e.1 (ell ^ l) ell,
      dv (loopVar (ell ^ l) ell (ubarTowerSU2 ell U l) e x) ≤ 6 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) := by
  intro x hx
  have hell0 : 0 < ell := by omega
  have hs : 0 < ell ^ l := pow_pos hell0 l
  rw [loopVar_eq_ladS (ell ^ l) ell _ e x hx]
  have hcurv := curv_tower_na_loc ell hell U q0 (fun z => ∀ ν μ : Fin 3, dv (pw 1 U z ν μ) ≤ q0) hq0
    (fun y hy => hy) l hdvd hN hsmall
  have hlen := length_coarseGammaPath_le hs hx
  have hX : 0 ≤ ((ell : ℝ) ^ 2) ^ l * q0 := by positivity
  refine le_trans (ladS_le (ell ^ l) _ e.2 ell (2 * (((ell : ℝ) ^ 2) ^ l * q0)) (coarseGammaPath (ell ^ l) e.1 x) e.1 ?_) ?_
  · intro t ht
    have hta := ladPlaqs_aligned (ell ^ l) hdvd e.2 ell _ e.1 he t ht
    obtain ⟨b, hb, j', hj', hte⟩ := mem_ladPlaqs (ell ^ l) e.2 ell _ e.1 t ht
    have h1 := pdist_pathBonds_le (ell ^ l) _ e.1 b hb
    have h2 : pdist b.1 t.1 ≤ ell ^ l * j' := by rw [hte]; exact pdist_coarseShift_le _ _ _
    have h3 := pdist_triangle e.1 b.1 t.1
    have hd : pdist e.1 t.1 ≤ 4 * (ell ^ l * ell) := by
      have a1 : ell ^ l * (coarseGammaPath (ell ^ l) e.1 x).length ≤ ell ^ l * (3 * ell) := Nat.mul_le_mul_left _ hlen
      have a2 : ell ^ l * j' ≤ ell ^ l * ell := Nat.mul_le_mul_left _ hj'.le
      nlinarith
    have hgood : GoodPl ell (fun z => ∀ ν μ : Fin 3, dv (pw 1 U z ν μ) ≤ q0) l t.1 :=
      goodPl_of_ball ell _ l t.1 (fun z hz => hR z (Ball_sub hd le_rfl hz))
    exact hcurv l le_rfl t.1 hta hgood t.2.1 t.2.2
  · have hlR : ((coarseGammaPath (ell ^ l) e.1 x).length : ℝ) ≤ 3 * (ell : ℝ) := by exact_mod_cast hlen
    have hl0 : (0 : ℝ) ≤ ((coarseGammaPath (ell ^ l) e.1 x).length : ℝ) := by positivity
    have hellR : (0 : ℝ) ≤ (ell : ℝ) := by positivity
    calc ((coarseGammaPath (ell ^ l) e.1 x).length : ℝ) * ((ell : ℝ) * (2 * (((ell : ℝ) ^ 2) ^ l * q0)))
        ≤ (3 * (ell : ℝ)) * ((ell : ℝ) * (2 * (((ell : ℝ) ^ 2) ^ l * q0))) :=
          mul_le_mul_of_nonneg_right hlR (by positivity)
      _ = 6 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) := by ring

/-- **row regularity from fine plaquettes.** -/
theorem regRow_of_plaq (ell : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L) (q0 : ℝ) (hq0 : 0 ≤ q0) (l : ℕ)
    (hdvd : ∀ ρ, ell ^ l ∣ L ρ + 1) (hN : ∀ ρ, 2 * ell ^ l < L ρ + 1)
    (hsmall : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) ≤ 1)
    (hthr : 6 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) < r0)
    (e : PeriodicLatticeEdge L) (he : e.1 ∈ CoarseLattice L (ell ^ l))
    (hR : ∀ z ∈ Ball e.1 (4 * (ell ^ l * ell) + 2 * rhoT ell l), ∀ ν μ : Fin 3, dv (pw 1 U z ν μ) ≤ q0) :
    RegRow (ell ^ l) ell (ubarTowerSU2 ell U l) e := by
  intro x hx
  exact mem_LogReg_of_frob_lt (lt_of_le_of_lt (loop_small ell hell U q0 hq0 l hdvd hN hsmall e he hR x hx) hthr)

/-! ## 3. the class bounds fine plaquettes of `Ω_m` -/

theorem pw_gauge_dv (γ : PeriodicLatticeSite L → SU2) (U : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    dv (pw 1 (periodicGaugeTransform γ U) y ν μ) = dv (pw 1 U y ν μ) := by
  have e : periodicGaugeTransform γ U = AdalyFormal.Balaban.QjComposite.coarseGaugeTransform 1 γ U := rfl
  rw [e]; exact AdalyFormal.CurvBlock.dv_pw_cgauge 1 γ U y ν μ

theorem pw_swap (U : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    pw 1 U y ν μ = (pw 1 U y μ ν)⁻¹ := by
  unfold pw; group

theorem pw_self (U : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) (ν : Fin 3) :
    pw 1 U y ν ν = 1 := by
  unfold pw; group

theorem shift_eq_coarse (y : PeriodicLatticeSite L) (μ : Fin 3) : coarseShift y 1 μ = periodicLatticeShift y μ := rfl

/-- the tower is decreasing. -/
theorem om_anti {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) {i j : ℕ} (h : i ≤ j) :
    S.Om j ⊆ S.Om i := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le h with e | e
      · rw [e]
      · exact le_trans (hS.1 j) (ih (by omega))

/-- a class cube of index `i` containing a site of `Ω_m` has `m ≤ i + 1`. -/
theorem cube_index_ge {ell M f k R : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hq : IsClassCube ell M f k S sites i)
    {m : ℕ} {z : PeriodicLatticeSite L} (hz : z ∈ sites) (hzm : z ∈ S.Om m) : m ≤ i + 1 := by
  by_contra hlt
  have hz2 : z ∈ S.Om (i + 2) := om_anti hS (by omega) hzm
  have hz1 : z ∈ S.Om (i + 1) := hS.1 (i + 1) hz2
  rcases hq.1.2.2.1 hz with h | h
  · exact h.2 hz1
  · exact h.2 hz2

/-- **fine plaquettes inside `Ω_m` are small.** -/
theorem plaq_small_class {ell M c k R : ℕ} {S : Tower L} {α₀ η : ℝ} {U : PeriodicLinkConfiguration SU2 L}
    (hell : 1 ≤ ell) (hη : 0 < η) (hS : Admissible ell M R k S) (hU : ClassCoupled ell M c k S α₀ η U)
    (ha0 : 0 ≤ (c : ℝ) * M * α₀) (ha1 : (c : ℝ) * M * α₀ ≤ 1)
    {m : ℕ} (z : PeriodicLatticeSite L) (hz : Ball z 2 ⊆ S.Om m) (ν μ : Fin 3) :
    dv (pw 1 U z ν μ) ≤ (4 * Real.pi + 4) * ((c : ℝ) * M * α₀) / (((ell : ℝ) ^ 2) ^ (m - 1)) := by
  set a : ℝ := (c : ℝ) * M * α₀ with ha
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpos : (0 : ℝ) < ((ell : ℝ) ^ 2) ^ (m - 1) := by positivity
  have hB0 : 0 ≤ (4 * Real.pi + 4) * a / (((ell : ℝ) ^ 2) ^ (m - 1)) := by
    have := Real.pi_pos; positivity
  -- the oriented case
  have main : ∀ ν μ : Fin 3, ν < μ → dv (pw 1 U z ν μ) ≤ (4 * Real.pi + 4) * a / (((ell : ℝ) ^ 2) ^ (m - 1)) := by
    intro ν μ hνμ
    have hmem : ∀ w, pdist z w ≤ 2 → w ∈ S.Om 0 := fun w hw => om_anti hS (Nat.zero_le m) (hz hw)
    have s1 := pdist_shift_le z ν
    have s2 := pdist_shift_le z μ
    have s3 := pdist_shift_le (periodicLatticeShift z ν) μ
    have s4 := pdist_shift_le (periodicLatticeShift z μ) ν
    have t3 := pdist_triangle z (periodicLatticeShift z ν) (periodicLatticeShift (periodicLatticeShift z ν) μ)
    have t4 := pdist_triangle z (periodicLatticeShift z μ) (periodicLatticeShift (periodicLatticeShift z μ) ν)
    have hz0 : pdist z z ≤ 2 := by rw [pdist_self]; omega
    have d1 : pdist z (periodicLatticeShift z ν) ≤ 2 := by omega
    have d2 : pdist z (periodicLatticeShift z μ) ≤ 2 := by omega
    have d3 : pdist z (periodicLatticeShift (periodicLatticeShift z ν) μ) ≤ 2 := by omega
    have d4 : pdist z (periodicLatticeShift (periodicLatticeShift z μ) ν) ≤ 2 := by omega
    let p : PeriodicLatticePlaquette L := (z, ⟨(ν, μ), hνμ⟩)
    have hp : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
      intro e he
      simp only [periodicPlaquetteBoundaryEdges, p, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact ⟨hmem z hz0, hmem _ d1⟩
      · exact ⟨hmem _ d1, hmem _ d3⟩
      · exact ⟨hmem _ d2, hmem _ d4⟩
      · exact ⟨hmem z hz0, hmem _ d2⟩
    obtain ⟨sites, i, hq, hcb⟩ := hU.1.2 p hp
    obtain ⟨g, A, hA, hD, -⟩ := hU.2 sites i hq
    have hbd : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e := hcb
    have e1 : CubeBond sites (z, ν) := hbd _ (by simp [periodicPlaquetteBoundaryEdges, p])
    have e2 : CubeBond sites (periodicLatticeShift z ν, μ) := hbd _ (by simp [periodicPlaquetteBoundaryEdges, p])
    have e3 : CubeBond sites (periodicLatticeShift z μ, ν) := hbd _ (by simp [periodicPlaquetteBoundaryEdges, p])
    have e4 : CubeBond sites (z, μ) := hbd _ (by simp [periodicPlaquetteBoundaryEdges, p])
    -- the chart of the cube
    let K : CubeChart U (CubeBond sites) η (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)) :=
      { g := g, A := A, hA := fun e he => hA e he, hD := fun μ' ν' x h1 h2 => hD μ' ν' x h1 h2 }
    have hKg : K.g = g := rfl
    have hc1 : η * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) = a / (ell : ℝ) ^ i := by
      field_simp
    have hc2 : η ^ 2 * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)) = a / ((ell : ℝ) ^ i) ^ 2 := by
      field_simp
    have hpi : (1 : ℝ) ≤ (ell : ℝ) ^ i := one_le_pow₀ hellR
    have hsm : η * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) ≤ 1 := by
      rw [hc1, div_le_one (by positivity)]; linarith
    have hcp := cube_plaq hη K hsm (z, ν, μ) ⟨e1, e2, e3, e4⟩
    rw [hKg, hc1, hc2] at hcp
    simp only at hcp
    rw [pw_gauge_dv] at hcp
    refine le_trans hcp ?_
    -- arithmetic: 2a/E + (4π+2)(a/e)^2 ≤ (4π+4) a / (ell^2)^(m-1), with E = e^2, e = ell^i, i ≥ m - 1
    have him : m - 1 ≤ i := by
      have := cube_index_ge hS hq e1.1 (hz (mem_Ball_self z 2)); omega
    have hE : ((ell : ℝ) ^ 2) ^ (m - 1) ≤ ((ell : ℝ) ^ i) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      exact pow_le_pow_right₀ hellR (by omega)
    have hpi2 : (0 : ℝ) < ((ell : ℝ) ^ i) ^ 2 := by positivity
    have hpiE : (0 : ℝ) < (ell : ℝ) ^ i := by positivity
    have hsq : (a / (ell : ℝ) ^ i) ^ 2 = a ^ 2 / ((ell : ℝ) ^ i) ^ 2 := by rw [div_pow]
    rw [hsq]
    have hpi0 := Real.pi_pos
    have hstep : 2 * (a / ((ell : ℝ) ^ i) ^ 2) + (4 * Real.pi + 2) * (a ^ 2 / ((ell : ℝ) ^ i) ^ 2)
        ≤ (4 * Real.pi + 4) * a / ((ell : ℝ) ^ i) ^ 2 := by
      have e5 : 2 * (a / ((ell : ℝ) ^ i) ^ 2) + (4 * Real.pi + 2) * (a ^ 2 / ((ell : ℝ) ^ i) ^ 2)
          = (2 * a + (4 * Real.pi + 2) * a ^ 2) / ((ell : ℝ) ^ i) ^ 2 := by ring
      rw [e5, div_le_div_iff_of_pos_right hpi2]
      have ha2 : a ^ 2 ≤ a := by nlinarith
      have h6 := mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi + 2)
      nlinarith
    refine le_trans hstep ?_
    exact div_le_div_of_nonneg_left (by positivity) hpos hE
  rcases lt_trichotomy ν μ with h | h | h
  · exact main ν μ h
  · subst h; rw [pw_self, dv_one]; exact hB0
  · rw [pw_swap, dv_inv]; exact main μ ν h

#print axioms pcd_le_off
#print axioms goodPl_of_ball
#print axioms loop_small
#print axioms regRow_of_plaq
#print axioms cube_index_ge
#print axioms plaq_small_class

end AdalyFormal.ClassJets
