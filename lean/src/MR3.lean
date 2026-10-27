import MR2
import M2B11

/-!
# MR3 -- local charts from the printed per-cube class at the G3 patches whose centred box is a class cube
(m2_route, 2026-10-14)

* `chartOn_of_cube` : a class cube `□` of index `idx` (`PerCubeRegular2 … f …`) containing the `ℓ¹` ball `Ball w (r+1)`
  gives `ChartOn ell U η (f M α₀) i w r` at every level `i ≤ idx` (the cube's own gauge; `A` set to `0` off the cube bonds).
* `cz B w` : the corner of the box of side `12 B` centred at `w` (`offc = 6B` when `12 B < N`; any wrap coordinate is the
  whole circle).  `cz_grid`, `mem_box_cz` (`pdist w y + 1 ≤ 6B ⇒ y ∈ box`), `pdist_le_of_box` (`q ∈ box ⇒ pdist w q ≤ 18 B`).
* `CentredIn S ell M j w` : the centred box of side `12 M ell^j` lies in `Ω_j`.
* `centredIn_of_up` : for a G3 patch at `κ = 1`, `c = 5` whose ball `Ball w (6 G_j)` meets `Ω_{j+1}`, `24 ≤ R` gives `CentredIn`.
* `classCube_of_centredIn` : `CentredIn` + `36 ≤ R ell` ⇒ the centred box is a class cube of index `j` (M2B8 `cube_isClass`).
* `chart_of_centredIn` : `CentredIn` ⇒ `ChartOn … (12 M α₀) i w (chartRad … j i)` for every `i ≤ j`, given
  `d + 64 ell² + 2 ≤ M`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Route

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_shift_le pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.M1 (IsPatch gsp strat strat_eq_iff om_anti)
open AdalyFormal.M1NonFlat (SU2)
open AdalyFormal.M2Bridge (offc offc_ball mem_siteBox_offc cube_isClass)

variable {L : PeriodicLatticeExtent}

/-! ## a chart from one class cube -/

theorem HT_zero : AdalyFormal.StatementLane.HT (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold AdalyFormal.StatementLane.HT; simp

theorem chartOn_of_cube {ell M f k : ℕ} {S : Tower L} (hell : 1 ≤ ell) {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀)
    {U : LinkCfg L} (hP : PerCubeRegular2 ell M f k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} {idx : ℕ} (hq : IsClassCube ell M f k S sites idx)
    {i : ℕ} (hi : i ≤ idx) {w : PeriodicLatticeSite L} {r : ℕ}
    (hball : ∀ y : PeriodicLatticeSite L, pdist w y ≤ r + 1 → y ∈ sites) :
    ChartOn ell U η ((f : ℝ) * M * α₀) i w r := by
  obtain ⟨g, A, hA, hD, -⟩ := hP sites idx hq
  classical
  set A' : Bond L → M2 := fun e => if CubeBond sites e then A e else 0 with hA'
  have hcb : ∀ e : Bond L, pdist w e.1 ≤ r → CubeBond sites e := by
    intro e he
    refine ⟨hball e.1 (by omega), hball _ ?_⟩
    have := pdist_triangle w e.1 (periodicLatticeShift e.1 e.2)
    have := pdist_shift_le e.1 e.2
    omega
  have hA'e : ∀ e : Bond L, CubeBond sites e → A' e = A e := fun e he => by simp [hA', he]
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp : (ell : ℝ) ^ i ≤ (ell : ℝ) ^ idx := pow_le_pow_right₀ hl hi
  have hp0 : 0 < (ell : ℝ) ^ i := by positivity
  have hinv : ((ell : ℝ) ^ idx * η)⁻¹ ≤ ((ell : ℝ) ^ i * η)⁻¹ :=
    inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right hp hη.le)
  have hinv0 : 0 ≤ ((ell : ℝ) ^ idx * η)⁻¹ := by positivity
  have hfM : 0 ≤ (f : ℝ) * M * α₀ := by positivity
  refine ⟨g, A', fun e => ?_, fun e he => ?_, fun e he => ?_, fun μ ν x hx hx' => ?_⟩
  · by_cases h : CubeBond sites e
    · rw [hA'e e h]; exact (hA e h).1
    · simp only [hA', h, if_false]; exact HT_zero
  · rw [hA'e e (hcb e he)]; exact (hA e (hcb e he)).2.1
  · rw [hA'e e (hcb e he)]
    refine ((hA e (hcb e he)).2.2).trans_le ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hinv0 hinv 1) hfM
  · have h1 : CubeBond sites ((x, ν) : Bond L) := hcb (x, ν) hx
    have h2 : CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) := hcb (periodicLatticeShift x μ, ν) hx'
    rw [hA'e _ h1, hA'e _ h2]
    refine (hD μ ν x h1 h2).trans_le ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hinv0 hinv 2) hfM

/-! ## the centred box -/

/-- corner of the box of side `12 B` centred at `w`. -/
def cz (B : ℕ) (w : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun σ => ⟨((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem cz_grid {B : ℕ} (hdiv : ∀ σ, B ∣ L σ + 1) {w : PeriodicLatticeSite L} (hw : GridCorner B w) :
    GridCorner B (cz B w) := by
  intro σ
  show (((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1)) % B = 0
  have h1 : B ∣ (w σ).val := Nat.dvd_of_mod_eq_zero (hw σ)
  have h2 : B ∣ (w σ).val + (L σ + 1 - 6 * B) :=
    Nat.dvd_add h1 (Nat.dvd_sub (hdiv σ) (Dvd.intro_left 6 rfl))
  exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_mod_iff (hdiv σ)).mpr h2)

theorem offc_cz {B : ℕ} (w : PeriodicLatticeSite L) (σ : Fin 3) (hN : 12 * B < L σ + 1) :
    offc (cz B w) w σ = 6 * B := by
  unfold offc
  have hu := (w σ).isLt
  show ((w σ).val + (L σ + 1 - (((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1)))) % (L σ + 1) = 6 * B
  by_cases hc : (w σ).val < 6 * B
  · have e1 : ((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1) = (w σ).val + (L σ + 1 - 6 * B) :=
      Nat.mod_eq_of_lt (by omega)
    rw [e1, show (w σ).val + (L σ + 1 - ((w σ).val + (L σ + 1 - 6 * B))) = 6 * B by omega]
    exact Nat.mod_eq_of_lt (by omega)
  · have e1 : ((w σ).val + (L σ + 1 - 6 * B)) % (L σ + 1) = (w σ).val - 6 * B := by
      rw [show (w σ).val + (L σ + 1 - 6 * B) = ((w σ).val - 6 * B) + (L σ + 1) by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, show (w σ).val + (L σ + 1 - ((w σ).val - 6 * B)) = 6 * B + (L σ + 1) by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

theorem pcd_le_pdist (w y : PeriodicLatticeSite L) (σ : Fin 3) : pcd (L σ + 1) (w σ).val (y σ).val ≤ pdist w y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (w μ).val (y μ).val) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ σ)

/-- sites within `6B - 1` of `w` lie in the centred box. -/
theorem mem_box_cz {B : ℕ} {w y : PeriodicLatticeSite L} (hy : pdist w y + 1 ≤ 6 * B) :
    y ∈ siteBox (cz B w) (12 * B) := by
  rw [mem_siteBox_offc]
  intro σ
  by_cases hN : 12 * B < L σ + 1
  · have hp := pcd_le_pdist w y σ
    have h := offc_ball (N := L σ + 1) (z := ((cz B w) σ).val) (u := (w σ).val) (v := (y σ).val) (h := 6 * B)
      (r := pdist w y) ((cz B w) σ).isLt (w σ).isLt (y σ).isLt (offc_cz w σ hN) (by omega) (by omega) hp
    unfold offc
    omega
  · have := AdalyFormal.M2Bridge.offc_lt (cz B w) y σ
    omega

theorem pcd_le_offs {N z u v : ℕ} (hz : z < N) (hu : u < N) (hv : v < N) :
    pcd N u v ≤ ((u + (N - z)) % N - (v + (N - z)) % N) + ((v + (N - z)) % N - (u + (N - z)) % N) := by
  have hu' : (u + (N - z)) % N = if u < z then u + (N - z) else u - z := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [show u + (N - z) = (u - z) + N by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  have hv' : (v + (N - z)) % N = if v < z then v + (N - z) else v - z := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [show v + (N - z) = (v - z) + N by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  rw [hu', hv']
  unfold pcd
  split_ifs <;> omega

/-- every site of the centred box is within `6B` of `w` in each coordinate, so within `18 B` in `ℓ¹`. -/
theorem pdist_le_of_box {B : ℕ} {w q : PeriodicLatticeSite L} (hq : q ∈ siteBox (cz B w) (12 * B)) :
    pdist w q ≤ 18 * B := by
  rw [mem_siteBox_offc] at hq
  have h : ∀ σ : Fin 3, pcd (L σ + 1) (w σ).val (q σ).val ≤ 6 * B := by
    intro σ
    by_cases hN : 12 * B < L σ + 1
    · have h1 := pcd_le_offs (N := L σ + 1) ((cz B w) σ).isLt (w σ).isLt (q σ).isLt
      have h2 := offc_cz (B := B) w σ hN
      have h3 := hq σ
      unfold offc at h2 h3
      omega
    · unfold pcd
      split_ifs <;> omega
  unfold pdist
  rw [Fin.sum_univ_three]
  have := h 0; have := h 1; have := h 2
  omega

/-! ## the centred box of a G3 patch (`κ = 1`, `c = 5`) -/

/-- the centred box of side `12 M ell^j` about `w` lies in `Ω_j`. -/
def CentredIn (S : Tower L) (ell M j : ℕ) (w : PeriodicLatticeSite L) : Prop :=
  siteBox (cz (bigSide M ell j) w) (12 * bigSide M ell j) ⊆ S.Om j

theorem gsp_one (ell M j : ℕ) : gsp ell M 1 j = bigSide M ell j := by unfold gsp; ring

/-- **up-case patches are centred**: if `Ball w (6 G_j)` meets `Ω_{j+1}` and `24 ≤ R`, the centred box lies in `Ω_j`. -/
theorem centredIn_of_up {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hR : 24 ≤ R)
    {j : ℕ} (hjk : j ≤ k) {w : PeriodicLatticeSite L}
    (hB : ∃ y ∈ Ball w ((5 + 1) * gsp ell M 1 j), y ∈ S.Om (j + 1)) : CentredIn S ell M j w := by
  obtain ⟨y, hyB, hy⟩ := hB
  intro q hq
  by_contra hqn
  have hcol := hS.2.2.2.2.1 j hjk q hqn y hy
  have h1 : pdist w y ≤ (5 + 1) * gsp ell M 1 j := hyB
  rw [gsp_one] at h1
  have h2 := pdist_le_of_box hq
  have h3 := pdist_triangle q w y
  have h4 := pdist_comm q w
  have h5 : 24 * bigSide M ell j ≤ R * bigSide M ell j := Nat.mul_le_mul_right _ hR
  omega

/-- the anchor of a G3 patch (`κ = 1`) lies in the centred box (`1 ≤ bigSide`). -/
theorem anchor_in_box {ell M k : ℕ} {S : Tower L} (hM : 0 < M) (hell : 0 < ell) {j : ℕ} {w : PeriodicLatticeSite L}
    (hp : IsPatch ell M k 1 S j w) :
    ∃ x₀ : PeriodicLatticeSite L, x₀ ∈ S.Om j ∧ strat S k x₀ = j ∧
      x₀ ∈ siteBox (cz (bigSide M ell j) w) (12 * bigSide M ell j) := by
  obtain ⟨x₀, hx0j, hxs, hd0⟩ := hp.anchor (by norm_num) hM hell
  refine ⟨x₀, hx0j, hxs, mem_box_cz ?_⟩
  rw [gsp_one] at hd0
  have hB : 1 ≤ bigSide M ell j := Nat.mul_pos hM (pow_pos hell j)
  rw [pdist_comm]
  omega

/-- a centred box in `Ω_j` is a class cube of index `j` (M2B8 `cube_isClass`). -/
theorem classCube_of_centredIn {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 0 < M)
    (hell : 0 < ell) (hR : 3 * 12 ≤ R * ell) {j : ℕ} {w : PeriodicLatticeSite L} (hp : IsPatch ell M k 1 S j w)
    (hc : CentredIn S ell M j w) :
    IsClassCube ell M 12 k S (siteBox (cz (bigSide M ell j) w) (12 * bigSide M ell j)) j := by
  have hjk : j ≤ k := hp.1
  have hgw : GridCorner (bigSide M ell j) w := by have := hp.2.1; rwa [gsp_one] at this
  have hdiv : ∀ σ, bigSide M ell j ∣ L σ + 1 := fun σ => hS.2.2.1 j hjk σ
  obtain ⟨x₀, hx0j, hxs, hx0box⟩ := anchor_in_box hM hell hp
  have hxB : x₀ ∈ towerBj S j := (strat_eq_iff hS hjk x₀).mpr ⟨om_anti hS (Nat.zero_le j) hx0j, hxs⟩
  exact cube_isClass hS hjk (cz_grid hdiv hgw) hc hx0box hxB hR

/-- **chart at a centred patch**: `CentredIn` gives `ChartOn … (12 M α₀) i w (chartRad ell M 1 5 d j i)` for `i ≤ j`. -/
theorem chart_of_centredIn {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 0 < M)
    (hell : 1 ≤ ell) (hR : 3 * 12 ≤ R * ell) {d : ℕ} (hdM : d + 64 * ell ^ 2 + 2 ≤ M)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2 ell M 12 k S α₀ η U)
    {j : ℕ} {w : PeriodicLatticeSite L} (hp : IsPatch ell M k 1 S j w) (hc : CentredIn S ell M j w)
    {i : ℕ} (hij : i ≤ j) :
    ChartOn ell U η ((12 : ℕ) * M * α₀) i w (chartRad ell M 1 5 d j i) := by
  have hq := classCube_of_centredIn hS hM (by omega) hR hp hc
  refine chartOn_of_cube hell hη hα hP hq hij (fun y hy => mem_box_cz ?_)
  have hpi : ell ^ i ≤ ell ^ j := Nat.pow_le_pow_right (by omega) hij
  have hpj : 1 ≤ ell ^ j := Nat.one_le_pow _ _ (by omega)
  have hroom : (d + 64 * ell ^ 2 + 2) * ell ^ j ≤ M * ell ^ j := Nat.mul_le_mul_right _ hdM
  have hy' : pdist w y ≤ 5 * gsp ell M 1 j + d * ell ^ i + 64 * ell ^ (i + 2) + 1 := hy
  rw [gsp_one] at hy'
  have e2 : ell ^ (i + 2) = ell ^ 2 * ell ^ i := by ring
  have hbs : bigSide M ell j = M * ell ^ j := rfl
  rw [e2] at hy'
  have h1 : d * ell ^ i ≤ d * ell ^ j := Nat.mul_le_mul_left _ hpi
  have h2 : 64 * (ell ^ 2 * ell ^ i) ≤ 64 * ell ^ 2 * ell ^ j := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hpi
  rw [hbs]
  nlinarith

end AdalyFormal.M2Route

#print axioms AdalyFormal.M2Route.HT_zero
#print axioms AdalyFormal.M2Route.chartOn_of_cube
#print axioms AdalyFormal.M2Route.cz_grid
#print axioms AdalyFormal.M2Route.offc_cz
#print axioms AdalyFormal.M2Route.pcd_le_pdist
#print axioms AdalyFormal.M2Route.mem_box_cz
#print axioms AdalyFormal.M2Route.pcd_le_offs
#print axioms AdalyFormal.M2Route.pdist_le_of_box
#print axioms AdalyFormal.M2Route.gsp_one
#print axioms AdalyFormal.M2Route.centredIn_of_up
#print axioms AdalyFormal.M2Route.anchor_in_box
#print axioms AdalyFormal.M2Route.classCube_of_centredIn
#print axioms AdalyFormal.M2Route.chart_of_centredIn
