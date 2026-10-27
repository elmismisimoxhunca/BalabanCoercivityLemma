import UD1

/-!
# UD2 -- an index-`k` class cube around a given unit site, inside `Ω_k`, whose core contains a ball (lane m2_unitcharts_20261014)

`class_cube_at`: for a unit site `q` within unit distance `D` of a point `y0 ∈ Λ` with `D + 21 M ≤ R M`, and a fine radius `r` with
`r + 128 n + 5 ≤ 5 M n` (`n = ℓ^k`), there is a grid corner `z` such that `siteBox z (12 M n)` is a class cube of index `k` (factor 12),
and for every fine site `x'` in `Ball (embY q) r`, every coordinate with `12 M n ≤ L_σ + 1` has offset in `[128 n + 4, 12 M n - 128 n - 5]`
(the core condition of `regime_of_class` with `w = 64 n`).  No hypothesis on `Ω_k` beyond `Admissible` and `LambdaOK2`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8 (Ball pcd_comm pcd_self pcd_triangle pcd_le_diff pdist_triangle pdist_comm pdist_self mem_Ball_self)
open AdalyFormal.IngredientFamilyR2 (embY embY_val)
open AdalyFormal.M2Bridge (offc offc_lt mem_siteBox_offc)

theorem scaleUp_succ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (σ : Fin 3) :
    scaleUp ell k Lu σ + 1 = (Lu σ + 1) * ell ^ k := by
  unfold scaleUp
  have : 1 ≤ (Lu σ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

theorem offc_eq {L : PeriodicLatticeExtent} (z x : PeriodicLatticeSite L) (σ : Fin 3) :
    offc z x σ = offN (L σ + 1) (z σ).val (x σ).val := rfl

theorem pcd_le_pdist {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) (σ : Fin 3) :
    pcd (L σ + 1) (x σ).val (y σ).val ≤ pdist x y := by
  unfold pdist
  exact Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ σ)

/-- the corner site -/
def cornerOf {L : PeriodicLatticeExtent} (B : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun σ => ⟨zc (L σ + 1) B (x σ).val, zc_lt (Nat.succ_pos _)⟩

theorem cornerOf_grid {L : PeriodicLatticeExtent} {B : ℕ} (hB : 0 < B) (hBN : ∀ σ : Fin 3, B ∣ L σ + 1)
    (x : PeriodicLatticeSite L) : GridCorner B (cornerOf B x) := by
  intro σ; exact zc_mod hB (hBN σ)

/-- the ball condition: the offset of every point within `r` of `x` lies in `[5B - r, 6B - 1 + r]`. -/
theorem corner_off_ball {L : PeriodicLatticeExtent} {B r : ℕ} (hB : 0 < B) (hr : r ≤ 5 * B)
    {x x' : PeriodicLatticeSite L} (σ : Fin 3) (hx : 12 * B ≤ L σ + 1) (hp : pdist x x' ≤ r) :
    5 * B ≤ offc (cornerOf B x) x' σ + r ∧ offc (cornerOf B x) x' σ + 1 ≤ 6 * B + r := by
  rw [offc_eq]
  exact off_bounds hB hx (x σ).isLt (x' σ).isLt hr (le_trans (pcd_le_pdist x x' σ) hp)

theorem box_pcd {L : PeriodicLatticeExtent} {B : ℕ} (hB : 0 < B) (x x'' : PeriodicLatticeSite L)
    (hbox : x'' ∈ siteBox (cornerOf B x) (12 * B)) (σ : Fin 3) :
    pcd (L σ + 1) (x σ).val (x'' σ).val ≤ 7 * B := by
  have h := (mem_siteBox_offc _ _ _).mp hbox σ
  by_cases h12 : 12 * B ≤ L σ + 1
  · have : offN (L σ + 1) (zc (L σ + 1) B (x σ).val) (x'' σ).val < 12 * B := h
    exact pcd_of_off hB h12 (x σ).isLt (x'' σ).isLt this
  · have := pcd_le_N_half (L σ + 1) (x σ).val (x'' σ).val (x σ).isLt (x'' σ).isLt
    omega

/-- a unit site within `R M` of a point of `Λ` has its embedding in `Ω_k`. -/
theorem embY_mem_Om {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} (hL : AdalyFormal.StatementLane.LambdaOK ell M R k S Lam)
    {y0 : PeriodicLatticeSite Lu} (hy0 : y0 ∈ Lam) {u : PeriodicLatticeSite Lu} (hu : pdist y0 u ≤ R * M) :
    embY ell k Lu hell u ∈ S.Om k := by
  obtain ⟨-, emb, hemb, hin, hfar⟩ := hL
  have he : emb u = embY ell k Lu hell u := by
    funext μ; apply Fin.ext; rw [hemb, embY_val]
  by_contra hno
  rw [← he] at hno
  have := hfar y0 hy0 u hno
  omega

/-- every fine site close (in the `7 B` sense) to `embY q` with `q` within `R M - 21 M` of `Λ` lies in `Ω_k`. -/
theorem near_mem_Om {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) {Lam : Set (PeriodicLatticeSite Lu)}
    (hL : AdalyFormal.StatementLane.LambdaOK ell M R k S Lam)
    {y0 : PeriodicLatticeSite Lu} (hy0 : y0 ∈ Lam) (q : PeriodicLatticeSite Lu)
    (hD : pdist y0 q + 21 * M ≤ R * M) (x'' : PeriodicLatticeSite (scaleUp ell k Lu))
    (hn : ∀ σ : Fin 3, pcd (scaleUp ell k Lu σ + 1) (embY ell k Lu hell q σ).val (x'' σ).val ≤ 7 * (M * ell ^ k)) :
    x'' ∈ S.Om k := by
  set n := ell ^ k with hn0
  have hnpos : 0 < n := pow_pos hell k
  let y' : PeriodicLatticeSite Lu := fun σ => ⟨(x'' σ).val / n, by
    have h1 := (x'' σ).isLt
    have h2 : scaleUp ell k Lu σ + 1 = (Lu σ + 1) * n := scaleUp_succ ell k Lu hell σ
    exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq h1 (by rw [h2, mul_comm]))⟩
  have hy'cd : ∀ σ : Fin 3, pcd (Lu σ + 1) (q σ).val (y' σ).val ≤ 7 * M := by
    intro σ
    have hN : scaleUp ell k Lu σ + 1 = (Lu σ + 1) * n := scaleUp_succ ell k Lu hell σ
    have hmul := pcd_mul (Lu σ + 1) n (q σ).val (y' σ).val hnpos
    rw [← hN] at hmul
    have e1 : (embY ell k Lu hell q σ).val = n * (q σ).val := embY_val ell k Lu hell q σ
    have e2 : n * (y' σ).val ≤ (x'' σ).val := by
      show n * ((x'' σ).val / n) ≤ _
      exact Nat.mul_div_le _ _
    have e3 : (x'' σ).val < n * (y' σ).val + n := by
      show _ < n * ((x'' σ).val / n) + n
      have := Nat.mod_add_div (x'' σ).val n
      have h3 := Nat.mod_lt (x'' σ).val hnpos
      omega
    have hyN : n * (y' σ).val < scaleUp ell k Lu σ + 1 := lt_of_le_of_lt e2 (x'' σ).isLt
    have hqN : n * (q σ).val < scaleUp ell k Lu σ + 1 := by rw [← e1]; exact (embY ell k Lu hell q σ).isLt
    have t1 := pcd_triangle (scaleUp ell k Lu σ + 1) (n * (q σ).val) (x'' σ).val (n * (y' σ).val) hqN (x'' σ).isLt hyN
    have t2 : pcd (scaleUp ell k Lu σ + 1) (x'' σ).val (n * (y' σ).val) < n := by
      rw [pcd_comm]
      have := pcd_le_diff (scaleUp ell k Lu σ + 1) (n * (y' σ).val) (x'' σ).val e2
      omega
    have t0 := hn σ
    rw [e1] at t0
    have hlt : n * pcd (Lu σ + 1) (q σ).val (y' σ).val < n * (7 * M + 1) := by
      rw [← hmul]; nlinarith
    have := Nat.lt_of_mul_lt_mul_left hlt
    omega
  have hpd : pdist q y' ≤ 21 * M := by
    unfold pdist
    calc ∑ μ : Fin 3, pcd (Lu μ + 1) (q μ).val (y' μ).val ≤ ∑ _μ : Fin 3, 7 * M :=
          Finset.sum_le_sum (fun σ _ => hy'cd σ)
      _ = 21 * M := by simp; ring
  have hy'Om : embY ell k Lu hell y' ∈ S.Om k :=
    embY_mem_Om hell hL hy0 (le_trans (pdist_triangle y0 q y') (by omega))
  have hbc := hS.2.2.2.1 k le_rfl
  refine hbc _ hy'Om x'' (fun μ => ?_)
  rw [embY_val]
  show (x'' μ).val / (M * n) = (n * ((x'' μ).val / n)) / (M * n)
  rw [mul_comm M n, Nat.mul_div_mul_left _ _ hnpos, Nat.div_div_eq_div_mul]

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.corner_off_ball
#print axioms AdalyFormal.M2UnitCharts.box_pcd
#print axioms AdalyFormal.M2UnitCharts.embY_mem_Om
#print axioms AdalyFormal.M2UnitCharts.near_mem_Om
