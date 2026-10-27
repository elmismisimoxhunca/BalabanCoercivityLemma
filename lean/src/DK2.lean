import DK1

/-!
# DK2 -- the level-`k` blocked background near `Λ` is `O(β)`, in the gauge of `M1Regular` (KD sub-lane, 2026-10-13)

* `chart_bounds` : from `U^g = exp(iηA)` (`η = ℓ^{-k}`) and lane B's `M1Bounds` (clauses 0, 1, 2 at `j = k`), on the bonds with
  both endpoints in `Ω_k`: `dv(U^g e) ≤ β/ℓ^k` (CB9 `cube_link`) and, on every plaquette whose four bonds are such bonds,
  `dv(pw 1 U^g …) ≤ (2β + (4π+2)β²)/ℓ^{2k}` (CB9 `cube_plaq`), `β = 12Mα₀ ≤ 1`.
* **`tower_near`** : for a fine configuration `V` with those two bounds on `Ω_k` (constants `e1/ℓ^k`, `q1/ℓ^{2k}`,
  `4·10⁶ℓ²q1 ≤ 1`), every unit site `z` with `|y − z| + 17 ≤ RM` for some `y ∈ Λ`, every direction `μ`:
  `dv(Ū^k(V)(embY z, μ)) ≤ e1 + 3π q1` (NB25 `link_tower_na_loc`, cones in `pdist` balls (DK1), all inside `Ω_k` by DK1
  `deep_mem`).  Torus: only `Lu_σ + 1 ≥ 3` (no-wrap NOT needed).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DK

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible bigSide pdist pcd scaleUp)
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_self pdist_coarseShift_le)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.CurvBlock (dv pw PlaqT plaqIn CubeChart cube_link cube_plaq link_tower_na_loc)
open AdalyFormal.IngredientFamilyR2 (embY embY_val)

variable {L : PeriodicLatticeExtent}

/-- the bond predicate "both endpoints in `Ω_k`" -/
def BK (S : Tower L) (k : ℕ) (e : PeriodicLatticeEdge L) : Prop :=
  e.1 ∈ S.Om k ∧ periodicLatticeShift e.1 e.2 ∈ S.Om k

/-- **the M1 chart on `Ω_k`**: links and plaquettes. -/
theorem chart_bounds (ell M k : ℕ) (hell : 0 < ell) (S : Tower L) (α₀ : ℝ) (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (hη : η = ((ell : ℝ) ^ k)⁻¹)
    (hg : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hb : AdalyFormal.M1.M1Bounds S ell M 12 k α₀ η A)
    (hα : 0 ≤ α₀) (hβ1 : (12 : ℝ) * M * α₀ ≤ 1) :
    (∀ e : PeriodicLatticeEdge L, BK S k e → dv (periodicGaugeTransform g U e) ≤ (12 * M * α₀) / (ell : ℝ) ^ k) ∧
    (∀ t : PlaqT L, plaqIn (BK S k) t →
      dv (pw 1 (periodicGaugeTransform g U) t.1 t.2.1 t.2.2)
        ≤ (2 * (12 * M * α₀) + (4 * Real.pi + 2) * (12 * M * α₀) ^ 2) / ((ell : ℝ) ^ k) ^ 2) := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hn1 : (1 : ℝ) ≤ (ell : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hell)
  have hη0 : 0 < η := by rw [hη]; positivity
  have hnη : (ell : ℝ) ^ k * η = 1 := by rw [hη]; exact mul_inv_cancel₀ hn.ne'
  set β : ℝ := 12 * M * α₀ with hβ
  have hc1 : ((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 1) = β := by rw [hnη]; push_cast; ring
  have hc2 : ((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 2) = β := by rw [hnη]; push_cast; ring
  have hbs : ∀ e : Bond L, BK S k e → k ≤ AdalyFormal.M1.bstrat S k e :=
    fun e he => AdalyFormal.M1.le_bstrat_of_mem le_rfl e he.1 he.2
  let K : CubeChart U (BK S k) η β β :=
    ⟨g, A, fun e he => ⟨hb.1 e, hg e, by rw [← hc1]; exact hb.2.1 e k (hbs e he)⟩,
      fun μ ν x h1 h2 => by rw [← hc2]; exact hb.2.2.1 μ ν x k (hbs _ h1) (hbs _ h2)⟩
  have hsmall : η * β ≤ 1 := by
    have : η ≤ 1 := by rw [hη]; exact inv_le_one_of_one_le₀ hn1
    have hβ0 : 0 ≤ β := by positivity
    nlinarith
  refine ⟨fun e he => ?_, fun t ht => ?_⟩
  · have := cube_link hη0 K e he
    refine this.trans (le_of_eq ?_)
    rw [hη, div_eq_inv_mul]
  · have := cube_plaq hη0 K hsmall t ht
    refine this.trans (le_of_eq ?_)
    rw [hη]; field_simp

theorem pdist_shift1 {L : PeriodicLatticeExtent} {x w : PeriodicLatticeSite L} {n : ℕ} (h : pdist x w ≤ n) (d : Fin 3) :
    pdist x (coarseShift w 1 d) ≤ n + 1 := by
  have h1 := pdist_coarseShift_le w 1 d
  have h2 := pdist_triangle x w (coarseShift w 1 d)
  omega

/-- **the level-`k` background at unit sites near `Λ`.** -/
theorem tower_near (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell2 : 2 ≤ ell) (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (hA : Admissible ell M R k S) (Lam : Set (PeriodicLatticeSite Lu))
    (hL : LambdaOK2 ell M R k S Lam) (hT3 : ∀ μ, 3 ≤ Lu μ + 1)
    (V : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) (e1 q1 : ℝ) (hq1 : 0 ≤ q1)
    (hlink : ∀ e : PeriodicLatticeEdge (scaleUp ell k Lu), BK S k e → dv (V e) ≤ e1 / (ell : ℝ) ^ k)
    (hplaq : ∀ t : PlaqT (scaleUp ell k Lu), plaqIn (BK S k) t → dv (pw 1 V t.1 t.2.1 t.2.2) ≤ q1 / ((ell : ℝ) ^ k) ^ 2)
    (hsm : 4000000 * (ell : ℝ) ^ 2 * q1 ≤ 1)
    {y z : PeriodicLatticeSite Lu} (hy : y ∈ Lam) (hz : pdist y z + 17 ≤ R * M) (μ : Fin 3) :
    dv (AdalyFormal.Balaban.BlockedBackground.ubarTowerSU2 ell V k (embY ell k Lu hell z, μ)) ≤ e1 + 3 * Real.pi * q1 := by
  have hs1 : 1 ≤ ell ^ k := Nat.one_le_pow _ _ hell
  -- every fine site within `14 ℓ^k` of `embY z` lies in `Ω_k`
  have hdeep : ∀ x, pdist (embY ell k Lu hell z) x ≤ 14 * ell ^ k → x ∈ S.Om k :=
    fun x hx => deep_mem hA hL hell hy 14 (by omega) hx
  set Rp : PeriodicLatticeSite (scaleUp ell k Lu) → Prop := fun w => ∀ ν μ' : Fin 3, plaqIn (BK S k) (w, ν, μ') with hRp
  set Rl : PeriodicLatticeEdge (scaleUp ell k Lu) → Prop := fun b => BK S k b with hRl
  set q0 : ℝ := q1 / ((ell : ℝ) ^ k) ^ 2 with hq0d
  set e : ℝ := e1 / (ell : ℝ) ^ k with hed
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hq0 : 0 ≤ q0 := by positivity
  have h0 : ∀ w, Rp w → ∀ ν μ', dv (pw 1 V w ν μ') ≤ q0 := fun w hw ν μ' => hplaq (w, ν, μ') (hw ν μ')
  have he : ∀ b, Rl b → dv (V b) ≤ e := fun b hb => hlink b hb
  have hdvd : ∀ ρ, ell ^ k ∣ scaleUp ell k Lu ρ + 1 := fun ρ => by
    rw [AdalyFormal.GaugeCov.scaleUp_succ ell k Lu hell ρ]; exact dvd_mul_left _ _
  have hN : ∀ ρ, 2 * ell ^ k < scaleUp ell k Lu ρ + 1 := fun ρ => by
    rw [AdalyFormal.GaugeCov.scaleUp_succ ell k Lu hell ρ]
    have := Nat.mul_le_mul_right (ell ^ k) (hT3 ρ)
    omega
  have hsm' : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ k * q0) ≤ 1 := by
    have e2 : ((ell : ℝ) ^ 2) ^ k * q0 = q1 := by
      rw [hq0d, ← pow_mul, mul_comm 2 k, pow_mul]; field_simp
    rw [e2]; exact hsm
  have hc : (embY ell k Lu hell z) ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k) := by
    rw [mem_CoarseLattice]; intro ν; rw [embY_val]; exact Nat.mul_mod_right _ _
  -- the cones
  have hBK : ∀ w, pdist (embY ell k Lu hell z) w ≤ 13 * ell ^ k → ∀ d : Fin 3, BK S k (w, d) := by
    intro w hw d
    refine ⟨hdeep w (by omega), hdeep _ ?_⟩
    have := pdist_shift1 hw d
    show pdist (embY ell k Lu hell z) (coarseShift w 1 d) ≤ 14 * ell ^ k
    omega
  have hgB : AdalyFormal.CurvBlock.GoodBd ell Rp k (embY ell k Lu hell z, μ) := by
    refine goodBd_pd ell hell2 Rp k _ hc hdvd (fun w hw0 => fun ν μ' => ?_)
    have hw : pdist (embY ell k Lu hell z) w ≤ 12 * ell ^ k := hw0
    have hw1 : ∀ d, pdist (embY ell k Lu hell z) (coarseShift w 1 d) ≤ 13 * ell ^ k := fun d => by
      have := pdist_shift1 hw d; omega
    exact ⟨hBK w (by omega) ν, hBK _ (hw1 ν) μ', hBK _ (hw1 μ') ν, hBK w (by omega) μ'⟩
  have hgL : AdalyFormal.CurvBlock.goodL ell Rl k (embY ell k Lu hell z, μ) := by
    refine goodL_pd ell hell2 Rl k _ (fun b _ hb => ?_)
    have hb' : pdist (embY ell k Lu hell z) b.1 ≤ 13 * ell ^ k := by
      have : pdist (embY ell k Lu hell z, μ).1 b.1 ≤ ell ^ k := hb
      simp only at this; omega
    exact hBK b.1 hb' b.2
  have hmain := link_tower_na_loc ell hell2 V Rp Rl q0 e hq0 h0 he k hdvd hN hsm' k le_rfl _ hc hgB hgL
  refine hmain.trans (le_of_eq ?_)
  have e3 : ((ell : ℝ) ^ 2) ^ k * q0 = q1 := by
    rw [hq0d, ← pow_mul, mul_comm 2 k, pow_mul]; field_simp
  rw [e3, hed]; field_simp

#print axioms BK
#print axioms chart_bounds
#print axioms pdist_shift1
#print axioms tower_near

end AdalyFormal.M1DK
