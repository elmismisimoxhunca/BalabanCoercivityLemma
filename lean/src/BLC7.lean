import BLC6

/-!
# BLC7 -- the ball chart at `j = 0`: complete axial gauge on the `ℓ¹` ball (m2_ballcharts, 2026-10-15)

At `j = 0` the target constants are `C · 12 M α₀` for BOTH clauses (no scale separation), the ball lies in `Ω₀`, but there
need not be any point of `Ω₁` within `(R - 18) M` of it, so the vertex machinery (GE5 `slab_cube` needs an `Ω_{m+1}` anchor)
does not apply.  Instead: the complete axial gauge `axG` (paths `0 → (p₀,0,0) → (p₀,p₁,0) → p`) makes `U^g(·,2) ≡ 1`,
`U^g(·,1) = 1` on `p₂ = 0`, `U^g(·,0) = 1` on `p₁ = p₂ = 0`; every plaquette of the ball is in `Ω₀`, so `CoversPlaqOm0c` +
`PerCubeRegular2` bound its holonomy by `4 · 12 M α₀`; the ladders give `|U^g − 1| ≤ 4 r · 12 M α₀` on the ball.
`ball_chart_zero`: `GChart` on `Ball w r` at `(56 M · X, 56 M · X)`, `X = 12 M α₀`, for `r ≤ 7M`, `Ball ⊆ Ω₀`, `X ≤ 1/2`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open Matrix

variable {L : PeriodicLatticeExtent}

/-! ## SU(2) norm facts -/

theorem su2_mul_sub_one (A B : SU2) :
    frobNorm (((A * B : SU2) : M2) - 1) ≤ frobNorm ((A : M2) - 1) + frobNorm ((B : M2) - 1) := by
  rw [coe_mul]
  have e : (A : M2) * (B : M2) - 1 = (A : M2) * ((B : M2) - 1) + ((A : M2) - 1) := by noncomm_ring
  rw [e]
  refine (AdalyFormal.Balaban.Bch2.frobNorm_add_le _ _).trans ?_
  rw [frobNorm_su2_mul]; linarith

theorem su2_inv_sub_one (A : SU2) : frobNorm (((A⁻¹ : SU2) : M2) - 1) = frobNorm ((A : M2) - 1) := by
  rw [coe_inv]; exact frobNorm_star_sub_one A

theorem su2_mul_inv_sub_one (A B : SU2) : frobNorm (((A * B⁻¹ : SU2) : M2) - 1) = frobNorm ((A : M2) - (B : M2)) := by
  rw [coe_mul, coe_inv]
  have e : (A : M2) * (B : M2)ᴴ - 1 = ((A : M2) - (B : M2)) * (B : M2)ᴴ := by
    rw [sub_mul, su2_mul_star]
  rw [e, frobNorm_mul_su2_star]

/-! ## ladders over `ℤ` -/

noncomputable def pUp (f : ℤ → SU2) : ℕ → SU2
  | 0 => 1
  | n + 1 => pUp f n * f n

noncomputable def pDn (f : ℤ → SU2) : ℕ → SU2
  | 0 => 1
  | n + 1 => pDn f n * (f (-((n : ℤ) + 1)))⁻¹

noncomputable def lad (f : ℤ → SU2) (t : ℤ) : SU2 := if 0 ≤ t then pUp f t.toNat else pDn f (-t).toNat

theorem lad_zero (f : ℤ → SU2) : lad f 0 = 1 := by
  simp [lad, pUp]

theorem lad_succ (f : ℤ → SU2) (t : ℤ) : lad f (t + 1) = lad f t * f t := by
  rcases le_or_gt 0 t with h | h
  · have h1 : 0 ≤ t + 1 := by omega
    unfold lad; rw [if_pos h1, if_pos h]
    have e : (t + 1).toNat = t.toNat + 1 := by omega
    rw [e, pUp, Int.toNat_of_nonneg h]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, t = -((m : ℤ) + 1) := ⟨(-t - 1).toNat, by omega⟩
    have e : (-(-((m : ℤ) + 1))).toNat = m + 1 := by omega
    unfold lad
    rw [if_neg (by omega : ¬ (0 ≤ -((m : ℤ) + 1))), e, pDn]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have e0 : (-(((0 : ℕ) : ℤ) + 1) + 1) = 0 := by norm_num
      rw [e0, if_pos le_rfl]
      simp [pUp, pDn]
    · rw [if_neg (by omega)]
      have e2 : (-(-((m : ℤ) + 1) + 1)).toNat = m := by omega
      rw [e2]; group

/-! ## the axial gauge -/

def v3 (a b c : ℤ) : Z3 := ![a, b, c]

theorem v3_eta (p : Z3) : v3 (p 0) (p 1) (p 2) = p := by
  funext i; fin_cases i <;> rfl

noncomputable def axG (U : LinkCfg L) (w : PeriodicLatticeSite L) (p : Z3) : SU2 :=
  lad (fun t => U (iota w (v3 t 0 0), 0)) (p 0) *
  lad (fun t => U (iota w (v3 (p 0) t 0), 1)) (p 1) *
  lad (fun t => U (iota w (v3 (p 0) (p 1) t), 2)) (p 2)

theorem axG_e2 (U : LinkCfg L) (w : PeriodicLatticeSite L) (p : Z3) :
    axG U w (p + ev 2) = axG U w p * U (iota w p, 2) := by
  have e0 : (p + ev 2) 0 = p 0 := by simp [ev]
  have e1 : (p + ev 2) 1 = p 1 := by simp [ev]
  have e2 : (p + ev 2) 2 = p 2 + 1 := by simp [ev]
  unfold axG; rw [e0, e1, e2, lad_succ]
  simp only [v3_eta]; group

theorem axG_e1 (U : LinkCfg L) (w : PeriodicLatticeSite L) (p : Z3) (h2 : p 2 = 0) :
    axG U w (p + ev 1) = axG U w p * U (iota w p, 1) := by
  have e0 : (p + ev 1) 0 = p 0 := by simp [ev]
  have e1 : (p + ev 1) 1 = p 1 + 1 := by simp [ev]
  have e2 : (p + ev 1) 2 = 0 := by simp [ev, h2]
  have hp : v3 (p 0) (p 1) 0 = p := by have := v3_eta p; rwa [h2] at this
  unfold axG; rw [e0, e1, e2, h2, lad_succ]
  simp only [lad_zero, hp]; group

theorem axG_e0 (U : LinkCfg L) (w : PeriodicLatticeSite L) (p : Z3) (h1 : p 1 = 0) (h2 : p 2 = 0) :
    axG U w (p + ev 0) = axG U w p * U (iota w p, 0) := by
  have e0 : (p + ev 0) 0 = p 0 + 1 := by simp [ev]
  have e1 : (p + ev 0) 1 = 0 := by simp [ev, h1]
  have e2 : (p + ev 0) 2 = 0 := by simp [ev, h2]
  have hp : v3 (p 0) 0 0 = p := by have := v3_eta p; rwa [h1, h2] at this
  unfold axG; rw [e0, e1, e2, h1, h2, lad_succ]
  simp only [lad_zero, hp]; group

/-- the site gauge. -/
noncomputable def axg (U : LinkCfg L) (w : PeriodicLatticeSite L) (r : ℕ) (x : PeriodicLatticeSite L) : SU2 :=
  axG U w (coord w r x)

theorem axg_V {U : LinkCfg L} {w : PeriodicLatticeSite L} {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) {p : Z3} {ν : Fin 3}
    (hp : p ∈ Box r) (hpν : p + ev ν ∈ Box r) :
    periodicGaugeTransform (axg U w r) U (iota w p, ν) = axG U w p * U (iota w p, ν) * (axG U w (p + ev ν))⁻¹ := by
  have hinj := inj_box w hL
  simp only [periodicGaugeTransform, axg]
  rw [iota_shift, coord_iota hinj hp, coord_iota hinj hpν]

/-! ## the `ℓ¹` ball in coordinates -/

def Bz (r : ℕ) : Set Z3 := {p | (p 0).natAbs + (p 1).natAbs + (p 2).natAbs ≤ r}

theorem Bz_sub_box {r : ℕ} : Bz r ⊆ Box r := by
  intro p hp i
  have h : (p 0).natAbs + (p 1).natAbs + (p 2).natAbs ≤ r := hp
  rw [Int.abs_eq_natAbs]
  have := Finset.single_le_sum (f := fun j : Fin 3 => (p j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [Fin.sum_univ_three] at this
  have : (p i).natAbs ≤ r := by omega
  exact_mod_cast this

theorem pcd_le_of_rep (N a b : ℕ) (ha : a < N) (hb : b < N) (d : ℤ) (h : ((a : ℤ) + d) % (N : ℤ) = b) :
    pcd N a b ≤ d.natAbs := by
  have hN : (0 : ℤ) < N := by omega
  have hk := Int.mul_ediv_add_emod ((a : ℤ) + d) (N : ℤ)
  rw [h] at hk
  set k := ((a : ℤ) + d) / (N : ℤ)
  unfold pcd
  have hm1 : ∀ x y : ℕ, min x y ≤ x := fun x y => min_le_left x y
  have hm2 : ∀ x y : ℕ, min x y ≤ y := fun x y => min_le_right x y
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have : (N : ℤ) * k ≤ -(N : ℤ) := by nlinarith
    split_ifs with hab
    · have := hm2 (b - a) (N - (b - a)); omega
    · have := hm2 (a - b) (N - (a - b)); omega
  · rw [hk0, mul_zero, zero_add] at hk
    split_ifs with hab
    · have := hm1 (b - a) (N - (b - a)); omega
    · have := hm1 (a - b) (N - (a - b)); omega
  · have : (N : ℤ) ≤ (N : ℤ) * k := by nlinarith
    split_ifs with hab
    · have := hm2 (b - a) (N - (b - a)); omega
    · have := hm2 (a - b) (N - (a - b)); omega

theorem iota_mem_ball {w : PeriodicLatticeSite L} {r : ℕ} {q : Z3} (hq : q ∈ Bz r) : iota w q ∈ Ball w r := by
  show pdist w (iota w q) ≤ r
  have hb : ∀ μ : Fin 3, pcd (L μ + 1) (w μ).val (iota w q μ).val ≤ (q μ).natAbs := by
    intro μ
    refine pcd_le_of_rep _ _ _ (w μ).isLt (iota w q μ).isLt (q μ) ?_
    rw [iota_val_int]
  have h : (q 0).natAbs + (q 1).natAbs + (q 2).natAbs ≤ r := hq
  unfold pdist
  rw [Fin.sum_univ_three]
  have := hb 0; have := hb 1; have := hb 2
  omega

theorem ball_sub_liftL1 (w : PeriodicLatticeSite L) (r : ℕ) : Ball w r ⊆ lift w (Bz r) := by
  intro x hx
  have hx' : pdist w x ≤ r := hx
  have hrep : ∀ μ : Fin 3, ∃ d : ℤ, |d| ≤ (pcd (L μ + 1) (w μ).val (x μ).val : ℤ) ∧
      (((w μ).val : ℤ) + d) % ((L μ + 1 : ℕ) : ℤ) = (x μ).val :=
    fun μ => pcd_rep (L μ + 1) (w μ).val (x μ).val (w μ).isLt (x μ).isLt
  choose d hd using hrep
  refine ⟨d, ?_, ?_⟩
  · show (d 0).natAbs + (d 1).natAbs + (d 2).natAbs ≤ r
    have h0 := (hd 0).1; have h1 := (hd 1).1; have h2 := (hd 2).1
    rw [Int.abs_eq_natAbs] at h0 h1 h2
    unfold pdist at hx'
    rw [Fin.sum_univ_three] at hx'
    omega
  · funext μ
    apply Fin.ext
    have := iota_val_int w d μ
    rw [(hd μ).2] at this
    exact_mod_cast this

/-! ## plaquettes -/

noncomputable def plq (U : LinkCfg L) (γ : PeriodicLatticeSite L → SU2) (x : PeriodicLatticeSite L) (μ ν : Fin 3) : SU2 :=
  periodicGaugeTransform γ U (x, μ) * periodicGaugeTransform γ U (periodicLatticeShift x μ, ν) *
    (periodicGaugeTransform γ U (periodicLatticeShift x ν, μ))⁻¹ * (periodicGaugeTransform γ U (x, ν))⁻¹

theorem plq_conj (U : LinkCfg L) (γ γ' : PeriodicLatticeSite L → SU2) (x : PeriodicLatticeSite L) (μ ν : Fin 3)
    (hc : periodicLatticeShift (periodicLatticeShift x μ) ν = periodicLatticeShift (periodicLatticeShift x ν) μ) :
    plq U γ x μ ν = (γ x * (γ' x)⁻¹) * plq U γ' x μ ν * (γ x * (γ' x)⁻¹)⁻¹ := by
  simp only [plq, periodicGaugeTransform]
  rw [hc]; group

theorem plq_le_four (U : LinkCfg L) (γ : PeriodicLatticeSite L → SU2) (x : PeriodicLatticeSite L) (μ ν : Fin 3) :
    frobNorm (((plq U γ x μ ν : SU2) : M2) - 1) ≤
      frobNorm (((periodicGaugeTransform γ U (x, μ) : SU2) : M2) - 1)
      + frobNorm (((periodicGaugeTransform γ U (periodicLatticeShift x μ, ν) : SU2) : M2) - 1)
      + frobNorm (((periodicGaugeTransform γ U (periodicLatticeShift x ν, μ) : SU2) : M2) - 1)
      + frobNorm (((periodicGaugeTransform γ U (x, ν) : SU2) : M2) - 1) := by
  have a := su2_mul_sub_one (periodicGaugeTransform γ U (x, μ) * periodicGaugeTransform γ U (periodicLatticeShift x μ, ν) *
    (periodicGaugeTransform γ U (periodicLatticeShift x ν, μ))⁻¹) (periodicGaugeTransform γ U (x, ν))⁻¹
  have b := su2_mul_sub_one (periodicGaugeTransform γ U (x, μ) * periodicGaugeTransform γ U (periodicLatticeShift x μ, ν))
    (periodicGaugeTransform γ U (periodicLatticeShift x ν, μ))⁻¹
  have c := su2_mul_sub_one (periodicGaugeTransform γ U (x, μ)) (periodicGaugeTransform γ U (periodicLatticeShift x μ, ν))
  have d1 := su2_inv_sub_one (periodicGaugeTransform γ U (periodicLatticeShift x ν, μ))
  have d2 := su2_inv_sub_one (periodicGaugeTransform γ U (x, ν))
  unfold plq
  linarith

/-- the plaquette bound from the class (every plaquette with its four corners in `Ω₀`). -/
theorem plq_class {ell M R k : ℕ} {S : Tower L} (hcov : CoversOm0p ell M 12 k S) (hell : 0 < ell)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2 ell M 12 k S α₀ η U)
    (hX : (12 : ℝ) * M * α₀ ≤ 1 / 2) {x : PeriodicLatticeSite L} {μ ν : Fin 3} (hμν : μ < ν)
    (h0 : x ∈ S.Om 0) (h1 : periodicLatticeShift x μ ∈ S.Om 0) (h2 : periodicLatticeShift x ν ∈ S.Om 0)
    (h3 : periodicLatticeShift (periodicLatticeShift x μ) ν ∈ S.Om 0)
    (hc : periodicLatticeShift (periodicLatticeShift x μ) ν = periodicLatticeShift (periodicLatticeShift x ν) μ)
    (γ : PeriodicLatticeSite L → SU2) :
    frobNorm (((plq U γ x μ ν : SU2) : M2) - 1) ≤ 4 * ((12 : ℝ) * M * α₀) := by
  have _hR : R = R := rfl
  set P : PeriodicLatticePlaquette L := (x, ⟨(μ, ν), hμν⟩) with hPdef
  have hedge : ∀ e ∈ periodicPlaquetteBoundaryEdges P, CubeBond (S.Om 0) e := by
    intro e he
    simp only [periodicPlaquetteBoundaryEdges, hPdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨h0, h1⟩
    · exact ⟨h1, h3⟩
    · exact ⟨h2, hc ▸ h3⟩
    · exact ⟨h0, h2⟩
  obtain ⟨sites, i, hq, hall⟩ := hcov.2 P hedge
  have hX0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hli : ((ell : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hell))
  have hli0 : 0 ≤ ((ell : ℝ) ^ i)⁻¹ := by positivity
  have ht : ((12 : ℕ) : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹ ≤ (12 : ℝ) * M * α₀ := by
    push_cast; nlinarith
  have hsm : ((12 : ℕ) : ℝ) * M * α₀ * ((ell : ℝ) ^ i)⁻¹ + ((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ 1 := by
    push_cast
    have : ((ell : ℝ) ^ i)⁻¹ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  obtain ⟨gc, hgc⟩ := gchart_of_cube hη hP hq hsm hell
  have eb : ∀ e ∈ periodicPlaquetteBoundaryEdges P,
      frobNorm (((periodicGaugeTransform gc U e : SU2) : M2) - 1) ≤ (12 : ℝ) * M * α₀ := by
    intro e he
    obtain ⟨a, b⟩ := hall e he
    exact (hgc.1 e.1 e.2 a b).trans ht
  have m : ∀ y τ, (y, τ) ∈ periodicPlaquetteBoundaryEdges P →
      frobNorm (((periodicGaugeTransform gc U (y, τ) : SU2) : M2) - 1) ≤ (12 : ℝ) * M * α₀ := fun y τ h => eb _ h
  have e1 := m x μ (by simp [periodicPlaquetteBoundaryEdges, hPdef])
  have e2 := m (periodicLatticeShift x μ) ν (by simp [periodicPlaquetteBoundaryEdges, hPdef])
  have e3 := m (periodicLatticeShift x ν) μ (by simp [periodicPlaquetteBoundaryEdges, hPdef])
  have e4 := m x ν (by simp [periodicPlaquetteBoundaryEdges, hPdef])
  have h4 := plq_le_four U gc x μ ν
  rw [plq_conj U γ gc x μ ν hc, frobNorm_conj_sub_one]
  linarith

end AdalyFormal.M2BallCharts
