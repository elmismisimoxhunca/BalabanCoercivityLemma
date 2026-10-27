import OG7
import AC_Base

/-!
# AC_OG7 -- ALL patch charts from `BallChartsAt` (lane allc_20261016)

`OG7.interfaceCharts_of_ball` produced the interface (down-case) patch charts from `BallChartsAt`; the up-case patches were served by a class cube
containing the centred box of side `12 M ell^j` (MR3/MR4), which needs cube factor `>= 12`.  Here BOTH cases come from `BallChartsAt`:

* down case : as OG7 (index `j`, level `j-1`), without the (unused) `not CentredIn` premise;
* up case (`Ball w (6 G_j)` meets `Omega_{j+1}`) : `BallChartsAt` at index `j+1` (level `j`): `w` is within `6 G_j <= 3 M ell^{j+1}` of `Omega_{j+1}`,
  `Ball w (r+1) subset Omega_j` (`R >= 24`), and the ball misses `Omega_{j+2}` (the patch anchor lies outside `Omega_{j+1}` within `G_j`, and
  `R b_{j+1} >= 48 G_j > 7 G_j`).
No cube factor appears.  `patchCharts_of_ballAC : BallChartsAt .. -> PatchCharts ..` (constant `12 M (C alpha_0)`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.OneGap

open AdalyFormal.M2Bridge
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball AgreeAt pdist_comm pdist_shift_le pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (M1Bounds M1Regular bstrat strat StratReads om_anti le_bstrat_of_mem mem_strat_of_pos gsp strat_eq_iff)
open AdalyFormal.M1W2 (caseB_down)
open AdalyFormal.M2Route (PatchCharts ChartOn chartRad)

variable {L : PeriodicLatticeExtent}

/-- a region chart on `Ball w (r+1)` is a `ChartOn` of radius `r` (the construction at the end of OG7). -/
theorem chartOn_of_regionAC {ell M f : ℕ} {α η : ℝ} {U : LinkCfg L} {w : PeriodicLatticeSite L} {r i : ℕ}
    (h : RegionChart (Ball w (r + 1)) ell M f α η i U) :
    ChartOn ell U η ((f : ℝ) * M * α) i w r := by
  classical
  obtain ⟨g, A, hexp, hd⟩ := h
  have hcb : ∀ e : Bond L, pdist w e.1 ≤ r → CubeBond (Ball w (r + 1)) e := by
    intro e he
    refine ⟨Nat.le_succ_of_le he, ?_⟩
    have := pdist_triangle w e.1 (periodicLatticeShift e.1 e.2)
    have := pdist_shift_le e.1 e.2
    show pdist w (periodicLatticeShift e.1 e.2) ≤ r + 1
    omega
  refine ⟨g, fun e => if CubeBond (Ball w (r + 1)) e then A e else 0, fun e => ?_, fun e he => ?_, fun e he => ?_,
    fun μ ν x hx hx' => ?_⟩
  · by_cases hc : CubeBond (Ball w (r + 1)) e
    · show HT (if CubeBond (Ball w (r + 1)) e then A e else 0)
      rw [if_pos hc]; exact hd.ht e hc
    · show HT (if CubeBond (Ball w (r + 1)) e then A e else 0)
      rw [if_neg hc]; simp [AdalyFormal.StatementLane.HT]
  · beta_reduce
    rw [if_pos (hcb e he)]; exact hexp e (hcb e he)
  · beta_reduce
    rw [if_pos (hcb e he)]
    exact hd.c1 e (hcb e he)
  · have b0 : CubeBond (Ball w (r + 1)) ((x, ν) : Bond L) := hcb (x, ν) hx
    have b1 : CubeBond (Ball w (r + 1)) ((periodicLatticeShift x μ, ν) : Bond L) := hcb (periodicLatticeShift x μ, ν) hx'
    beta_reduce
    simp only [if_pos b0, if_pos b1]
    exact hd.c2 μ ν x b0 b1

/-- the radius bound: `chartRad .. j i + 1 <= 6 G_j` for `i <= j` (when `d + 64 ell^2 + 2 <= M`). -/
theorem chartRad_le_sixAC {ell M d j i : ℕ} (hell : 2 ≤ ell) (hdM : d + 64 * ell ^ 2 + 2 ≤ M) (hij : i ≤ j) :
    chartRad ell M 1 5 d j i + 1 ≤ (5 + 1) * gsp ell M 1 j := by
  have hpi : ell ^ i ≤ ell ^ j := Nat.pow_le_pow_right (by omega) hij
  have hroom : (d + 64 * ell ^ 2 + 2) * ell ^ j ≤ M * ell ^ j := Nat.mul_le_mul_right _ hdM
  have hpj : 1 ≤ ell ^ j := Nat.one_le_pow _ _ (by omega)
  have hy' : chartRad ell M 1 5 d j i + 1 = 5 * gsp ell M 1 j + d * ell ^ i + 64 * ell ^ (i + 2) + 1 := rfl
  rw [AdalyFormal.M2Route.gsp_one] at hy' ⊢
  have e2 : ell ^ (i + 2) = ell ^ 2 * ell ^ i := by ring
  rw [e2] at hy'
  have h1' : d * ell ^ i ≤ d * ell ^ j := Nat.mul_le_mul_left _ hpi
  have h2' : 64 * (ell ^ 2 * ell ^ i) ≤ 64 * ell ^ 2 * ell ^ j := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hpi
  have hbs : bigSide M ell j = M * ell ^ j := rfl
  rw [hbs]
  nlinarith

theorem patchCharts_of_ballAC {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 0 < M)
    (hell : 2 ≤ ell) (hR : 24 ≤ R) (hR4 : (5 + 4) * 1 * ell ≤ R) {d : ℕ} (hdM : d + 64 * ell ^ 2 + 2 ≤ M)
    (hLthick : ∀ σ : Fin 3, 13 * (M * ell ^ k) ≤ L σ + 1)
    {C α₀ η : ℝ} {U : LinkCfg L} (hB : BallChartsAt ell M k S U C α₀ η) :
    PatchCharts ell M k 1 5 d S U η ((12 : ℕ) * M * (C * α₀)) := by
  classical
  intro j w hp
  have hjk' : j ≤ k := hp.1
  have hbs : ∀ i, bigSide M ell i = M * ell ^ i := fun i => rfl
  have hg1 := AdalyFormal.M2Route.gsp_one ell M j
  obtain ⟨x₀, hx0j, hxs, hd0⟩ := hp.anchor one_pos hM (by omega)
  rw [hg1, hbs] at hd0
  have hBj : 0 < M * ell ^ j := Nat.mul_pos hM (pow_pos (by omega) j)
  refine ⟨fun hup => ?_, fun hj hdown => ?_⟩
  · -- up case: BallChartsAt at index j + 1, level j
    obtain ⟨y, hyB, hy⟩ := hup
    have hjk1 : j + 1 ≤ k := by
      by_contra hc
      have : S.Om (j + 1) = ∅ := hS.2.1 (j + 1) (by omega)
      rw [this] at hy; exact hy
    set r : ℕ := chartRad ell M 1 5 d j j with hr
    have hr6 : r + 1 ≤ (5 + 1) * gsp ell M 1 j := chartRad_le_sixAC hell hdM le_rfl
    rw [hg1, hbs] at hr6
    have hyB' : pdist w y ≤ (5 + 1) * (M * ell ^ j) := by
      have := hyB; rw [hg1, hbs] at this; exact this
    have hb1 : bigSide M ell (j + 1) = ell * (M * ell ^ j) := by
      rw [hbs, pow_succ]; ring
    have hell1 : 2 * (M * ell ^ j) ≤ ell * (M * ell ^ j) := Nat.mul_le_mul_right _ hell
    have hRB : 24 * (M * ell ^ j) ≤ R * (M * ell ^ j) := Nat.mul_le_mul_right _ hR
    have hRB1 : 24 * (ell * (M * ell ^ j)) ≤ R * (ell * (M * ell ^ j)) := Nat.mul_le_mul_right _ hR
    -- the anchor lies outside Omega_{j+1}
    have hx0n : x₀ ∉ S.Om (j + 1) := by
      have : x₀ ∈ towerBj S j := (strat_eq_iff hS hjk' x₀).mpr ⟨om_anti hS (Nat.zero_le j) hx0j, hxs⟩
      exact this.2
    have hmiss1 : ∀ x ∈ Ball w (r + 1), x ∉ S.Om (j + 1 + 1) := by
      intro x hx hxO
      have hcol := hS.2.2.2.2.1 (j + 1) hjk1 x₀ hx0n x hxO
      have h1 : pdist w x ≤ r + 1 := hx
      have h3 := pdist_triangle x₀ w x
      rw [hb1] at hcol
      omega
    have hmiss : ∀ x ∈ Ball w (r + 1), x ∉ S.Om (j + 1 + 2) := fun x hx hxO =>
      hmiss1 x hx (om_anti hS (by omega : j + 1 + 1 ≤ j + 1 + 2) hxO)
    have hin : ∀ x ∈ Ball w (r + 1), x ∈ S.Om (j + 1 - 1) := by
      intro x hx
      show x ∈ S.Om j
      by_contra hxn
      have hcol := hS.2.2.2.2.1 j hjk' x hxn y hy
      have h1 : pdist w x ≤ r + 1 := hx
      have h3 := pdist_triangle x w y
      rw [pdist_comm x w] at h3
      rw [hbs] at hcol
      omega
    have hanc : ∃ x₁ ∈ S.Om (j + 1), pdist w x₁ ≤ 3 * (M * ell ^ (j + 1)) := by
      refine ⟨y, hy, ?_⟩
      have : M * ell ^ (j + 1) = ell * (M * ell ^ j) := by ring
      rw [this]; omega
    have hr7 : r + 1 ≤ 7 * M * ell ^ (j + 1) := by
      have : 7 * M * ell ^ (j + 1) = 7 * (ell * (M * ell ^ j)) := by ring
      rw [this]; omega
    have hnw : ∀ σ : Fin 3, 2 * (r + 1) + 2 ≤ L σ + 1 := by
      intro σ
      have hBjk : M * ell ^ j ≤ M * ell ^ k := Nat.mul_le_mul_left M (Nat.pow_le_pow_right (by omega) hjk')
      have hM2 : 2 ≤ M := by nlinarith [Nat.zero_le (64 * ell ^ 2), Nat.zero_le d]
      have hB2 : 2 ≤ M * ell ^ j := by
        have : 1 ≤ ell ^ j := Nat.one_le_pow _ _ (by omega)
        nlinarith
      have := hLthick σ
      omega
    have hreg := hB (j + 1) hjk1 w hanc (r + 1) hr7 hnw hin hmiss (Or.inr hmiss1)
    exact chartOn_of_regionAC hreg
  · -- down case: OG7 `interfaceCharts_of_ball` without the unused premise
    have hZi := caseB_down hS hell one_pos hM hR4 hp hj
    have hjk : j - 1 ≤ k := by omega
    set r : ℕ := chartRad ell M 1 5 d j (j - 1) with hr
    have hr6 : r + 1 ≤ (5 + 1) * gsp ell M 1 j := chartRad_le_sixAC hell hdM (by omega)
    have hr7 : r + 1 ≤ 7 * M * ell ^ j := by
      rw [hg1, hbs] at hr6
      nlinarith [Nat.zero_le (M * ell ^ j)]
    have hin : ∀ x ∈ Ball w (r + 1), x ∈ S.Om (j - 1) := fun x hx => hZi (le_trans hx hr6)
    have hmiss1 : ∀ x ∈ Ball w (r + 1), x ∉ S.Om (j + 1) := fun x hx hxO =>
      hdown ⟨x, le_trans hx hr6, hxO⟩
    have hmiss : ∀ x ∈ Ball w (r + 1), x ∉ S.Om (j + 2) := fun x hx hxO =>
      hmiss1 x hx (om_anti hS (by omega : j + 1 ≤ j + 2) hxO)
    have hanc : ∃ x₁ ∈ S.Om j, pdist w x₁ ≤ 3 * (M * ell ^ j) := by
      refine ⟨x₀, hx0j, ?_⟩
      rw [pdist_comm]
      omega
    have hnw : ∀ σ : Fin 3, 2 * (r + 1) + 2 ≤ L σ + 1 := by
      intro σ
      rw [hg1, hbs] at hr6
      have hBjk : M * ell ^ j ≤ M * ell ^ k := Nat.mul_le_mul_left M (Nat.pow_le_pow_right (by omega) hjk')
      have hB2 : 2 ≤ M * ell ^ j := by
        have hM2 : 2 ≤ M := by nlinarith [Nat.zero_le (64 * ell ^ 2), Nat.zero_le d]
        have : 1 ≤ ell ^ j := Nat.one_le_pow _ _ (by omega)
        nlinarith
      have := hLthick σ
      omega
    exact chartOn_of_regionAC (hB j hjk' w hanc (r + 1) hr7 hnw hin hmiss (Or.inr hmiss1))

theorem patchCharts_monoAC {ell M k d : ℕ} {S : Tower L} {U : LinkCfg L} {η a' b' : ℝ}
    (hη : 0 < η) (hab : a' ≤ b') (h : PatchCharts ell M k 1 5 d S U η a') :
    PatchCharts ell M k 1 5 d S U η b' := by
  intro j w hp
  obtain ⟨h1, h2⟩ := h j w hp
  exact ⟨fun hup => (h1 hup).mono_const hη hab, fun hj hd => (h2 hj hd).mono_const hη hab⟩

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.patchCharts_of_ballAC
