import OG4
import SG3

/-!
# OG5 -- from a region chart on a ball to an `AnchorChart` (lane m2_onegap_20261015)

* `cubeData12_of_region` : a `RegionChart` at scale `ℓ^{j-1}` on a region containing `sites` gives `CubeData12` at index `j` and constant `ℓ³·α'` (`bound_transfer`).
* geometry : `ball_mem_below`, `ball_not_above` (collars), `offc_corner`, `cornerSite`.
* `anchorChart_of_ball` : `BallChartsAt` at an anchor `y ∈ Ω_j \ Ω_{j+1}` (`1 ≤ j ≤ k`) gives `AnchorChart ell M k S U (ℓ³·(C α₀)) η y (16 ℓ^j)` through `regime_of_virtual`.
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
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.M1 (M1Bounds M1Regular bstrat strat StratReads om_anti le_bstrat_of_mem mem_strat_of_pos)
open AdalyFormal.M2F123 (AnchorChart)

variable {L : PeriodicLatticeExtent}

section cd
variable {ell M f : ℕ} {α' η : ℝ}

theorem cubeData12_of_region (hell : 1 ≤ ell) (hη : 0 < η) (hα : 0 ≤ α')
    {Rg sites : Set (PeriodicLatticeSite L)} (hsub : sites ⊆ Rg) {j : ℕ} (hj : 1 ≤ j) {U : LinkCfg L}
    (h : RegionChart Rg ell M f α' η (j - 1) U) :
    ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → M2m),
      (∀ e : Bond L, CubeBond sites e →
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : M2m)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e)) ∧
      CubeData12 ell M f ((ell : ℝ) ^ 3 * α') η sites j A := by
  obtain ⟨g, A, hexp, hd⟩ := h
  have hsubB : ∀ e : Bond L, CubeBond sites e → CubeBond Rg e := fun e he => cubeBond_mono hsub he
  refine ⟨g, A, fun e he => hexp e (hsubB e he), fun e he => hd.ht e (hsubB e he), ?_, ?_⟩
  · intro e he
    exact bound_transfer hell hη (j := j - 1) (j' := j) (by omega) (by norm_num) hα (hd.c1 e (hsubB e he))
  · intro μ ν x h1' h2'
    exact bound_transfer hell hη (j := j - 1) (j' := j) (by omega) (by norm_num) hα
      (hd.c2 μ ν x (hsubB _ h1') (hsubB _ h2'))

end cd

section geom
variable {ell M R k : ℕ} {S : Tower L}

theorem strat_le_of_not_mem (hS : Admissible ell M R k S) {j : ℕ} {x : PeriodicLatticeSite L} (hx : x ∉ S.Om (j + 2)) :
    strat S k x ≤ j + 1 := by
  by_contra h
  push_neg at h
  exact hx (om_anti hS (by omega : j + 2 ≤ strat S k x) (mem_strat_of_pos (by omega)))

theorem bstrat_le_of_not_mem (hS : Admissible ell M R k S) {j : ℕ} {e : Bond L} (hx : e.1 ∉ S.Om (j + 2)) :
    bstrat S k e ≤ j + 1 :=
  le_trans (min_le_left _ _) (strat_le_of_not_mem hS hx)

theorem ball_mem_below (hS : Admissible ell M R k S) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {w : PeriodicLatticeSite L}
    (hw : w ∈ S.Om j) {r : ℕ} (hr : r ≤ R * bigSide M ell (j - 1)) : ∀ x ∈ Ball w r, x ∈ S.Om (j - 1) := by
  intro x hx
  by_contra hxn
  have hw' : w ∈ S.Om (j - 1 + 1) := by rw [show j - 1 + 1 = j by omega]; exact hw
  have h1 := hS.2.2.2.2.1 (j - 1) (by omega) x hxn w hw'
  have h2 : pdist w x ≤ r := hx
  have h3 := pdist_comm w x
  omega

theorem ball_not_above (hS : Admissible ell M R k S) {j : ℕ} {y : PeriodicLatticeSite L} (hy : y ∉ S.Om (j + 1))
    {r : ℕ} (hr : r ≤ R * bigSide M ell (j + 1)) : ∀ x ∈ Ball y r, x ∉ S.Om (j + 2) := by
  intro x hx hxO
  by_cases hjk : j + 1 ≤ k
  · have h1 := hS.2.2.2.2.1 (j + 1) hjk y hy x hxO
    have h2 : pdist y x ≤ r := hx
    omega
  · rw [hS.2.1 (j + 2) (by omega)] at hxO
    exact hxO

end geom

section corner

theorem offc_corner {N u h : ℕ} (hN : 0 < N) (hu : u < N) (hh : h < N) : (u + (N - (u + N - h) % N)) % N = h := by
  by_cases hle : h ≤ u
  · have e1 : (u + N - h) % N = u - h := by
      rw [show u + N - h = (u - h) + N by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    rw [e1, show u + (N - (u - h)) = h + N by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hh
  · have e1 : (u + N - h) % N = u + N - h := Nat.mod_eq_of_lt (by omega)
    rw [e1, show u + (N - (u + N - h)) = h by omega]; exact Nat.mod_eq_of_lt hh

/-- the corner `y - (h,h,h)` -/
def cornerSite (y : PeriodicLatticeSite L) (h : ℕ) : PeriodicLatticeSite L :=
  fun σ => ⟨((y σ).val + (L σ + 1) - h) % (L σ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem offc_cornerSite (y : PeriodicLatticeSite L) {h : ℕ} (hh : ∀ σ, h < L σ + 1) (σ : Fin 3) :
    offc (cornerSite y h) y σ = h :=
  offc_corner (Nat.succ_pos _) (y σ).isLt (hh σ)

end corner

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.cubeData12_of_region
#print axioms AdalyFormal.OneGap.ball_mem_below
#print axioms AdalyFormal.OneGap.ball_not_above
#print axioms AdalyFormal.OneGap.offc_cornerSite
