import UW6

/-!
# UW7 -- the clause-2 stacking step: velocity bounds and the profile in `ℤ³` (lane unif_20261016)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.UnifLane.Z

open Matrix
open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (frobNorm_sub_le' frobNorm_sub_comm frobNorm_su2_mul frobNorm_mul_su2 gauge_step_one
  gauge_step_two icay cay acos2 acos2_nonneg cay_icay frobNorm_icay_sub_le frobNorm_icay_le isSu2_icay frobNorm_mul_le)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv coe_one)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul IsSu2)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)

/-- the element whose inverse Cayley image is the velocity. -/
def hV (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (c : ℤ) (Go Gn : Z3 → SU2) (x : Z3) : SU2 :=
  (Az W σ Go x)⁻¹ * gt W (G0 W σ c Go Gn) x σ

/-- the plane velocity, extended to `ℤ³` by the plane projection. -/
noncomputable def fh (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (c : ℤ) (lo hi : Z3) (Go Gn : Z3 → SU2) (y : Z3) : M2 :=
  Vf W σ c Go Gn (clampP σ c lo hi y)

/-- the height above the plane. -/
def tp (σ : Fin 3) (c : ℤ) (p : Z3) : ℕ := (p σ - c).toNat

/-- the profile at a point of `ℤ³`. -/
noncomputable def Fz (W : Z3 → Fin 3 → SU2) (σ τ₁ τ₂ : Fin 3) (c : ℤ) (lo hi : Z3) (Go Gn : Z3 → SU2) (w : ℕ) (p : Z3) : M2 :=
  Phi w (fun n => P2 τ₁ τ₂ n (fh W σ c lo hi Go Gn)) (tp σ c p) (bp σ c p)

noncomputable def VBc (o1 n1 : ℝ) : ℝ := o1 + n1
noncomputable def Dvc (o1 o2 n1 n2 η : ℝ) : ℝ := 2 * (o2 + g02c o1 o2 n1 n2 η)
noncomputable def F1c (o1 o2 n1 n2 η : ℝ) (w : ℕ) : ℝ := 21 * VBc o1 n1 + 8 * w * Dvc o1 o2 n1 n2 η
noncomputable def F2c (o1 o2 n1 n2 η : ℝ) (w : ℕ) : ℝ := 84 * VBc o1 n1 / w + 186 * Dvc o1 o2 n1 n2 η

theorem tp_add_self {σ : Fin 3} {c : ℤ} {p : Z3} (h : c ≤ p σ) : tp σ c (p + ev σ) = tp σ c p + 1 := by
  simp only [tp, Pi.add_apply, ev_apply_self]; omega

theorem tp_add_ne {σ : Fin 3} {c : ℤ} (p : Z3) {ν : Fin 3} (h : ν ≠ σ) : tp σ c (p + ev ν) = tp σ c p := by
  simp [tp, ev_apply_ne (Ne.symm h)]

theorem tp_plane {σ : Fin 3} {c : ℤ} {p : Z3} (h : p σ = c) : tp σ c p = 0 := by simp [tp, h]

section vel
variable {W : Z3 → Fin 3 → SU2} {σ : Fin 3} {lo hi : Z3} {c0 c ch : ℤ} {Go Gn : Z3 → SU2}
  (hc0 : c0 + 2 ≤ c) (hch : c + 2 ≤ ch)
  {o1 o2 n1 n2 η : ℝ}
  (hO1 : C1 W Go (SlabS σ lo hi c0 c) o1) (hO2 : C2 W Go (SlabS σ lo hi c0 c) o2)
  (hN1 : C1 W Gn (SlabS σ lo hi c ch) n1) (hN2 : C2 W Gn (SlabS σ lo hi c ch) n2)
  (hH : HolB W (SlabS σ lo hi c0 ch) η)
  (ho1 : 0 ≤ o1) (hn1 : 0 ≤ n1) (hη : 0 ≤ η) (ho2 : 0 ≤ o2) (hn2 : 0 ≤ n2) (hsm : o1 + n1 ≤ 2)
include hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm

theorem hv_bound {x : Z3} (hx : x ∈ SlabS σ lo hi c ch) (hxc : x σ = c) :
    frobNorm (((hV W σ c Go Gn x : SU2) : M2) - 1) ≤ VBc o1 n1 := by
  unfold hV VBc
  refine (n_mul _ _).trans ?_
  rw [n_inv, gt_G0, bp_add_self, n_conj]
  have := az_bound hc0 hch hO1 hx hxc
  have := hN1 x σ hx (plane_N hch hx hxc)
  linarith

theorem vf_bound {x : Z3} (hx : x ∈ SlabS σ lo hi c ch) (hxc : x σ = c) :
    frobNorm (Vf W σ c Go Gn x) ≤ VBc o1 n1 := by
  have h := hv_bound hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hx hxc
  exact (frobNorm_icay_le (h.trans (by unfold VBc; linarith))).trans h

theorem cay_vf {x : Z3} (hx : x ∈ SlabS σ lo hi c ch) (hxc : x σ = c) : cay (Vf W σ c Go Gn x) = hV W σ c Go Gn x := by
  have h := hv_bound hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hx hxc
  exact cay_icay (h.trans (by unfold VBc; linarith))

theorem vf_d1 {x : Z3} (hx : x ∈ SlabS σ lo hi c ch) (hxc : x σ = c) {ν : Fin 3} (hν : ν ≠ σ)
    (hxν : x + ev ν ∈ SlabS σ lo hi c ch) :
    frobNorm (Vf W σ c Go Gn (x + ev ν) - Vf W σ c Go Gn x) ≤ Dvc o1 o2 n1 n2 η := by
  have hxc' : (x + ev ν) σ = c := by simp [ev_apply_ne (Ne.symm hν), hxc]
  have h0 := hv_bound hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hx hxc
  have h1 := hv_bound hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hxν hxc'
  unfold Vf
  refine (frobNorm_icay_sub_le (acos2_nonneg (h1.trans (by unfold VBc; linarith)))
    (acos2_nonneg (h0.trans (by unfold VBc; linarith)))).trans ?_
  unfold Dvc
  have m := mul_diff ((Az W σ Go (x + ev ν))⁻¹) (gt W (G0 W σ c Go Gn) (x + ev ν) σ)
    ((Az W σ Go x)⁻¹) (gt W (G0 W σ c Go Gn) x σ)
  rw [inv_diff] at m
  -- Az difference
  have hb := plane_below σ lo hi c0 c ch hc0 (by omega) hx hxc
  have hbν := plane_below σ lo hi c0 c ch hc0 (by omega) hxν hxc'
  have az : frobNorm (((Az W σ Go (x + ev ν) : SU2) : M2) - ((Az W σ Go x : SU2) : M2)) ≤ o2 := by
    have := hO2 (x - ev σ - ev σ) ν σ hb.2 (by rw [show x - ev σ - ev σ + ev σ = x - ev σ by abel]; exact hb.1)
      (by rw [show x - ev σ - ev σ + ev ν = x + ev ν - ev σ - ev σ by abel]; exact hbν.2)
      (by rw [show x - ev σ - ev σ + ev ν + ev σ = x + ev ν - ev σ by abel]; exact hbν.1)
    simp only [Az]; rw [show x + ev ν - ev σ - ev σ = x - ev σ - ev σ + ev ν by abel]; exact this
  -- the σ-bond difference from the clause 2 of `G0`
  have g := g0_c2 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 x ν σ hx (plane_N hch hx hxc) hxν
    (by rw [show x + ev ν + ev σ = x + ev ν + ev σ from rfl]; exact plane_N hch hxν hxc')
  have : 0 ≤ g02c o1 o2 n1 n2 η := by unfold g02c K0c; positivity
  unfold hV
  nlinarith

end vel

end AdalyFormal.UnifLane.Z
