import DE3
import LF3

/-!
# DF -- `HarmDecayAt` at the flat configuration (m1_w2_decay, 2026-10-14)

On the two-stratum patch geometry `G = geomOf ell (i+1) (patchTower i Rg)` (`Rg` block-closed at `ell^{i+1}`,
`ell^{i+1} ∣ L μ + 1`), the constraint blocks form a `Classes L (ell^i) ell` partition (`patchClasses`: big blocks
`ell^{i+1}` in `Rg`, small blocks `ell^i` outside, ancestor `cc`).  For `h ∈ HK G 1 K` (`K = Ball w (s + d ell^i)`):
* `h = Δ μ`, `μ ∈ N(Q')`: zero class sums (`hsum_patch`), Poincaré `‖μ‖² ≤ 6 (ell·ell^i)² ‖Dμ‖²` (`poinc_patch`);
* `h ⟂ Δ N_K` gives `Δh` constant on every class inside `K` (`kconst_patch`);
* `interior_bound` + `S_bound` with the smoothed cutoff `smoothCut w a R R`, `R = r·ell^i`, `r = (d − 12 ell − 3)/7`.
**`harmDecay_flat`** : for `12 ell + 10 ≤ d`, `HarmDecayAt ell L 1 (epsD ell d) d`, `epsD ell d = CB·CA ell·ell²/r`.
**`epsD_small`** : `epsD ell d → 0` (for every `δ > 0` there is `D` with `epsD ell d ≤ δ` for `d ≥ D`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1Decay

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (pdist BlockClosed)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf)
open AdalyFormal.M1Patch (corner corner_dvd patchTower mem_lam_j mem_lam_succ om0_univ patch_proper Pc poincare_patch
  flat_hU flat_hT)
open AdalyFormal.LemIFlat (cc corner_mem_Rg mem_blockOf_iff_corner corner_idem single_diff_mem Qlev_flat)
open AdalyFormal.M1W2 (HK VK NK suppIn HarmDecayAt)

variable {L : PeriodicLatticeExtent}

theorem fit_of_dvd {m c N : ℕ} (hc : m ∣ c) (hN : m ∣ N) (hlt : c < N) : c + m ≤ N := by
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨b, rfl⟩ := hN
  have hab : a < b := Nat.lt_of_mul_lt_mul_left hlt
  have h2 := Nat.mul_le_mul_left m (show a + 1 ≤ b by omega)
  rw [Nat.mul_succ] at h2
  exact h2

open Classical in
/-- the side of the constraint block of `x`. -/
noncomputable def pnn (ell i : ℕ) (Rg : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L) : ℕ :=
  if x ∈ Rg then ell ^ (i + 1) else ell ^ i

section geom
variable {ell i : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (i + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1)

include hell hRg in
theorem cc_mem_Rg (x : PeriodicLatticeSite L) : cc ell i Rg x ∈ Rg ↔ x ∈ Rg := by
  classical
  have hn : 0 < ell ^ i := pow_pos hell i
  have hN : 0 < ell ^ (i + 1) := pow_pos hell (i + 1)
  have hnN : ell ^ i ∣ ell ^ (i + 1) := pow_dvd_pow ell (Nat.le_succ i)
  unfold cc
  by_cases hx : x ∈ Rg
  · rw [if_pos hx]; exact ⟨fun _ => hx, fun _ => (corner_mem_Rg hell hRg hN (dvd_refl _) x).mpr hx⟩
  · rw [if_neg hx]; exact corner_mem_Rg hell hRg hn hnN x

include hell hRg in
theorem pnn_cc (x : PeriodicLatticeSite L) : pnn ell i Rg (cc ell i Rg x) = pnn ell i Rg x := by
  classical
  unfold pnn
  by_cases hx : x ∈ Rg
  · rw [if_pos hx, if_pos ((cc_mem_Rg hell hRg x).mpr hx)]
  · rw [if_neg hx, if_neg (fun h => hx ((cc_mem_Rg hell hRg x).mp h))]

/-- the constraint blocks of the patch geometry as a `Classes` partition. -/
noncomputable def patchClasses : Classes L (ell ^ i) ell where
  anc := cc ell i Rg
  nn := pnn ell i Rg
  nn_ge := fun x => by
    classical
    unfold pnn; split_ifs
    · exact Nat.pow_le_pow_right hell (Nat.le_succ i)
    · exact le_rfl
  nn_le := fun x => by
    classical
    unfold pnn; split_ifs
    · exact le_of_eq (by ring)
    · exact Nat.le_mul_of_pos_left _ hell
  mem := fun x z => by
    classical
    have hn : 0 < ell ^ i := pow_pos hell i
    have hN : 0 < ell ^ (i + 1) := pow_pos hell (i + 1)
    have hnN : ell ^ i ∣ ell ^ (i + 1) := pow_dvd_pow ell (Nat.le_succ i)
    have cN : ∀ y : PeriodicLatticeSite L, corner (ell ^ (i + 1)) y ∈ Rg ↔ y ∈ Rg :=
      fun y => corner_mem_Rg hell hRg hN (dvd_refl _) y
    have cn : ∀ y : PeriodicLatticeSite L, corner (ell ^ i) y ∈ Rg ↔ y ∈ Rg :=
      fun y => corner_mem_Rg hell hRg hn hnN y
    unfold cc pnn
    by_cases hx : x ∈ Rg <;> by_cases hz : z ∈ Rg
    · rw [if_pos hx, if_pos hx, if_pos hz, mem_blockOf_iff_corner hN _ z (corner_dvd _ x)]
    · rw [if_pos hx, if_pos hx, if_neg hz, mem_blockOf_iff_corner hN _ z (corner_dvd _ x)]
      constructor
      · intro h; exact absurd ((cn z).mp (by rw [h]; exact (cN x).mpr hx)) hz
      · intro h; exact absurd ((cN z).mp (by rw [h]; exact (cN x).mpr hx)) hz
    · rw [if_neg hx, if_neg hx, if_pos hz, mem_blockOf_iff_corner hn _ z (corner_dvd _ x)]
      constructor
      · intro h; exact absurd ((cn x).mp (by rw [← h]; exact (cN z).mpr hz)) hx
      · intro h; exact absurd ((cn x).mp (by rw [← h]; exact (cn z).mpr hz)) hx
    · rw [if_neg hx, if_neg hx, if_neg hz, mem_blockOf_iff_corner hn _ z (corner_dvd _ x)]
  fit := fun x μ => by
    classical
    have hnN : ell ^ i ∣ ell ^ (i + 1) := pow_dvd_pow ell (Nat.le_succ i)
    unfold cc pnn
    split_ifs
    · exact fit_of_dvd (corner_dvd _ x μ) (hdvd μ) (corner _ x μ).isLt
    · exact fit_of_dvd (corner_dvd _ x μ) (hnN.trans (hdvd μ)) (corner _ x μ).isLt
  nn_eq := fun x z h => by
    rw [← pnn_cc hell hRg z, ← pnn_cc hell hRg x, h]

theorem patchClasses_anc (x : PeriodicLatticeSite L) : (patchClasses hell hRg hdvd).anc x = cc ell i Rg x := rfl

theorem patchClasses_nn (x : PeriodicLatticeSite L) : (patchClasses hell hRg hdvd).nn x = pnn ell i Rg x := rfl

/-- the ancestor is a constraint-lattice point of the right level. -/
theorem qlev_class_zero (μ : SiteL2 L) (hμ : μ ∈ NQp (geomOf ell (i + 1) (patchTower i Rg)) (flatCfg : Cfg L))
    (x : PeriodicLatticeSite L) : ∑ z ∈ (patchClasses hell hRg hdvd).cls x, μ z = 0 := by
  classical
  rw [Classes.cls_eq_block, patchClasses_anc, patchClasses_nn]
  have hG : (geomOf ell (i + 1) (patchTower i Rg)).ell = ell := rfl
  have hc0 : ∀ j : ℕ, ((1 / (ell : ℝ) ^ 3) ^ j) ≠ 0 := fun j => by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  unfold cc pnn
  by_cases hx : x ∈ Rg
  · rw [if_pos hx, if_pos hx]
    have hL : corner (ell ^ (i + 1)) x ∈ (geomOf ell (i + 1) (patchTower i Rg)).Lam (i + 1) :=
      (mem_lam_succ ell i Rg _).mpr ⟨corner_dvd _ x,
        (corner_mem_Rg hell hRg (pow_pos hell _) (dvd_refl _) x).mpr hx⟩
    have h := hμ.2 (i + 1) le_rfl _ hL
    rw [Qlev_flat _ (by rw [hG]; exact hell), hG] at h
    exact (smul_eq_zero.mp h).resolve_left (hc0 _)
  · rw [if_neg hx, if_neg hx]
    have hL : corner (ell ^ i) x ∈ (geomOf ell (i + 1) (patchTower i Rg)).Lam i :=
      (mem_lam_j ell i Rg _).mpr ⟨corner_dvd _ x, fun h => hx ((corner_mem_Rg hell hRg (pow_pos hell _)
        (pow_dvd_pow ell (Nat.le_succ i)) x).mp h)⟩
    have h := hμ.2 i (Nat.le_succ i) _ hL
    rw [Qlev_flat _ (by rw [hG]; exact hell), hG] at h
    exact (smul_eq_zero.mp h).resolve_left (hc0 _)

end geom

/-- `lapDir = lapFull` on the patch geometry (`Ω₀ = univ`). -/
theorem lapDir_patch (ell i : ℕ) (Rg : Set (PeriodicLatticeSite L)) (U : Cfg L) (f : SiteL2 L) :
    lapDir (geomOf ell (i + 1) (patchTower i Rg)) U f = lapFull U f := by
  simp only [lapDir, ContinuousLinearMap.comp_apply, om0_univ i Rg ell, AdalyFormal.SliceCoerc.siteMask_univ,
    ContinuousLinearMap.id_apply]

/-- Poincaré on `N(Q')` of the patch, flat: `‖μ‖² ≤ 6 (ell · ell^i)² ‖Dμ‖²`. -/
theorem poinc_patch {ell i : ℕ} (hell : 2 ≤ ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (i + 1)) Rg)
    (hdvd : ∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1) (μ : SiteL2 L)
    (hμ : μ ∈ NQp (geomOf ell (i + 1) (patchTower i Rg)) (flatCfg : Cfg L)) :
    ‖μ‖ ^ 2 ≤ 6 * ((ell : ℝ) * (ell ^ i : ℕ)) ^ 2 * ‖gradL2 (U0 L) μ‖ ^ 2 := by
  have hell0 : 0 < ell := by omega
  have h := poincare_patch hell hdvd (patch_proper hell0 hRg) (om0_univ i Rg ell) (flatCfg : Cfg L) 1 one_pos 0 le_rfl
    (by norm_num) (flat_hU ell (i + 1) _) (flat_hT ell (i + 1) _) μ hμ
  have hPc : Pc ell (i + 1) 1 0 ^ 2 = 6 * ((ell : ℝ) * (ell ^ i : ℕ)) ^ 2 := by
    unfold Pc
    rw [Real.sq_sqrt (by positivity)]
    have e1 : max (6 : ℝ) (16 / (3 * 1)) = 6 := by norm_num
    have e2 : (1 : ℝ) - 216 * 0 ^ 2 = 1 := by norm_num
    rw [e1, e2, div_one]; push_cast; ring
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, hPc] at h2
  exact h2

/-- `h ⟂ Δ N_K` makes `Δh` take the same value at `z` and `cc z` when both lie in `K`. -/
theorem kcc_patch {ell i : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (i + 1)) Rg)
    (K : Set (PeriodicLatticeSite L)) (μ : SiteL2 L)
    (hperp : lapFull (U0 L) μ ∈ (VK (geomOf ell (i + 1) (patchTower i Rg)) (flatCfg : Cfg L) K)ᗮ)
    (z : PeriodicLatticeSite L) (hz : z ∈ K) (hcz : cc ell i Rg z ∈ K) :
    lapFull (U0 L) (lapFull (U0 L) μ) z = lapFull (U0 L) (lapFull (U0 L) μ) (cc ell i Rg z) := by
  classical
  set k := lapFull (U0 L) (lapFull (U0 L) μ) with hk
  set s : SuTwo := k z - k (cc ell i Rg z) with hs
  set ν : SiteL2 L := WithLp.toLp 2 (Pi.single z s - Pi.single (cc ell i Rg z) s) with hν
  have hνN : ν ∈ NK (geomOf ell (i + 1) (patchTower i Rg)) (flatCfg : Cfg L) K := by
    refine ⟨single_diff_mem hell hRg z s, fun y hy => ?_⟩
    have h1 : y ≠ z := fun h => hy (h ▸ hz)
    have h2 : y ≠ cc ell i Rg z := fun h => hy (h ▸ hcz)
    show (Pi.single z s - Pi.single (cc ell i Rg z) s : PeriodicLatticeSite L → SuTwo) y = 0
    rw [Pi.sub_apply, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, sub_zero]
  have hV : lapDir (geomOf ell (i + 1) (patchTower i Rg)) (flatCfg : Cfg L) ν
      ∈ VK (geomOf ell (i + 1) (patchTower i Rg)) (flatCfg : Cfg L) K :=
    Submodule.mem_map_of_mem hνN
  have h00 := (Submodule.mem_orthogonal _ _).mp hperp _ hV
  rw [lapDir_patch, lapFull_symm, real_inner_comm] at h00
  have h0 : ⟪k, ν⟫ = 0 := h00
  rw [PiLp.inner_apply] at h0
  simp only [hν, WithLp.ofLp_toLp, Pi.sub_apply, inner_sub_right] at h0
  rw [Finset.sum_sub_distrib] at h0
  have e1 : ∑ y, ⟪k y, (Pi.single z s : PeriodicLatticeSite L → SuTwo) y⟫ = ⟪k z, s⟫ := by
    rw [Finset.sum_eq_single z (fun y _ hy => by rw [Pi.single_eq_of_ne hy, inner_zero_right])
      (fun h => absurd (Finset.mem_univ z) h), Pi.single_eq_same]
  have e2 : ∑ y, ⟪k y, (Pi.single (cc ell i Rg z) s : PeriodicLatticeSite L → SuTwo) y⟫ = ⟪k (cc ell i Rg z), s⟫ := by
    rw [Finset.sum_eq_single (cc ell i Rg z) (fun y _ hy => by rw [Pi.single_eq_of_ne hy, inner_zero_right])
      (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same]
  rw [e1, e2, ← inner_sub_left, ← hs, real_inner_self_eq_norm_sq] at h0
  have : s = 0 := norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)
  exact sub_eq_zero.mp this

/-! ## the decay constant -/

/-- the number of cutoff widths (in units of `ell^i`). -/
def rD (ell d : ℕ) : ℕ := (d - 12 * ell - 3) / 7

/-- **the decay constant** `epsD ell d = CB · CA ell · ell² / rD ell d`. -/
noncomputable def epsD (ell d : ℕ) : ℝ := CB * CA ell * (ell : ℝ) ^ 2 / (rD ell d : ℝ)

theorem rD_pos {ell d : ℕ} (hd : 12 * ell + 10 ≤ d) : 1 ≤ rD ell d := by
  unfold rD; omega

theorem rD_room {ell d : ℕ} : 7 * rD ell d + 12 * ell + 3 ≤ d ∨ d < 12 * ell + 3 := by
  unfold rD; omega

theorem CB_pos : 0 < CB := by unfold CB; have := Kb_pos; linarith

theorem CA_pos {ell : ℕ} (hell : 1 ≤ ell) : 0 < CA ell := by
  unfold CA
  have := Kb_pos
  have : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  positivity

theorem epsD_nonneg (ell d : ℕ) (hell : 1 ≤ ell) : 0 ≤ epsD ell d := by
  unfold epsD
  have := CB_pos; have := CA_pos hell
  positivity

/-- `epsD ell d → 0` as `d → ∞`. -/
theorem epsD_small (ell : ℕ) (hell : 1 ≤ ell) (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℕ, 12 * ell + 10 ≤ D ∧ ∀ d, D ≤ d → epsD ell d ≤ δ := by
  set C := CB * CA ell * (ell : ℝ) ^ 2 with hC
  have hC0 : 0 < C := by
    have := CB_pos; have := CA_pos hell
    have : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (C / δ)
  refine ⟨7 * (n + 1) + 12 * ell + 10, by omega, fun d hd => ?_⟩
  have hr : n + 1 ≤ rD ell d := by unfold rD; omega
  have hr' : ((n : ℝ) + 1) ≤ (rD ell d : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < rD ell d := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  unfold epsD
  rw [← hC, div_le_iff₀ hrpos]
  have h1 : C < δ * n := by have := (div_lt_iff₀ hδ).mp hn; linarith
  nlinarith

/-! ## the main theorem -/

open Classical in
/-- **`HarmDecayAt` at `U = 1`**, polynomial decay `epsD ell d = CB·CA ell·ell²/rD ell d`. -/
theorem harmDecay_flat {ell : ℕ} (hell : 2 ≤ ell) (L : PeriodicLatticeExtent) (d : ℕ) (hd : 12 * ell + 10 ≤ d) :
    HarmDecayAt ell L (flatCfg : Cfg L) (epsD ell d) d := by
  intro i Rg hRg hdvd w s h hh
  have hell0 : 0 < ell := by omega
  have hell1 : 1 ≤ ell := by omega
  set B := ell ^ i with hBdef
  have hB : 1 ≤ B := Nat.one_le_pow _ _ hell0
  set G := geomOf ell (i + 1) (patchTower i Rg) with hG
  set K := Ball w (s + d * ell ^ i) with hK
  obtain ⟨hR, hperp⟩ := Submodule.mem_inf.mp hh
  obtain ⟨μ, hμN, hμh⟩ := Submodule.mem_map.mp hR
  have hhμ : h = lapFull (U0 L) μ := by rw [← hμh]; exact lapDir_patch ell i Rg _ μ
  subst hhμ
  set Cl := patchClasses hell0 hRg hdvd with hCl
  have hsum : ∀ x, ∑ z ∈ Cl.cls x, μ z = 0 := qlev_class_zero hell0 hRg hdvd μ hμN
  have hP := poinc_patch hell hRg hdvd μ hμN
  -- Δh constant on classes inside K
  have hconst : ∀ x, (∀ z ∈ Cl.cls x, z ∈ K) → ∀ z ∈ Cl.cls x,
      lapFull (U0 L) (lapFull (U0 L) μ) z = lapFull (U0 L) (lapFull (U0 L) μ) x := by
    intro x hx z hz
    have hanc : Cl.anc x ∈ Cl.cls x := Cl.anc_mem hB x
    have hzx : Cl.anc z = Cl.anc x := (Cl.mem_cls x z).mp hz
    have e1 := kcc_patch hell0 hRg K μ hperp z (hx z hz) (by
      show Cl.anc z ∈ K; rw [hzx]; exact hx _ hanc)
    have e2 := kcc_patch hell0 hRg K μ hperp x (hx x (Cl.self_mem x)) (by
      show Cl.anc x ∈ K; exact hx _ hanc)
    rw [e1, e2]
    show lapFull (U0 L) (lapFull (U0 L) μ) (Cl.anc z) = lapFull (U0 L) (lapFull (U0 L) μ) (Cl.anc x)
    rw [hzx]
  -- room arithmetic
  set r := rD ell d with hr
  have hr1 : 1 ≤ r := rD_pos hd
  have hroom : 7 * r + 12 * ell + 3 ≤ d := by
    rcases rD_room (ell := ell) (d := d) with h1 | h1
    · exact h1
    · omega
  have hroomB : 7 * (r * B) + 12 * (ell * B) + 3 * B ≤ d * B := by
    have := Nat.mul_le_mul_right B hroom
    nlinarith [this]
  have hellB : B ≤ ell * B := Nat.le_mul_of_pos_left B hell0
  set R := r * B with hRdef
  have hR0 : 0 < R := Nat.mul_pos (by omega) (by omega)
  have hRB : B ≤ R := Nat.le_mul_of_pos_left B (by omega)
  set ρY := s + 2 + B + 6 * (ell * B) with hρY
  -- interior estimate
  have hint := Cl.interior_bound hell hB μ K hconst w s ρY le_rfl (by
    intro x hx z hz
    have h1 := pdist_triangle w x z
    have h2 : pdist x z ≤ 6 * Cl.nn x := Cl.pdist_in_cls x z hz
    have h3 : Cl.nn x ≤ ell * B := Cl.nn_le x
    show pdist w z ≤ s + d * B
    omega)
  -- cutoff estimate
  set a := ρY + 3 * (R - 1) with ha
  set g := smoothCut w a R R with hg
  have hS := Cl.S_bound hell hB μ hsum hP K hconst g R hR0 hRB (sc_nonneg w a R R) (sc_lip w a R R hR0 hR0)
    (fun x => sc_lapR w a R R hR0 hR0 x) (by
      intro x hx z hz
      have hxw : pdist w x ≤ a + R + 3 * (R - 1) := by
        by_contra hc; exact hx (sc_zero w a R R hR0 hR0 x (by omega))
      have h1 := pdist_triangle w x z
      have h2 : pdist x z ≤ 6 * Cl.nn x := Cl.pdist_in_cls x z hz
      have h3 : Cl.nn x ≤ ell * B := Cl.nn_le x
      show pdist w z ≤ s + d * B
      omega)
  -- compare the two sums
  have hcmp : ∑ x, (if pdist w x ≤ ρY then ‖lapFull (U0 L) μ x‖ ^ 2 else 0)
      ≤ ∑ x, g x * ‖lapFull (U0 L) μ x‖ ^ 2 := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    split_ifs with hx
    · rw [show g x = 1 from sc_one w a R R hR0 hR0 ρY le_rfl x hx, one_mul]
    · exact mul_nonneg (sc_nonneg w a R R x) (sq_nonneg _)
  -- assemble
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hCB := CB_pos
  have hCA := CA_pos hell1
  have hRr : ((B : ℝ) / R) = 1 / r := by
    rw [hRdef]; push_cast; field_simp
  have hfin : CB / (B : ℝ) ^ 2 * (CA ell * ((B : ℝ) / R) * ‖lapFull (U0 L) μ‖ ^ 2)
      = epsD ell d * (((ell : ℝ) ^ (i + 1))⁻¹) ^ 2 * ‖lapFull (U0 L) μ‖ ^ 2 := by
    rw [hRr]
    unfold epsD
    rw [← hr]
    have hB' : (B : ℝ) = (ell : ℝ) ^ i := by rw [hBdef, Nat.cast_pow]
    rw [hB']
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    field_simp
    ring
  calc AdalyFormal.M1W2.gradOn (flatCfg : Cfg L) (Ball w s) (lapFull (U0 L) μ)
      ≤ CB / (B : ℝ) ^ 2 * ∑ x, (if pdist w x ≤ ρY then ‖lapFull (U0 L) μ x‖ ^ 2 else 0) := hint
    _ ≤ CB / (B : ℝ) ^ 2 * (CA ell * ((B : ℝ) / R) * ‖lapFull (U0 L) μ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hcmp.trans hS) (by positivity)
    _ = _ := hfin

end AdalyFormal.M1Decay

#print axioms AdalyFormal.M1Decay.fit_of_dvd
#print axioms AdalyFormal.M1Decay.pnn
#print axioms AdalyFormal.M1Decay.cc_mem_Rg
#print axioms AdalyFormal.M1Decay.pnn_cc
#print axioms AdalyFormal.M1Decay.patchClasses
#print axioms AdalyFormal.M1Decay.qlev_class_zero
#print axioms AdalyFormal.M1Decay.lapDir_patch
#print axioms AdalyFormal.M1Decay.poinc_patch
#print axioms AdalyFormal.M1Decay.kcc_patch
#print axioms AdalyFormal.M1Decay.rD
#print axioms AdalyFormal.M1Decay.epsD
#print axioms AdalyFormal.M1Decay.rD_pos
#print axioms AdalyFormal.M1Decay.rD_room
#print axioms AdalyFormal.M1Decay.CB_pos
#print axioms AdalyFormal.M1Decay.CA_pos
#print axioms AdalyFormal.M1Decay.epsD_nonneg
#print axioms AdalyFormal.M1Decay.epsD_small
#print axioms AdalyFormal.M1Decay.harmDecay_flat
