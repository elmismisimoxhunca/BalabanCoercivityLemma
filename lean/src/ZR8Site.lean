import ZR8Jet
import ZXR2Wire1

/-!
# ZR8Site -- r8 locality of the SITE operators and of `Δ_π` (the r6 "attack 1" paper argument, formalised)

Setting: `G = geomOf ell k S`, `S` admissible, room `17 ell ≤ R M`, two fine configurations `U, U'` that agree on every bond with
BOTH endpoints in `Ω₀` (`BothIn (S.Om 0)`).  Proved here:
 * `lapDir_congr`  : `Ω₀ D*D Ω₀` is the same operator (crossing bonds enter only through `|R(U)x|² = |x|²`);
 * `Qlev_congr`    : the rows `y ∈ Λ_j` of `Q'_j(U)` agree (level 0 is the identity; level `j ≥ 1` reads `U` within `2 rhoT j` of `y`);
 * `DelpA_congr`, `Gp_congr`, `NQp_congr`, `RImage_congr`, `Rproj_congr`;
 * `grad_RImage_congr` : on the range of `R` (supported within distance 1 of `Ω₁`), `D_U = D_{U'}` -- this is where the collar
   `R M ≥ 2` is used (exact room condition of the r6 argument: every bond with an endpoint within distance 1 of `Ω₁` has both endpoints
   in the `2`-ball of `Ω₁`, inside `Ω₀` as soon as `2 ≤ R M`);
 * `Tfull_congr`   : `R D*_U A = R D*_{U'} A` for EVERY bond field `A`;
 * `Wop_congr_both`: `W_U A` and `W_{U'} A` agree on every `BothIn Ω₀` bond;
 * `DpiFull_congr` : `W*ΔW` is the same operator (Δ reads only `BothIn Ω₀` values and bonds).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.StatementLaneR8

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (gradCovariantAdjointValue periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.QjComposite (Qcomposite)

variable {L : PeriodicLatticeExtent}

/-! ## 0. agreement from `BothIn` and the room arithmetic -/

theorem agreeAt_of_both {Om : Set (PeriodicLatticeSite L)} {U U' : Cfg L}
    (hUU : ∀ e : Bond L, BothIn Om e → U e = U' e) {y : PeriodicLatticeSite L} {r : ℕ}
    (hB : Ball y (r + 1) ⊆ Om) : AgreeAt (Ball y r) U U' := by
  intro z hz μ
  refine hUU (z, μ) ⟨hB (Ball_mono (by omega) hz), hB ?_⟩
  exact Ball_sub (y' := z) hz (by omega) (show pdist z (periodicLatticeShift z μ) ≤ 1 from pdist_shift_le z μ)

theorem pdist_shiftBack_le (x : PeriodicLatticeSite L) (μ : Fin 3) : pdist x (periodicLatticeShiftBack x μ) ≤ 1 := by
  have h := pdist_shift_le (periodicLatticeShiftBack x μ) μ
  rw [periodicLatticeShift_shiftBack] at h
  rw [pdist_comm]; exact h

/-- the room arithmetic: `ell^j + 2 rhoT j + 1 ≤ R M ell^(j-1)` once `17 ell ≤ R M` (`j ≥ 1`, `ell ≥ 2`). -/
theorem room_arith {ell M R : ℕ} (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) {j : ℕ} (hj : 1 ≤ j) :
    ell ^ j + 2 * rhoT ell j + 1 ≤ R * (M * ell ^ (j - 1)) := by
  have h1 := rhoT_le ell hell j
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  rw [pow_succ] at h1 ⊢
  have hp : 0 < ell ^ i := pow_pos (by omega) i
  have : 17 * ell * ell ^ i ≤ R * M * ell ^ i := Nat.mul_le_mul_right _ hroom
  nlinarith

/-- rows of level `j ≥ 1`: the `(2 rhoT j + 1)`-ball around a point within `ell^j` of `Ω_j` lies in `Ω₀`. -/
theorem row_ball_Om0 {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y x : PeriodicLatticeSite L} (hy : y ∈ S.Om j)
    (hxy : pdist y x ≤ ell ^ j) : Ball x (2 * rhoT ell j + 1) ⊆ S.Om 0 :=
  le_trans (Ball_sub hxy (room_arith hell hroom hj1)) (admissible_ball_Om0 hS hj1 (by omega) hy)

/-! ## 1. `Ω₀ D*D Ω₀` -/

open Classical in
theorem lapDir_inner (G : TowerGeom L) (U : Cfg L) (f g : SiteL2 L) :
    ⟪f, lapDir G U g⟫ = ⟪gradL2 U (siteMask G.Om0 f), gradL2 U (siteMask G.Om0 g)⟫ := by
  unfold lapDir lapFull
  simp only [ContinuousLinearMap.comp_apply]
  rw [← siteMask_symm, gradAdj, ContinuousLinearMap.adjoint_inner_right]

theorem bond_inner_congr {Om : Set (PeriodicLatticeSite L)} {U U' : Cfg L}
    (hUU : ∀ e : Bond L, BothIn Om e → U e = U' e) (h1 h2 : PeriodicLatticeSite L → SuTwo)
    (hz1 : ∀ x, x ∉ Om → h1 x = 0) (hz2 : ∀ x, x ∉ Om → h2 x = 0) (b : Bond L) :
    ⟪gradValueCovariant U h1 b, gradValueCovariant U h2 b⟫ = ⟪gradValueCovariant U' h1 b, gradValueCovariant U' h2 b⟫ := by
  unfold gradValueCovariant
  by_cases hb : BothIn Om b
  · rw [hUU b hb]
  · by_cases hp : periodicLatticeShift b.1 b.2 ∈ Om
    · have hm : b.1 ∉ Om := fun h => hb ⟨h, hp⟩
      rw [hz1 _ hm, hz2 _ hm, sub_zero, sub_zero, sub_zero, sub_zero,
        AdalyFormal.Balaban.SuTwoInner.inner_RMap, AdalyFormal.Balaban.SuTwoInner.inner_RMap]
    · rw [hz1 _ hp, hz2 _ hp]; simp only [map_zero]

open Classical in
theorem lapDir_congr (G : TowerGeom L) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn G.Om0 e → U e = U' e) :
    lapDir G U = lapDir G U' := by
  ext1 g
  refine ext_inner_left ℝ (fun f => ?_)
  rw [lapDir_inner, lapDir_inner, PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  show ⟪(WithLp.ofLp (gradL2 U (siteMask G.Om0 f))) b, (WithLp.ofLp (gradL2 U (siteMask G.Om0 g))) b⟫
    = ⟪(WithLp.ofLp (gradL2 U' (siteMask G.Om0 f))) b, (WithLp.ofLp (gradL2 U' (siteMask G.Om0 g))) b⟫
  rw [gradL2_apply, gradL2_apply, gradL2_apply, gradL2_apply]
  refine bond_inner_congr hUU _ _ (fun x hx => ?_) (fun x hx => ?_) b
  · show (siteMask G.Om0 f) x = 0; rw [siteMask_apply, if_neg hx]
  · show (siteMask G.Om0 g) x = 0; rw [siteMask_apply, if_neg hx]

/-! ## 2. the rows of `Q'_j` and the operators built on them -/

/-- the level-`j` rows `y ∈ Λ_j` of `Q'_j(U)` agree. -/
theorem Qlev_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e)
    {j : ℕ} (hjk : j ≤ k) {y : PeriodicLatticeSite L} (hy : y ∈ (geomOf ell k S).Lam j) :
    Qlev (geomOf ell k S) U j y = Qlev (geomOf ell k S) U' j y := by
  ext1 f
  rw [Qlev_apply, Qlev_apply]
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0; rfl
  · refine Qcomposite_congr (geomOf ell k S) (by show 0 < ell; omega) _ j y (agreeAt_of_both hUU ?_)
    show Ball y (2 * rhoT ell j + 1) ⊆ S.Om 0
    exact row_ball_Om0 hS hell hroom hj1 hjk hy.2.1 (x := y) (by rw [pdist_self]; exact Nat.zero_le _)

open Classical in
theorem Qpa_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) (a : ℝ) :
    Qpa (geomOf ell k S) U a = Qpa (geomOf ell k S) U' a := by
  unfold Qpa
  refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun y _ => ?_))
  split_ifs with hy
  · have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Qlev_congr hS hell hroom hUU hjk hy]
  · rfl

theorem DelpA_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) (a : ℝ) :
    DelpA (geomOf ell k S) U a = DelpA (geomOf ell k S) U' a := by
  have hl := lapDir_congr (geomOf ell k S) (U := U) (U' := U') hUU
  have hq := Qpa_congr hS hell hroom hUU a
  ext1 f
  unfold DelpA
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add]
  rw [hq]
  have : ∀ g, siteMask (geomOf ell k S).Om0 (lapFull U (siteMask (geomOf ell k S).Om0 g))
      = siteMask (geomOf ell k S).Om0 (lapFull U' (siteMask (geomOf ell k S).Om0 g)) := fun g => by
    have := congrArg (fun T => T g) hl
    simpa [lapDir] using this
  rw [this]

theorem Gp_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) (a : ℝ) :
    Gp (geomOf ell k S) U a = Gp (geomOf ell k S) U' a := by
  unfold Gp; rw [DelpA_congr hS hell hroom hUU a]

theorem NQp_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) :
    NQp (geomOf ell k S) U = NQp (geomOf ell k S) U' := by
  ext f
  show ((∀ x, x ∉ (geomOf ell k S).Om0 → f x = 0) ∧ ∀ j, j ≤ (geomOf ell k S).k → ∀ y, y ∈ (geomOf ell k S).Lam j →
      Qlev (geomOf ell k S) U j y f = 0) ↔
    ((∀ x, x ∉ (geomOf ell k S).Om0 → f x = 0) ∧ ∀ j, j ≤ (geomOf ell k S).k → ∀ y, y ∈ (geomOf ell k S).Lam j →
      Qlev (geomOf ell k S) U' j y f = 0)
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun j hj y hy => by rw [← Qlev_congr hS hell hroom hUU hj hy]; exact h2 j hj y hy⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun j hj y hy => by rw [Qlev_congr hS hell hroom hUU hj hy]; exact h2 j hj y hy⟩

theorem RImage_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) :
    RImage (geomOf ell k S) U = RImage (geomOf ell k S) U' := by
  unfold RImage
  rw [NQp_congr hS hell hroom hUU, lapDir_congr (geomOf ell k S) hUU]

theorem Rproj_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) :
    Rproj (geomOf ell k S) U = Rproj (geomOf ell k S) U' := by
  unfold Rproj
  simp only [RImage_congr hS hell hroom hUU]

/-! ## 3. `R D*` -/

/-- `D*D g` vanishes at `x` if `g` vanishes on the unit ball around `x`. -/
theorem lapFull_zero_of_ball (U : Cfg L) (g : SiteL2 L) (x : PeriodicLatticeSite L)
    (hg : ∀ z ∈ Ball x 1, g z = 0) : (lapFull U g) x = 0 := by
  unfold lapFull
  show (WithLp.ofLp (gradAdj U (gradL2 U g))) x = 0
  rw [gradAdj_apply, gradL2_apply]
  unfold gradCovariantAdjointValue gradValueCovariant
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  rw [periodicLatticeShift_shiftBack]
  have h0 : (WithLp.ofLp g) x = 0 := hg x (mem_Ball_self _ _)
  have h1 : (WithLp.ofLp g) (periodicLatticeShift x μ) = 0 := hg _ (pdist_shift_le x μ)
  have h2 : (WithLp.ofLp g) (periodicLatticeShiftBack x μ) = 0 := hg _ (pdist_shiftBack_le x μ)
  simp only [h0, h1, h2, map_zero, sub_zero]

open Classical in
/-- the range of `R` is supported within distance `1` of `Ω₁`. -/
theorem RImage_support {ell k : ℕ} (S : Tower L) (U : Cfg L) {v : SiteL2 L}
    (hv : v ∈ RImage (geomOf ell k S) U) (x : PeriodicLatticeSite L)
    (hx : ∀ y ∈ Ball x 1, y ∉ S.Om 1) : v x = 0 := by
  obtain ⟨f, hf, rfl⟩ := hv
  have hf0 : ∀ z, z ∉ S.Om 1 → (siteMask (geomOf ell k S).Om0 f) z = 0 := by
    intro z hz
    rw [siteMask_apply]
    split_ifs with h0
    · have := hf.2 0 (Nat.zero_le _) z ⟨fun μ => by simp, h0, hz⟩
      rw [Qlev_apply] at this
      exact this
    · rfl
  show (WithLp.ofLp (lapDir (geomOf ell k S) U f)) x = 0
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  show (siteMask (geomOf ell k S).Om0 (lapFull U (siteMask (geomOf ell k S).Om0 f))) x = 0
  rw [siteMask_apply]
  split_ifs
  · exact lapFull_zero_of_ball U _ x (fun z hz => hf0 z (hx z hz))
  · rfl

/-- **`D_U = D_{U'}` on the range of `R`** (room: `2 ≤ R M`). -/
theorem grad_RImage_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hRM : 2 ≤ R * M)
    {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) {v : SiteL2 L}
    (hv : v ∈ RImage (geomOf ell k S) U) : gradL2 U v = gradL2 U' v := by
  refine PiLp.ext (fun b => ?_)
  show (WithLp.ofLp (gradL2 U v)) b = (WithLp.ofLp (gradL2 U' v)) b
  rw [gradL2_apply, gradL2_apply]
  unfold gradValueCovariant
  by_cases hp : (WithLp.ofLp v) (periodicLatticeShift b.1 b.2) = 0
  · rw [hp, map_zero, map_zero]
  · have : ∃ y ∈ Ball (periodicLatticeShift b.1 b.2) 1, y ∈ S.Om 1 := by
      by_contra hne
      push_neg at hne
      exact hp (RImage_support S U hv _ hne)
    obtain ⟨y, hy1, hyO⟩ := this
    have hball : Ball y (R * M) ⊆ S.Om 0 := by
      have := admissible_ball hS (j := 0) (Nat.zero_le _) hyO
      simpa [bigSide] using this
    have h1 : pdist y (periodicLatticeShift b.1 b.2) ≤ 1 := by rw [pdist_comm]; exact hy1
    have h2 : pdist y b.1 ≤ 2 := by
      have := pdist_triangle y (periodicLatticeShift b.1 b.2) b.1
      have h3 : pdist (periodicLatticeShift b.1 b.2) b.1 ≤ 1 := by rw [pdist_comm]; exact pdist_shift_le _ _
      omega
    rw [hUU b ⟨hball (le_trans h2 hRM), hball (le_trans h1 (by omega))⟩]

theorem Tfull_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) :
    Tfull (geomOf ell k S) U = Tfull (geomOf ell k S) U' := by
  have hRM : 2 ≤ R * M := by omega
  ext1 A
  unfold Tfull
  simp only [ContinuousLinearMap.comp_apply]
  rw [← Rproj_congr hS hell hroom hUU]
  rw [← sub_eq_zero, ← map_sub]
  unfold Rproj
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro v hv
  rw [inner_sub_right, gradAdj, gradAdj, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right, grad_RImage_congr hS hRM hUU hv, sub_self]

/-! ## 4. `W = I − D G' R D*` and `Δ_π = W*ΔW` -/

theorem Wop_congr_both {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) (a : ℝ)
    (A : BondFnL2 L) (b : Bond L) (hb : BothIn (S.Om 0) b) :
    (Wop (geomOf ell k S) U a A) b = (Wop (geomOf ell k S) U' a A) b := by
  have hT := Tfull_congr hS hell hroom hUU
  have hh : Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U A))
      = Gp (geomOf ell k S) U' a (Rproj (geomOf ell k S) U' (gradAdj U' A)) := by
    rw [Gp_congr hS hell hroom hUU a]
    have := congrArg (fun T => T A) hT
    simp only [Tfull, ContinuousLinearMap.comp_apply] at this
    rw [this]
  unfold Wop
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  rw [hh]
  show (WithLp.ofLp A) b - (WithLp.ofLp (gradL2 U _)) b = (WithLp.ofLp A) b - (WithLp.ofLp (gradL2 U' _)) b
  rw [gradL2_apply, gradL2_apply]
  unfold gradValueCovariant
  rw [hUU b hb]

theorem Delta_inner_congr_both (G : TowerGeom L) (U : Cfg L) {X X' Y Y' : BondFnL2 L}
    (hX : ∀ e : Bond L, BothIn G.Om0 e → X e = X' e) (hY : ∀ e : Bond L, BothIn G.Om0 e → Y e = Y' e) :
    ⟪X, Delta G U Y⟫ = ⟪X', Delta G U Y'⟫ := by
  have h1 : Delta G U (Y - Y') = 0 :=
    Delta_outside_zero G U _ (fun e he => by simp [hY e he])
  have h2 : Delta G U (X - X') = 0 :=
    Delta_outside_zero G U _ (fun e he => by simp [hX e he])
  have e1 : ⟪X, Delta G U Y⟫ = ⟪X, Delta G U Y'⟫ := by
    rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, h1, inner_zero_right]
  have e2 : ⟪X, Delta G U Y'⟫ = ⟪X', Delta G U Y'⟫ := by
    rw [← sub_eq_zero, ← inner_sub_left]
    have hs : ⟪X - X', Delta G U Y'⟫ = ⟪Delta G U (X - X'), Y'⟫ :=
      (AdalyFormal.StatementLaneR6.deltaKLocCLM_symm U (plaqIn G.Om0) (X - X') Y').symm
    rw [hs, h2, inner_zero_left]
  rw [e1, e2]

theorem DpiFull_congr {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {U U' : Cfg L} (hUU : ∀ e : Bond L, BothIn (S.Om 0) e → U e = U' e) (a : ℝ) :
    DpiFull (geomOf ell k S) U a = DpiFull (geomOf ell k S) U' a := by
  ext1 A
  refine ext_inner_left ℝ (fun B => ?_)
  unfold DpiFull
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [Delta_congr_outside (geomOf ell k S) hUU]
  exact Delta_inner_congr_both (geomOf ell k S) U' (fun e he => Wop_congr_both hS hell hroom hUU a B e he)
    (fun e he => Wop_congr_both hS hell hroom hUU a A e he)

#print axioms agreeAt_of_both
#print axioms room_arith
#print axioms lapDir_congr
#print axioms Qlev_congr
#print axioms DelpA_congr
#print axioms Rproj_congr
#print axioms RImage_support
#print axioms grad_RImage_congr
#print axioms Tfull_congr
#print axioms Wop_congr_both
#print axioms DpiFull_congr

end AdalyFormal.StatementLaneR8
