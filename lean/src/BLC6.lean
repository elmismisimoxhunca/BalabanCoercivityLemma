import BLC5

/-!
# BLC6 -- the ball chart for `j ≥ 1`: vertex charts → rows → slabs → ball, at k-free constants (m2_ballcharts, 2026-10-15)

`level_scaled`: `level_Ib` with input constants `(a X u, b X u²)` gives output `(sc1 a (cτ a) d · X u, sc2 a b (cτ a) d e · X u²)`,
`cτ a = 2(28ℓ+1) M a`, `d = 6/M`, `e = 128/M²`, under `s u = M`, `r ≤ 7ℓs`, `X ≤ 1`, `cτ a · X ≤ 2`.
`ball_chart_pos`: for `1 ≤ j ≤ k`, one gauge on `Ball w r` with `GChart` constants `CC ℓ M · 12 M α₀ ℓ^{-(j-1)}` and
`CC ℓ M · 12 M α₀ ℓ^{-2(j-1)}`, `CC` depending on `ℓ, M` only, whenever `12 M α₀ ≤ Xthr ℓ M` (also `ℓ, M` only).
Three levels: σ = 0 (T = {1,2}), σ = 1 (T = {2}), σ = 2 (T = ∅).  The closeness τ at level i is `cτ(a_i) X`: it is multiplied by
a fixed factor per level, never by the number of blocks.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

/-- the closeness coefficient of a level. -/
noncomputable def cτ (ell M : ℕ) (a : ℝ) : ℝ := 2 * (28 * (ell : ℝ) + 1) * M * a

theorem level_scaled {r s ell M : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) (hs : 24 ≤ s) (hM : 0 < M)
    (hr : r ≤ 7 * ell * s) (w : PeriodicLatticeSite L) {U : LinkCfg L} (σ : Fin 3) (T : Finset (Fin 3)) (hσ : σ ∉ T)
    {X u a b : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hu : 0 ≤ u) (hsu : (s : ℝ) * u = M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcτ : cτ ell M a * X ≤ 2)
    (hch : ∀ (n : Fin 3 → ℕ), ∃ g : PeriodicLatticeSite L → SU2,
      ZCh U g w (Ib r s (qv r s w n) (insert σ T)) (fun _ => a * X * u) (fun _ => b * X * u ^ 2))
    (n : Fin 3 → ℕ) :
    ∃ G : PeriodicLatticeSite L → SU2, ZCh U G w (Ib r s (qv r s w n) T)
      (fun _ => sc1 a (cτ ell M a) (6 / M) * X * u)
      (fun _ => sc2 a b (cτ ell M a) (6 / M) (128 / (M : ℝ) ^ 2) * X * u ^ 2) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hs' : (24 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hell0 : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  -- the collar diameter
  have hdm : ((s - 8 + 4 * r : ℕ) : ℝ) ≤ (28 * (ell : ℝ) + 1) * s := by
    have h1 : s - 8 + 4 * r ≤ 28 * ell * s + s := by
      have : 4 * r ≤ 28 * ell * s := by nlinarith
      omega
    calc ((s - 8 + 4 * r : ℕ) : ℝ) ≤ ((28 * ell * s + s : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (28 * (ell : ℝ) + 1) * s := by push_cast; ring
  have hτle : ((s - 8 + 4 * r : ℕ) : ℝ) * (2 * (a * X * u)) ≤ cτ ell M a * X := by
    have h0 : 0 ≤ 2 * (a * X * u) := by positivity
    calc ((s - 8 + 4 * r : ℕ) : ℝ) * (2 * (a * X * u)) ≤ ((28 * (ell : ℝ) + 1) * s) * (2 * (a * X * u)) :=
          mul_le_mul_of_nonneg_right hdm h0
      _ = 2 * (28 * (ell : ℝ) + 1) * ((s : ℝ) * u) * a * X := by ring
      _ = cτ ell M a * X := by rw [hsu]; unfold cτ; ring
  obtain ⟨G, hG⟩ := level_Ib (L := L) hL hs w σ T hσ n (t1 := a * X * u) (t2 := b * X * u ^ 2)
    (by positivity) (by positivity) (fun k => hch (Function.update n σ k)) (hτle.trans hcτ)
  refine ⟨G, zch_mono hG subset_rfl ?_ ?_⟩
  all_goals
    have hcast : ((s - 12 : ℕ) : ℝ) = (s : ℝ) - 12 := by
      have : 12 ≤ s := by omega
      push_cast [Nat.cast_sub this]; ring
    obtain ⟨k1, k2, k10, k20⟩ := kap_bounds hs'
    rw [hcast]
    have hu0 : 0 < u := by
      rcases hu.lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hsu; linarith
    have hd : 6 / (s : ℝ) = 6 / M * u := by
      rw [← hsu]; field_simp
    have he : 128 / (s : ℝ) ^ 2 = 128 / (M : ℝ) ^ 2 * u ^ 2 := by
      rw [← hsu]; field_simp
    have hcτ0 : 0 ≤ cτ ell M a := by unfold cτ; positivity
    have gs := glue_scale (t1 := a * X * u) (t2 := b * X * u ^ 2)
      (τ := ((s - 8 + 4 * r : ℕ) : ℝ) * (2 * (a * X * u))) (κ1 := kap1 ((s : ℝ) - 12)) (κ2 := kap2 ((s : ℝ) - 12))
      (a := a) (b := b) (c := cτ ell M a) (d := 6 / M) (e := 128 / (M : ℝ) ^ 2) (X := X) (u := u)
      hX0 hX1 hu ha hb hcτ0 (by positivity) (by positivity) (by positivity) le_rfl (by positivity) le_rfl
      (by positivity) hτle k10 (hd ▸ k1) k20 (he ▸ k2)
  · exact gs.1
  · exact gs.2

/-! ## the constants -/

noncomputable def a1 (M : ℕ) : ℝ := 6 * KT1 4 1152 * M
noncomputable def b1 : ℝ := 2 * KT2 4 1152
noncomputable def a2 (ell M : ℕ) : ℝ := sc1 (a1 M) (cτ ell M (a1 M)) (6 / M)
noncomputable def b2 (ell M : ℕ) : ℝ := sc2 (a1 M) b1 (cτ ell M (a1 M)) (6 / M) (128 / (M : ℝ) ^ 2)
noncomputable def a3 (ell M : ℕ) : ℝ := sc1 (a2 ell M) (cτ ell M (a2 ell M)) (6 / M)
noncomputable def b3 (ell M : ℕ) : ℝ := sc2 (a2 ell M) (b2 ell M) (cτ ell M (a2 ell M)) (6 / M) (128 / (M : ℝ) ^ 2)
noncomputable def aF (ell M : ℕ) : ℝ := sc1 (a3 ell M) (cτ ell M (a3 ell M)) (6 / M)
noncomputable def bF (ell M : ℕ) : ℝ := sc2 (a3 ell M) (b3 ell M) (cτ ell M (a3 ell M)) (6 / M) (128 / (M : ℝ) ^ 2)
/-- the final constant `C(ℓ, M)` of the gluing route. -/
noncomputable def CC (ell M : ℕ) : ℝ := 1 + aF ell M + bF ell M
/-- the smallness threshold on `X = 12 M α₀` (depends on `ℓ, M` only). -/
noncomputable def Xthr (ell M : ℕ) : ℝ :=
  min (1 / 47) (min (1 / (18 * (4 * cB 1152 5 + 1) * (M : ℝ) ^ 2))
    (min (2 / (1 + cτ ell M (a1 M))) (min (2 / (1 + cτ ell M (a2 ell M))) (2 / (1 + cτ ell M (a3 ell M))))))

theorem consts_nonneg (ell M : ℕ) :
    0 ≤ a1 M ∧ 0 ≤ b1 ∧ 0 ≤ a2 ell M ∧ 0 ≤ b2 ell M ∧ 0 ≤ a3 ell M ∧ 0 ≤ b3 ell M ∧ 0 ≤ aF ell M ∧ 0 ≤ bF ell M := by
  have k1 := KT1_nonneg; have k2 := KT2_nonneg
  have h1 : 0 ≤ a1 M := by unfold a1; positivity
  have h2 : 0 ≤ b1 := by unfold b1; positivity
  have hc : ∀ a, 0 ≤ a → 0 ≤ cτ ell M a := fun a ha => by unfold cτ; positivity
  have hd : (0 : ℝ) ≤ 6 / M := by positivity
  have he : (0 : ℝ) ≤ 128 / (M : ℝ) ^ 2 := by positivity
  have h3 : 0 ≤ a2 ell M := sc1_nonneg h1 (hc _ h1) hd
  have h4 : 0 ≤ b2 ell M := sc2_nonneg h1 h2 (hc _ h1) hd he
  have h5 : 0 ≤ a3 ell M := sc1_nonneg h3 (hc _ h3) hd
  have h6 : 0 ≤ b3 ell M := sc2_nonneg h3 h4 (hc _ h3) hd he
  have h7 : 0 ≤ aF ell M := sc1_nonneg h5 (hc _ h5) hd
  have h8 : 0 ≤ bF ell M := sc2_nonneg h5 h6 (hc _ h5) hd he
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem Xthr_pos (ell M : ℕ) (hM : 0 < M) : 0 < Xthr ell M := by
  obtain ⟨h1, -, h3, -, h5, -, -, -⟩ := consts_nonneg ell M
  have hc : ∀ a, 0 ≤ a → 0 < 2 / (1 + cτ ell M a) := fun a ha => by
    have : 0 ≤ cτ ell M a := by unfold cτ; positivity
    positivity
  have hcb : 0 ≤ cB 1152 5 := by unfold cB; positivity
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  unfold Xthr
  refine lt_min (by norm_num) (lt_min (by positivity) (lt_min (hc _ h1) (lt_min (hc _ h3) (hc _ h5))))

theorem cτ_small {ell M : ℕ} {a X : ℝ} (ha : 0 ≤ a) (hX : 0 ≤ X) (h : X ≤ 2 / (1 + cτ ell M a)) :
    cτ ell M a * X ≤ 2 := by
  have hc : 0 ≤ cτ ell M a := by unfold cτ; positivity
  have h1 : 0 < 1 + cτ ell M a := by linarith
  rw [le_div_iff₀ h1] at h
  nlinarith

/-! ## the ball chart for `j ≥ 1` -/

theorem ball_chart_pos {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    (hcov : CoversOm0p ell M 12 k S) (hell : 2 ≤ ell) (hM : 24 ≤ M) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om j) {w : PeriodicLatticeSite L} (hw : pdist w x0 ≤ 3 * (M * ell ^ j))
    {r : ℕ} (hr7 : r ≤ 7 * M * ell ^ j) (hnw : ∀ σ : Fin 3, 2 * r + 2 ≤ L σ + 1) (hR : 45 * ell + 30 ≤ R)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2 ell M 12 k S α₀ η U)
    (hX : (12 : ℝ) * M * α₀ ≤ Xthr ell M) :
    ∃ g : PeriodicLatticeSite L → SU2, GChart U g (Ball w r)
      (CC ell M * ((12 : ℝ) * M * α₀ * ((ell : ℝ) ^ (j - 1))⁻¹))
      (CC ell M * ((12 : ℝ) * M * α₀ * (((ell : ℝ) ^ (j - 1))⁻¹) ^ 2)) := by
  set s := bigSide M ell (j - 1) with hsdef
  set X : ℝ := (12 : ℝ) * M * α₀ with hXdef
  set u : ℝ := ((ell : ℝ) ^ (j - 1))⁻¹ with hudef
  have hL : ∀ μ, 2 * r + 1 < L μ + 1 := fun μ => by have := hnw μ; omega
  have hM0 : 0 < M := by omega
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hell0 : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hs24 : 24 ≤ s := by
    have : M ≤ s := by rw [hsdef, bigSide]; exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    omega
  have hpow : (0 : ℝ) < (ell : ℝ) ^ (j - 1) := by positivity
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    rw [hudef]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (show 1 ≤ ell by omega)))
  have hsu : (s : ℝ) * u = M := by
    rw [hsdef, bigSide, hudef]; push_cast; field_simp
  have hMl : M * ell ^ j = ell * s := by
    rw [hsdef, bigSide]
    have : ell ^ j = ell * ell ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this]; ring
  have hr : r ≤ 7 * ell * s := by
    have : 7 * M * ell ^ j = 7 * ell * s := by rw [mul_assoc, hMl]; ring
    omega
  have hX0 : 0 ≤ X := by positivity
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := consts_nonneg ell M
  have hcb : 0 ≤ cB 1152 5 := by unfold cB; positivity
  -- the threshold pieces
  have t47 : X ≤ 1 / 47 := hX.trans (min_le_left _ _)
  have tsm : X ≤ 1 / (18 * (4 * cB 1152 5 + 1) * (M : ℝ) ^ 2) := hX.trans ((min_le_right _ _).trans (min_le_left _ _))
  have tc1 : X ≤ 2 / (1 + cτ ell M (a1 M)) :=
    hX.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have tc2 : X ≤ 2 / (1 + cτ ell M (a2 ell M)) :=
    hX.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have tc3 : X ≤ 2 / (1 + cτ ell M (a3 ell M)) :=
    hX.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hX1 : X ≤ 1 := by linarith
  -- vertex constants
  have hFv : Fv ell M (j - 1) α₀ ≤ 2 * X * u ^ 2 := by
    unfold Fv
    rw [← hXdef, ← hudef]
    have hXu : X * u ≤ X := by nlinarith
    nlinarith [mul_nonneg hX0 (sq_nonneg u)]
  have hFv0 : 0 ≤ Fv ell M (j - 1) α₀ := by unfold Fv; rw [← hXdef, ← hudef]; positivity
  have hR3 : (3 * ((s - 4 : ℕ) : ℝ) + 2) ≤ 3 * s := by
    have : ((s - 4 : ℕ) : ℝ) = (s : ℝ) - 4 := by push_cast [Nat.cast_sub (show 4 ≤ s by omega)]; ring
    rw [this]; linarith
  have hR30 : 0 ≤ (3 * ((s - 4 : ℕ) : ℝ) + 2) := by positivity
  have hv1 : KT1 4 1152 * (3 * ((s - 4 : ℕ) : ℝ) + 2) * Fv ell M (j - 1) α₀ ≤ a1 M * X * u := by
    have k1 := KT1_nonneg
    calc KT1 4 1152 * (3 * ((s - 4 : ℕ) : ℝ) + 2) * Fv ell M (j - 1) α₀
        ≤ KT1 4 1152 * (3 * s) * (2 * X * u ^ 2) := by gcongr
      _ = 6 * KT1 4 1152 * ((s : ℝ) * u) * X * u := by ring
      _ = a1 M * X * u := by rw [hsu]; unfold a1; ring
  have hv2 : KT2 4 1152 * Fv ell M (j - 1) α₀ ≤ b1 * X * u ^ 2 := by
    have k2 := KT2_nonneg
    calc KT2 4 1152 * Fv ell M (j - 1) α₀ ≤ KT2 4 1152 * (2 * X * u ^ 2) := by gcongr
      _ = b1 * X * u ^ 2 := by unfold b1; ring
  have hsmall : (4 * cB 1152 5 + 1) * (3 * ((s - 4 : ℕ) : ℝ) + 2) ^ 2 * Fv ell M (j - 1) α₀ ≤ 1 := by
    have hq : (3 * ((s - 4 : ℕ) : ℝ) + 2) ^ 2 ≤ (3 * s) ^ 2 := pow_le_pow_left₀ hR30 hR3 2
    calc (4 * cB 1152 5 + 1) * (3 * ((s - 4 : ℕ) : ℝ) + 2) ^ 2 * Fv ell M (j - 1) α₀
        ≤ (4 * cB 1152 5 + 1) * (3 * s) ^ 2 * (2 * X * u ^ 2) := by gcongr
      _ = 18 * (4 * cB 1152 5 + 1) * ((s : ℝ) * u) ^ 2 * X := by ring
      _ = 18 * (4 * cB 1152 5 + 1) * (M : ℝ) ^ 2 * X := by rw [hsu]
      _ ≤ 1 := by
        have hpos : 0 < 18 * (4 * cB 1152 5 + 1) * (M : ℝ) ^ 2 := by positivity
        rw [le_div_iff₀ hpos] at tsm; linarith
  have hsm : X * u + X * u ^ 2 ≤ 1 := by nlinarith
  have ht12 : X * u ≤ 2 := by nlinarith
  -- level 0: vertex charts
  have hV : ∀ n : Fin 3 → ℕ, ∃ g : PeriodicLatticeSite L → SU2,
      ZCh U g w (Ib r s (qv r s w n) (insert (0 : Fin 3) ({1, 2} : Finset (Fin 3))))
        (fun _ => a1 M * X * u) (fun _ => b1 * X * u ^ 2) := by
    intro n
    have huniv : insert (0 : Fin 3) ({1, 2} : Finset (Fin 3)) = Finset.univ := by decide
    rw [huniv]
    obtain ⟨g, hg⟩ := vertex_zch hS hcov hell hM0 hj1 hjk hx0 hw hr7 hR hs24 hη hα hP
      (by rw [← hXdef, ← hudef]; exact hsm) (by rw [← hXdef, ← hudef]; exact ht12) hsmall n
    exact ⟨g, zch_mono hg subset_rfl hv1 hv2⟩
  -- level 1: rows (σ = 0, T = {1,2})
  have hL1 : ∀ n : Fin 3 → ℕ, ∃ g : PeriodicLatticeSite L → SU2,
      ZCh U g w (Ib r s (qv r s w n) (insert (1 : Fin 3) ({2} : Finset (Fin 3))))
        (fun _ => a2 ell M * X * u) (fun _ => b2 ell M * X * u ^ 2) := by
    intro n
    have he : insert (1 : Fin 3) ({2} : Finset (Fin 3)) = ({1, 2} : Finset (Fin 3)) := by decide
    rw [he]
    exact level_scaled hL hs24 hM0 hr w 0 {1, 2} (by decide) hX0 hX1 hu0.le hsu c1 c2
      (cτ_small c1 hX0 tc1) hV n
  -- level 2: slabs (σ = 1, T = {2})
  have hL2 : ∀ n : Fin 3 → ℕ, ∃ g : PeriodicLatticeSite L → SU2,
      ZCh U g w (Ib r s (qv r s w n) (insert (2 : Fin 3) (∅ : Finset (Fin 3))))
        (fun _ => a3 ell M * X * u) (fun _ => b3 ell M * X * u ^ 2) := by
    intro n
    have he : insert (2 : Fin 3) (∅ : Finset (Fin 3)) = ({2} : Finset (Fin 3)) := by decide
    rw [he]
    exact level_scaled hL hs24 hM0 hr w 1 {2} (by decide) hX0 hX1 hu0.le hsu c3 c4
      (cτ_small c3 hX0 tc2) hL1 n
  -- level 3: the box (σ = 2, T = ∅)
  obtain ⟨G, hG⟩ := level_scaled hL hs24 hM0 hr w 2 ∅ (by decide) hX0 hX1 hu0.le hsu c5 c6
    (cτ_small c5 hX0 tc3) hL2 (fun _ => 0)
  -- to sites, then to the ball
  have hGs := gchart_sub_of_zch (v := w) hL (S := Box r) subset_rfl (P := fun _ => True)
    (T := Ib r s (qv r s w (fun _ => 0)) ∅) (fun p hp _ => mem_Ib.mpr ⟨hp, fun i hi => absurd hi (Finset.notMem_empty i)⟩) hG
  refine ⟨G, hGs.mono (fun x hx => ⟨ball_sub_lift w r hx, trivial⟩) ?_ ?_⟩
  · have : aF ell M * X * u ≤ CC ell M * (X * u) := by
      unfold CC; have : 0 ≤ X * u := by positivity
      nlinarith
    exact this
  · have : bF ell M * X * u ^ 2 ≤ CC ell M * (X * u ^ 2) := by
      unfold CC; have : 0 ≤ X * u ^ 2 := by positivity
      nlinarith
    exact this

end AdalyFormal.M2BallCharts
