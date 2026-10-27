import Q409L1

/-!
# Q409L2 -- the p.409 containment fails for EVERY cube factor and EVERY index (box cubes), in the regime of `ballChartsG`.

Tower `TU` (union of three coordinate slabs, `k = 1`), stratum-0 patch centred at `w = (B0-M, B0-M, B0-M)`.  The three points
`w + M e_mu` (mu = 0,1,2) lie in the patch and in `Om 0`; any axis box containing them contains `q = (B0,B0,B0) = w + (M,M,M)`,
which is NOT in `Om 0` (the corner of the cube `H = complement of Om 0`).  Hence no `DescribedAt` box (any factor `f`, any index `i`)
contains `patch cap Om 0`; in particular neither `IsClassCubeG` nor `IsClassCube`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.M1 (strat strat_eq_iff IsPatch patch gsp om_anti)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice)

/-- the full statement (quantifier by quantifier in REPORT.md). -/
def LFail (ell M R : ℕ) (Lu Lf : PeriodicLatticeExtent) : Prop :=
  ∃ (S : Tower Lf) (Lam : Set (PeriodicLatticeSite Lu)),
    TorusOK ell M Lu ∧ Admissible ell M R 1 S ∧ CoversOm0p ell M 12 1 S ∧
    LambdaOK2 (Lu := Lu) (Lf := Lf) ell M R 1 S Lam ∧ Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
    (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj S 0) ∧ (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj S 1) ∧
    ∃ w : PeriodicLatticeSite Lf, IsPatch ell M 1 1 S 0 w ∧
      (¬ ∃ (f : ℕ) (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), DescribedAt ell M f 1 S sites i ∧
          {y | y ∈ patch ell M 1 5 0 w ∧ y ∈ S.Om 0} ⊆ sites) ∧
      (¬ ∃ (f : ℕ) (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), IsClassCubeG ell M f 1 S sites i ∧
          {y | y ∈ patch ell M 1 5 0 w ∧ y ∈ S.Om 0} ⊆ sites) ∧
      (¬ ∃ (f : ℕ) (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), IsClassCube ell M f 1 S sites i ∧
          {y | y ∈ patch ell M 1 5 0 w ∧ y ∈ S.Om 0} ⊆ sites) ∧
      (∃ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), IsClassSetW ell M 11 1 S sites i ∧
          {y | y ∈ patch ell M 1 5 0 w ∧ y ∈ S.Om 0} ⊆ sites)

theorem lf_counterexample {ell M R : ℕ} {Lu Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hellM : ell ∣ M) (hR : 12 ≤ R)
    (hLu : ∀ μ, Lu μ + 1 = M * (4 * R + 8)) (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) :
    LFail ell M R Lu Lf := by
  -- numerics
  have hg2 : M * 2 ≤ M * ell := Nat.mul_le_mul_left M hell
  have hg0 : 0 < M * ell := by omega
  have hRM12 : 12 * M ≤ R * M := by have := Nat.mul_le_mul_right M hR; omega
  have hRMg : R * M ≤ R * (M * ell) := Nat.mul_le_mul_left R (by omega)
  have hge : M * ell * 12 ≤ M * ell * R := Nat.mul_le_mul_left _ hR
  obtain ⟨A, hAd⟩ : ∃ A, A = ell * (R * M + M) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = ell * (3 * (R * M) + 4 * M) := ⟨_, rfl⟩
  obtain ⟨N, hNd⟩ : ∃ N, N = ell * (4 * (R * M) + 8 * M) := ⟨_, rfl⟩
  have hA' : A = M * ell * R + M * ell := by rw [hAd]; ring
  have hB' : B = 3 * (M * ell * R) + 4 * (M * ell) := by rw [hBd]; ring
  have hN' : N = 4 * (M * ell * R) + 8 * (M * ell) := by rw [hNd]; ring
  have hLf' : ∀ μ, Lf μ + 1 = N := fun μ => by rw [hLf μ, hN']; ring
  have hLu' : ∀ μ, Lu μ + 1 = 4 * (R * M) + 8 * M := fun μ => by rw [hLu μ]; ring
  obtain ⟨q, hq⟩ : ∃ q, ell * (R + 1) = q + R := ⟨ell * (R + 1) - R, by
    have : R ≤ ell * (R + 1) := by nlinarith
    omega⟩
  have hqpos : 0 < q := by
    have : 2 * (R + 1) ≤ ell * (R + 1) := Nat.mul_le_mul_right _ hell
    omega
  obtain ⟨A0, hA0d⟩ : ∃ A0, A0 = M * q := ⟨_, rfl⟩
  obtain ⟨B0, hB0d⟩ : ∃ B0, B0 = B + R * M := ⟨_, rfl⟩
  have hA0 : A0 + R * M = A := by
    rw [hA0d, hA', show M * ell * R + M * ell = M * (ell * (R + 1)) by ring, hq]; ring
  have hA0pos : 0 < A0 := by rw [hA0d]; exact Nat.mul_pos hM hqpos
  have hApos : 0 < A := by omega
  have hMA0 : M ∣ A0 := ⟨q, hA0d⟩
  have hgA : M * ell ∣ A := ⟨R + 1, by rw [hA']; ring⟩
  have hgB : M * ell ∣ B := ⟨3 * R + 4, by rw [hB']; ring⟩
  have hgN : M * ell ∣ N := ⟨4 * R + 8, by rw [hN']; ring⟩
  have hMB : M ∣ B := ⟨ell * (3 * R + 4), by rw [hB']; ring⟩
  have hMB0 : M ∣ B0 := by rw [hB0d]; exact Nat.dvd_add hMB ⟨R, by ring⟩
  have hMN : M ∣ N := ⟨ell * (4 * R + 8), by rw [hN']; ring⟩
  have hsh1 : A0 + 12 * M ≤ A := by omega
  have hsh2 : B + 12 * M ≤ B0 := by omega
  have hW : A + 12 * (M * ell) ≤ B := by omega
  have hW0 : A0 + 12 * M ≤ B0 := by omega
  have hB0N : B0 < N := by omega
  have hBN : B ≤ N := by omega
  have hNb : 12 * M + 12 * (M * ell) ≤ N := by omega
  have hN1 : 1 < N := by omega
  have hAdm : Admissible ell M R 1 (TU A0 A B B0 Lf) :=
    TU_admissible hLf' hM hell hA0 hB0d.symm hMA0 hMB0 hgA hgB hMN hgN (by omega) (by omega)
  have hCov : CoversOm0p ell M 12 1 (TU A0 A B B0 Lf) :=
    TU_coversp hLf' hN1 hM hell hMA0 hMB0 hgA hgB hA0pos hApos hW0 hW (by omega) hBN hNb
  -- Lambda
  have hcd : ell ∣ 2 * (R * M) + 2 * M := by
    obtain ⟨t, ht⟩ := hellM
    exact ⟨2 * (R * t) + 2 * t, by rw [ht]; ring⟩
  have hcMd : ell ∣ 2 * (R * M) + 2 * M + M := by
    obtain ⟨t, ht⟩ := hellM
    exact ⟨2 * (R * t) + 3 * t, by rw [ht]; ring⟩
  have hMc : M ∣ 2 * (R * M) + 2 * M := ⟨2 * R + 2, by ring⟩
  have hMcM : M ∣ 2 * (R * M) + 2 * M + M := ⟨2 * R + 3, by ring⟩
  have hTor : TorusOK ell M Lu := by
    refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩
    · rw [hLu μ]; exact Dvd.dvd.mul_right hellM _
    · have := hLu μ
      have h1 : ell ≤ M := Nat.le_of_dvd hM hellM
      have h2 : M * 8 ≤ M * (4 * R + 8) := Nat.mul_le_mul_left M (by omega)
      omega
    · rw [hLu μ]; exact Dvd.intro _ rfl
  have hLamOK : LambdaOK (Lu := Lu) (Lf := Lf) ell M R 1 (TU A0 A B B0 Lf) (LamG (2 * (R * M) + 2 * M) M Lu) := by
    have hemb : ∀ (y : PeriodicLatticeSite Lu) (μ : Fin 3), ell ^ 1 * (y μ).val < Lf μ + 1 := by
      intro y μ
      have h1 := (y μ).isLt
      rw [pow_one, hLf' μ, hNd, ← hLu' μ]
      exact (Nat.mul_lt_mul_left (by omega)).mpr h1
    refine ⟨?_, fun y μ => ⟨ell ^ 1 * (y μ).val, hemb y μ⟩, ?_, ?_, ?_⟩
    · intro x hx y hy
      simp only [LamG, Set.mem_setOf_eq] at hx ⊢
      exact blk_iv hM hMc hMcM (hy 0) hx
    · intro y μ; rfl
    · intro y hy
      simp only [LamG, Set.mem_setOf_eq] at hy
      rw [TU_om1]
      refine ⟨0, ?_⟩
      show A ≤ ell ^ 1 * (y 0).val ∧ ell ^ 1 * (y 0).val < B
      rw [pow_one, hAd, hBd]
      exact ⟨Nat.mul_le_mul_left ell (by omega), (Nat.mul_lt_mul_left (by omega)).mpr (by omega)⟩
    · intro y hy y' hy'
      simp only [LamG, Set.mem_setOf_eq] at hy
      have hy'' : ¬ (A ≤ ell ^ 1 * (y' 0).val ∧ ell ^ 1 * (y' 0).val < B) :=
        fun h => hy' ((TU_om1 _).mpr ⟨0, h⟩)
      have hsplit : (y' 0).val < R * M + M ∨ 3 * (R * M) + 4 * M ≤ (y' 0).val := by
        by_contra hcon
        push Not at hcon
        apply hy''
        rw [pow_one]
        constructor
        · rw [hAd]; exact Nat.mul_le_mul_left ell hcon.1
        · rw [hBd]; exact (Nat.mul_lt_mul_left (by omega)).mpr hcon.2
      have hlt : R * M < pcd (Lu 0 + 1) (y 0).val (y' 0).val := by
        have := hLu' 0; have := (y' 0).isLt; have := (y 0).isLt
        unfold pcd; split_ifs <;> omega
      exact lt_of_lt_of_le hlt (pcd_le_pdist y y')
  have hLam2 : LambdaOK2 (Lu := Lu) (Lf := Lf) ell M R 1 (TU A0 A B B0 Lf) (LamG (2 * (R * M) + 2 * M) M Lu) :=
    ⟨hLamOK, LamG_blockSum (by omega) hcd hcMd⟩
  have hLne : (LamG (2 * (R * M) + 2 * M) M Lu).Nonempty :=
    ⟨fun μ => ⟨if μ = 0 then 2 * (R * M) + 2 * M else 0, by have := hLu' μ; split_ifs <;> omega⟩, by
      simp only [LamG, Set.mem_setOf_eq]; simp; omega⟩
  -- sites
  have hB0lt : ∀ μ : Fin 3, B0 < Lf μ + 1 := fun μ => by have := hLf' μ; omega
  have hwlt : ∀ μ : Fin 3, B0 - M < Lf μ + 1 := fun μ => by have := hLf' μ; omega
  let w : PeriodicLatticeSite Lf := fun μ => ⟨B0 - M, hwlt μ⟩
  have hwv : ∀ μ, (w μ).val = B0 - M := fun μ => rfl
  have hwOm0 : w ∈ (TU A0 A B B0 Lf).Om 0 := (TU_om0 w).mpr ⟨0, by rw [hwv]; omega, by rw [hwv]; omega⟩
  have hwB : w ∈ towerBj (TU A0 A B B0 Lf) 0 :=
    (TU_bj0 w).mpr ⟨⟨0, by rw [hwv]; omega, by rw [hwv]; omega⟩, by
      rintro ⟨μ, h1, h2⟩
      rw [hwv] at h1 h2
      omega⟩
  have hs0 : strat (TU A0 A B B0 Lf) 1 w = 0 := ((strat_eq_iff hAdm (Nat.zero_le 1) w).mp hwB).2
  have hAlt : ∀ μ : Fin 3, A < Lf μ + 1 := fun μ => by have := hLf' μ; omega
  let u : PeriodicLatticeSite Lf := fun μ => ⟨A, hAlt μ⟩
  have huB : u ∈ towerBj (TU A0 A B B0 Lf) 1 := (TU_bj1 u).mpr ⟨0, le_refl _, by show A < B; omega⟩
  have hgsp : gsp ell M 1 0 = M := by simp [gsp, bigSide]
  have hpatch : IsPatch ell M 1 1 (TU A0 A B B0 Lf) 0 w := by
    refine ⟨Nat.zero_le 1, ?_, w, hwOm0, hs0, fun μ => rfl⟩
    intro μ
    show (w μ).val % (1 * bigSide M ell 0) = 0
    rw [one_mul, bigSide0, hwv]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hMB0 (dvd_refl M))
  -- the obstruction
  have hobs : ¬ ∃ (f : ℕ) (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ),
      DescribedAt ell M f 1 (TU A0 A B B0 Lf) sites i ∧
        {y | y ∈ patch ell M 1 5 0 w ∧ y ∈ (TU A0 A B B0 Lf).Om 0} ⊆ sites := by
    rintro ⟨f, sites, i, ⟨hik, ⟨z, hgc, hsites⟩, hbj, hne⟩, hsub⟩
    -- the three points w + M e_rho
    have hp : ∀ ρ : Fin 3, Function.update w ρ ⟨B0, hB0lt ρ⟩ ∈ sites := by
      intro ρ
      apply hsub
      refine ⟨?_, ?_⟩
      · show pdist w (Function.update w ρ ⟨B0, hB0lt ρ⟩) ≤ 5 * gsp ell M 1 0
        rw [pdist_update, hgsp]
        have := hLf' ρ
        unfold pcd; rw [hwv]; split_ifs <;> omega
      · obtain ⟨σ, hσ⟩ : ∃ σ : Fin 3, σ ≠ ρ := by
          fin_cases ρ
          exacts [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]
        refine (TU_om0 _).mpr ⟨σ, ?_, ?_⟩ <;>
          (rw [Function.update_of_ne hσ, hwv]; omega)
    let q : PeriodicLatticeSite Lf := fun μ => ⟨B0, hB0lt μ⟩
    have hq : q ∈ sites := by
      rw [hsites, memBoxAll hLf']
      intro ρ
      have h1 := hp ρ
      rw [hsites, memBoxAll hLf'] at h1
      have h2 := h1 ρ
      simpa using h2
    have hq0 : q ∈ (TU A0 A B B0 Lf).Om 0 := by
      rcases hbj hq with h | h
      · exact om_anti hAdm (Nat.zero_le i) h.1
      · exact om_anti hAdm (Nat.zero_le (i + 1)) h.1
    obtain ⟨μ, h1, h2⟩ := (TU_om0 q).mp hq0
    exact absurd h2 (by show ¬ B0 < B0; omega)
  -- the non-box set class (factor 11) does contain the patch
  have hw0P : w ∈ {y | y ∈ patch ell M 1 5 0 w ∧ y ∈ (TU A0 A B B0 Lf).Om 0} :=
    ⟨show pdist w w ≤ 5 * gsp ell M 1 0 by
      have h0 : pdist w w = 0 := by unfold pdist pcd; simp
      omega, hwOm0⟩
  have hp0lt : B0 < Lf 0 + 1 := hB0lt 0
  have hp0P : Function.update w 0 ⟨B0, hp0lt⟩ ∈
      {y | y ∈ patch ell M 1 5 0 w ∧ y ∈ (TU A0 A B B0 Lf).Om 0} := by
    refine ⟨?_, (TU_om0 _).mpr ⟨1, ?_, ?_⟩⟩
    · show pdist w (Function.update w 0 ⟨B0, hp0lt⟩) ≤ 5 * gsp ell M 1 0
      rw [pdist_update, hgsp]
      have := hLf' 0
      unfold pcd; rw [hwv]; split_ifs <;> omega
    · rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0), hwv]; omega
    · rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0), hwv]; omega
  obtain ⟨tB, htB⟩ := hMB0
  have hz5 : 5 * M ≤ B0 - M := by omega
  have hzlt : ∀ μ : Fin 3, B0 - M - 5 * M < Lf μ + 1 := fun μ => by have := hLf' μ; omega
  let z5 : PeriodicLatticeSite Lf := fun μ => ⟨B0 - M - 5 * M, hzlt μ⟩
  have hsetW : IsClassSetW ell M 11 1 (TU A0 A B B0 Lf)
      {y | y ∈ patch ell M 1 5 0 w ∧ y ∈ (TU A0 A B B0 Lf).Om 0} 0 := by
    refine ⟨Nat.zero_le 1, ?_, ⟨w, hw0P, hwB⟩, ⟨z5, ?_⟩,
      w, hw0P, Function.update w 0 ⟨B0, hp0lt⟩, hp0P, 0, ?_⟩
    · intro y hy
      by_cases h1 : y ∈ (TU A0 A B B0 Lf).Om 1
      · right; exact (TU_bj1 y).mpr ((TU_om1 y).mp h1)
      · left; rw [TU_bj0]; exact ⟨(TU_om0 y).mp hy.2, fun h => h1 ((TU_om1 y).mpr h)⟩
    · intro y hy
      rw [memBoxAll hLf', bigSide0]
      intro ρ
      have hc := pcd_le_pd w y ρ
      have hc' : pcd (Lf ρ + 1) (w ρ).val (y ρ).val ≤ 5 * M := by
        have := hy.1; simp only [patch, Set.mem_setOf_eq, hgsp] at this; omega
      have hyN := site_lt hLf' y ρ
      have hzN : (z5 ρ).val < N := site_lt hLf' z5 ρ
      rw [off_lt_iff _ _ _ _ hyN hzN]
      have e := hLf' ρ
      simp only [z5, hwv] at hc' ⊢
      unfold pcd at hc'
      split_ifs at hc' <;> omega
    · rw [hwv, bigSide0]
      simp only [Function.update_self, ne_eq]
      intro h
      have : (B0 - M) / M = B0 / M := h
      rw [htB] at this
      have h3 : M * tB - M = M * (tB - 1) := by rw [Nat.mul_sub, mul_one]
      rw [h3, Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM] at this
      have : 0 < tB := by
        rcases Nat.eq_zero_or_pos tB with h0 | h0
        · rw [h0] at htB; omega
        · exact h0
      omega
  refine ⟨TU A0 A B B0 Lf, LamG (2 * (R * M) + 2 * M) M Lu, hTor, hAdm, hCov, hLam2, hLne,
    LamG_blockSum (by omega) hcd hcMd |>.lamPrime_nonempty hLne, ⟨w, hwB⟩, ⟨u, huB⟩, w, hpatch, hobs, ?_, ?_,
    ⟨_, 0, hsetW, fun y hy => hy⟩⟩
  · rintro ⟨f, sites, i, ⟨-, hd, -⟩, hsub⟩
    exact hobs ⟨f, sites, i, hd, hsub⟩
  · rintro ⟨f, sites, i, ⟨hd, -⟩, hsub⟩
    exact hobs ⟨f, sites, i, hd, hsub⟩

/-- unconditional existence of the tori and the conclusion. -/
theorem lf_counterexample_exists {ell M R : ℕ}
    (hell : 2 ≤ ell) (hM : 0 < M) (hellM : ell ∣ M) (hR : 12 ≤ R) :
    ∃ Lu Lf : PeriodicLatticeExtent, (∀ μ, Lu μ + 1 = M * (4 * R + 8)) ∧ (∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) ∧
      LFail ell M R Lu Lf := by
  have h1 : 0 < M * (4 * R + 8) := Nat.mul_pos hM (by omega)
  have h2 : 0 < M * ell * (4 * R + 8) := Nat.mul_pos (Nat.mul_pos hM (by omega)) (by omega)
  have e1 : ∀ μ : Fin 3, (fun _ : Fin 3 => M * (4 * R + 8) - 1) μ + 1 = M * (4 * R + 8) := fun μ => by
    show M * (4 * R + 8) - 1 + 1 = _
    omega
  have e2 : ∀ μ : Fin 3, (fun _ : Fin 3 => M * ell * (4 * R + 8) - 1) μ + 1 = M * ell * (4 * R + 8) := fun μ => by
    show M * ell * (4 * R + 8) - 1 + 1 = _
    omega
  exact ⟨fun _ => M * (4 * R + 8) - 1, fun _ => M * ell * (4 * R + 8) - 1, e1, e2,
    lf_counterexample hell hM hellM hR e1 e2⟩

/-- the regime of the repair `ballChartsG`: `M = ell^m`, `m ≥ 5`, `R ≥ 45 ell + 30`, every `ell ≥ 2`. -/
theorem lf_counterexample_pow {ell m R : ℕ} {Lu Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hm : 5 ≤ m) (hR : 45 * ell + 30 ≤ R)
    (hLu : ∀ μ, Lu μ + 1 = ell ^ m * (4 * R + 8)) (hLf : ∀ μ, Lf μ + 1 = ell ^ m * ell * (4 * R + 8)) :
    LFail ell (ell ^ m) R Lu Lf :=
  lf_counterexample hell (pow_pos (by omega) m) (dvd_pow_self ell (by omega)) (by omega) hLu hLf

end AdalyFormal.P409
