import P409C

/-!
# P409D -- the in-regime counterexample to the p.409 containment (one-factor class, factor 12).

For `ell >= 2`, `0 < M`, `ell | M`, `R >= 12` (in particular `M = ell^m`, `m >= 1`, and every `R >= 45 ell + 30`):
a one-slab tower `TG` with `TorusOK`, `Admissible ell M R 1`, `CoversOm0p ell M 12 1`, `LambdaOK2`, a patch `IsPatch ell M 1 1 S 1 w`,
such that NO class cube of factor 12 contains `patch ∩ Ω₀` (via `patch_inter_not_in_class_cube`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.M1 (strat strat_eq_iff IsPatch patch gsp)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice)

/-- `Λ`: the unit slab `c ≤ y₀ < c + M`. -/
def LamG (c M : ℕ) (Lu : PeriodicLatticeExtent) : Set (PeriodicLatticeSite Lu) :=
  {y | c ≤ (y 0).val ∧ (y 0).val < c + M}

theorem align_lt {ell b x : ℕ} (hell : 0 < ell) (hb : ell ∣ b) (h : x < b) : ell * (x / ell) + ell ≤ b := by
  obtain ⟨r, rfl⟩ := hb
  have h1 : x / ell < r := (Nat.div_lt_iff_lt_mul hell).mpr (by rw [mul_comm]; exact h)
  have := Nat.mul_le_mul_left ell (Nat.succ_le_of_lt h1)
  rw [Nat.mul_succ] at this
  exact this

theorem LamG_blockSum {Lu : PeriodicLatticeExtent} {ell c M : ℕ} (hell : 0 < ell) (hc : ell ∣ c) (hcM : ell ∣ c + M) :
    LamBlockSum ell (LamG c M Lu) := by
  intro x hx
  simp only [LamG, Set.mem_setOf_eq] at hx
  have hd : ∀ μ : Fin 3, ell * ((x μ).val / ell) < Lu μ + 1 := fun μ => by
    have := (div_facts ell (x μ).val hell).1; have := (x μ).isLt; omega
  let y : PeriodicLatticeSite Lu := fun μ => ⟨ell * ((x μ).val / ell), hd μ⟩
  have hy : ∀ μ, (y μ).val = ell * ((x μ).val / ell) := fun μ => rfl
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_CoarseLattice]
    intro μ
    show (ell * ((x μ).val / ell)) % ell = 0
    exact Nat.mul_mod_right _ _
  · intro x' hx'
    rw [mem_blockOf] at hx'
    have h0 := hx' 0
    simp only [LamG, Set.mem_setOf_eq]
    have h1 := align_ge hell hc hx.1
    have h2 := align_lt hell hcM hx.2
    rw [hy 0] at h0
    show c ≤ (x' 0).val ∧ (x' 0).val < c + M
    omega
  · rw [mem_blockOf]
    intro μ
    have := div_facts ell (x μ).val hell
    show ell * ((x μ).val / ell) ≤ (x μ).val ∧ (x μ).val < ell * ((x μ).val / ell) + ell
    omega

/-- the full conclusion, quantified over the data (this is the statement of the main theorems). -/
def InRegimeCounterexample (ell M R : ℕ) (Lu Lf : PeriodicLatticeExtent) : Prop :=
  ∃ (S : Tower Lf) (Lam : Set (PeriodicLatticeSite Lu)),
    TorusOK ell M Lu ∧ Admissible ell M R 1 S ∧ CoversOm0p ell M 12 1 S ∧
    LambdaOK2 (Lu := Lu) (Lf := Lf) ell M R 1 S Lam ∧ Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
    (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj S 0) ∧ (∃ p : PeriodicLatticeSite Lf, p ∈ towerBj S 1) ∧
    ∃ w : PeriodicLatticeSite Lf, IsPatch ell M 1 1 S 1 w ∧
      ¬ ∃ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), IsClassCube ell M 12 1 S sites i ∧
          {y | y ∈ patch ell M 1 5 1 w ∧ y ∈ S.Om 0} ⊆ sites

theorem p409_regime_counterexample {ell M R : ℕ} {Lu Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hellM : ell ∣ M) (hR : 12 ≤ R)
    (hLu : ∀ μ, Lu μ + 1 = M * (4 * R + 8)) (hLf : ∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) :
    InRegimeCounterexample ell M R Lu Lf := by
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
  obtain ⟨A0, hA0d⟩ : ∃ A0, A0 = M * q := ⟨_, rfl⟩
  obtain ⟨B0, hB0d⟩ : ∃ B0, B0 = B + R * M := ⟨_, rfl⟩
  have hA0 : A0 + R * M = A := by
    rw [hA0d, hA', show M * ell * R + M * ell = M * (ell * (R + 1)) by ring, hq]; ring
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
  have hB0N : B0 < N := by omega
  have hNb : 12 * M + 12 * (M * ell) ≤ N := by omega
  have hN1 : 1 < N := by omega
  have hAdm : Admissible ell M R 1 (TG A0 A B B0 Lf) :=
    TG_admissible hLf' hM hell hA0 hB0d.symm hMA0 hMB0 hgA hgB hMN hgN (by omega) (by omega)
  have hCov : CoversOm0p ell M 12 1 (TG A0 A B B0 Lf) :=
    TG_coversp hLf' hN1 hM hell hMA0 hMB0 hgA hgB hsh1 hsh2 hW hB0N hNb
  -- Lambda
  have hcd : ell ∣ 2 * (R * M) + 2 * M := by
    obtain ⟨t, ht⟩ := hellM
    exact ⟨2 * (R * t) + 2 * t, by rw [show 2 * (R * M) + 2 * M = 2 * (R * M) + 2 * M from rfl, ht]; ring⟩
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
  have hLamOK : LambdaOK (Lu := Lu) (Lf := Lf) ell M R 1 (TG A0 A B B0 Lf) (LamG (2 * (R * M) + 2 * M) M Lu) := by
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
      rw [TG_om1]
      show A ≤ ell ^ 1 * (y 0).val ∧ ell ^ 1 * (y 0).val < B
      rw [pow_one, hAd, hBd]
      exact ⟨Nat.mul_le_mul_left ell (by omega), (Nat.mul_lt_mul_left (by omega)).mpr (by omega)⟩
    · intro y hy y' hy'
      simp only [LamG, Set.mem_setOf_eq] at hy
      have hy'' : ¬ (A ≤ ell ^ 1 * (y' 0).val ∧ ell ^ 1 * (y' 0).val < B) := fun h => hy' ((TG_om1 _).mpr h)
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
  have hLam2 : LambdaOK2 (Lu := Lu) (Lf := Lf) ell M R 1 (TG A0 A B B0 Lf) (LamG (2 * (R * M) + 2 * M) M Lu) :=
    ⟨hLamOK, LamG_blockSum (by omega) hcd hcMd⟩
  have hLne : (LamG (2 * (R * M) + 2 * M) M Lu).Nonempty :=
    ⟨fun μ => ⟨if μ = 0 then 2 * (R * M) + 2 * M else 0, by have := hLu' μ; split_ifs <;> omega⟩, by
      simp only [LamG, Set.mem_setOf_eq]; simp; omega⟩
  -- sites
  have hAN : A < N := by omega
  let w : PeriodicLatticeSite Lf := fun μ => ⟨if μ = 0 then A else 0, by have := hLf' μ; split_ifs <;> omega⟩
  have hw0 : (w 0).val = A := by simp [w]
  have hw1 : (w 1).val = 0 := by simp [w]
  have hw2 : (w 2).val = 0 := by simp [w]
  have hwOm1 : w ∈ (TG A0 A B B0 Lf).Om 1 := (TG_om1 w).mpr (by rw [hw0]; omega)
  have hwOm0 : w ∈ (TG A0 A B B0 Lf).Om 0 := (TG_om0 w).mpr (by rw [hw0]; omega)
  have hwB : w ∈ towerBj (TG A0 A B B0 Lf) 1 := (TG_bj1 w).mpr (by rw [hw0]; omega)
  have hs1 : strat (TG A0 A B B0 Lf) 1 w = 1 := ((strat_eq_iff hAdm (le_refl 1) w).mp hwB).2
  have hvlt : A - 1 < Lf 0 + 1 := by have := hLf' 0; omega
  let v : PeriodicLatticeSite Lf := Function.update w 0 ⟨A - 1, hvlt⟩
  have hv0 : (v 0).val = A - 1 := by simp [v]
  have hvB : v ∈ towerBj (TG A0 A B B0 Lf) 0 := (TG_bj0 v).mpr (by rw [hv0]; omega)
  have hs0 : strat (TG A0 A B B0 Lf) 1 v = 0 := ((strat_eq_iff hAdm (Nat.zero_le 1) v).mp hvB).2
  have hpatch : IsPatch ell M 1 1 (TG A0 A B B0 Lf) 1 w := by
    refine ⟨le_refl 1, ?_, w, hwOm0, hs1, fun μ => rfl⟩
    intro μ
    show (w μ).val % (1 * bigSide M ell 1) = 0
    rw [one_mul, bigSide1]
    fin_cases μ
    · show (w 0).val % (M * ell) = 0
      rw [hw0]; exact Nat.mod_eq_zero_of_dvd hgA
    · show (w 1).val % (M * ell) = 0
      rw [hw1]; exact Nat.zero_mod _
    · show (w 2).val % (M * ell) = 0
      rw [hw2]; exact Nat.zero_mod _
  have hgsp : gsp ell M 1 1 = M * ell := by simp [gsp, bigSide]
  have hvp : v ∈ patch ell M 1 5 1 w := by
    show pdist w v ≤ 5 * gsp ell M 1 1
    rw [pdist_update, hgsp]
    have := hLf' 0
    unfold pcd; rw [hw0]; split_ifs <;> omega
  have hv0Om : v ∈ (TG A0 A B B0 Lf).Om 0 := ((TG_bj0 v).mp hvB).1 |> fun h => (TG_om0 v).mpr h
  have h5lt : 5 * (M * ell) < Lf 1 + 1 := by have := hLf' 1; omega
  have hN5lt : N - 5 * (M * ell) < Lf 1 + 1 := by have := hLf' 1; omega
  let p1 : PeriodicLatticeSite Lf := Function.update w 1 ⟨5 * (M * ell), h5lt⟩
  let p2 : PeriodicLatticeSite Lf := Function.update w 1 ⟨N - 5 * (M * ell), hN5lt⟩
  have hp1 : p1 ∈ patch ell M 1 5 1 w := by
    show pdist w p1 ≤ 5 * gsp ell M 1 1
    rw [pdist_update, hgsp, hw1]
    have := hLf' 1
    unfold pcd; split_ifs <;> omega
  have hp2 : p2 ∈ patch ell M 1 5 1 w := by
    show pdist w p2 ≤ 5 * gsp ell M 1 1
    rw [pdist_update, hgsp, hw1]
    have := hLf' 1
    unfold pcd; split_ifs <;> omega
  have hp10 : p1 ∈ (TG A0 A B B0 Lf).Om 0 := (TG_om0 p1).mpr (by
    simp only [p1, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]; rw [hw0]; omega)
  have hp20 : p2 ∈ (TG A0 A B B0 Lf).Om 0 := (TG_om0 p2).mpr (by
    simp only [p2, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1)]; rw [hw0]; omega)
  have hfar : 12 * bigSide M ell (1 - 1) ≤ pcd (Lf 1 + 1) (p1 1).val (p2 1).val := by
    show 12 * bigSide M ell 0 ≤ _
    rw [bigSide0]
    simp only [p1, p2, Function.update_self]
    have := hLf' 1
    unfold pcd; split_ifs <;> omega
  refine ⟨TG A0 A B B0 Lf, LamG (2 * (R * M) + 2 * M) M Lu, hTor, hAdm, hCov, hLam2, hLne,
    LamG_blockSum (by omega) hcd hcMd |>.lamPrime_nonempty hLne, ⟨v, hvB⟩, ⟨w, hwB⟩, w, hpatch, ?_⟩
  exact patch_inter_not_in_class_cube (c := 5) (κ := 1) (f := 12) hAdm (by norm_num) hM (by omega) (by norm_num)
    hpatch hvp hv0Om (by rw [hs0]) hp1 hp10 hp2 hp20 1 hfar

/-- unconditional existence of the tori and the conclusion. -/
theorem p409_regime_counterexample_exists {ell M R : ℕ}
    (hell : 2 ≤ ell) (hM : 0 < M) (hellM : ell ∣ M) (hR : 12 ≤ R) :
    ∃ Lu Lf : PeriodicLatticeExtent, (∀ μ, Lu μ + 1 = M * (4 * R + 8)) ∧ (∀ μ, Lf μ + 1 = M * ell * (4 * R + 8)) ∧
      InRegimeCounterexample ell M R Lu Lf := by
  refine ⟨fun _ => M * (4 * R + 8) - 1, fun _ => M * ell * (4 * R + 8) - 1, ?_, ?_, ?_⟩
  · intro μ
    have : 0 < M * (4 * R + 8) := Nat.mul_pos hM (by omega)
    show M * (4 * R + 8) - 1 + 1 = _
    omega
  · intro μ
    have : 0 < M * ell * (4 * R + 8) := Nat.mul_pos (Nat.mul_pos hM (by omega)) (by omega)
    show M * ell * (4 * R + 8) - 1 + 1 = _
    omega
  · apply p409_regime_counterexample hell hM hellM hR
    · intro μ
      have : 0 < M * (4 * R + 8) := Nat.mul_pos hM (by omega)
      show M * (4 * R + 8) - 1 + 1 = _
      omega
    · intro μ
      have : 0 < M * ell * (4 * R + 8) := Nat.mul_pos (Nat.mul_pos hM (by omega)) (by omega)
      show M * ell * (4 * R + 8) - 1 + 1 = _
      omega

/-- the regime of the repair `ballChartsG`: `M = ell^m`, `m ≥ 5`, `R ≥ 45 ell + 30`, every `ell ≥ 2`. -/
theorem p409_regime_counterexample_pow {ell m R : ℕ} {Lu Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hm : 5 ≤ m) (hR : 45 * ell + 30 ≤ R)
    (hLu : ∀ μ, Lu μ + 1 = ell ^ m * (4 * R + 8)) (hLf : ∀ μ, Lf μ + 1 = ell ^ m * ell * (4 * R + 8)) :
    InRegimeCounterexample ell (ell ^ m) R Lu Lf :=
  p409_regime_counterexample hell (pow_pos (by omega) m) (dvd_pow_self ell (by omega)) (by omega) hLu hLf

#print axioms p409_regime_counterexample
#print axioms p409_regime_counterexample_exists
#print axioms p409_regime_counterexample_pow

end AdalyFormal.P409
