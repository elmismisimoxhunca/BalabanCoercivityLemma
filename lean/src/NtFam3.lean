import NtFam2

/-!
# NfFam3 -- the refuting witness carries a class cube, an uncovered site, and its tower is exposed (lane ncwdh_family_20261018, response to VERDICT2)

* `exists_classCube_ne` : on the witness tower `neS ell M R` (`k = 2`, any `ell ≥ 3`, `M > 0`, `R ≥ max 1 cf`), the box at the grid corner `P1 = neP1 ell M R` (first coordinate; others 0) of side `cf * (M * ell)` is a
  class cube of factor `cf` with index `1` (contained in `B^1 = Ω₁ \ Ω₂`, so levels `0` and `2` are excluded).  Regime: level 1 only, `R ≥ cf`.
* `FailAtCS` / `FailEllCS`: copies of `FailAtC` / `FailEllC` that EXPOSE the witness data (torus `neLu M R`, tower `neS ell M R`, `k = 2`, `Λ = neLam M R`).
  `nested_stag_failAtS` ... `failEllCS_ok` re-run the wrapper chain of `nested_stag_failAt` ... `failEllC_ok` verbatim with `FailAtC` -> `FailAtCS` (same hypotheses, same lemmas).
* `exists_uncovered_site` : a site of `Ω₀` (first coordinate `neC`) lies in no class cube of factor `cf` (from `ne_layer_uncovered`), so `CovSitesF .. (constFam c)` FAILS: the site-coverage clause is the one that fails.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.CoverOmega.Struct

set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.NcwdhStrong
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVac (mem_box_N)

/-! ## part A: a class cube on the witness tower -/

omit [CfData] in
theorem box_coord {N z x s : ℕ} (hx : x < N) (hzs : z + s ≤ N) (h : (x + N - z) % N < s) : z ≤ x ∧ x < z + s := by
  by_cases hzx : z ≤ x
  · have h1 : x + N - z = (x - z) + N := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · have h1 : x + N - z < N := by omega
    rw [Nat.mod_eq_of_lt h1] at h
    omega

theorem exists_classCube_ne {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR1 : 1 ≤ R) (hR : CfData.cf ≤ R) :
    ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell 2 (neLu M R)))) (j : ℕ),
      IsClassCube ell M CfData.cf 2 (neS ell M R) sites j := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR1
  obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c (M := M) hell
  have hcf := CfData.hcf
  have hN := ne_scaleUp (ell := ell) (R := R) (by omega) hM
  have hNe : neN ell M R = 4 * (ell * (ell * (R * M))) + 2 * (CfData.cf * (ell * (ell * M))) + 6 * (ell * (ell * M)) := rfl
  -- P1 is a multiple of the level-1 block side
  have hP1 : neP1 ell M R = M * ell ^ 1 * (R * (ell - 1) + ell) := by
    obtain ⟨e, rfl⟩ : ∃ e, ell = e + 1 := ⟨ell - 1, by omega⟩
    simp only [neP1, neA', Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  -- the cube side `s = cf * (M * ell)` fits in `[P1, A')`
  have hs : CfData.cf * (M * ell ^ 1) = CfData.cf * (ell * M) := by ring
  have hRs : CfData.cf * (ell * M) ≤ ell * (R * M) := by
    calc CfData.cf * (ell * M) ≤ R * (ell * M) := Nat.mul_le_mul_right _ hR
      _ = ell * (R * M) := by ring
  have hspos : 0 < CfData.cf * (ell * M) := by omega
  have hP1lt : neP1 ell M R + CfData.cf * (ell * M) ≤ neA' ell M R := by
    simp only [neP1, neA']; omega
  have hA'N : neA' ell M R < neN ell M R := by simp only [neA']; omega
  have hlt : ∀ y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)), ∀ μ, (y μ).val < neN ell M R :=
    fun y μ => by have := (y μ).isLt; have := hN μ; omega
  let z : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) :=
    fun μ => ⟨if μ = 0 then neP1 ell M R else 0, by
      have := hN μ; split_ifs <;> omega⟩
  have hz0 : (z 0).val = neP1 ell M R := by simp [z]
  have hz1 : (z 1).val = 0 := by simp [z]
  have hz2 : (z 2).val = 0 := by simp [z]
  have hsub : ∀ x ∈ siteBox z (CfData.cf * bigSide M ell 1),
      x ∈ (neS ell M R).Om 1 ∧ x ∉ (neS ell M R).Om 2 := by
    intro x hx
    have h0 := ((mem_box_N hN z x _).1 hx).1
    simp only [bigSide, hs, hz0] at h0
    obtain ⟨hlo, hhi⟩ := box_coord (hlt x 0) (by omega) h0
    refine ⟨?_, ?_⟩
    · rw [neS_om1]; simp only [neP1, neQ1, neB, neA'] at hlo hhi ⊢; omega
    · rw [neS_om2]; simp only [neP1, neA', neB', neA, neB] at hlo hhi ⊢; omega
  refine ⟨siteBox z (CfData.cf * bigSide M ell 1), 1, ⟨⟨by norm_num, ⟨z, ?_, rfl⟩, ?_, ?_⟩, ?_⟩⟩
  · intro μ
    fin_cases μ
    · show (z 0).val % bigSide M ell 1 = 0
      rw [hz0, hP1]; simp only [bigSide]; exact Nat.mul_mod_right _ _
    · show (z 1).val % bigSide M ell 1 = 0
      rw [hz1]; exact Nat.zero_mod _
    · show (z 2).val % bigSide M ell 1 = 0
      rw [hz2]; exact Nat.zero_mod _
  · intro x hx
    left
    exact hsub x hx
  · refine ⟨z, ?_, ?_⟩
    · rw [mem_box_N hN z z _]
      simp only [bigSide, hs]
      refine ⟨?_, ?_, ?_⟩ <;> simp [Nat.add_sub_cancel] <;> omega
    · have hh : neP1 ell M R + 0 ≤ neP1 ell M R := le_refl _
      refine ⟨?_, ?_⟩
      · rw [neS_om1]; simp only [neP1, neQ1, neB, neA']
        rw [show (z 0).val = neP1 ell M R from hz0]; simp only [neP1, neA', neQ1, neB]; omega
      · rw [neS_om2]; rw [show (z 0).val = neP1 ell M R from hz0]
        simp only [neP1, neA', neB', neA, neB]; omega
  · rintro i ⟨hi, -, hsub', ⟨w, hw, hwB⟩⟩
    have hwB1 := hsub w hw
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exfalso
      -- w ∈ Ω₀ \ Ω₁ but w ∈ Ω₁
      exact hwB.2 hwB1.1
    · rfl
    · exfalso
      exact hwB1.2 hwB.1

/-! ## part B: the witness chain with the tower exposed -/

/-- `FailAtC CfData.cf ell M R` with the witness tower/torus/`Λ` (`k = 2`) EXPOSED. -/
def FailAtCS (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∀ γ : ℝ, 0 < γ →
    TorusOK ell M (neLu M R) ∧ Admissible ell M R 2 (neS ell M R) ∧ LambdaOK2 ell M R 2 (neS ell M R) (neLam M R) ∧
    ∃ U : LinkCfg (scaleUp ell 2 (neLu M R)),
      PerCubeRegular2 ell M CfData.cf 2 (neS ell M R) α ((ell : ℝ) ^ 2)⁻¹ U ∧
      GenP.WellDefG (gparams ell 2 (neLu M R) hell (neS ell M R) U a (neLam M R)) ∧
      ∃ Bt : Bond (neLu M R) → SuTwo, OnLambdaTildeIn (neLam M R) ell Bt ∧ OnLambdaT (neLam M R) Bt ∧
        GenP.genForm (gparams ell 2 (neLu M R) hell (neS ell M R) U a (neLam M R))
          (WithLp.toLp 2 (GenP.genC (gparams ell 2 (neLu M R) hell (neS ell M R) U a (neLam M R)) Bt)) < γ * bondEnergy Bt

theorem FailAtCS.toFailAtC {ell M R : ℕ} {hell : 0 < ell} {a : ℝ} (h : FailAtCS ell M R hell a) :
    FailAtC CfData.cf ell M R hell a := fun α hα γ hγ => by
  obtain ⟨hT, hA, hL, U, hU, hW, Bt, h1, h2, hlt⟩ := h α hα γ hγ
  exact ⟨2, by norm_num, neLu M R, hT, neS ell M R, hA, neLam M R, hL, U, hU, hW, Bt, h1, h2, hlt⟩

def FailEllCS (ell : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ FailAtCS ell (ell ^ m) R hell a

theorem nested_stag_failAtS {ell M R : ℕ} (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hMe : ell + 3 ≤ M) (hM : 0 < M) (hR : 1 ≤ R) (a : ℝ) :
    ∃ cs : ℝ, IsCrossingN ell M R cs ∧ Real.cos (tcap ell) < cs ∧ (NearUnits ell M R (by omega) a cs → FailAtCS ell M R (by omega) a) := by
  obtain ⟨cs, h1, h2, hcr, p, hp, ε, hε, hneg⟩ := nested_genForm_neg hell3 hE hdvd hMe hM hR a
  refine ⟨cs, hcr, h1, fun hU α hα γ hγ => ?_⟩
  obtain ⟨t, htπ, hc1, hc2, hW⟩ := hU ε hε
  have hneg' := hneg t htπ hc1 hc2 hW.1.2.2 hW.1.2.1
  have hE0 : 0 ≤ bondEnergy (zfun (gU M R p) : Bond (neLu M R) → SuTwo) :=
    AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg _
  refine ⟨torusOK_ne hell3 hdvd hM, ne_admissible hell3 hM hR, lambdaOK2_ne hell3 hdvd hM hR, stagU ell M R t, ne_stag_class hell3 hM hR t hα, hW, zfun (gU M R p),
    onLambdaTildeIn_gU hell3 hdvd hp, onLambdaT_gU hell3 hdvd hMe hp, ?_⟩
  exact lt_of_lt_of_le hneg' (mul_nonneg hγ.le hE0)

theorem not_WDH_of_nearUnitsS (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧
      ∃ cs : ℝ, IsCrossingN ell (ell ^ m) R cs ∧ NearUnits ell (ell ^ m) R (by omega) a cs) :
    FailEllCS ell (by omega) a := by
  intro m₀
  obtain ⟨m, hm, hR⟩ := h (max m₀ 2)
  have hm1 : 2 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, cs, hcs, hnu⟩ := hR (max R₀ 1)
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  have hMe : ell + 3 ≤ ell ^ m := ell_add3_le_pow hell3 hm1
  refine ⟨R, le_trans (le_max_left _ _) hRR, ?_⟩
  obtain ⟨cs', hcs', _, hF⟩ := nested_stag_failAtS hell3 hE hdvd hMe hM (le_trans (le_max_right _ _) hRR) a
  have := crossing_unique hcs hcs'
  subst this
  exact hF hnu

theorem not_WDH_of_nearUnitsRestS (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧
      ∃ cs : ℝ, IsCrossingN ell (ell ^ m) R cs ∧ NearUnitsRest ell (ell ^ m) R (by omega) a cs) :
    FailEllCS ell (by omega) a := by
  refine not_WDH_of_nearUnitsS ell hell3 hE a ha (fun m₀ => ?_)
  obtain ⟨m, hm, hR⟩ := h (max m₀ 2)
  have hm1 : 2 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, cs, hcs, hnu⟩ := hR (max R₀ 1)
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  exact ⟨R, le_trans (le_max_left _ _) hRR, cs, hcs,
    nearUnits_of_rest hell3 hM (le_trans (le_max_right _ _) hRR) a cs ha hnu⟩

theorem not_WDH_of_anUnitsS (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ AnUnits ell (ell ^ m) R (by omega) a) :
    FailEllCS ell (by omega) a := by
  refine not_WDH_of_nearUnitsRestS ell hell3 hE a ha (fun m₀ => ?_)
  obtain ⟨m, hm, hR⟩ := h (max m₀ 2)
  have hm1 : 2 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hA⟩ := hR (max R₀ 1)
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega : m ≠ 0)
  have hMe : ell + 3 ≤ ell ^ m := ell_add3_le_pow hell3 hm1
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hRR
  obtain ⟨cs, hcs, hcs1, -⟩ := nested_stag_failAt hell3 hE hdvd hMe hM hR1 a
  exact ⟨R, le_trans (le_max_left _ _) hRR, cs, hcs, nearUnitsRest_of_anUnits (ell := ell) (M := ell ^ m) (R := R) (by omega) a cs hcs1 hcs.1 hA⟩

theorem not_WDH_of_anUnits4S (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ H0Good ell (ell ^ m) R (by omega) a ∧ AnUnits4 ell (ell ^ m) R (by omega) a) :
    FailEllCS ell (by omega) a := by
  refine not_WDH_of_anUnitsS ell hell3 hE a ha (fun m₀ => ?_)
  obtain ⟨m, hm, hR⟩ := h (max m₀ 2)
  have hm1 : 2 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hH, hA⟩ := hR (max R₀ 1)
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega : m ≠ 0)
  exact ⟨R, le_trans (le_max_left _ _) hRR,
    anUnits_of_four hell3 hdvd hM (le_trans (le_max_right _ _) hRR) a hH hA⟩

theorem not_WDH_of_unitsFour_pointsS (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a)
    (h : ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ ∃ t0 : ℝ, |t0| < tcap ell ∧
      UnitsFour (PN ell (ell ^ m) R (by omega) a t0)) : FailEllCS ell (by omega) a := by
  refine not_WDH_of_anUnits4S ell hell3 hE a ha (fun m₀ => ?_)
  obtain ⟨m, hm, hR⟩ := h (max m₀ 2)
  have hm1 : 2 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, fun R₀ => ?_⟩
  obtain ⟨R, hRR, t0, ht0, hu⟩ := hR (max R₀ 1)
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega : m ≠ 0)
  exact ⟨R, le_trans (le_max_left _ _) hRR,
    pn_H0_good hell3 hE hdvd hM (le_trans (le_max_right _ _) hRR) a,
    anUnits4_of_unitsFour_point hell3 hE hdvd hM (le_trans (le_max_right _ _) hRR) (by omega) ha t0 ht0 hu⟩

theorem failEllCS_ok (ell : ℕ) (hell3 : 3 ≤ ell) (hE : StagOK ell) (a : ℝ) (ha : 0 < a) :
    FailEllCS ell (by omega) a := by
  refine not_WDH_of_unitsFour_pointsS ell hell3 hE a ha ?_
  intro m₀
  refine ⟨m₀ + 1, by omega, fun R₀ => ⟨R₀ + 1, by omega, 0, by rw [abs_zero]; exact tcap_pos ell, ?_⟩⟩
  have hdvd : ell ∣ ell ^ (m₀ + 1) := dvd_pow_self ell (by omega)
  exact AdalyFormal.CoverOmega.unitsFour_flat_regime (ell := ell) (M := ell ^ (m₀ + 1)) (R := R₀ + 1)
    hell3 hE hdvd (pow_pos (by omega) _) (by omega) a ha

#print axioms exists_classCube_ne
#print axioms nested_stag_failAtS
#print axioms failEllCS_ok

end AdalyFormal.CoverOmega.Struct
