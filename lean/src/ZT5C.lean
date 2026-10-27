import ZT5B

/-!
# ZT5C -- NON-VACUITY of the r5 statement at `k ≥ 1`: the CLOSED POINT (full tower, `Λ = torus`, flat `U`, `ell = 2`, `M = 2^m`, every `m ≥ 1`).

Ported from `GenuineU1.closed_point_all_k` (GU1J; rebuilt here on the r5 fork `ZGU1*`).  What is proved here (declaration names):

* `closedPt_hyps`        : every hypothesis of `CoercG8At` holds at `(ell = 2, M = 2^m, k ≥ 1, Lu = 10·M − 1, S = fullTower, Λ = univ, U = 1)`:
                           `TorusOK`, `Admissible` (ℓ¹ distance, collar), `CoversOm0c .. 12 ..`, `LambdaOK2` (incl. `Λ = B(Λ')`), `PerCubeRegular2 .. 12 ..`,
                           a NONZERO `B̃ ∈ Λ̃` (touching AND both-endpoint class), and `WellDef` of the genuine family;
* `closedPt_ineq`        : the conclusion `InstIneq` (and `InstAtWD`) holds there with `γ₀ = 1/1728`, independent of `k`, `m`, `a`;
* `closedPt_consumes`    : the statement APPLIED: any `CoercG8At 2 (2^m) R k ..` at this `Lu` yields `InstIneq` at the point AND the plaquette gauge control (r7: via `CoercG8At.apply_gauge`, the single-binder `ClassCoupled`);
* `closedPt_class_excludes_some_U` : the class `PerCubeRegular2 .. 12 ..` is restrictive there.

(`WellDefG` = `WellDef ∧ GuardsUnit` at this point is `ZT5G.closedPt_instAtWD`.)
What does NOT transfer from the r4 closed points: every r4 point was at `k = 0` (`closed_point_gen`, `closed_point_M3`, `proper_tower_point2`); `k = 0` is outside
the printed range.  These points are an INSTANCE (one tower, `Λ = torus`, `U = 1`), not `CoercG8At` itself, and not a proper `Λ`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- the full tower of height `k` is admissible for ANY `(ell, M)` whose big blocks tile the torus (needs `1 ≤ k`: the collar law). -/
theorem SkG_admissible {L : PeriodicLatticeExtent} (ell M R k : ℕ) (hk1 : 1 ≤ k)
    (hdiv : ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, M * ell ^ j ∣ L μ + 1) :
    Admissible ell M R k (Sk L k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h : j ≤ k
    · simp [Sk, h]
    · have h2 : ¬ j + 1 ≤ k := by omega
      simp [Sk, h2] at hx
  · intro j hj
    have : ¬ j ≤ k := by omega
    simp [Sk, this]
  · intro j hj μ
    exact hdiv j hj μ
  · intro j hj x _ y _
    simp [Sk, hj]
  · intro j hj x hx
    simp [Sk, hj] at hx
  · intro x
    simp only [Sk, Nat.zero_le, if_true, Set.mem_univ, true_iff]
    refine ⟨x, ?_, x, fun μ => rfl, ?_⟩
    · simp [hk1]
    · rw [pdist_self]; exact Nat.zero_le _

theorem SkG_lambdaOK {Lu Lf : PeriodicLatticeExtent} (ell M R k : ℕ)
    (hf : ∀ μ, Lf μ + 1 = (Lu μ + 1) * ell ^ k) (hell : 0 < ell) :
    LambdaOK (Lu := Lu) (Lf := Lf) ell M R k (Sk Lf k) Set.univ := by
  have hemb : ∀ (y : PeriodicLatticeSite Lu) (μ : Fin 3), ell ^ k * (y μ).val < Lf μ + 1 := by
    intro y μ
    rw [hf μ, mul_comm]
    exact Nat.mul_lt_mul_of_pos_right (y μ).isLt (pow_pos hell k)
  refine ⟨?_, fun y μ => ⟨ell ^ k * (y μ).val, hemb y μ⟩, ?_, ?_, ?_⟩
  · intro x _ y _; exact Set.mem_univ y
  · intro y μ; rfl
  · intro y _; simp [Sk]
  · intro y _ y' hy'
    simp [Sk] at hy'

theorem SkG_coversc {L : PeriodicLatticeExtent} (ell M k c : ℕ) (hell : 0 < ell) (hM : 0 < M) (hc : 0 < c)
    (hle : ∀ μ : Fin 3, L μ + 1 ≤ c * (M * ell ^ k)) :
    CoversOm0c ell M c k (Sk L k) := by
  intro x _
  have hsz : 0 < c * bigSide M ell k := by
    simp only [bigSide]; exact Nat.mul_pos hc (Nat.mul_pos hM (pow_pos hell k))
  have hB : ∀ i, i < k → towerBj (Sk L k) i = ∅ := by
    intro i hi
    have h1 : i ≤ k := by omega
    have h2 : i + 1 ≤ k := by omega
    ext y
    simp [towerBj, Sk, h1, h2]
  have hBk : towerBj (Sk L k) k = Set.univ := by
    ext y
    simp [towerBj, Sk]
  have hnon : (siteBox (L := L) (fun μ => ⟨0, Nat.succ_pos _⟩) (c * bigSide M ell k)
      ∩ towerBj (Sk L k) k).Nonempty := by
    refine ⟨fun μ => ⟨0, Nat.succ_pos _⟩, ?_, by rw [hBk]; exact Set.mem_univ _⟩
    intro μ
    simpa using hsz
  refine ⟨siteBox (fun μ => ⟨0, Nat.succ_pos _⟩) (c * bigSide M ell k), k,
    ⟨⟨le_refl k, ⟨_, ?_, rfl⟩, ?_, hnon⟩, ?_⟩, ?_⟩
  · intro μ; simp
  · intro y _; left; rw [hBk]; exact Set.mem_univ _
  · intro i hi
    by_contra hne
    have hlt : i < k := lt_of_le_of_ne hi.1 hne
    obtain ⟨y, _, hy⟩ := hi.2.2.2
    rw [hB i hlt] at hy
    exact hy
  · intro μ
    have h1 := (x μ).isLt
    have h2 := hle μ
    have : ((x μ).val + (L μ + 1) - 0) % (L μ + 1) = (x μ).val := by
      rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt h1]
    simp only [bigSide, this]
    exact lt_of_lt_of_le h1 h2

/-- `Λ = univ` is a sum of `ell`-blocks -/
theorem lamBlockSum_univ {Lu : PeriodicLatticeExtent} (ell : ℕ) (hell : 0 < ell) :
    LamBlockSum ell (Set.univ : Set (PeriodicLatticeSite Lu)) := by
  intro x _
  have hq := hell
  let y : PeriodicLatticeSite Lu := fun μ => ⟨(x μ).val - (x μ).val % ell,
    lt_of_le_of_lt (Nat.sub_le _ _) (x μ).isLt⟩
  have hy : ∀ μ, (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + ell ∧ ell ∣ (y μ).val := by
    intro μ
    exact AdalyFormal.IngredientFamilyR2.sub_mod_facts (x μ).val ell hq
  refine ⟨y, ⟨?_, fun _ _ => Set.mem_univ _⟩, ?_⟩
  · rw [mem_CoarseLattice]
    intro μ
    exact Nat.mod_eq_zero_of_dvd (hy μ).2.2
  · rw [mem_blockOf]
    intro μ
    exact ⟨(hy μ).1, (hy μ).2.1⟩

theorem flat_perCubeRegular2cG (ell M c k : ℕ) (hell : 1 ≤ ell) (hM : 1 ≤ M) (hc : 10 ≤ c) {α₀ : ℝ} (hα : 0 < α₀)
    {L : PeriodicLatticeExtent} (S : Tower L) :
    PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ (flatCfg : LinkCfg L) := by
  have h := ufield_perCubeRegular2 (L := L) (ell := ell) (M := M) (f := c) (k := k) hell hM hc S hα
    (fun _ => 0) (fun e => by simp; positivity)
  have hU : Ufield ((ell : ℝ) ^ k)⁻¹ (fun _ : Bond L => (0 : ℝ)) = (flatCfg : LinkCfg L) := by
    funext e
    simp [Ufield, flatCfg, Ug_zero]
  rw [hU] at h
  exact h

/-- the closed-point unit torus: `Lu μ + 1 = 10 · M` -/
def LuM (M : ℕ) : PeriodicLatticeExtent := fun _ => 10 * M - 1

theorem LuM_succ {M : ℕ} (hM : 0 < M) (μ : Fin 3) : LuM M μ + 1 = 10 * M := by
  simp only [LuM]; omega

/-- **THE CLOSED POINT AT `k ≥ 1`, `M = 2^m`: every hypothesis of the r5 inner claim holds, and `WellDef` too.** -/
theorem closedPt_hyps (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : 1 ≤ k) (R : ℕ) (a : ℝ) (ha : 0 < a) {α₀ : ℝ} (hα : 0 < α₀) :
    let M := 2 ^ m
    let Lu := LuM M
    TorusOK 2 M Lu ∧
    Admissible 2 M R k (fullTower 2 k Lu) ∧
    CoversOm0p 2 M 12 k (fullTower 2 k Lu) ∧
    LambdaOK2 (Lu := Lu) (Lf := scaleUp 2 k Lu) 2 M R k (fullTower 2 k Lu) Set.univ ∧
    PerCubeRegular2 2 M 12 k (fullTower 2 k Lu) α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹ (flatCfg : LinkCfg (scaleUp 2 k Lu)) ∧
    GenP.WellDef (gparams 2 k Lu (by norm_num) (fullTower 2 k Lu) flatCfg a Set.univ) ∧
    ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Set.univ 2 Bt ∧ OnLambdaT Set.univ Bt ∧
      OnLambda Set.univ Bt ∧ 0 < bondEnergy Bt := by
  intro M Lu
  have hMpos : 0 < M := pow_pos (by norm_num) m
  have hM2 : 2 ∣ M := dvd_pow_self 2 (by omega)
  have hM4 : 2 ≤ M := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hLu : ∀ μ, Lu μ + 1 = 10 * M := LuM_succ hMpos
  have hf : ∀ μ, scaleUp 2 k Lu μ + 1 = (Lu μ + 1) * 2 ^ k := by
    intro μ
    have : 0 < (Lu μ + 1) * 2 ^ k := Nat.mul_pos (Nat.succ_pos _) (pow_pos (by norm_num) k)
    simp only [scaleUp]
    omega
  have hdiv : ∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, M * 2 ^ j ∣ scaleUp 2 k Lu μ + 1 := by
    intro j hj μ
    rw [hf μ, hLu μ]
    exact ⟨10 * 2 ^ (k - j), by
      have : (2 : ℕ) ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← pow_add]; congr 1; omega
      rw [this]; ring⟩
  have hdvd : ∀ μ : Fin 3, 2 ∣ Lu μ + 1 := by
    intro μ; rw [hLu μ]; exact Dvd.dvd.mul_left hM2 10
  have hL4 : ∀ μ : Fin 3, 4 ≤ Lu μ := by
    intro μ; have := hLu μ; omega
  have hN : ∀ μ : Fin 3, 1 ≤ Lu μ := fun μ => by have := hL4 μ; omega
  have hT : TorusOK 2 M Lu := by
    refine ⟨fun μ => hdvd μ, fun μ => ?_, fun μ => ?_⟩
    · rw [hLu μ]; omega
    · rw [hLu μ]; exact Dvd.intro_left 10 rfl
  obtain ⟨Bt, hBt, hpos⟩ :=
    AdalyFormal.Balaban.CoercUMainDesigned.lambdaTilde_nonvacuous (L := Lu) (ell := 2) (by norm_num) hdvd
  have hle : ∀ μ : Fin 3, scaleUp 2 k Lu μ + 1 ≤ 12 * (M * 2 ^ k) := by
    intro μ
    rw [hf μ, hLu μ]
    have : 10 * M * 2 ^ k ≤ 12 * (M * 2 ^ k) := by nlinarith [Nat.zero_le (M * 2 ^ k)]
    exact this
  refine ⟨hT, SkG_admissible 2 M R k hk hdiv, SkG_coversp 2 M k 12 (by norm_num) hMpos (by norm_num) hle,
    ⟨SkG_lambdaOK 2 M R k hf (by norm_num), lamBlockSum_univ 2 (by norm_num)⟩, ?_,
    AdalyFormal.GenuineU1.PK_wellDef 2 k Lu (by norm_num) a Set.univ hN hdvd ha, Bt,
    (onLambdaTildeIn_univ 2 Bt).mpr hBt, ?_, ?_, hpos⟩
  · exact flat_perCubeRegular2cG 2 M 12 k (by norm_num) hMpos (by norm_num) hα _
  · intro b hb; exact absurd (Or.inl (Set.mem_univ _)) hb
  · intro b hb; exact absurd ⟨Set.mem_univ _, Set.mem_univ _⟩ hb

/-- the CONCLUSION at the closed point, with `γ₀ = 1/1728` (independent of `k`, `m`, `a`), together with `WellDef` (hb, hG, hN).
NOT claimed here: `GuardsUnit` (the three `Ring.inverse` units of `WellDefG`); it is proved in `ZT5G.PK_guardsUnit` and `ZT5G.closedPt_instAtWD` gives the `WellDefG` form. -/
theorem closedPt_ineq (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (a : ℝ) (ha : 0 < a) :
    GenP.WellDef (gparams 2 k (LuM (2 ^ m)) (by norm_num) (fullTower 2 k (LuM (2 ^ m))) flatCfg a Set.univ) ∧
    InstIneq 2 k (by norm_num) a (LuM (2 ^ m)) (1 / 1728) (fullTower 2 k (LuM (2 ^ m))) Set.univ flatCfg := by
  have hMpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hLu : ∀ μ, LuM (2 ^ m) μ + 1 = 10 * 2 ^ m := LuM_succ hMpos
  have hM2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hM4 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hL4 : ∀ μ : Fin 3, 4 ≤ LuM (2 ^ m) μ := by
    intro μ; have := hLu μ; omega
  have hd : ∀ μ, 2 ∣ LuM (2 ^ m) μ + 1 := by
    intro μ; rw [hLu μ]; exact Dvd.dvd.mul_left hM2 10
  obtain ⟨hW, hI⟩ := AdalyFormal.GenuineU1.closed_point_all_k k (LuM (2 ^ m)) hL4 hd a ha
  exact ⟨hW, fun Bt h1 h2 => hI Bt h1 h2⟩

/-- **the statement CONSUMED at the closed point**: if the inner claim holds at `(2, 2^m, R, k)` over the closed-point torus, then `InstIneq` holds there
for the constants of the claim (all five hypotheses of `CoercG8At` are supplied by `closedPt_hyps`). -/
theorem closedPt_consumes (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : 1 ≤ k) (R : ℕ) (a : ℝ) (ha : 0 < a)
    {α₀ γ₀ : ℝ} (hα : 0 < α₀)
    (h : CoercG8At 2 (2 ^ m) R k (by norm_num) a (LuM (2 ^ m)) 12 α₀ γ₀) :
    InstIneq 2 k (by norm_num) a (LuM (2 ^ m)) γ₀ (fullTower 2 k (LuM (2 ^ m))) Set.univ flatCfg ∧
      ∀ p ∈ plaqIn ((fullTower 2 k (LuM (2 ^ m))).Om 0),
        PlaqGaugeAt 2 (2 ^ m) 12 α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹ (flatCfg : LinkCfg (scaleUp 2 k (LuM (2 ^ m)))) p := by
  obtain ⟨hT, hA, hC, hL, hU, -, -⟩ := closedPt_hyps m hm k hk R a ha hα
  exact h.apply_gauge hT hA hL ⟨hC, hU⟩

/-- **the HEADLINE constants block consumed at the closed point**: if `P428Core8 2 (2^m) R ..` holds, then for every `k ≥ 1` there is `γ₀ > 0` with
`InstIneq` at the closed point (all hypotheses supplied by `closedPt_hyps`; the smallness threshold `a₀/(12 M)` is used). -/
theorem closedPt_headline (m : ℕ) (hm : 1 ≤ m) (R : ℕ) (a : ℝ) (ha : 0 < a)
    (h : P428Core8 2 (2 ^ m) R (by norm_num) a) (k : ℕ) (hk : 1 ≤ k) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ InstIneq 2 k (by norm_num) a (LuM (2 ^ m)) γ₀ (fullTower 2 k (LuM (2 ^ m))) Set.univ flatCfg := by
  obtain ⟨a₀, ha₀, γ₀, hγ, hall⟩ := h
  have hMpos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
  have hα : 0 < a₀ / (12 * ((2 ^ m : ℕ) : ℝ)) := by positivity
  refine ⟨γ₀, hγ, (closedPt_consumes m hm k hk R a ha hα (hall k hk (LuM (2 ^ m)) _ hα ?_)).1⟩
  have : (12 : ℝ) * ((2 ^ m : ℕ) : ℝ) * (a₀ / (12 * ((2 ^ m : ℕ) : ℝ))) = a₀ := by
    field_simp
  exact le_of_eq this

/-- the fixed-factor class is restrictive at the closed-point tower -/
theorem closedPt_class_excludes_some_U (m : ℕ) (hm : 1 ≤ m) (k : ℕ) {α₀ : ℝ} (hα : 0 < α₀)
    (hsmall : (12 : ℝ) * (((2 ^ m : ℕ)) : ℝ) * α₀ ≤ 1 / 2) :
    ∃ U : LinkCfg (scaleUp 2 k (LuM (2 ^ m))),
      ¬ PerCubeRegular2 2 (2 ^ m) 12 k (fullTower 2 k (LuM (2 ^ m))) α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹ U := by
  have hMpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hLu : ∀ μ, LuM (2 ^ m) μ + 1 = 10 * 2 ^ m := LuM_succ hMpos
  have hM2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hf : ∀ μ, scaleUp 2 k (LuM (2 ^ m)) μ + 1 = (LuM (2 ^ m) μ + 1) * 2 ^ k := by
    intro μ
    have : 0 < (LuM (2 ^ m) μ + 1) * 2 ^ k := Nat.mul_pos (Nat.succ_pos _) (pow_pos (by norm_num) k)
    simp only [scaleUp]
    omega
  have hN : ∀ μ, 1 ≤ scaleUp 2 k (LuM (2 ^ m)) μ := by
    intro μ
    have e : scaleUp 2 k (LuM (2 ^ m)) μ + 1 = 10 * (2 ^ m * 2 ^ k) := by rw [hf μ, hLu μ]; ring
    have h3 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hP : 2 ≤ 2 ^ m * 2 ^ k := by nlinarith
    omega
  have hle : ∀ μ : Fin 3, scaleUp 2 k (LuM (2 ^ m)) μ + 1 ≤ 12 * (2 ^ m * 2 ^ k) := by
    intro μ
    rw [hf μ, hLu μ]
    nlinarith [Nat.zero_le (2 ^ m * 2 ^ k)]
  have hne : ((fullTower 2 k (LuM (2 ^ m))).Om 0).Nonempty :=
    ⟨fun μ => ⟨0, Nat.succ_pos _⟩, by simp [fullTower]⟩
  exact coveredc_class_excludes_some_U hN (by norm_num) hMpos (by norm_num) (fullTower 2 k (LuM (2 ^ m)))
    (SkG_coversc 2 (2 ^ m) k 12 (by norm_num) hMpos (by norm_num) hle) hne (by positivity) hα hsmall

#print axioms SkG_admissible
#print axioms SkG_lambdaOK
#print axioms SkG_coversc
#print axioms lamBlockSum_univ
#print axioms flat_perCubeRegular2cG
#print axioms closedPt_hyps
#print axioms closedPt_ineq
#print axioms closedPt_consumes
#print axioms closedPt_headline
#print axioms closedPt_class_excludes_some_U

end AdalyFormal.StatementLaneG
