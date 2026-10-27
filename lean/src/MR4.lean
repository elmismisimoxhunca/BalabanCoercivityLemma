import MR3

/-!
# MR4 -- `PatchCoercive` for the PRINTED PER-CUBE CLASS, with the interface charts as the one named input
(m2_route, 2026-10-14)

G3 patches at `κ = 1`, `c = 5` (the values `m1_assembly` uses, MA19).

* `InterfaceCharts ell M k d S U η a'` : `ChartOn … a' (j-1) w (chartRad ell M 1 5 d j (j-1))` at every INTERFACE patch:
  `IsPatch … j w`, `1 ≤ j`, `Ball w (6 G_j)` misses `Ω_{j+1}` (NP12's down case), and the centred box of side `12 M ell^j`
  is NOT inside `Ω_j` (`¬ CentredIn`).  These are exactly the patches no single class cube serves (M2B2/M2B3).
* `patchCharts_class` : `PerCubeRegular2 ell M 12 k S α₀ η U` + `InterfaceCharts … a'` (`12 M α₀ ≤ a'`) ⇒ `PatchCharts … a'`
  (up-case patches: `centredIn_of_up`; centred down-case patches: `chart_of_centredIn` at level `j-1`).
* **`patchCoercive_class_exists`** : NP12's constants `cW`, `a₀`, `D` (depending on `ell`, `a` only); for every admissible
  tower with `24 ≤ R`, `36 ≤ R ell`, `9 ell ≤ R`, `17 ell ≤ R M`, `D ≤ d`, `d + 64 ell² + 2 ≤ M`, every `U` with
  `PerCubeRegular2 ell M 12 k S α₀ η U` (`0 < α₀`, `0 < η`) and `InterfaceCharts … η a'` for some `a'` with
  `12 M α₀ ≤ a' ≤ a₀` (the interface constant may exceed the cube constant), and
  lane E's sandwich data: `PatchCoercive ell M k 1 5 … U a Lam ((1 − etaC)·min a (cW − epsNF …) − 2 nuC)`.
* `interfaceCharts_of_M1`, `classHyps_of_M1` : lane B's `M1Regular` gives both class hypotheses (consistency: the M1
  regime is a special case, so the hypothesis set is satisfiable wherever M1's is).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Route

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_shift_le pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M1 (IsPatch gsp M1Regular)
open AdalyFormal.M1W2 (caseB_down)
open AdalyFormal.M1IMS (HatPack HolRegime etaC nuC PatchCoercive)
open AdalyFormal.M1NonFlat (epsNF PkA thetaN)

variable {L : PeriodicLatticeExtent}

/-- **the remaining per-patch input**: a level-`(j-1)` chart at every interface patch. -/
def InterfaceCharts (ell M k d : ℕ) (S : Tower L) (U : Cfg L) (η a' : ℝ) : Prop :=
  ∀ (j : ℕ) (w : PeriodicLatticeSite L), IsPatch ell M k 1 S j w → 1 ≤ j →
    (¬ ∃ y ∈ Ball w ((5 + 1) * gsp ell M 1 j), y ∈ S.Om (j + 1)) → ¬ CentredIn S ell M j w →
    ChartOn ell U η a' (j - 1) w (chartRad ell M 1 5 d j (j - 1))

/-- a chart at constant `a'` is a chart at every larger constant. -/
theorem ChartOn.mono_const {ell : ℕ} {U : Cfg L} {η a' b' : ℝ} (hη : 0 < η) (hab : a' ≤ b') {i : ℕ} {w : PeriodicLatticeSite L}
    {r : ℕ} (h : ChartOn ell U η a' i w r) : ChartOn ell U η b' i w r := by
  obtain ⟨g, A, hHT, hUA, h1, h2⟩ := h
  refine ⟨g, A, hHT, hUA, fun e he => (h1 e he).trans_le ?_, fun μ ν x hx hx' => (h2 μ ν x hx hx').trans_le ?_⟩
  · exact mul_le_mul_of_nonneg_right hab (by positivity)
  · exact mul_le_mul_of_nonneg_right hab (by positivity)

theorem patchCharts_class {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 0 < M)
    (hell : 1 ≤ ell) (hR : 24 ≤ R) (hRl : 3 * 12 ≤ R * ell) {d : ℕ} (hdM : d + 64 * ell ^ 2 + 2 ≤ M)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2 ell M 12 k S α₀ η U)
    {a' : ℝ} (ha' : ((12 : ℕ) : ℝ) * M * α₀ ≤ a')
    (hI : InterfaceCharts ell M k d S U η a') :
    PatchCharts ell M k 1 5 d S U η a' := by
  intro j w hp
  refine ⟨fun hB => ?_, fun hj hB => ?_⟩
  · exact (chart_of_centredIn hS hM hell hRl hdM hη hα hP hp (centredIn_of_up hS hR hp.1 hB) le_rfl).mono_const hη ha'
  · by_cases hc : CentredIn S ell M j w
    · exact (chart_of_centredIn hS hM hell hRl hdM hη hα hP hp hc (by omega)).mono_const hη ha'
    · exact hI j w hp hj hB hc

/-- **`PatchCoercive` for the printed per-cube class** (interface charts named). -/
theorem patchCoercive_class_exists {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (_hS : Admissible ell M R k S) (_hM : 0 < M) (_hR1 : 1 ≤ R)
      (_hR24 : 24 ≤ R) (_hRl : 3 * 12 ≤ R * ell)
      (_hR4 : (5 + 4) * 1 * ell ≤ R) (_hroom : 17 * ell ≤ R * M) {d : ℕ} (_hdD : D ≤ d)
      (_hdM : d + 64 * ell ^ 2 + 2 ≤ M)
      {W : ℕ} (_hW : 1 ≤ W) (_hWR : W ≤ R * M * ell)
      (U : LinkCfg (scaleUp ell k Lu)) (cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
      (_hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
      (ρ : ℝ) (_hρ : 0 ≤ ρ) (_hreg : HolRegime S ell k U ρ) (ε1 : ℝ) (_hε1 : 0 < ε1) (_hη : etaC ell W cs ρ ε1 < 1)
      (η : ℝ) (_hη0 : 0 < η) (α₀ : ℝ) (_hα0 : 0 < α₀)
      (_hP : PerCubeRegular2 ell M 12 k S α₀ η U)
      (a' : ℝ) (_ha'1 : ((12 : ℕ) : ℝ) * M * α₀ ≤ a') (_ha'a : a' ≤ a₀)
      (_hI : InterfaceCharts ell M k d S U η a'),
      PatchCoercive ell M k 1 5 Lu hell0 S U a Lam
        ((1 - etaC ell W cs ρ ε1) * min a (cW - epsNF ell (PkA a) (thetaN ell) d) - 2 * nuC ell ρ) := by
  obtain ⟨cW, hcW, a₀, ha₀, D, hD, hDle, hmain⟩ := patchCoercive_charts_exists hell ha
  refine ⟨cW, hcW, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k Lu hell0 S hS hM hR1 hR24 hRl hR4 hroom d hdD hdM W hW hWR U cs Lam hp ρ hρ hreg ε1 hε1 hη η hη0 α₀
    hα0 hP a' ha'1 ha'a hI
  have hdM' : d + 64 * ell ^ 2 ≤ 1 * M := by omega
  have ha'0 : (0 : ℝ) < a' := by
    have : (0 : ℝ) < ((12 : ℕ) : ℝ) * M * α₀ := by
      have : (0 : ℝ) < M := by exact_mod_cast hM
      positivity
    linarith
  exact hmain hell0 hS one_pos hM hR1 hR4 hroom hdD hdM' hW hWR U cs Lam hp ρ hρ hreg ε1 hε1 hη η hη0 a' ha'0 ha'a
    (patchCharts_class hS hM (by omega) hR24 hRl hdM hη0 hα0.le hP ha'1 hI)

/-- lane B's global regime gives the interface charts (the M1 regime is a special case of the hypothesis). -/
theorem interfaceCharts_of_M1 {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 0 < M)
    (hell : 2 ≤ ell) (hR4 : (5 + 4) * 1 * ell ≤ R) {d : ℕ} (hdM : d + 64 * ell ^ 2 + 2 ≤ M)
    {α₀ η : ℝ} {U : LinkCfg L} (h : M1Regular ell M 12 k S α₀ η U) :
    InterfaceCharts ell M k d S U η ((12 : ℕ) * M * α₀) := by
  intro j w hp hj _hB _hc
  obtain ⟨g, A, hU, hHT, h1, h2, -⟩ := h
  have hZi := caseB_down hS hell one_pos hM hR4 hp hj
  have hjk : j - 1 ≤ k := by have := hp.1; omega
  have hin : ∀ y : PeriodicLatticeSite L, pdist w y ≤ chartRad ell M 1 5 d j (j - 1) + 1 → y ∈ S.Om (j - 1) := by
    intro y hy
    apply hZi
    show pdist w y ≤ (5 + 1) * gsp ell M 1 j
    have hpi : ell ^ (j - 1) ≤ ell ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    have hroom : (d + 64 * ell ^ 2 + 2) * ell ^ j ≤ M * ell ^ j := Nat.mul_le_mul_right _ hdM
    have hpj : 1 ≤ ell ^ j := Nat.one_le_pow _ _ (by omega)
    have hy' : pdist w y ≤ 5 * gsp ell M 1 j + d * ell ^ (j - 1) + 64 * ell ^ (j - 1 + 2) + 1 := hy
    rw [gsp_one] at hy' ⊢
    have e2 : ell ^ (j - 1 + 2) = ell ^ 2 * ell ^ (j - 1) := by ring
    rw [e2] at hy'
    have h1' : d * ell ^ (j - 1) ≤ d * ell ^ j := Nat.mul_le_mul_left _ hpi
    have h2' : 64 * (ell ^ 2 * ell ^ (j - 1)) ≤ 64 * ell ^ 2 * ell ^ j := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hpi
    have hbs : bigSide M ell j = M * ell ^ j := rfl
    rw [hbs]
    nlinarith
  have hbst : ∀ e : Bond L, pdist w e.1 ≤ chartRad ell M 1 5 d j (j - 1) →
      j - 1 ≤ AdalyFormal.M1.bstrat S k e := by
    intro e he
    refine AdalyFormal.M1.le_bstrat_of_mem hjk e (hin e.1 (by omega)) (hin _ ?_)
    have := pdist_triangle w e.1 (periodicLatticeShift e.1 e.2)
    have := pdist_shift_le e.1 e.2
    omega
  refine ⟨g, A, hHT, fun e _ => hU e, fun e he => ?_, fun μ ν x hx hx' => ?_⟩
  · exact h1 e (j - 1) (hbst e he)
  · exact h2 μ ν x (j - 1) (hbst (x, ν) hx) (hbst (periodicLatticeShift x μ, ν) hx')

/-- consistency: lane B's `M1Regular` implies both hypotheses of `patchCoercive_class_exists`. -/
theorem classHyps_of_M1 {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 0 < M)
    (hell : 2 ≤ ell) (hR4 : (5 + 4) * 1 * ell ≤ R) {d : ℕ} (hdM : d + 64 * ell ^ 2 + 2 ≤ M)
    {α₀ η : ℝ} {U : LinkCfg L} (h : M1Regular ell M 12 k S α₀ η U) :
    PerCubeRegular2 ell M 12 k S α₀ η U ∧ InterfaceCharts ell M k d S U η ((12 : ℕ) * M * α₀) :=
  ⟨AdalyFormal.M1.perCube_of_M1 hS h, interfaceCharts_of_M1 hS hM hell hR4 hdM h⟩

end AdalyFormal.M2Route

#print axioms AdalyFormal.M2Route.InterfaceCharts
#print axioms AdalyFormal.M2Route.ChartOn.mono_const
#print axioms AdalyFormal.M2Route.patchCharts_class
#print axioms AdalyFormal.M2Route.patchCoercive_class_exists
#print axioms AdalyFormal.M2Route.interfaceCharts_of_M1
#print axioms AdalyFormal.M2Route.classHyps_of_M1
