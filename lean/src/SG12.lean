import SG11

/-!
# SG12 -- good towers: where the charts come from (lane m2_fields123_20261015)

* `GoodTower ell M k S` : every anchor `y ∈ Λ_j` (`j ≥ 1`) has its `16 ℓ^j`-ball in the core of a class cube (`PlacedAt`).  THIS is the residual of F1/F2/F3 in this lane:
  anchors for which no class cube contains the ball with margin need a gauge glued from several cube gauges (the F4 obstruction).
* `NoBand ell M k S` (sufficient): every anchor is `DeepAt` (the `7 M ℓ^j`-box lies in `Ω_j`) or `ShallowAt (j-1)` (a point outside `Ω_j` within `5 M ℓ^{j-1}`).
  `good_of_noBand` : `NoBand ⇒ GoodTower` (needs `R ≥ 26`, `M ≥ 4ℓ + 30`).
* `blockCharts`, `rowCharts` : a good tower plus the printed class `PerCubeRegular2` gives the per-block (radius `7 ℓ^j` at `y_q`) and per-row (radius `rhoT ell j` at `b.1`) charts.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M2F123

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (PerCubeRegular2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT)
open AdalyFormal.IngredientFamilyR2 (geomOf BIdx bondsLam)
open AdalyFormal.M1Site (QIdx yq jq yq_mem jq_le)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

theorem AnchorChart.mono {L : PeriodicLatticeExtent} {ell M k : ℕ} {S : Tower L} {U : LinkCfg L} {α₀ η : ℝ}
    {x : PeriodicLatticeSite L} {r : ℕ} (h : AnchorChart ell M k S U α₀ η x r) (x' : PeriodicLatticeSite L) (r' : ℕ)
    (hsub : Ball x' r' ⊆ Ball x r) : AnchorChart ell M k S U α₀ η x' r' := by
  obtain ⟨g, V, hV, hag⟩ := h
  exact ⟨g, V, hV, hag.mono hsub⟩

/-- every anchor of level `≥ 1` has its `16 ℓ^j`-ball placed in a class cube -/
def GoodTower {L : PeriodicLatticeExtent} (ell M k : ℕ) (S : Tower L) : Prop :=
  ∀ j, 1 ≤ j → j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, PlacedAt ell M k S y (16 * ell ^ j)

/-- sufficient geometric condition: every anchor is deep or shallow -/
def NoBand {L : PeriodicLatticeExtent} (ell M k : ℕ) (S : Tower L) : Prop :=
  ∀ j, 1 ≤ j → j ≤ k → ∀ y ∈ (geomOf ell k S).Lam j, DeepAt ell M S j y ∨ ShallowAt ell M S (j - 1) y

theorem good_of_noBand {L : PeriodicLatticeExtent} {ell M R k : ℕ} (hell : 2 ≤ ell) (hM : 4 * ell + 30 ≤ M)
    {S : Tower L} (hS : Admissible ell M R k S) (hR : 26 ≤ R) (hnb : NoBand ell M k S) : GoodTower ell M k S := by
  intro j hj1 hjk y hy
  have hM0 : 0 < M := by omega
  have hell0 : 0 < ell := by omega
  obtain ⟨hdv, hyO, hyO1⟩ := hy
  rcases hnb j hj1 hjk y ⟨hdv, hyO, hyO1⟩ with hd | hsh
  · have hn : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell0
    refine placed_deep hell hM0 hS hR hjk y hyO1 hd (16 * ell ^ j) ?_
    nlinarith
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hn : 1 ≤ ell ^ i := Nat.one_le_pow _ _ hell0
    have e : 16 * ell ^ (i + 1) = 16 * ell * ell ^ i := by ring
    simp only [Nat.add_sub_cancel] at hsh
    refine (e ▸ placed_shallow hell hM0 hS hR hjk y hyO hsh (16 * ell ^ (i + 1)) ?_)
    rw [e]
    nlinarith

section charts
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

theorem blockCharts (hell : 2 ≤ ell) (hM : 0 < M) (hS : Admissible ell M R k S) (hgood : GoodTower ell M k S)
    (hL : ∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ) {α₀ η : ℝ} (hα : 0 < α₀) (hη : 0 < η) {U : LinkCfg (scaleUp ell k Lu)}
    (hP : PerCubeRegular2 ell M 12 k S α₀ η U) :
    ∀ q : QIdx (geomOf ell k S), 1 ≤ jq q → AnchorChart ell M k S U α₀ η (yq q) (7 * ell ^ jq q) := by
  intro q hq
  have hell0 : 0 < ell := by omega
  have hpl := hgood (jq q) hq (jq_le q) (yq q) (yq_mem q)
  have hc := chart_of_placed hell0 hM hS (yq q) _ hpl hL hα hη hP
  refine AnchorChart.mono hc (yq q) _ ?_
  intro z hz
  have : pdist (yq q) z ≤ 7 * ell ^ jq q := hz
  show pdist (yq q) z ≤ 16 * ell ^ jq q
  omega

theorem rowCharts (hell : 2 ≤ ell) (hM : 0 < M) (hS : Admissible ell M R k S) (hgood : GoodTower ell M k S)
    (hL : ∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ) {α₀ η : ℝ} (hα : 0 < α₀) (hη : 0 < η) {U : LinkCfg (scaleUp ell k Lu)}
    (hP : PerCubeRegular2 ell M 12 k S α₀ η U) :
    ∀ p : BIdx (geomOf ell k S), 1 ≤ (p.1 : ℕ) → AnchorChart ell M k S U α₀ η p.2.1.1 (rhoT ell p.1) := by
  intro p hp
  have hell0 : 0 < ell := by omega
  have hjk : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have h8 := rhoT_le_eight ell hell p.1
  obtain ⟨⟨hb, -⟩⟩ : Nonempty (_ ∧ _) := ⟨p.2.2⟩
  rcases hb with hb | hb
  · have hpl := hgood p.1 hp hjk p.2.1.1 hb
    have hc := chart_of_placed hell0 hM hS p.2.1.1 _ hpl hL hα hη hP
    refine AnchorChart.mono hc _ _ ?_
    intro z hz
    have : pdist p.2.1.1 z ≤ rhoT ell p.1 := hz
    show pdist p.2.1.1 z ≤ 16 * ell ^ (p.1 : ℕ)
    omega
  · have hpl := hgood p.1 hp hjk _ hb
    have hc := chart_of_placed hell0 hM hS _ _ hpl hL hα hη hP
    refine AnchorChart.mono hc _ _ ?_
    intro z hz
    have h1 : pdist p.2.1.1 z ≤ rhoT ell p.1 := hz
    have h2 := AdalyFormal.StatementLaneR8.pdist_coarseShift_le p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2
    have h3 := AdalyFormal.StatementLaneR8.pdist_comm (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) p.2.1.1
    have h4 := AdalyFormal.StatementLaneR8.pdist_triangle (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) p.2.1.1 z
    show pdist (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) z ≤ 16 * ell ^ (p.1 : ℕ)
    omega

end charts

end AdalyFormal.M2F123

#print axioms AdalyFormal.M2F123.AnchorChart.mono
#print axioms AdalyFormal.M2F123.good_of_noBand
#print axioms AdalyFormal.M2F123.blockCharts
#print axioms AdalyFormal.M2F123.rowCharts
