import OG14
import PP10

/-!
# OG8 -- F1-F3 from `BallChartsAt` (lane m2_onegap_20261015)

`FieldsKAt` / `FieldsK` : the SK1 fields F1-F4 with the chart constant `K·α₀` in place of `α₀` in every CONCLUSION (the class hypothesis stays at `α₀`);
`K = ℓ³·C` where `C` is the `BallCharts` constant.
`blockCharts_ball`, `rowCharts_ball` : anchor charts at every constraint block / row of level `≥ 1` from `BallChartsAt`.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.OneGap

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (gparams LambdaOK2)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.IngredientFamilyR2 (geomOf BIdx bondsLam)
open AdalyFormal.M1Site AdalyFormal.M1IMS
open AdalyFormal.TowerLoc (rho1 SstarM CMcStar)
open AdalyFormal.M2Skel (SiteS1 RowBound alpha1)
open AdalyFormal.OneGap12 (AnchorChart12)

/-- the F1-F4 content of the K-shifted fields at one configuration -/
def FieldsKAt (ell : ℕ) (hell : 0 < ell) (a : ℝ) (df M R k : ℕ) (Lu : PeriodicLatticeExtent) (K : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) : Prop :=
  AdalyFormal.M2Skel.SiteS1 ell k S U a (csOf a (AdalyFormal.M1GaugeW4.rhoT ell 12 M (alpha1 ell (K * α₀)))) ∧
  AdalyFormal.M2Skel.RowBound ell k S U a (gamC ell a (AdalyFormal.M1GaugeW4.rhoT ell 12 M (alpha1 ell (K * α₀)))
    (AdalyFormal.M1GaugeW4.epsXnum ell (R * M * ell) a (AdalyFormal.M1GaugeW4.rhoT ell 12 M (alpha1 ell (K * α₀))))) ∧
  MassComm ell M k 1 5 S U a (CMcStar ell M 1 5 a (SstarM ell 12 M (alpha1 ell (K * α₀)))) ∧
  (∀ d : ℕ, df ≤ d → d + 64 * ell ^ 2 + 2 ≤ M →
    AdalyFormal.M2Route.InterfaceCharts ell M k d S U ((ell : ℝ) ^ k)⁻¹ (((12 : ℕ) : ℝ) * M * (K * α₀))) ∧
  (ExitFree ell k Lu S → Function.Injective (gparams ell k Lu hell S U a Lam).data.Qs)

/-- the K-shifted F1-F4: one constant `K ≥ 1` for all four, chosen after `(ℓ, a, m, R)`, before `k, Lu, α₀, S, Λ, U` -/
def FieldsK (ell : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ df m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∃ K : ℝ, 1 ≤ K ∧ ∃ s : ℝ, 0 < s ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s →
    TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    (∀ σ : Fin 3, 13 * (ell ^ m) ≤ Lu σ + 1) →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam → Lam.Nonempty →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ e : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell k Lu),
      ¬ AdalyFormal.StatementLaneR8.ClassBond ell (ell ^ m) 12 k S e → U e = 1) →
    FieldsKAt ell hell a df (ell ^ m) R k Lu K S Lam U α₀

theorem AnchorChart12.mono {L : PeriodicLatticeExtent} {ell M k : ℕ} {S : Tower L} {U : LinkCfg L} {α₀ η : ℝ}
    {x : PeriodicLatticeSite L} {r : ℕ} (h : AnchorChart12 ell M k S U α₀ η x r) (x' : PeriodicLatticeSite L) (r' : ℕ)
    (hsub : Ball x' r' ⊆ Ball x r) : AnchorChart12 ell M k S U α₀ η x' r' := by
  obtain ⟨g, V, hV, hag⟩ := h
  exact ⟨g, V, hV, hag.mono hsub⟩

section charts
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

theorem blockCharts_ball (hell : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 2002 ≤ M) (hRM : 1000 * ell ≤ R * M)
    (hL : ∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ) {C α₀ η : ℝ} (hC : 1 ≤ C) (hα : 0 < α₀) (hη : 0 < η)
    {U : LinkCfg (scaleUp ell k Lu)} (hB : BallChartsAt ell M k S U C α₀ η) :
    ∀ q : QIdx (geomOf ell k S), 1 ≤ jq q →
      AnchorChart12 ell M k S U ((ell : ℝ) ^ 3 * (C * α₀)) η (yq q) (7 * ell ^ jq q) := by
  intro q hq
  obtain ⟨hdv, hyO, hyO1⟩ := yq_mem q
  have hc := anchorChart12_of_ball hS hell hM hRM hL hq (jq_le q) hC hα hη hB hyO hyO1
  refine AnchorChart12.mono hc (yq q) _ ?_
  intro z hz
  have : pdist (yq q) z ≤ 7 * ell ^ jq q := hz
  show pdist (yq q) z ≤ 16 * ell ^ jq q
  omega

theorem rowCharts_ball (hell : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 2002 ≤ M) (hRM : 1000 * ell ≤ R * M)
    (hL : ∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ) {C α₀ η : ℝ} (hC : 1 ≤ C) (hα : 0 < α₀) (hη : 0 < η)
    {U : LinkCfg (scaleUp ell k Lu)} (hB : BallChartsAt ell M k S U C α₀ η) :
    ∀ p : BIdx (geomOf ell k S), 1 ≤ (p.1 : ℕ) →
      AnchorChart12 ell M k S U ((ell : ℝ) ^ 3 * (C * α₀)) η p.2.1.1 (AdalyFormal.StatementLaneR8.rhoT ell p.1) := by
  intro p hp
  have hjk : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have h8 := AdalyFormal.M2F123.rhoT_le_eight ell hell p.1
  obtain ⟨⟨hb, -⟩⟩ : Nonempty (_ ∧ _) := ⟨p.2.2⟩
  rcases hb with hb | hb
  · obtain ⟨hdv, hyO, hyO1⟩ := hb
    have hc := anchorChart12_of_ball hS hell hM hRM hL hp hjk hC hα hη hB hyO hyO1
    refine AnchorChart12.mono hc _ _ ?_
    intro z hz
    have : pdist p.2.1.1 z ≤ AdalyFormal.StatementLaneR8.rhoT ell p.1 := hz
    show pdist p.2.1.1 z ≤ 16 * ell ^ (p.1 : ℕ)
    omega
  · obtain ⟨hdv, hyO, hyO1⟩ := hb
    have hc := anchorChart12_of_ball hS hell hM hRM hL hp hjk hC hα hη hB hyO hyO1
    refine AnchorChart12.mono hc _ _ ?_
    intro z hz
    have h1 : pdist p.2.1.1 z ≤ AdalyFormal.StatementLaneR8.rhoT ell p.1 := hz
    have h2 := AdalyFormal.StatementLaneR8.pdist_coarseShift_le p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2
    have h3 := AdalyFormal.StatementLaneR8.pdist_comm (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) p.2.1.1
    have h4 := AdalyFormal.StatementLaneR8.pdist_triangle (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) p.2.1.1 z
    show pdist (coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) z ≤ 16 * ell ^ (p.1 : ℕ)
    omega

end charts

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.blockCharts_ball
#print axioms AdalyFormal.OneGap.rowCharts_ball
