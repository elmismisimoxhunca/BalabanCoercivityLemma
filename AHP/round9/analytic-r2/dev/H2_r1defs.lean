/-! DEV ONLY: verbatim copies of round-1 definitions. -/
namespace AdalyFormal.Round9.Guarded.AnalyticR1

open scoped RealInnerProductSpace Topology
open Set Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

/-- The carrier space of the twist family at scale `q` and radius `R`. -/
abbrev TwistSpace (q R : ℕ) : Type := ↥(bondSupp (geomOf 2 1 (dilTower q R)))

/-- The pinned parameters of the curved dilated family with an arbitrary exterior field. -/
noncomputable def extP (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilU q R ε V) 1 (dilLam q R)

/-- The all-plaquette carrier with exterior field `V`. -/
noncomputable def extA (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →L[ℝ] TwistSpace q R :=
  (dataS selAll selAll (extP q R ε V)).Ginv

/-- The localized correction with exterior field `V` (independent of `V`, `extD_congr`). -/
noncomputable def extD (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →L[ℝ] TwistSpace q R :=
  (dataS selIn selIn (extP q R ε V)).Delta2 (dataS_laws selIn selIn _)

/-- Soft regularity of the single interior family `ε ↦ dilU q R ε 1` (curved interior,
trivial exterior), as `ε → 0⁺`: continuity of the carrier and of the dressing `W`, and the
first-order coefficient `D₁` of the correction.  No exterior angle appears.  NOT proved here. -/
def InteriorRegularity (q R : ℕ) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R) : Prop :=
  Tendsto (fun ε : ℝ => extA q R ε 1) (𝓝[>] 0) (𝓝 (extA q R 0 1)) ∧
  Tendsto (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (dilU q R ε 1) 1) (𝓝[>] 0)
    (𝓝 (Wop (geomOf 2 1 (dilTower q R)) (dilU q R 0 1) 1)) ∧
  Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁)

/-- The soft half of the final premise, exterior-free.  NOT proved here. -/
def InteriorSoft : Prop :=
  ∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R →
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, InteriorRegularity q R D₁


end AdalyFormal.Round9.Guarded.AnalyticR1
