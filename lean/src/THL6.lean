import THL5
import THL2

/-!
# THL6 -- the headlines for ARBITRARY level-0 domains (lane thin_layer_20261019)

`THL5` replays (kernel-checked) every declaration of the proved headlines that mentions `Admissible` with the base law (T6) removed (`ThinReplay.AdmT`).  Here the
mirrored headlines `ThinScan.*` are turned into statements about towers whose level-0 domain is ARBITRARY:

`AdmSplitNB ell M R0 Rs k S` : nesting; vanishing above `k`; `M ell^j ∣` every extent; `Omega_j` a union of blocks of side `M ell^j`; the strict collar
`R0 M < dist(Omega_0^c, Omega_1)` at level 0 and `Rs j * M ell^j < dist(Omega_j^c, Omega_{j+1})` at the levels `1 <= j <= k`.  NO base law: `Omega_0` is any union of `M`-blocks
containing `Omega_1` at `ell^1`-distance `> R0 M` from its complement (so `Omega_0 ⊇ {blocks within R0 M of Omega_1}`; any thinner or thicker or non-radial shape allowed, up to the
radius).  The threshold `R1` of the headline binds `R0` only.

* `admT_iff` / `admNoBase_of_splitNB` : `AdmSplitNB` with `R0 <= Rs j` gives `AdmT` (= T1-T5 at radius `R0`).
* `famTorusLayer_union`, `famTorusLayer_box`, `famTorusLayerCap`, `totalLayer`, `mixedLayer`, `target8Layer` : the headline forms for `AdmSplitNB` towers.
* `famTorusThin_of_layer` etc. : they imply the radial thin forms of `THL1` (an `AdmSplit` tower is an `AdmSplitNB` tower).
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 8000

namespace AdalyFormal.ThinLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open UNI.AllC UNI.Total
open AdalyFormal.L0C
open ThinReplay (AdmT)

variable {L : PeriodicLatticeExtent}

/-- tower with separate level-0 radius and NO base law. -/
def AdmSplitNB {L : PeriodicLatticeExtent} (ell M R0 : ℕ) (Rs : ℕ → ℕ) (k : ℕ) (S : Tower L) : Prop :=
  (∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) ∧
  (∀ j : ℕ, k < j → S.Om j = ∅) ∧
  (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, bigSide M ell j ∣ (L μ + 1)) ∧
  (∀ j : ℕ, j ≤ k → BlockClosed (bigSide M ell j) (S.Om j)) ∧
  (∀ x : PeriodicLatticeSite L, x ∉ S.Om 0 → ∀ y ∈ S.Om 1, R0 * bigSide M ell 0 < pdist x y) ∧
  (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ x : PeriodicLatticeSite L, x ∉ S.Om j →
      ∀ y ∈ S.Om (j + 1), Rs j * bigSide M ell j < pdist x y)

theorem admT_iff {ell M R k : ℕ} {S : Tower L} : AdmT ell M R k S ↔ AdmNoBase ell M R k S :=
  ⟨fun ⟨a, b, c, d, e, _⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e, fun _ => Iff.rfl⟩⟩

theorem admNoBase_of_splitNB {ell M R0 k : ℕ} {Rs : ℕ → ℕ} {S : Tower L} (hR : ∀ j, 1 ≤ j → R0 ≤ Rs j)
    (h : AdmSplitNB ell M R0 Rs k S) : AdmNoBase ell M R0 k S := by
  obtain ⟨h1, h2, h3, h4, h5, h5'⟩ := h
  refine ⟨h1, h2, h3, h4, fun j hj x hx y hy => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · exact h5 x hx y hy
  · exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (hR j hpos)) (h5' j hpos hj x hx y hy)

theorem admT_of_splitNB {ell M R0 k : ℕ} {Rs : ℕ → ℕ} {S : Tower L} (hR : ∀ j, 1 ≤ j → R0 ≤ Rs j)
    (h : AdmSplitNB ell M R0 Rs k S) : AdmT ell M R0 k S :=
  admT_iff.2 (admNoBase_of_splitNB hR h)

/-- an `AdmSplit` tower (base law at `R0`) is an `AdmSplitNB` tower (drop the base law). -/
theorem admSplitNB_of_admSplit {ell M R0 k : ℕ} {Rs : ℕ → ℕ} {S : Tower L} (h : AdmSplit ell M R0 Rs k S) :
    AdmSplitNB ell M R0 Rs k S := by
  obtain ⟨h1, h2, h3, h4, h5, h5', -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h5'⟩

/-! ## the headline forms for `AdmSplitNB` towers -/

def FamTorusLayerP (Cl : ClassPred) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledP Cl ell (ell ^ m) F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

/-- the union-class family headline (printed class: unions of big blocks) for arbitrary level-0 domains. -/
theorem famTorusLayer_union : FamTorusLayerP unionClass := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := ThinScan.UNI.Total.p428Target8FamilyTorusU ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  exact hF m hm R0 hR0 k hk Lu α₀ hα F hFs hT S (admT_of_splitNB hR hS) Lam (lambdaOK2_mono hRL hL) U hU

/-- the box-class family headline for arbitrary level-0 domains. -/
theorem famTorusLayer_box : FamTorusLayerP boxClass := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := ThinScan.MXQ.Total.p428Target8FamilyTorus ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  exact hF m hm R0 hR0 k hk Lu α₀ hα F hFs hT S (admT_of_splitNB hR hS) Lam (lambdaOK2_mono hRL hL) U hU

/-- the cap headline (p.408 level-0 cubes) for arbitrary level-0 domains. -/
def FamTorusCapLayer : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledCap ell (ell ^ m) F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem famTorusLayerCap : FamTorusCapLayer := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := ThinScan.AdalyFormal.L0C.cap_unconditional ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  exact hF m hm R0 hR0 k hk Lu α₀ hα F hFs hT S (admT_of_splitNB hR hS) Lam (lambdaOK2_mono hRL hL) U hU

def TotalLayer : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ c : ℕ, 10 ≤ c → ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupled ell (ell ^ m) c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem totalLayer : TotalLayer := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := ThinScan.AdalyFormal.Total.p428Target8Total ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun c hc m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα h2 hTor S hS Lam hL U hU => ?_⟩
  exact hT c hc m hm R0 hR0 k hk Lu α₀ hα h2 hTor S (admT_of_splitNB hR hS) Lam (lambdaOK2_mono hRL hL) U hU

def MixedLayer : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Φ : Set ℕ, (∀ f ∈ Φ, 10 ≤ f) → ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 →
        ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (∀ f ∈ Φ, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            MXP.AllC.ClassCoupledΦ ell (ell ^ m) Φ k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem mixedLayer : MixedLayer := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := ThinScan.MXP.Total.p428Target8Mixed ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun Φ hΦ m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα h2 hTor S hS Lam hL U hU => ?_⟩
  exact hT Φ hΦ m hm R0 hR0 k hk Lu α₀ hα h2 hTor S (admT_of_splitNB hR hS) Lam (lambdaOK2_mono hRL hL) U hU

/-- the frozen headline `P428Target8` (cube factor 12, `InstIneq` conclusion) for arbitrary level-0 domains: one radius `R` (levels `>= 1` and `Lambda`), threshold `R0` of the proof
is the threshold of the frozen statement. -/
def Target8Layer : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), AdmNoBase ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneq ell k (by omega) a Lu γ₀ S Lam U

theorem target8Layer : Target8Layer := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, h⟩ := ThinScan.AdalyFormal.M2RightInv.p428Target8 ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR₀⟩ := h m hm
  refine ⟨R₀, fun R hR => ?_⟩
  obtain ⟨hp, a₀, ha₀, γ₀, hγ, hc⟩ := hR₀ R hR
  refine ⟨hp, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ hα h2 hT S hS Lam hL U hU => ?_⟩
  exact hc k hk Lu α₀ hα h2 hT S (admT_iff.2 hS) Lam hL U hU

/-! ## consequences: the radial thin forms of `THL1` are special cases -/

theorem famTorusThin_of_layer {Cl : ClassPred} (h : FamTorusLayerP Cl) : FamTorusThinP Cl := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  exact ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Lam hL U hU =>
      hF m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S (admSplitNB_of_admSplit hS) Lam hL U hU⟩

theorem famTorusThinU' : FamTorusThinP unionClass := famTorusThin_of_layer famTorusLayer_union

theorem totalThin_of_layer (h : TotalLayer) : TotalThin := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  exact ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun c hc m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα h2 hT S hS Lam hL U hU =>
      hF c hc m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα h2 hT S (admSplitNB_of_admSplit hS) Lam hL U hU⟩

/-! ## the class is strictly larger than the radial one -/

/-- `asymTower` (layers 12 on the left, 8 on the right, `ell = 2`, `M = 2`, `k = 1`) is an `AdmSplitNB` tower at level-0 radius `4`, and for NO radii is it an `AdmSplit` tower
(nor `Admissible`): the arbitrary-layer headlines contain towers the radial ones do not. -/
theorem asym_layer_class :
    AdmSplitNB 2 2 4 (fun _ => 4) 1 asymTower ∧ (∀ R0 Rs, ¬ AdmSplit 2 2 R0 Rs 1 asymTower) := by
  refine ⟨?_, fun R0 Rs => asym_not_admSplit R0 Rs⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := asym_adm5
  exact ⟨h1, h2, h3, h4, h5 0 (Nat.zero_le _), fun j hj1 hj2 => h5 j hj2⟩

end AdalyFormal.ThinLayer

#print axioms AdalyFormal.ThinLayer.admT_iff
#print axioms AdalyFormal.ThinLayer.admNoBase_of_splitNB
#print axioms AdalyFormal.ThinLayer.admSplitNB_of_admSplit
#print axioms AdalyFormal.ThinLayer.famTorusLayer_union
#print axioms AdalyFormal.ThinLayer.famTorusLayer_box
#print axioms AdalyFormal.ThinLayer.famTorusLayerCap
#print axioms AdalyFormal.ThinLayer.totalLayer
#print axioms AdalyFormal.ThinLayer.mixedLayer
#print axioms AdalyFormal.ThinLayer.target8Layer
#print axioms AdalyFormal.ThinLayer.famTorusThin_of_layer
#print axioms AdalyFormal.ThinLayer.famTorusThinU'
#print axioms AdalyFormal.ThinLayer.totalThin_of_layer
#print axioms AdalyFormal.ThinLayer.asym_layer_class
