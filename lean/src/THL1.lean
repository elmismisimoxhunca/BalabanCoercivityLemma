import L0C2
import TT_F
import MX_F

/-!
# TL1 -- radially thinner level-0 layers (lane thin_layer_20261019)

CMP99b p.394 allows `Omega_0` to be the layer "with distances to `Omega_1` <= RM" or "a thinner layer of the big blocks surrounding `Omega_1`";
the frozen `Admissible` hard-codes the first.  Here the level-0 radius `R0` is separated from the radius `R` of the levels `>= 1`:
`AdmSplit ell M R0 R k S` = the six clauses of `Admissible` with the level-0 strict collar AND the base law (T6) taken at radius `R0`, and the
collars of the levels `1..k` at radii `Rs j` (a function of the level; the constant function is the uniform case).

Main facts (all reductions to the proved headlines; no new analysis):
* `admissible_of_admSplit` : `R0 <= R` and `AdmSplit R0 R` give `Admissible R0` (the strict collar `R * M ell^j < pdist` is monotone in `R`).
* `lambdaOK2_mono` : `LambdaOK2` at radius `R'` gives it at every `R0 <= R'`.
* `famTorusThin_of` : for EVERY class predicate `Cl`, `FamTorusP Cl` (union headline, box headline, ...) gives the thin form
  `FamTorusThinP Cl`: the threshold `R1` binds the LEVEL-0 radius only; the levels `>= 1` (any radii `Rs j >= R0`) and `Lambda` may carry any larger radius.
* the same for the cap headline (`famTorusCapThin_of`), `P428Target8Total` (`totalThin_of`) and `P428Target8Mixed` (`mixedThin_of`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.ThinLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open UNI.AllC UNI.Total
open AdalyFormal.L0C

variable {L : PeriodicLatticeExtent}

/-- **tower with a separate level-0 radius.**  Clauses T1-T4 of `Admissible`; the level-0 strict collar at radius `R0`; the strict collars of the
levels `1..k` at radius `R`; the base law (T6, `Omega_0` = union of `M`-blocks with a site within `R0 M` of `Omega_1`) at radius `R0`. -/
def AdmSplit {L : PeriodicLatticeExtent} (ell M R0 : ℕ) (Rs : ℕ → ℕ) (k : ℕ) (S : Tower L) : Prop :=
  (∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) ∧
  (∀ j : ℕ, k < j → S.Om j = ∅) ∧
  (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, bigSide M ell j ∣ (L μ + 1)) ∧
  (∀ j : ℕ, j ≤ k → BlockClosed (bigSide M ell j) (S.Om j)) ∧
  (∀ x : PeriodicLatticeSite L, x ∉ S.Om 0 → ∀ y ∈ S.Om 1, R0 * bigSide M ell 0 < pdist x y) ∧
  (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ x : PeriodicLatticeSite L, x ∉ S.Om j →
      ∀ y ∈ S.Om (j + 1), Rs j * bigSide M ell j < pdist x y) ∧
  (∀ x : PeriodicLatticeSite L, x ∈ S.Om 0 ↔
      ∃ y ∈ S.Om 1, ∃ z : PeriodicLatticeSite L,
        (∀ μ : Fin 3, (z μ).val / M = (x μ).val / M) ∧ pdist z y ≤ R0 * M)

/-- the uniform tower is the special case `R0 = R`. -/
theorem admSplit_of_admissible {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) :
    AdmSplit ell M R (fun _ => R) k S := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5 0 (Nat.zero_le _), fun j _ hj => h5 j hj, h6⟩

/-- **monotonicity**: a tower whose level-0 radius is `R0 <= R` is admissible at radius `R0`. -/
theorem admissible_of_admSplit {ell M R0 k : ℕ} {Rs : ℕ → ℕ} {S : Tower L} (hR : ∀ j, 1 ≤ j → R0 ≤ Rs j)
    (h : AdmSplit ell M R0 Rs k S) : Admissible ell M R0 k S := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun j hj x hx y hy => ?_, h6⟩
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · exact h5 x hx y hy
  · exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (hR j hpos)) (h5' j hpos hj x hx y hy)

theorem admSplit_iff_admissible {ell M R k : ℕ} {S : Tower L} :
    AdmSplit ell M R (fun _ => R) k S ↔ Admissible ell M R k S :=
  ⟨admissible_of_admSplit (fun _ _ => le_rfl), admSplit_of_admissible⟩

/-- `Lambda` collar monotone in the radius. -/
theorem lambdaOK_mono {Lu Lf : PeriodicLatticeExtent} {ell M R R0 k : ℕ} {S : Tower Lf}
    {Lam : Set (PeriodicLatticeSite Lu)} (hR : R0 ≤ R) (h : LambdaOK ell M R k S Lam) :
    LambdaOK ell M R0 k S Lam := by
  obtain ⟨hb, emb, he1, he2, he3⟩ := h
  exact ⟨hb, emb, he1, he2, fun y hy y' hy' => lt_of_le_of_lt (Nat.mul_le_mul_right _ hR) (he3 y hy y' hy')⟩

theorem lambdaOK2_mono {Lu Lf : PeriodicLatticeExtent} {ell M R R0 k : ℕ} {S : Tower Lf}
    {Lam : Set (PeriodicLatticeSite Lu)} (hR : R0 ≤ R) (h : LambdaOK2 ell M R k S Lam) :
    LambdaOK2 ell M R0 k S Lam :=
  ⟨lambdaOK_mono hR h.1, h.2⟩

/-! ## the thin form of the family headline, for an arbitrary class predicate -/

/-- **`FamTorusP` with a separate level-0 radius.**  Identical to `FamTorusP Cl` except: the tower is `AdmSplit ell (ell^m) R0 R k S`
(level-0 radius `R0`, level `j >= 1` radius `Rs j`), `Lambda` carries a third radius `RL`, and the threshold `R1` is imposed on `R0` ONLY
(`R0 <= Rs j`, `R0 <= RL`). -/
def FamTorusThinP (Cl : ClassPred) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplit ell (ell ^ m) R0 Rs k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledP Cl ell (ell ^ m) F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

/-- **the reduction**: the (proved) family headline for any class implies its thin form, with the same constants `m₁, R₁, a₀, γ₀`. -/
theorem famTorusThin_of {Cl : ClassPred} (h : FamTorusP Cl) : FamTorusThinP Cl := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  exact hF m hm R0 hR0 k hk Lu α₀ hα F hFs hT S (admissible_of_admSplit hR hS) Lam (lambdaOK2_mono hRL hL) U hU

/-- the converse (specialise `R0 = R = RL`, `Rs = const R`): the thin form is EQUIVALENT to the original; nothing is lost or gained in the constants, only the roles of the radii are separated. -/
theorem famTorus_of_thin {Cl : ClassPred} (h : FamTorusThinP Cl) : FamTorusP Cl := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  exact hF m hm R hR (fun _ => R) (fun _ _ => le_rfl) R le_rfl k hk Lu α₀ hα F hFs hT S (admSplit_of_admissible hS) Lam hL U hU

theorem famTorusThin_iff {Cl : ClassPred} : FamTorusThinP Cl ↔ FamTorusP Cl :=
  ⟨famTorus_of_thin, famTorusThin_of⟩

/-- the thin union headline (the strongest family form in the repository: printed "union of big blocks" class). -/
theorem famTorusThinU : FamTorusThinP unionClass :=
  famTorusThin_of UNI.Total.p428Target8FamilyTorusU

/-- the thin box headline (original grid-aligned box class). -/
theorem famTorusThinBox : FamTorusThinP boxClass :=
  famTorusThin_of MXQ.Total.p428Target8FamilyTorus

/-! ## the cap headline (p.408 level-0 cubes, regularity on cube ∩ Omega_0) -/

def FamTorusCapThin : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplit ell (ell ^ m) R0 Rs k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledCap ell (ell ^ m) F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem famTorusCapThin_of (h : FamTorusCap) : FamTorusCapThin := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα F hFs hT S hS Lam hL U hU => ?_⟩
  exact hF m hm R0 hR0 k hk Lu α₀ hα F hFs hT S (admissible_of_admSplit hR hS) Lam (lambdaOK2_mono hRL hL) U hU

theorem famTorusCapThin_unconditional : FamTorusCapThin := famTorusCapThin_of cap_unconditional

/-! ## the single-cube-factor forms (`Total`, `Mixed`) -/

def TotalThin : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ c : ℕ, 10 ≤ c → ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplit ell (ell ^ m) R0 Rs k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupled ell (ell ^ m) c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem totalThin_of (h : AdalyFormal.Total.P428Target8Total) : TotalThin := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun c hc m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα h2 hTor S hS Lam hL U hU => ?_⟩
  exact (hT c hc m hm R0 hR0 k hk Lu α₀ hα h2 hTor S (admissible_of_admSplit hR hS) Lam
    (lambdaOK2_mono hRL hL) U hU)

theorem totalThin_unconditional : TotalThin := totalThin_of AdalyFormal.Total.p428Target8Total

def MixedThin : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Φ : Set ℕ, (∀ f ∈ Φ, 10 ≤ f) → ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 →
        ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (∀ f ∈ Φ, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplit ell (ell ^ m) R0 Rs k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            MXP.AllC.ClassCoupledΦ ell (ell ^ m) Φ k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U

theorem mixedThin_of (h : MXP.Total.P428Target8Mixed) : MixedThin := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ,
    fun Φ hΦ m hm R0 hR0 Rs hR RL hRL k hk Lu α₀ hα h2 hTor S hS Lam hL U hU => ?_⟩
  exact (hT Φ hΦ m hm R0 hR0 k hk Lu α₀ hα h2 hTor S (admissible_of_admSplit hR hS) Lam
    (lambdaOK2_mono hRL hL) U hU)

theorem mixedThin_unconditional : MixedThin := mixedThin_of MXP.Total.p428Target8Mixed

end AdalyFormal.ThinLayer

#print axioms AdalyFormal.ThinLayer.admissible_of_admSplit
#print axioms AdalyFormal.ThinLayer.lambdaOK2_mono
#print axioms AdalyFormal.ThinLayer.famTorus_of_thin
#print axioms AdalyFormal.ThinLayer.famTorusThin_iff
#print axioms AdalyFormal.ThinLayer.famTorusThinU
#print axioms AdalyFormal.ThinLayer.famTorusThinBox
#print axioms AdalyFormal.ThinLayer.famTorusCapThin_unconditional
#print axioms AdalyFormal.ThinLayer.totalThin_unconditional
#print axioms AdalyFormal.ThinLayer.mixedThin_unconditional
