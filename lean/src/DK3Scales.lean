import CurvedReproduced
import QJIdentification
import CarrierBridge

/-!
DK3: side256, eta=1/8, T^(3) of side32. No enlargement or CubeClass.
This file builds the linear objects of RESEARCH §7.1(1), not Delta_2.
The eventual operator target is ROUTE 5B ONLY, NOT YET IDENTIFIED with
CMP99b (3.156) at k=3. In particular no PhaseI.gamma0 is reused.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
noncomputable section
namespace HConstruction.DK3
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2 ubarSU2 ubarSU2_trivialU)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyQIdentification.QJ
open AdalyFormal.DeltaKR85 (q124Principal)
open AdalySI1.Multiscale (qCompositeBond)
attribute [local irreducible] CoarseLattice

abbrev fineL : PeriodicLatticeExtent := fun _ => 255
abbrev unitL : PeriodicLatticeExtent := fun _ => 31
abbrev US := PeriodicLatticeSite unitL
abbrev FS := PeriodicLatticeSite fineL

def origin : FS := fun _ => 0
/-- The same explicit side256 single-link family as LTBackground.nonflatU.
The definition is reproduced to avoid importing the k=1 CubeClass dependency
of LTBackground; it is not the earlier side-four nonflatU. -/
def U (t : ℝ) : PeriodicLinkConfiguration SU2 fineL := fun b =>
  if b = (origin,0) then HConstruction.NfRepair.Reproduced.rotElem t else 1

def tower (t : ℝ) := ubarTowerSU2 2 (U t)
def Vfine (t : ℝ) : PeriodicLinkConfiguration SU2 fineL := tower t 3

/-- Multiplication by eight, NOT by four or two, identifies T^(3) with its fine-grid sites. -/
def embed (x : US) : FS := fun μ => ⟨8 * (x μ).val, by
  have h : (x μ).val < 32 := (x μ).isLt
  change 8 * (x μ).val < 256
  omega⟩

theorem embed_coarse (x : US) : embed x ∈ CoarseLattice fineL 8 := by
  apply mem_CoarseLattice.mpr
  intro μ
  change (8 * (x μ).val) % 8 = 0
  omega

def siteEquiv : US ≃ {x : FS // x ∈ CoarseLattice fineL 8} where
  toFun x := ⟨embed x, embed_coarse x⟩
  invFun y μ := ⟨(y.1 μ).val / 8, by
    have h : (y.1 μ).val < 256 := (y.1 μ).isLt
    change (y.1 μ).val / 8 < 32
    omega⟩
  left_inv x := by
    funext μ
    apply Fin.ext
    change (8 * (x μ).val) / 8 = (x μ).val
    omega
  right_inv y := by
    apply Subtype.ext
    funext μ
    apply Fin.ext
    have h := mem_CoarseLattice.mp y.2 μ
    change 8 * ((y.1 μ).val / 8) = (y.1 μ).val
    omega

/-- V_t = Ubar^3_t reindexed to the unit lattice, with no replacement background. -/
def V (t : ℝ) : PeriodicLinkConfiguration SU2 unitL := fun b => Vfine t (embed b.1,b.2)

theorem U_zero : U 0 = AdalyFormal.Balaban.CovariantHjMinimizer.trivialU fineL := by
  funext b
  simp [U, AdalyFormal.Balaban.CovariantHjMinimizer.trivialU,
    (HConstruction.NfRepair.Reproduced.rotElem_eq_one_iff 0).mpr rfl]

theorem tower_zero (j : ℕ) : tower 0 j =
    AdalyFormal.Balaban.CovariantHjMinimizer.trivialU fineL := by
  induction j with
  | zero => exact U_zero
  | succ j ih =>
    change ubarSU2 (2^j) 2 (tower 0 j) = _
    rw [ih, ubarSU2_trivialU]

theorem V_zero : V 0 = AdalyFormal.Balaban.CovariantHjMinimizer.trivialU unitL := by
  funext b
  change tower 0 3 (embed b.1,b.2) = 1
  rw [tower_zero]
  rfl

/-- Fine-to-T^(3): the certified ordered composite, not Q1 at the unit scale. -/
def fineQ3 (t : ℝ) : (CoarseBond fineL 1 → SuTwo) →ₗ[ℝ]
    (CoarseBond fineL 8 → SuTwo) := qCompositeBond (tower t) 2 3

/-- CMP99b (3.15), j=3, as an equality of operators on all inputs. -/
theorem fineQ3_source (t : ℝ) : QjInChart (tower t) 2 3 = fineQ3 t :=
  QjInChart_eq_qCompositeBond (tower t) 2 3

theorem fineQ3_order (t : ℝ) (A : CoarseBond fineL 1 → SuTwo) :
    fineQ3 t A = q124Principal 4 2 (tower t 2)
      (q124Principal 2 2 (ubarSU2 1 2 (U t))
        (q124Principal 1 2 (U t) A)) := rfl

/-- Unit-lattice Q1 in (3.155): one factor, block size two on T^(3).
The current fine-grid stride is eight; the output stride there is sixteen.
Here, after reindexing T^(3), the current stride is one and the output two. -/
def unitQ1 (t : ℝ) : (CoarseBond unitL 1 → SuTwo) →ₗ[ℝ]
    (CoarseBond unitL 2 → SuTwo) := q124Principal 1 2 (V t)

/-- Chart-level identification of the one-step Q1; no two-step composition. -/
theorem unitQ1_source (t : ℝ) :
    QjInChart (fun _ => V t) 2 1 = unitQ1 t :=
  QjInChart_eq_qCompositeBond (fun _ => V t) 2 1

/-- The (3.14)/(3.110) factor ell^k eta equals one at k=3. -/
theorem normalization : (2 : ℝ)^3 * (1/8 : ℝ) = 1 := by norm_num

theorem unnormalized_depth3 (t : ℝ) :
    unnormalizedLinearChain (tower t) 2 (1/8) 3 = sourceQj (tower t) 2 3 := by
  rw [unnormalizedLinearChain_eq]
  norm_num

theorem tiling : (∀ μ : Fin 3, 2^3 ∣ (fineL μ + 1)) ∧
    (∀ μ : Fin 3, 2 ∣ (unitL μ + 1)) := by
  constructor <;> intro μ <;> norm_num
end HConstruction.DK3
