
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## I. The curved dilated family at the flat point: smoothness and the units

`ε ↦ dilU q R ε 1` (curvature `ε` on the round-4 defect line, trivial exterior) has smooth
links and is the trivial background at `ε = 0`.  At the trivial background the Dirichlet
operator, the constraint Gram `Γ` (frozen `MS6.exists_Gami_strat` with `ρ = 0` on the proper
tower of an admissible tower, `MS7.properTower_geomOf`) and `Q*` (frozen `W6F.qs_injective_strat`
with zero drift) are units resp. injective. -/
section DilFamily

open scoped Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (Ug Xm sig Ug_zero)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilPattern dilU)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem contDiff_Xm : ContDiff ℝ ⊤ (fun t : ℝ => Xm t) := by
  have e : (fun t : ℝ => Xm t) = fun t => t • (Complex.I • sig) := by
    funext t
    ext i j
    simp [Xm, Matrix.smul_apply, Complex.real_smul, mul_assoc]
  rw [e]
  exact contDiff_id.smul contDiff_const

theorem contDiffAt_Ug (t₀ : ℝ) : ContDiffAt ℝ ⊤ (fun t : ℝ => ((Ug t : SU2) : M2)) t₀ :=
  (NormedSpace.exp_analytic (Xm t₀)).contDiffAt.comp t₀ contDiff_Xm.contDiffAt

theorem dilU_link_contDiff (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) :
    ContDiff ℝ ⊤ (fun ε : ℝ => ((dilU q R ε 1 e : SU2) : M2)) := by
  classical
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [dilU, if_pos he]
    exact contDiff_const
  · simp only [dilU, if_neg he]
    by_cases hp : dilPattern q R e
    · simp only [if_pos hp]
      exact contDiff_iff_contDiffAt.mpr contDiffAt_Ug
    · simp only [if_neg hp]
      exact contDiff_const

theorem dilU_smooth (q R : ℕ) : SmoothAt0 (fun ε : ℝ => dilU q R ε 1) :=
  fun e => (dilU_link_contDiff q R e).contDiffAt

theorem dilU_contFam (q R : ℕ) : AdalyFormal.D1Literal.ContFam (fun ε : ℝ => dilU q R ε 1) :=
  fun e => (dilU_link_contDiff q R e).continuous

end DilFamily

section DilUnits

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2 (Ug Ug_zero)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilPattern dilU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

theorem dilU_zero (q R : ℕ) : dilU q R 0 1 = fun _ => 1 := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [dilU, if_pos he]
    rfl
  · simp only [dilU, if_neg he, ite_self, Ug_zero]

theorem dil_G_k (q R : ℕ) : (geomOf 2 1 (dilTower q R)).k = 1 := rfl
theorem dil_G_ell (q R : ℕ) : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl

theorem dil_out_site (q R : ℕ) (hq : 0 < q) :
    ∃ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)), x ∉ (geomOf 2 1 (dilTower q R)).Om0 := by
  refine ⟨fun _ => 0, ?_⟩
  show ¬ (4 * q ≤ ((0 : Fin _) : ℕ) ∧ _)
  simp only [Fin.val_zero]
  omega

theorem dil_LP_unit (q R : ℕ) (hq : 0 < q) (U : Cfg (scaleUp 2 1 (dilLu q R))) :
    IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) U 1) :=
  delpA_unit (geomOf 2 1 (dilTower q R)) U one_pos (le_refl 2) (dil_out_site q R hq)

theorem dil_wq_pos (q R : ℕ) (j : ℕ) : 0 < AdalyFormal.M1Site.wq (geomOf 2 1 (dilTower q R)) 1 j :=
  wq_pos (geomOf 2 1 (dilTower q R)) one_pos (le_refl 2) j

theorem bgTower_one {L : PeriodicLatticeExtent} (G : TowerGeom L) (i : ℕ) :
    bgTower G (fun _ => 1) i = fun _ => 1 :=
  AdalyFormal.SliceCoerc.ubarTower_trivial G.ell i

theorem dil_Gam_unit {q R : ℕ} (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (Gam (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1) := by
  obtain ⟨Gi, h1, h2⟩ := AdalyFormal.M1Site.exists_Gami_strat 2 1 (le_refl 2)
    (AdalyFormal.M1Site.hdvd_of_admissible hS) (AdalyFormal.M1Site.properTower_geomOf (by norm_num) hS)
    (fun _ => 1) 1 one_pos 0 le_rfl (by norm_num)
    (fun j _ y _ b _ => by simp)
    (fun j _ y _ i _ z _ _ μ _ => by rw [bgTower_one]; simp)
  refine ⟨⟨Gam (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1, Gi, ?_, ?_⟩, rfl⟩
  · ext1 u; exact h1 u
  · ext1 u; exact h2 u

theorem delW_zero (ell k : ℕ) (hell : 0 < ell) : AdalyFormal.W6.delW ell k (fun _ => 0) = 0 := by
  unfold AdalyFormal.W6.delW AdalyFormal.W6.SS
  simp [AdalyFormal.BondComposite.thetaOf_zero ell hell]

theorem dil_Qs_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R) (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (trivialU (scaleUp 2 1 (dilLu q R))) 1 (dilLam q R)).data.Qs :=
  AdalyFormal.W6.qs_injective_strat (by norm_num) (le_refl 2) hS (by omega) (by omega)
    (trivialU _) 1 (dilLam q R) (fun _ => 0) (AdalyFormal.W6.regTower_triv (by norm_num))
    (AdalyFormal.W6.towerClass_triv (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => AdalyFormal.W6.rhoOf_zero_lt 2) (by rw [delW_zero 2 1 (by norm_num)]; norm_num)

end DilUnits

end AdalyFormal.Round9.Guarded.AnalyticR2
