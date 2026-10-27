import SK1

/-!
# SK6a -- localisation to the class-constrained bonds (lane m2_skeleton_20261015)

`Uloc U` agrees with `U` on `ClassBond` and is `1` elsewhere.  `ClassCoupled` is a statement about the class-constrained bonds only, so it passes to `Uloc U`;
`InstIneq` at `Uloc U` gives `InstIneq` at `U` by the r8 locality theorem `InstIneq_congr_class`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
namespace AdalyFormal.M2Skel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG (LambdaOK2 InstIneq)
open AdalyFormal.StatementLaneR8 (ClassBond LocHyp InstIneq_congr_class)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

open Classical in
/-- the localisation: `U` on the class-constrained bonds, `1` elsewhere. -/
noncomputable def Uloc {ell k : ℕ} {Lu : PeriodicLatticeExtent} (M : ℕ) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) : LinkCfg (scaleUp ell k Lu) :=
  fun e => if ClassBond ell M 12 k S e then U e else 1

theorem Uloc_eq {ell k M : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
    {U : LinkCfg (scaleUp ell k Lu)} {e : Bond (scaleUp ell k Lu)} (h : ClassBond ell M 12 k S e) :
    Uloc M S U e = U e := by
  classical
  unfold Uloc; rw [if_pos h]

theorem Uloc_triv {ell k M : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
    {U : LinkCfg (scaleUp ell k Lu)} {e : Bond (scaleUp ell k Lu)} (h : ¬ ClassBond ell M 12 k S e) :
    Uloc M S U e = 1 := by
  classical
  unfold Uloc; rw [if_neg h]

theorem classCoupled_loc {ell k M : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
    {α₀ η : ℝ} {U : LinkCfg (scaleUp ell k Lu)} (h : ClassCoupled ell M 12 k S α₀ η U) :
    ClassCoupled ell M 12 k S α₀ η (Uloc M S U) := by
  refine ⟨h.1, fun sites j hq => ?_⟩
  obtain ⟨g, A, hA, hD, hLap⟩ := h.2 sites j hq
  refine ⟨g, A, fun e he => ?_, hD, hLap⟩
  obtain ⟨h1, h2, h3⟩ := hA e he
  have hu : Uloc M S U e = U e := Uloc_eq ⟨sites, j, hq, he⟩
  refine ⟨h1, ?_, h3⟩
  unfold periodicGaugeTransform
  rw [hu]
  exact h2

theorem inst_of_loc {ell k M R : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (hell2 : 2 ≤ ell) (hk : 1 ≤ k)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hroom : 17 * ell ≤ R * M) (hM2 : 2 ≤ M)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam) {α₀ η : ℝ}
    {U : LinkCfg (scaleUp ell k Lu)} (h : ClassCoupled ell M 12 k S α₀ η U) (a γ₀ : ℝ)
    (hI : InstIneq ell k hell0 a Lu γ₀ S Lam (Uloc M S U)) : InstIneq ell k hell0 a Lu γ₀ S Lam U :=
  (InstIneq_congr_class hell0 a γ₀ ⟨hS, hk, hell2, hroom, hL⟩ hM2 h.1 (fun e he => (Uloc_eq he).symm)).2 hI

end AdalyFormal.M2Skel

#print axioms AdalyFormal.M2Skel.classCoupled_loc
#print axioms AdalyFormal.M2Skel.inst_of_loc
