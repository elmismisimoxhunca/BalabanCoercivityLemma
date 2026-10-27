import UNI_Base
import UNI_CJ
import TL22a
import TL1n

/-!
# UNI_Thin -- thin-torus lift of the FAMILY class (lane mixed_20261017, round 2)

`liftFam L Fm` : the lifted family on a covering torus: a triple `(sites', j, f)` belongs to it iff `sites'` projects ONTO a member `(sites0, j, f)` of `Fm L`.
`coversSites_liftQ`, `coversPlaq_liftQ` (text copies of TL1m; the lifted cube projects onto the covering base cube), `regBody_lift` (tail of TL1l.perCube_lift at ONE cube),
`perCube_liftHQ`, `classCoupled_liftHQ`, `geometry_liftHQ`, `jetReg_of_classHQ`, `unitReg_of_classHQ` (TL22a with `classRows_readΦ`, `classRows_unitΦ`).
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
namespace UNI.Thin
open AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open UNI.AllC

/-- membership in the lifted family: the lifted cube is the PREIMAGE of a member of the base family under the covering map. -/
def LiftMem (L : PeriodicLatticeExtent) (Fm : CF) {L'' : PeriodicLatticeExtent} (t : Set (PeriodicLatticeSite L'') × ℕ × ℕ) : Prop :=
  ∃ (hLL : Covers L'' L) (sites0 : Set (PeriodicLatticeSite L)), (sites0, t.2.1, t.2.2) ∈ Fm L ∧ t.1 = projS hLL ⁻¹' sites0

def liftFam (L : PeriodicLatticeExtent) (Fm : CF) : CF := fun _ => {t | LiftMem L Fm t}

theorem mem_liftFam {L : PeriodicLatticeExtent} {Fm : CF} {L'' : PeriodicLatticeExtent} {s : Set (PeriodicLatticeSite L'')} {j f : ℕ} :
    (s, j, f) ∈ liftFam L Fm L'' ↔ ∃ (hLL : Covers L'' L) (sites0 : Set (PeriodicLatticeSite L)), (sites0, j, f) ∈ Fm L ∧
      s = projS hLL ⁻¹' sites0 := Iff.rfl

instance liftFam_ok {L : PeriodicLatticeExtent} {Fm : CF} [h : CubeFamOK Fm] : CubeFamOK (liftFam L Fm) :=
  ⟨fun L'' s j f hm => by
    obtain ⟨hLL, s0, hm0, -⟩ := (mem_liftFam).1 hm
    exact h.ge L s0 j f hm0⟩

/-- an embedding of the base torus into the covering torus (first fundamental domain), a section of `projS`. -/
def embedS {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (y : PeriodicLatticeSite L) : PeriodicLatticeSite Lt :=
  fun μ => ⟨(y μ).val, lt_of_lt_of_le (y μ).isLt (Nat.le_of_dvd (Nat.succ_pos _) (h μ))⟩

theorem projS_embedS {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (y : PeriodicLatticeSite L) :
    projS h (embedS h y) = y := by
  funext μ
  apply Fin.ext
  simp only [projS_val, embedS]
  exact Nat.mod_eq_of_lt (y μ).isLt

theorem mem_towerBj_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (S : Tower L) (j : ℕ) (x : PeriodicLatticeSite Lt) :
    x ∈ towerBj (liftTower h S) j ↔ projS h x ∈ towerBj S j := Iff.rfl

/-- the preimage of a class union under the covering map is a class union of the lifted tower. -/
theorem unionAt_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : UnionAt ell M k S sites j) :
    UnionAt ell M k (liftTower h S) (projS h ⁻¹' sites) j := by
  obtain ⟨hj, hbc, hsub, ⟨y, hy1, hy2⟩⟩ := hq
  refine ⟨hj, blockClosed_lift h _ (fun μ => hS.2.2.1 j hj μ) sites hbc, fun x hx => ?_, ⟨embedS h y, ?_, ?_⟩⟩
  · rcases hsub hx with hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
  · show projS h (embedS h y) ∈ sites
    rw [projS_embedS]; exact hy1
  · show projS h (embedS h y) ∈ towerBj S j
    rw [projS_embedS]; exact hy2

/-- converse: if the preimage is a class union of the lifted tower, so is the base set. -/
theorem unionAt_unlift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : UnionAt ell M k (liftTower h S) (projS h ⁻¹' sites) j) :
    UnionAt ell M k S sites j := by
  obtain ⟨hj, hbc, hsub, ⟨x, hx1, hx2⟩⟩ := hq
  have hs0 : 0 < bigSide M ell j := bigSide_pos hS hj
  refine ⟨hj, ?_, fun y hy => ?_, ⟨projS h x, hx1, hx2⟩⟩
  · intro y1 hy1 y2 hy2
    obtain ⟨w, hw1, hw2⟩ := exists_lift_in_block h (bigSide M ell j) hs0 (fun μ => hS.2.2.1 j hj μ) (embedS h y1) y2
      (fun μ => by rw [projS_embedS]; exact hy2 μ)
    have hm : w ∈ projS h ⁻¹' sites := hbc (embedS h y1) (by show projS h (embedS h y1) ∈ sites; rw [projS_embedS]; exact hy1) w hw2
    have : projS h w ∈ sites := hm
    rwa [hw1] at this
  · have hm : embedS h y ∈ projS h ⁻¹' sites := by show projS h (embedS h y) ∈ sites; rw [projS_embedS]; exact hy
    have := hsub hm
    rcases this with hh | hh
    · left; have : projS h (embedS h y) ∈ towerBj S j := hh
      rwa [projS_embedS] at this
    · right; have : projS h (embedS h y) ∈ towerBj S (j + 1) := hh
      rwa [projS_embedS] at this

theorem coversSites_liftQ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R k : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L} (hS : Admissible ell M R k S) 
    (hCov : CoversOmcQ ell M Fm k S) : CoversOmcQ ell M (liftFam L Fm) k (liftTower h S) := by
  intro x hx
  obtain ⟨C, j, ⟨c, hcΦ, hC⟩, hxC⟩ := hCov (projS h x) hx
  exact ⟨projS h ⁻¹' C, j, ⟨c, (mem_liftFam).2 ⟨h, C, hcΦ, rfl⟩,
    isClassUnion_of_unionAt (liftTower_mono h hS.1) (unionAt_lift h hS hC.1)⟩, hxC⟩

theorem cubeBond_of_preimage {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {C : Set (PeriodicLatticeSite L)}
    (e : Bond Lt) (he : CubeBond C (projE h e)) : CubeBond (projS h ⁻¹' C) e := by
  refine ⟨he.1, ?_⟩
  have := he.2
  show projS h (periodicLatticeShift e.1 e.2) ∈ C
  rw [projS_shift]; exact this

theorem coversPlaq_liftQ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R k : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L} (hS : Admissible ell M R k S) 
    (hCov : CoversPlaqQ ell M Fm k S) : CoversPlaqQ ell M (liftFam L Fm) k (liftTower h S) := by
  intro pt hpt
  obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := pt
  let p : PeriodicLatticePlaquette L := (projS h x, ⟨(μ, ν), hμν⟩)
  have hbd : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
    intro e he
    rw [edge_mem'] at he
    have m1 := cubeBond_om_lift h (hpt (x, μ) ((edge_mem' _ _).mpr (Or.inl rfl)))
    have m2 := cubeBond_om_lift h (hpt (periodicLatticeShift x μ, ν) ((edge_mem' _ _).mpr (Or.inr (Or.inl rfl))))
    have m3 := cubeBond_om_lift h (hpt (periodicLatticeShift x ν, μ) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))))
    have m4 := cubeBond_om_lift h (hpt (x, ν) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inr rfl)))))
    simp only [projE, projS_shift] at m1 m2 m3 m4
    rcases he with rfl | rfl | rfl | rfl
    · exact m1
    · exact m2
    · exact m3
    · exact m4
  obtain ⟨C, j, ⟨c, hcΦ, hC⟩, hall⟩ := hCov p hbd
  refine ⟨projS h ⁻¹' C, j, ⟨c, (mem_liftFam).2 ⟨h, C, hcΦ, rfl⟩,
    isClassUnion_of_unionAt (liftTower_mono h hS.1) (unionAt_lift h hS hC.1)⟩, ?_⟩
  intro e he
  rw [edge_mem'] at he
  have e1 := hall (projS h x, μ) ((edge_mem' _ _).mpr (Or.inl rfl))
  have e2 := hall (periodicLatticeShift (projS h x) μ, ν) ((edge_mem' _ _).mpr (Or.inr (Or.inl rfl)))
  have e3 := hall (periodicLatticeShift (projS h x) ν, μ) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have e4 := hall (projS h x, ν) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inr rfl))))
  rcases he with rfl | rfl | rfl | rfl
  · exact cubeBond_of_preimage h _ (by simpa [projE] using e1)
  · exact cubeBond_of_preimage h _ (by simpa [projE, projS_shift] using e2)
  · exact cubeBond_of_preimage h _ (by simpa [projE, projS_shift] using e3)
  · exact cubeBond_of_preimage h _ (by simpa [projE] using e4)

theorem cubeBond_preimage {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {C : Set (PeriodicLatticeSite L)}
    {e : Bond Lt} (he : CubeBond (projS h ⁻¹' C) e) : CubeBond C (projE h e) := by
  refine ⟨he.1, ?_⟩
  have := he.2
  show projS h e.1 |> fun y => periodicLatticeShift y e.2 ∈ C
  have h2 : projS h (periodicLatticeShift e.1 e.2) ∈ C := this
  rwa [projS_shift] at h2

theorem curlReads_preimage {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {C : Set (PeriodicLatticeSite L)}
    {x : PeriodicLatticeSite Lt} {a b : Fin 3} (hr : CurlReads (projS h ⁻¹' C) x a b) :
    CurlReads C (projS h x) a b := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have e1 := cubeBond_preimage h h1
  have e2 := cubeBond_preimage h h2
  have e3 := cubeBond_preimage h h3
  have e4 := cubeBond_preimage h h4
  simp only [projE, projS_shift] at e1 e2 e3 e4
  exact ⟨e1, e2, e3, e4⟩

theorem regBody_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M b : ℕ} {C : Set (PeriodicLatticeSite L)} {j : ℕ}
    {α₀ η : ℝ} {U : LinkCfg L} (hReg : RegBodyH ell M b C j α₀ η U) :
    RegBodyH ell M b (projS h ⁻¹' C) j α₀ η (liftU h U) := by
  obtain ⟨g, A, hA1, hA2, hA3⟩ := hReg
  refine ⟨fun x => g (projS h x), liftA h A, fun e he => ?_, fun μ ν x hx1 hx2 => ?_, fun μ x hx => ?_⟩
  · obtain ⟨c1, c2, c3⟩ := hA1 (projE h e) (cubeBond_preimage h he)
    refine ⟨c1, ?_, c3⟩
    rw [gauge_lift]; exact c2
  · have hx1' := cubeBond_preimage h hx1
    have hx2' := cubeBond_preimage h hx2
    simp only [projE, projS_shift] at hx1' hx2'
    have := hA2 μ ν (projS h x) hx1' hx2'
    simp only [liftA, projE, projS_shift]
    exact this
  · have := hA3 μ (projS h x) (fun ν hν => by
      have h1 := curlReads_preimage h (hx ν hν).1
      have h2 := curlReads_preimage h (hx ν hν).2
      rw [projS_shiftBack] at h1
      exact ⟨h1, h2⟩)
    rw [ddA_lift]; exact this

theorem perCube_liftHQ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M R b k : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} (hS : Admissible ell M R k S) (hU : PerCubeRegular2HQ ell M Fm b k S α₀ η U) :
    PerCubeRegular2HQ ell M (liftFam L Fm) b k (liftTower h S) α₀ η (liftU h U) := by
  intro f Ct j hmem hCt
  obtain ⟨hLL, sites0, hm0, rfl⟩ := (mem_liftFam).1 hmem
  exact regBody_lift h (hU f sites0 j hm0 (isClassUnion_of_unionAt hS.1 (unionAt_unlift h hS hCt.1)))

theorem classCoupled_liftHQ {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R b k : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (hS : Admissible ell M R k S)
    (hCU : ClassCoupledHQ ell M Fm b k S α₀ η U) :
    ClassCoupledHQ ell M (liftFam L Fm) b k (liftTower h S) α₀ η (liftU h U) :=
  ⟨⟨coversSites_liftQ h hstrict hS hCU.1.1, coversPlaq_liftQ h hstrict hS hCU.1.2⟩, perCube_liftHQ h hS hCU.2⟩

theorem geometry_liftHQ {ell M R b k : ℕ} {Fm : CF} [CubeFamOK Fm] {hell : 0 < ell} {Lut Lu : PeriodicLatticeExtent}
    (g : GeomLift ell k hell Lut Lu)
    (hT : TorusOK ell M Lu) {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam)
    {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hCU : ClassCoupledHQ ell M Fm b k S α₀ ((ell : ℝ) ^ k)⁻¹ U) :
    TorusOK ell M Lut ∧ Admissible ell M R k (liftTower g.fine S) ∧
      LambdaOK2 ell M R k (liftTower g.fine S) (projS g.cover ⁻¹' Lam) ∧
      ClassCoupledHQ ell M (liftFam (scaleUp ell k Lu) Fm) b k (liftTower g.fine S) α₀ ((ell : ℝ) ^ k)⁻¹ (liftU g.fine U) :=
  ⟨torusOK_lift g.cover hT, admissible_lift g.fine hS,
    ⟨lambdaOK_lift g.cover hell hT hL.1, lamBlockSum_lift g.cover hell hT.1 hL.2⟩,
    classCoupled_liftHQ g.fine (covers_scaleUp_strict ell k hell g.strict) hS hCU⟩

section reg
open AdalyFormal.ClassJets (ClassSmall ReadRow classRows_read classRows_unit)

theorem jetReg_of_classHQ {ell M R k bf : ℕ} {Fm : CF} [CubeFamOK Fm] {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : LinkCfg (scaleUp ell k Lu)} (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S)
    (hT : TorusOK ell M Lu) (hU : ClassCoupledHQ ell M Fm bf k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : ClassSmall ell ((bf : ℝ) * M * α₀)) :
    JetReg ell k S (UbarTower su2LogExp ell U) := by
  intro j hj b hb l e hr
  have hj1 : 1 ≤ j := by
    have := hr.1
    omega
  exact (UNI.ClassJets.classRows_readΦ hell hroom hS hT hU hsm hj1 hj hb hr).of_le (by exact_mod_cast le_top)

theorem unitReg_of_classHQ {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell M R k bf : ℕ} {Fm : CF} [CubeFamOK Fm] (hell0 : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) {α₀ : ℝ}
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M)
    (hS : Admissible ell M R k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S)) (hT : TorusOK ell M Lut)
    (hL : LambdaOK2 ell M R k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S) (phiS hu (fun _ => 0) ⁻¹' Lam))
    (hU : ClassCoupledHQ ell M Fm bf k (towerPull (covers_scaleUp ell k hell0 hu) (fun _ => 0) S) α₀ ((ell : ℝ) ^ k)⁻¹
      (pullCfg (covers_scaleUp ell k hell0 hu) (fun _ => 0) U))
    (hsm : ClassSmall ell ((bf : ℝ) * M * α₀)) :
    UnitReg hu hell0 S U a Lam := by
  intro cb hc
  exact (UNI.ClassJets.classRows_unitΦ hell0 hell hk hroom hS hT hL hU hsm cb hc).of_le (by exact_mod_cast le_top)

end reg

end UNI.Thin

#print axioms UNI.Thin.geometry_liftHQ
#print axioms UNI.Thin.jetReg_of_classHQ
#print axioms UNI.Thin.unitReg_of_classHQ
