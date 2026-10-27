import ZStatementP428
import ZR2A
import ZR6A
import ZR2Ops2
import AdalyFormal.Target.ClayStatement
import D1Final

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.NonVac
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Fidelity.S1

def TouchBond {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∨ periodicLatticeShift b.1 b.2 ∈ sites

def plaqCorner {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L)) :
    Set (PeriodicLatticePlaquette L) :=
  {p | p.1 ∈ S
    ∨ periodicLatticeShift p.1 p.2.1.1 ∈ S
    ∨ periodicLatticeShift p.1 p.2.1.2 ∈ S
    ∨ periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S}

def ReadBond {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  ∃ p : PeriodicLatticePlaquette L, p ∈ plaqCorner sites ∧ b ∈ periodicPlaquetteBoundaryEdges p

def CurlReadsRead {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (a b : Fin 3) : Prop :=
  ReadBond sites (periodicLatticeShift x a, b) ∧ ReadBond sites (x, b) ∧
  ReadBond sites (periodicLatticeShift x b, a) ∧ ReadBond sites (x, a)

def PerCubeRegularShell {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j →
    ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ e : Bond L, ReadBond sites e →
        HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
      (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
        ReadBond sites ((x, ν) : Bond L) → ReadBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
        frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
      (∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
        (∀ ν : Fin 3, ν ≠ μ → CurlReadsRead sites (periodicLatticeShiftBack x ν) ν μ ∧
          CurlReadsRead sites x ν μ) →
        frobNorm (ddA η A x μ)
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

def ClassCoupledShell {L : PeriodicLatticeExtent} (ell M c k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0p ell M c k S ∧ PerCubeRegularShell ell M c k S α₀ η U

def L6 : PeriodicLatticeExtent := fun _ => 5

def slab6 : Set (PeriodicLatticeSite L6) :=
  {x | (x 0).val < 2}

lemma cubeBond_readBond
    {L : PeriodicLatticeExtent} {sites : Set (PeriodicLatticeSite L)}
    {e : Bond L} : CubeBond sites e → ReadBond sites e := by
  classical
  intro he
  rcases e with ⟨x, μ⟩
  by_cases h : μ = 0
  · subst μ
    refine ⟨(x, ⟨(0, 1), by decide⟩), Or.inl he.1, ?_⟩
    simp [periodicPlaquetteBoundaryEdges]
  · have hμ : (0 : Fin 3) < μ := by omega
    refine ⟨(x, ⟨(0, μ), hμ⟩), Or.inl he.1, ?_⟩
    simp [periodicPlaquetteBoundaryEdges]

lemma perCubeRegularShell_toFrozen
    {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} :
    PerCubeRegularShell ell M f k S α₀ η U →
      PerCubeRegular2 ell M f k S α₀ η U := by
  intro h sites j hq
  obtain ⟨g, A, hA, hD, hC⟩ := h sites j hq
  refine ⟨g, A, ?_, ?_, ?_⟩
  · intro e he
    exact hA e (cubeBond_readBond he)
  · intro μ ν x hx hy
    exact hD μ ν x (cubeBond_readBond hx) (cubeBond_readBond hy)
  · intro μ x hx
    apply hC μ x
    have transfer : ∀ y a b, CurlReads sites y a b → CurlReadsRead sites y a b := by
      intro y a b hh
      exact ⟨cubeBond_readBond hh.1, cubeBond_readBond hh.2.1,
        cubeBond_readBond hh.2.2.1, cubeBond_readBond hh.2.2.2⟩
    intro ν hν
    exact ⟨transfer _ _ _ (hx ν hν).1, transfer _ _ _ (hx ν hν).2⟩

lemma classCoupledShell_toFrozen
    {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} :
    ClassCoupledShell ell M c k S α₀ η U →
      ClassCoupled ell M c k S α₀ η U := by
  intro h
  exact ⟨h.1, perCubeRegularShell_toFrozen h.2⟩

lemma classCoupledShell_one
    {L : PeriodicLatticeExtent} {ell M c k : ℕ} (S : Tower L)
    {α₀ η : ℝ} (hell : 0 < ell) (hM : 0 < M) (hc : 0 < c)
    (hα : 0 < α₀) (hη : 0 < η)
    (hcov : CoversOm0p ell M c k S) :
    ClassCoupledShell ell M c k S α₀ η (fun _ => 1) := by
  refine ⟨hcov, ?_⟩
  intro sites j hq
  have hpos : ∀ n : ℕ, 0 < (c : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ n) := by
    intro n
    have : (0 : ℝ) < (ell : ℝ) ^ j * η := mul_pos (pow_pos (by exact_mod_cast hell) j) hη
    have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  refine ⟨fun _ => 1, fun _ => 0, ?_, ?_, ?_⟩
  · intro e he
    refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
    · simp [periodicGaugeTransform]
    · simpa [frobNorm_zero'] using hpos 1
  · intro μ ν x _ _
    simpa [frobNorm_zero'] using hpos 2
  · intro μ x _
    have h0 : ddA η (fun _ => (0 : Matrix (Fin 2) (Fin 2) ℂ)) x μ = 0 := by
      unfold ddA curlA
      simp
    rw [h0, frobNorm_zero']
    exact hpos 3

lemma shell_slab_nonvacuous
    (M R : ℕ) (hM : 0 < M) (hdvd : 2 ∣ M) (hR : 18 ≤ R)
    (a₀ : ℝ) (ha₀ : 0 < a₀) :
    TorusOK 2 M (nvLu M R) ∧
    Admissible 2 M R 2 (SlabNv 2 M R) ∧
    LambdaOK2 2 M R 2 (SlabNv 2 M R) (LamN M R) ∧
    ((SlabNv 2 M R).Om 0).Nonempty ∧
    (SlabNv 2 M R).Om 0 ≠ Set.univ ∧
    ∃ α₀ : ℝ, 0 < α₀ ∧ (12 : ℝ) * (M : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupledShell 2 M 12 2 (SlabNv 2 M R)
        α₀ (((2 : ℝ) ^ 2)⁻¹) (fun _ => 1) := by
  have G := slabGeo_inst (ell := 2) le_rfl hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := 2) le_rfl hM hR
  have hN : ∀ μ, scaleUp 2 2 (nvLu M R) μ + 1 = nvN 2 M R := fun μ => scaleUp_nv (by norm_num) hM μ
  have hAdm : Admissible 2 M R 2 (SlabNv 2 M R) := slab3_admissible G hN
  have hcov : CoversOm0p 2 M 12 2 (SlabNv 2 M R) := slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  obtain ⟨x, hbd⟩ := SlabNv_bdpt (ell := 2) le_rfl hdvd hM hR
  refine ⟨torusOK_nv le_rfl hdvd hM, hAdm,
    lambdaOK2_nv le_rfl hdvd hM (by omega), ⟨x, hbd.1⟩, ?_, ?_⟩
  · intro heq
    exact hbd.hx' (heq ▸ Set.mem_univ _)
  · have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have hα : 0 < a₀ / (12 * (M : ℝ)) := by positivity
    refine ⟨a₀ / (12 * (M : ℝ)), hα, ?_, ?_⟩
    · exact le_of_eq (mul_div_cancel₀ a₀ (by positivity : (12 : ℝ) * M ≠ 0))
    · exact classCoupledShell_one _ (by norm_num) hM (by norm_num) hα (by positivity) hcov

lemma readBond_not_touchBond_slab6 :
    ∃ e : Bond L6, ReadBond slab6 e ∧ ¬ TouchBond slab6 e := by
  classical
  let x : PeriodicLatticeSite L6 := fun μ => if μ = 0 then 1 else 0
  let y := periodicLatticeShift x 0
  refine ⟨(y, 1), ⟨(x, ⟨(0, 1), by decide⟩), ?_, ?_⟩, ?_⟩
  · exact Or.inl (by norm_num [slab6, x, L6])
  · simp [periodicPlaquetteBoundaryEdges, y]
  · change ¬ ((y 0).val < 2 ∨ ((periodicLatticeShift y 1) 0).val < 2)
    decide

lemma no_plaqIn_eq_plaqCorner_slab6 :
    ¬ ∃ T : Set (PeriodicLatticeSite L6),
      plaqIn T = plaqCorner slab6 := by
  classical
  rintro ⟨T, hT⟩
  have face : ∀ x : PeriodicLatticeSite L6, x 0 = 2 → x ∈ T := by
    intro x hx
    let y : PeriodicLatticeSite L6 := Function.update x 0 1
    have hy : periodicLatticeShift y 0 = x := by
      funext μ
      by_cases hμ : μ = 0
      · subst μ
        change (1 : Fin 6) + 1 = x 0
        exact hx.symm
      · simp [periodicLatticeShift, y, hμ]
    have hp : (y, ⟨(0, 1), by decide⟩) ∈ plaqIn T := by
      rw [hT]
      exact Or.inl (by norm_num [slab6, y, L6])
    have he := hp (y, 0) (by simp [periodicPlaquetteBoundaryEdges])
    simpa [hy] using he.2
  let x : PeriodicLatticeSite L6 := fun μ => if μ = 0 then 2 else 0
  let p : PeriodicLatticePlaquette L6 := (x, ⟨(1, 2), by decide⟩)
  have hp : p ∈ plaqIn T := by
    intro e he
    simp only [p, periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      constructor <;> apply face <;> decide
  have hn : p ∉ plaqCorner slab6 := by
    change ¬ ((x 0).val < 2 ∨ ((periodicLatticeShift x 1) 0).val < 2 ∨
      ((periodicLatticeShift x 2) 0).val < 2 ∨
      ((periodicLatticeShift (periodicLatticeShift x 1) 2) 0).val < 2)
    decide
  exact hn (hT ▸ hp)

end Fidelity.S1

#print axioms Fidelity.S1.cubeBond_readBond
#print axioms Fidelity.S1.perCubeRegularShell_toFrozen
#print axioms Fidelity.S1.classCoupledShell_toFrozen
#print axioms Fidelity.S1.classCoupledShell_one
#print axioms Fidelity.S1.shell_slab_nonvacuous
#print axioms Fidelity.S1.readBond_not_touchBond_slab6
#print axioms Fidelity.S1.no_plaqIn_eq_plaqCorner_slab6
