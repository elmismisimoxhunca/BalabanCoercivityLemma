import D1Main
import NV7

/-!
# D1Final -- the literal (all-plaquette) reading of the r8 headline is FALSE.
`not_P428Target8S_selAll : ¬ P428Target8S selAll sJ` for every `sJ` (in particular `¬ P428Target8Literal` and `¬ P428Target8LiteralDelta`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NonVac
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)

theorem frobNorm_zero' : frobNorm (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  unfold frobNorm frobSq; simp

theorem om_sub_om0 {L : PeriodicLatticeExtent} (S : Tower L) (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) :
    ∀ i, S.Om i ⊆ S.Om 0
  | 0 => le_rfl
  | (i + 1) => (hS i).trans (om_sub_om0 S hS i)

theorem classCube_sub_om0 {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (h : IsClassCube ell M f k S sites j) : sites ⊆ S.Om 0 := by
  intro x hx
  rcases h.1.2.2.1 hx with h1 | h1
  · exact om_sub_om0 S hS j h1.1
  · exact om_sub_om0 S hS (j + 1) h1.1

/-- **the class is blind off `Ω₀`** (port of `statement_audit_r5_opus/PXClassFree.lean`): `U = 1` on the bonds based in `Ω₀` ⇒ in `PerCubeRegular2` for every `α₀ > 0`. -/
theorem perCubeRegular2_of_one_on_om0 {L : PeriodicLatticeExtent} {ell M f k : ℕ} (S : Tower L)
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) {α₀ η : ℝ} (hα : 0 < α₀) (hM : 0 < M) (hf : 0 < f)
    (hell : 0 < ell) (hη : 0 < η) (U : LinkCfg L)
    (hU : ∀ e : Bond L, e.1 ∈ S.Om 0 → periodicLatticeShift e.1 e.2 ∈ S.Om 0 → U e = 1) :
    PerCubeRegular2 ell M f k S α₀ η U := by
  intro sites j hq
  have hsub := classCube_sub_om0 hS hq
  have hpos : ∀ n : ℕ, 0 < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ n) := by
    intro n
    have : (0 : ℝ) < (ell : ℝ) ^ j * η := mul_pos (pow_pos (by exact_mod_cast hell) j) hη
    have hf' : (0 : ℝ) < f := by exact_mod_cast hf
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  refine ⟨fun _ => 1, fun _ => 0, ?_, ?_, ?_⟩
  · intro e he
    refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
    · have h1 : U e = 1 := hU e (hsub he.1) (hsub he.2)
      simp [periodicGaugeTransform, h1]
    · simpa [frobNorm_zero'] using hpos 1
  · intro μ ν x _ _
    simpa [frobNorm_zero'] using hpos 2
  · intro μ x _
    have h0 : ddA η (fun _ => (0 : Matrix (Fin 2) (Fin 2) ℂ)) x μ = 0 := by
      unfold ddA curlA; simp
    rw [h0, frobNorm_zero']
    exact hpos 3

#print axioms perCubeRegular2_of_one_on_om0

/-- the NV slab tower (k = 2). -/
noncomputable def SlabNv (ell M R : ℕ) : Tower (scaleUp ell 2 (nvLu M R)) :=
  slab3 (scaleUp ell 2 (nvLu M R)) (nvP0 ell M R) (nvQ0 ell M R) (nvP1 ell M R) (nvQ1 ell M R) (nvP2 ell M R) (nvQ2 ell M R)

theorem SlabNv_bdpt {ell M R : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 18 ≤ R) :
    ∃ x : PeriodicLatticeSite (scaleUp ell 2 (nvLu M R)), BdPt ((SlabNv ell M R).Om 0) x := by
  have hell0 : 0 < ell := by omega
  have G := slabGeo_inst hell hM hdvd (show 1 ≤ R by omega)
  have g1 := G.nest01; have g2 := G.nest12; have g3 := G.nestw; have g4 := G.nest21; have g5 := G.nest10
  have g6 := G.QN
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths hell hM hR
  have hN : ∀ μ, scaleUp ell 2 (nvLu M R) μ + 1 = nvN ell M R := fun μ => scaleUp_nv hell0 hM μ
  have hN1 : 1 < nvN ell M R := by omega
  have hQ : nvQ0 ell M R - 1 < nvN ell M R := by omega
  refine ⟨siteAt0 (R := R) hell0 hM (nvQ0 ell M R - 1) hQ, ?_⟩
  have hv := siteAt0_val (R := R) hell0 hM (nvQ0 ell M R - 1) hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · show _ ∈ (slab3 _ _ _ _ _ _ _).Om 0
    rw [om0_mem, hv]; omega
  · show ¬ (periodicLatticeShift _ 0) ∈ (slab3 _ _ _ _ _ _ _).Om 0
    rw [om0_mem, shift_val_N hN hN1, if_pos rfl, hv, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro z ν hν
    show periodicLatticeShift z ν ∈ (slab3 _ _ _ _ _ _ _).Om 0 ↔ z ∈ (slab3 _ _ _ _ _ _ _).Om 0
    rw [om0_mem, om0_mem, adj_shift_coord_N hN hN1 z (Ne.symm hν)]
  · intro ν hxe
    have h1 := congrArg (fun y : PeriodicLatticeSite (scaleUp ell 2 (nvLu M R)) => (y ν).val) hxe
    rw [shift_val_N hN hN1, if_pos rfl] at h1
    have hx : ((siteAt0 (R := R) hell0 hM (nvQ0 ell M R - 1) hQ) ν).val < nvN ell M R := by
      have := ((siteAt0 (R := R) hell0 hM (nvQ0 ell M R - 1) hQ) ν).isLt
      have e := hN ν
      omega
    generalize ((siteAt0 (R := R) hell0 hM (nvQ0 ell M R - 1) hQ) ν).val = w at h1 hx
    rcases Nat.lt_or_ge (w + 1) (nvN ell M R) with h | h
    · rw [Nat.mod_eq_of_lt h] at h1; omega
    · have : w + 1 = nvN ell M R := by omega
      rw [this, Nat.mod_self] at h1
      omega


/-- **THE LITERAL READING IS FALSE.**  For every choice `sJ` of the plaquette set in `J`, the headline with `Δ` summed over ALL plaquettes of the torus is refuted
(`ell = 2`, `a = 1`).  The proof instantiates the headline at `m := m₀` and `R := max R₀ 18` (the point-level argument `exists_nonunit_Ginv` + `SlabNv_bdpt` works for every `m ≥ 1`, `R ≥ 18`);
tower: the NV three-stratum slab, `k = 2`; in-class configuration: `U_θ` equal to `diag(e^{iθ}, e^{-iθ})` on the bonds with no endpoint in `Ω₀`, identity elsewhere, `θ` the IVT point at which the literal `Ginv` is not a unit
(so the printed `G = Ginv⁻¹` of (3.122) does not exist there and `genForm` takes the `Ring.inverse` junk value `-a‖B‖²`). -/
theorem not_P428Target8S_selAll (sJ : PlaqSel) : ¬ P428Target8S selAll sJ := by
  intro h
  obtain ⟨m₀, hm₀, hm⟩ := h 2 le_rfl 1 one_pos
  obtain ⟨R₀, hR₀⟩ := hm m₀ le_rfl
  have hRge : R₀ ≤ max R₀ 18 := le_max_left _ _
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₀ (max R₀ 18) hRge
  obtain ⟨R, hRdef⟩ : ∃ R, R = max R₀ 18 := ⟨_, rfl⟩
  rw [← hRdef] at hcore
  have hR18 : 18 ≤ R := by rw [hRdef]; exact le_max_right _ _
  obtain ⟨M, hMdef⟩ : ∃ M, M = 2 ^ m₀ := ⟨_, rfl⟩
  rw [← hMdef] at hcore
  have hM : 0 < M := by rw [hMdef]; exact pow_pos (by norm_num) m₀
  have hM2 : 2 ≤ M := by
    rw [hMdef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m₀ := Nat.pow_le_pow_right (by norm_num) hm₀
  have hdvd : 2 ∣ M := by rw [hMdef]; exact dvd_pow_self 2 (by omega)
  have hell : 2 ≤ 2 := le_rfl
  have hell0 : 0 < 2 := by norm_num
  have G := slabGeo_inst (ell := 2) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := 2) hell hM hR18
  have hN : ∀ μ, scaleUp 2 2 (nvLu M R) μ + 1 = nvN 2 M R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible 2 M R 2 (SlabNv 2 M R) := slab3_admissible G hN
  have hcov : CoversOm0p 2 M 12 2 (SlabNv 2 M R) := slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  obtain ⟨x, hbd⟩ := SlabNv_bdpt hell hdvd hM hR18
  have hroom : 17 * 2 ≤ R * M := by nlinarith
  obtain ⟨θ, h0, h1, hnu⟩ := exists_nonunit_Ginv sJ (ell := 2) (M := M) (R := R) (k := 2) (Lu := nvLu M R) hell0
    (S := SlabNv 2 M R) 1 (LamN M R) hAdm hell hroom hbd (by norm_num) (by norm_num)
  -- the smallness parameter `α₀`
  obtain ⟨α₀, hα0def⟩ : ∃ α₀ : ℝ, α₀ = min (a₀ / (12 * M)) 1 / 2 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hα0 : 0 < α₀ := by
    rw [hα0def]
    have : 0 < a₀ / (12 * (M : ℝ)) := by positivity
    have := lt_min this one_pos; positivity
  have hαS : (12 : ℝ) * M * α₀ ≤ a₀ := by
    rw [hα0def]
    have h := min_le_left (a₀ / (12 * (M : ℝ))) 1
    have h2 : (12 : ℝ) * M * (a₀ / (12 * M)) = a₀ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 12 * M)
    have h0 : 0 ≤ min (a₀ / (12 * (M : ℝ))) 1 := le_min (by positivity) zero_le_one
    nlinarith
  have hcls : ClassCoupled 2 M 12 2 (SlabNv 2 M R) α₀ ((((2 : ℕ) : ℝ)) ^ 2)⁻¹ (Uth ((SlabNv 2 M R).Om 0) θ) :=
    ⟨hcov, perCubeRegular2_of_one_on_om0 _ hAdm.1 hα0 hM (by norm_num) hell0 (by positivity) _
      (fun e he _ => Uth_in _ _ e he)⟩
  have hineq := hcore 2 (by norm_num) (nvLu M R) α₀ hα0 (by simpa using hαS) (torusOK_nv hell hdvd hM)
    (SlabNv 2 M R) hAdm (LamN M R) (lambdaOK2_nv hell hdvd hM (show 1 ≤ R by omega)) (Uth ((SlabNv 2 M R).Om 0) θ) hcls
  obtain ⟨hB1, hB2, hB3, hB4⟩ := BseedNv_props (R := R) hell hdvd hM
  exact not_InstIneqS_of_not_unit selAll sJ 2 2 hell0 1 zero_le_one (nvLu M R) γ₀ hγ (SlabNv 2 M R) (LamN M R)
    (Uth ((SlabNv 2 M R).Om 0) θ) hnu _ hB1 hB2 hB3 hineq

theorem not_P428Target8Literal : ¬ P428Target8Literal := not_P428Target8S_selAll selAll
theorem not_P428Target8LiteralDelta : ¬ P428Target8LiteralDelta := not_P428Target8S_selAll selIn

#print axioms not_P428Target8S_selAll
#print axioms not_P428Target8Literal
#print axioms not_P428Target8LiteralDelta

end AdalyFormal.D1Literal
