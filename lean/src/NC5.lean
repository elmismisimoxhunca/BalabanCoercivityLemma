import NC4
import NC1

/-!
# NC5 -- the class gap in the headline regime (lane nocover_20261015)

`nc_class_gap`: for every `ell ≥ 3`, `m ≥ 1`, `R ≥ 1` (so in particular for all `m ≥ m₀`, `R ≥ R₀`, whatever the thresholds), with
`M = ell^m`, there are a unit torus, an admissible height-1 tower, `Λ ≠ ∅` with `LambdaOK2`, a nonzero `B̃ ∈ Λ̃`, and a site `x*` of `Ω₀`
such that
* `x*` lies in NO class cube of factor 12, so `CoversOm0p` fails and `ClassCoupled` is unsatisfiable on this tower (the r8 headline is
  vacuous here), while
* the coverage-free class `PerCubeRegular2 .. 12 ..` leaves the link `b* = (x*, 1)` completely free: `1` with `b*` set to ANY
  `v ∈ SU(2)` is in the class for every `α₀ > 0`, and every class member stays in the class when `b*` is changed;
* the plaquette `p* = (x*; 0, 1)` has `b*` as a boundary bond, lies in `plaqIn Ω₀` (so the operators `Δ` (3.10) and `J` (3.11) of the
  headline's `genForm` read it), and its holonomy for `v = -1` is `-1`.
Hence every hypothesis of `CoercG8AtNC` (NC1) holds at `(S, Λ, 1[b* ↦ v])` for all `v`, including configurations whose curvature on a
plaquette read by the operators is maximal.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NoCover

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 (plaqIn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVac (shift_val_N)

/-- the uncovered site `x*`: `x*₀ = P1' + 12 M`, other coordinates `0`. -/
def xsNc (ell M R : ℕ) (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : PeriodicLatticeSite (scaleUp ell 1 (ncLu M R)) :=
  fun μ => ⟨if μ = 0 then ncP1' ell M R + 12 * M else 0, by
    have h := nc_scaleUp (ell := ell) (R := R) (by omega) hM μ
    obtain ⟨l1, l2, l3, l4⟩ := nc_lin hell hM hR
    obtain ⟨e1, e2, e3, e4, e5⟩ := nc_expand ell M R
    split_ifs <;> omega⟩

theorem xsNc_val0 {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    ((xsNc ell M R hell hM hR) 0).val = ncP1' ell M R + 12 * M := by simp [xsNc]

/-- the plaquette `p* = (x*; 0, 1)`. -/
def pStar {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) : PeriodicLatticePlaquette L :=
  (x, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩)

theorem bStar_mem {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) :
    ((x, 1) : Bond L) ∈ periodicPlaquetteBoundaryEdges (pStar x) := by
  simp [periodicPlaquetteBoundaryEdges, pStar]

theorem pStar_plaqIn {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    pStar (xsNc ell M R hell hM hR) ∈ plaqIn ((ncS ell M R).Om 0) := by
  obtain ⟨l1, l2, l3, l4⟩ := nc_lin hell hM hR
  obtain ⟨e1, e2, e3, e4, e5⟩ := nc_expand ell M R
  have hN := nc_scaleUp (ell := ell) (R := R) (by omega) hM
  have hN1 : 1 < ncN ell M R := by rw [e5]; omega
  have hx0 := xsNc_val0 hell hM hR
  set x := xsNc ell M R hell hM hR
  have memJ : ∀ y : PeriodicLatticeSite (scaleUp ell 1 (ncLu M R)),
      ((y 0).val = (x 0).val ∨ (y 0).val = (x 0).val + 1) → y ∈ (ncS ell M R).Om 0 := by
    intro y hy
    rw [ncS_om0]
    right
    simp only [ncP0', ncQ0']
    rcases hy with h | h <;> rw [h, hx0] <;> constructor <;> omega
  have s0 : ∀ y : PeriodicLatticeSite (scaleUp ell 1 (ncLu M R)), (y 0).val = (x 0).val →
      ((periodicLatticeShift y 0) 0).val = (x 0).val + 1 := by
    intro y hy
    rw [shift_val_N hN hN1, if_pos rfl, hy, hx0, Nat.mod_eq_of_lt (by omega)]
  have s1 : ∀ y : PeriodicLatticeSite (scaleUp ell 1 (ncLu M R)),
      ((periodicLatticeShift y 1) 0).val = (y 0).val := by
    intro y
    rw [shift_val_N hN hN1, if_neg (by decide)]
  intro e he
  simp only [periodicPlaquetteBoundaryEdges, pStar, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨memJ _ (Or.inl rfl), memJ _ (Or.inr (s0 x rfl))⟩
  · exact ⟨memJ _ (Or.inr (s0 x rfl)), memJ _ (Or.inr (by rw [s1, s0 x rfl]))⟩
  · exact ⟨memJ _ (Or.inl (s1 x)), memJ _ (Or.inr (s0 _ (s1 x)))⟩
  · exact ⟨memJ _ (Or.inl rfl), memJ _ (Or.inl (s1 x))⟩

theorem xsNc_om0 {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    xsNc ell M R hell hM hR ∈ (ncS ell M R).Om 0 := by
  obtain ⟨l1, l2, l3, l4⟩ := nc_lin hell hM hR
  obtain ⟨e1, e2, e3, e4, e5⟩ := nc_expand ell M R
  rw [ncS_om0, xsNc_val0]
  right
  simp only [ncP0', ncQ0']
  constructor <;> omega

theorem xsNc_uncovered {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (sites : Set (PeriodicLatticeSite (scaleUp ell 1 (ncLu M R)))) (j : ℕ)
    (hq : IsClassCube ell M 12 1 (ncS ell M R) sites j) : xsNc ell M R hell hM hR ∉ sites :=
  tw2_uncovered (nc_thin hell hM hR) (nc_scaleUp (by omega) hM) _ (xsNc_val0 hell hM hR) sites j hq

theorem nc_not_covers {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    ¬ CoversOm0p ell M 12 1 (ncS ell M R) := by
  intro h
  obtain ⟨sites, j, hq, hx⟩ := h.1 _ (xsNc_om0 hell hM hR)
  exact xsNc_uncovered hell hM hR sites j hq hx

/-- **the class gap in the headline regime.** -/
theorem nc_class_gap {ell m R : ℕ} (hell : 3 ≤ ell) (hm : 1 ≤ m) (hR : 1 ≤ R) :
    ∃ (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell 1 Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (Bt : Bond Lu → SuTwo) (x : PeriodicLatticeSite (scaleUp ell 1 Lu)),
      TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R 1 S ∧ LambdaOK2 ell (ell ^ m) R 1 S Lam ∧ Lam.Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧
      x ∈ S.Om 0 ∧
      (∀ (sites : Set (PeriodicLatticeSite (scaleUp ell 1 Lu))) (j : ℕ), IsClassCube ell (ell ^ m) 12 1 S sites j → x ∉ sites) ∧
      ¬ CoversOm0p ell (ell ^ m) 12 1 S ∧
      (∀ (α₀ η : ℝ) (U : LinkCfg (scaleUp ell 1 Lu)), ¬ ClassCoupled ell (ell ^ m) 12 1 S α₀ η U) ∧
      (∀ α₀ : ℝ, 0 < α₀ → ∀ v : Matrix.specialUnitaryGroup (Fin 2) ℂ,
        PerCubeRegular2 ell (ell ^ m) 12 1 S α₀ ((ell : ℝ) ^ 1)⁻¹ (Function.update (fun _ => 1) ((x, 1) : Bond _) v)) ∧
      (∀ (α₀ η : ℝ) (U : LinkCfg (scaleUp ell 1 Lu)), PerCubeRegular2 ell (ell ^ m) 12 1 S α₀ η U →
        ∀ v : Matrix.specialUnitaryGroup (Fin 2) ℂ,
          PerCubeRegular2 ell (ell ^ m) 12 1 S α₀ η (Function.update U ((x, 1) : Bond _) v)) ∧
      pStar x ∈ plaqIn (S.Om 0) ∧ ((x, 1) : Bond _) ∈ periodicPlaquetteBoundaryEdges (pStar x) ∧
      periodicPlaquetteHolonomy (Function.update (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) ((x, 1) : Bond _) negOne)
        (pStar x) = negOne := by
  have hell0 : 0 < ell := by omega
  have hM : 0 < ell ^ m := pow_pos hell0 m
  have hdvd : ell ∣ ell ^ m := dvd_pow_self ell (by omega)
  obtain ⟨Bp1, Bp2, Bp3, -⟩ := BseedNc_props (R := R) hell hdvd hM
  have hunc := xsNc_uncovered (R := R) hell hM hR
  have hN := nc_scaleUp (ell := ell) (R := R) hell0 hM
  have hN1 : 1 < ncN ell (ell ^ m) R := by
    obtain ⟨l1, l2, l3, l4⟩ := nc_lin hell hM hR
    obtain ⟨e1, e2, e3, e4, e5⟩ := nc_expand ell (ell ^ m) R
    rw [e5]; omega
  refine ⟨ncLu (ell ^ m) R, ncS ell (ell ^ m) R, ncLam (ell ^ m) R, BseedNc (R := R) ell hM, xsNc ell (ell ^ m) R hell hM hR,
    torusOK_nc hell hdvd hM, nc_admissible hell hM hR, lambdaOK2_nc hell hdvd hM hR, ncLam_nonempty hM, Bp1, Bp2, Bp3,
    xsNc_om0 hell hM hR, hunc, nc_not_covers hell hM hR, fun α₀ η U h => nc_not_covers hell hM hR h.1, ?_, ?_,
    pStar_plaqIn hell hM hR, bStar_mem _, hol_update_negOne hN hN1 _⟩
  · intro α₀ hα v
    have hη : (0 : ℝ) < ((ell : ℝ) ^ 1)⁻¹ := by positivity
    exact perCube_update (perCube_one hell0 hM (by norm_num) hα hη) _ (fun sites j hq => hunc sites j hq) v
  · intro α₀ η U hU v
    exact perCube_update hU _ (fun sites j hq => hunc sites j hq) v

#print axioms pStar_plaqIn
#print axioms xsNc_uncovered
#print axioms nc_not_covers
#print axioms nc_class_gap

end AdalyFormal.NoCover
