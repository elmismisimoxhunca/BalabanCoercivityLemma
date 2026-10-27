import NC3
import NV6

/-!
# NC4 -- the instance, in the headline regime: `k = 1`, every `ell ≥ 3`, `M` with `ell ∣ M` (so every `M = ell^m`, `m ≥ 1`), every
`R ≥ 1` (lane nocover_20261015)

Unit torus side `N_u = M (5R+17)` per direction (`ncLu`), fine side `N = ell N_u`.  With `B = R M`:
* `Ω₁ = [ell(B+M), ell(3B+4M)) ∪ [ell(4B+5M), ell(4B+16M))` (thick component, then a THIN one of width `11 M ell`),
* `Ω₀ = Ω₁` widened by `R M` on each side of each component,
* `Λ = {M(2R+2) ≤ y₀ < M(2R+3)}` on the unit torus (inside the thick component, collar `> R M`),
* the site `x*` with `x*₀ = ell(4B+5M) + 12 M` (in the thin component), and the bond `b* = (x*, 1)`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NoCover

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.FullReparamC (freeBond freeBond_not_mem_staircase freeBond_not_dropped freeBond_coord_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVac (pcd_gt_right2 pcd_gt_left2 iv_iff shift_val_N)

/-! ## numbers -/

def ncNu (M R : ℕ) : ℕ := M * (5 * R + 17)
def ncLu (M R : ℕ) : PeriodicLatticeExtent := fun _ => ncNu M R - 1
def ncP1 (ell M R : ℕ) : ℕ := ell * (R * M + M)
def ncQ1 (ell M R : ℕ) : ℕ := ell * (3 * (R * M) + 4 * M)
def ncP1' (ell M R : ℕ) : ℕ := ell * (4 * (R * M) + 5 * M)
def ncQ1' (ell M R : ℕ) : ℕ := ell * (4 * (R * M) + 16 * M)
def ncP0 (ell M R : ℕ) : ℕ := ncP1 ell M R - R * M
def ncQ0 (ell M R : ℕ) : ℕ := ncQ1 ell M R + R * M
def ncP0' (ell M R : ℕ) : ℕ := ncP1' ell M R - R * M
def ncQ0' (ell M R : ℕ) : ℕ := ncQ1' ell M R + R * M
def ncN (ell M R : ℕ) : ℕ := ell * (5 * (R * M) + 17 * M)

/-- the tower on the fine torus. -/
def ncS (ell M R : ℕ) : Tower (scaleUp ell 1 (ncLu M R)) :=
  tw2 _ (ncP0 ell M R) (ncQ0 ell M R) (ncP1 ell M R) (ncQ1 ell M R) (ncP0' ell M R) (ncQ0' ell M R) (ncP1' ell M R) (ncQ1' ell M R)

theorem ncNu_pos {M R : ℕ} (hM : 0 < M) : 0 < ncNu M R := Nat.mul_pos hM (by omega)

theorem ncLu_succ {M R : ℕ} (hM : 0 < M) (μ : Fin 3) : ncLu M R μ + 1 = ncNu M R := by
  have := ncNu_pos (R := R) hM; simp only [ncLu]; omega

theorem nc_scaleUp {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) (μ : Fin 3) :
    scaleUp ell 1 (ncLu M R) μ + 1 = ncN ell M R := by
  have h1 := ncLu_succ (R := R) hM μ
  have hN : ncN ell M R = ncNu M R * ell := by simp only [ncN, ncNu]; ring
  have : 0 < ncNu M R * ell := Nat.mul_pos (ncNu_pos hM) hell
  simp only [scaleUp, h1, pow_one]; omega

theorem ncS_om0 {ell M R : ℕ} (x : PeriodicLatticeSite (scaleUp ell 1 (ncLu M R))) :
    x ∈ (ncS ell M R).Om 0 ↔ (ncP0 ell M R ≤ (x 0).val ∧ (x 0).val < ncQ0 ell M R) ∨
      (ncP0' ell M R ≤ (x 0).val ∧ (x 0).val < ncQ0' ell M R) := tw2_om0 x

theorem ncS_om1 {ell M R : ℕ} (x : PeriodicLatticeSite (scaleUp ell 1 (ncLu M R))) :
    x ∈ (ncS ell M R).Om 1 ↔ (ncP1 ell M R ≤ (x 0).val ∧ (x 0).val < ncQ1 ell M R) ∨
      (ncP1' ell M R ≤ (x 0).val ∧ (x 0).val < ncQ1' ell M R) := tw2_om1 x

/-- the linear facts (atoms `ell·(R M)`, `ell·M`, `R M`, `M`). -/
theorem nc_lin {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    R * M ≤ ell * (R * M) ∧ 2 * (R * M) ≤ ell * (R * M) ∧ 3 * M ≤ ell * M ∧ 1 ≤ R * M := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.le_mul_of_pos_left _ (by omega)
  · exact Nat.mul_le_mul_right _ (by omega)
  · exact Nat.mul_le_mul_right _ hell
  · exact Nat.mul_pos (by omega) hM

theorem nc_expand (ell M R : ℕ) :
    ncP1 ell M R = ell * (R * M) + ell * M ∧ ncQ1 ell M R = 3 * (ell * (R * M)) + 4 * (ell * M) ∧
    ncP1' ell M R = 4 * (ell * (R * M)) + 5 * (ell * M) ∧ ncQ1' ell M R = 4 * (ell * (R * M)) + 16 * (ell * M) ∧
    ncN ell M R = 5 * (ell * (R * M)) + 17 * (ell * M) := by
  simp only [ncP1, ncQ1, ncP1', ncQ1', ncN]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem nc_geo2 {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    Geo2 M ell R (ncN ell M R) (ncP0 ell M R) (ncQ0 ell M R) (ncP1 ell M R) (ncQ1 ell M R)
      (ncP0' ell M R) (ncQ0' ell M R) (ncP1' ell M R) (ncQ1' ell M R) := by
  obtain ⟨l1, l2, l3, l4⟩ := nc_lin hell hM hR
  obtain ⟨e1, e2, e3, e4, e5⟩ := nc_expand ell M R
  have dM : M ∣ R * M := Dvd.intro_left R rfl
  have dMe : M * ell ∣ ell * (R * M) := ⟨R, by ring⟩
  have dMe' : M * ell ∣ ell * M := ⟨1, by ring⟩
  have dM1 : M ∣ ell * (R * M) := Dvd.dvd.mul_left dM ell
  have dM2 : M ∣ ell * M := Dvd.intro_left ell rfl
  have hPdv : ∀ a b : ℕ, M * ell ∣ a * (ell * (R * M)) + b * (ell * M) := fun a b =>
    Nat.dvd_add (Dvd.dvd.mul_left dMe a) (Dvd.dvd.mul_left dMe' b)
  have hPdv0 : ∀ a b : ℕ, M ∣ a * (ell * (R * M)) + b * (ell * M) := fun a b =>
    Nat.dvd_add (Dvd.dvd.mul_left dM1 a) (Dvd.dvd.mul_left dM2 b)
  refine ⟨hM, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, e2]; omega
  · rw [e3, e4]; omega
  · simp only [ncQ0, ncP0']; rw [e2, e3]; omega
  · simp only [ncQ0']; rw [e4, e5]; omega
  · rw [e5]; simpa using hPdv0 5 17
  · rw [e5]; simpa using hPdv 5 17
  · simp only [ncP0]; rw [e1]; exact Nat.dvd_sub (by simpa using hPdv0 1 1) dM
  · simp only [ncQ0]; rw [e2]; exact Nat.dvd_add (hPdv0 3 4) dM
  · simp only [ncP0']; rw [e3]; exact Nat.dvd_sub (hPdv0 4 5) dM
  · simp only [ncQ0']; rw [e4]; exact Nat.dvd_add (hPdv0 4 16) dM
  · rw [e1]; simpa using hPdv 1 1
  · rw [e2]; exact hPdv 3 4
  · rw [e3]; exact hPdv 4 5
  · rw [e4]; exact hPdv 4 16
  · simp only [ncP0]; rw [e1]; omega
  · rfl
  · simp only [ncP0']; rw [e3]; omega
  · rfl

theorem nc_thin {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    Thin M ell (ncN ell M R) (ncP0 ell M R) (ncQ0 ell M R) (ncP1 ell M R) (ncQ1 ell M R)
      (ncP0' ell M R) (ncQ0' ell M R) (ncP1' ell M R) (ncQ1' ell M R) := by
  obtain ⟨l1, l2, l3, l4⟩ := nc_lin hell hM hR
  obtain ⟨e1, e2, e3, e4, e5⟩ := nc_expand ell M R
  have hme : M * ell = ell * M := Nat.mul_comm _ _
  refine ⟨hM, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [ncQ0]; omega
  · simp only [ncQ0, ncP0']; rw [e2, e3]; omega
  · simp only [ncP0']; rw [e3]; omega
  · rw [e4, e5]; omega
  · rw [e3, e4]; omega
  · rw [e3, e4, hme]; omega

theorem nc_admissible {ell M R : ℕ} (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) :
    Admissible ell M R 1 (ncS ell M R) :=
  tw2_admissible (nc_geo2 hell hM hR) (nc_scaleUp (by omega) hM)

/-! ## the unit torus, `TorusOK`, `Λ`, `LambdaOK2` -/

theorem nc_lt {M R : ℕ} (hM : 0 < M) (x : PeriodicLatticeSite (ncLu M R)) (μ : Fin 3) : (x μ).val < ncNu M R := by
  have := (x μ).isLt; have := ncLu_succ (R := R) hM μ; omega

def ncLam (M R : ℕ) : Set (PeriodicLatticeSite (ncLu M R)) :=
  {y | M * (2 * R + 2) ≤ (y 0).val ∧ (y 0).val < M * (2 * R + 2) + M}

theorem torusOK_nc {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    TorusOK ell M (ncLu M R) := by
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;> rw [ncLu_succ hM] <;> simp only [ncNu]
  · exact Dvd.dvd.mul_right hdvd _
  · have : ell ≤ M := Nat.le_of_dvd hM hdvd
    nlinarith
  · exact Dvd.intro _ rfl

theorem blockClosed_ncLam {M R : ℕ} (hM : 0 < M) : BlockClosed M (ncLam M R) := by
  intro x hx y hy
  have h := hy 0
  have hx' : M * (2 * R + 2) ≤ (x 0).val ∧ (x 0).val < M * (2 * R + 3) := by
    refine ⟨hx.1, ?_⟩; have := hx.2; rw [show M * (2 * R + 3) = M * (2 * R + 2) + M by ring]; exact this
  rw [iv_iff hM] at hx'
  have : M * (2 * R + 2) ≤ (y 0).val ∧ (y 0).val < M * (2 * R + 3) := by
    rw [iv_iff hM, h]; exact hx'
  refine ⟨this.1, ?_⟩
  have := this.2; rw [show M * (2 * R + 3) = M * (2 * R + 2) + M by ring] at this; exact this

theorem lamBlockSum_nc {ell M R : ℕ} (hell : 0 < ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    LamBlockSum ell (ncLam M R) := by
  intro x hx
  obtain ⟨a, ha⟩ := hdvd
  have hxN : ∀ μ, (x μ).val < ncNu M R := fun μ => nc_lt hM x μ
  let y : PeriodicLatticeSite (ncLu M R) := fun μ => ⟨ell * ((x μ).val / ell),
    lt_of_le_of_lt (Nat.mul_div_le _ _) (by have := ncLu_succ (R := R) hM μ; have := hxN μ; omega)⟩
  have hyv : ∀ μ, (y μ).val = ell * ((x μ).val / ell) := fun μ => rfl
  have e1 : M * (2 * R + 2) = ell * (a * (2 * R + 2)) := by rw [ha]; ring
  have e2 : M * (2 * R + 2) + M = ell * (a * (2 * R + 3)) := by rw [ha]; ring
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_CoarseLattice]; intro μ; rw [hyv]; exact Nat.mul_mod_right _ _
  · intro x' hx'
    rw [mem_blockOf] at hx'
    have h0 := hx' 0
    rw [hyv] at h0
    have hx0 : ell * (a * (2 * R + 2)) ≤ (x 0).val ∧ (x 0).val < ell * (a * (2 * R + 3)) := by
      have := hx.1; have := hx.2; omega
    rw [iv_iff hell] at hx0
    have hq1 : a * (2 * R + 2) ≤ (x 0).val / ell := hx0.1
    have hq2 : (x 0).val / ell + 1 ≤ a * (2 * R + 3) := hx0.2
    have m1 : ell * (a * (2 * R + 2)) ≤ ell * ((x 0).val / ell) := Nat.mul_le_mul_left ell hq1
    have m2 : ell * ((x 0).val / ell + 1) ≤ ell * (a * (2 * R + 3)) := Nat.mul_le_mul_left ell hq2
    constructor
    · omega
    · have : ell * ((x 0).val / ell + 1) = ell * ((x 0).val / ell) + ell := by ring
      omega
  · rw [mem_blockOf]
    intro μ
    rw [hyv]
    have h1 := Nat.div_add_mod (x μ).val ell
    have h2 := Nat.mod_lt (x μ).val hell
    refine ⟨Nat.mul_div_le _ _, ?_⟩
    generalize ell * ((x μ).val / ell) = A at h1 ⊢
    omega

theorem ncLam_nonempty {M R : ℕ} (hM : 0 < M) : (ncLam M R).Nonempty := by
  refine ⟨fun μ => ⟨if μ = 0 then M * (2 * R + 2) else 0, ?_⟩, ?_⟩
  · rw [ncLu_succ hM]
    have : 0 < ncNu M R := ncNu_pos hM
    split_ifs
    · simp only [ncNu]; nlinarith
    · exact this
  · show M * (2 * R + 2) ≤ (if (0 : Fin 3) = 0 then M * (2 * R + 2) else 0) ∧
      (if (0 : Fin 3) = 0 then M * (2 * R + 2) else 0) < M * (2 * R + 2) + M
    simp only [if_true]; omega

/-- the embedding `y ↦ ell · y`. -/
def embNc (ell M R : ℕ) (hell : 0 < ell) (hM : 0 < M) (y : PeriodicLatticeSite (ncLu M R)) :
    PeriodicLatticeSite (scaleUp ell 1 (ncLu M R)) :=
  fun μ => ⟨ell ^ 1 * (y μ).val, by
    have h2 := nc_scaleUp (ell := ell) (R := R) hell hM μ
    have h3 : (y μ).val < ncNu M R := nc_lt hM y μ
    have h4 : ell ^ 1 * (y μ).val < ell ^ 1 * ncNu M R := Nat.mul_lt_mul_of_pos_left h3 (by simpa using hell)
    have h5 : ell ^ 1 * ncNu M R = ncN ell M R := by simp only [ncN, ncNu]; ring
    omega⟩

theorem lambdaOK_nc {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK ell M R 1 (ncS ell M R) (ncLam M R) := by
  have hell0 : 0 < ell := by omega
  obtain ⟨e1, e2, -, -, -⟩ := nc_expand ell M R
  refine ⟨blockClosed_ncLam hM, embNc ell M R hell0 hM, fun y μ => rfl, ?_, ?_⟩
  · intro y hy
    rw [ncS_om1]
    left
    show ncP1 ell M R ≤ ell ^ 1 * (y 0).val ∧ ell ^ 1 * (y 0).val < ncQ1 ell M R
    simp only [ncP1, ncQ1, pow_one]
    have h1 := hy.1; have h2 := hy.2
    constructor
    · calc ell * (R * M + M) ≤ ell * (M * (2 * R + 2)) := Nat.mul_le_mul_left _ (by nlinarith)
        _ ≤ ell * (y 0).val := Nat.mul_le_mul_left _ h1
    · calc ell * (y 0).val < ell * (M * (2 * R + 2) + M) := Nat.mul_lt_mul_of_pos_left h2 hell0
        _ ≤ ell * (3 * (R * M) + 4 * M) := Nat.mul_le_mul_left _ (by nlinarith)
  · intro y hy y' hy'
    have hcase : (y' 0).val < R * M + M ∨ 3 * (R * M) + 4 * M ≤ (y' 0).val := by
      by_contra hcon
      push Not at hcon
      apply hy'
      rw [ncS_om1]
      left
      show ncP1 ell M R ≤ ell ^ 1 * (y' 0).val ∧ ell ^ 1 * (y' 0).val < ncQ1 ell M R
      simp only [ncP1, ncQ1, pow_one]
      exact ⟨Nat.mul_le_mul_left _ hcon.1, Nat.mul_lt_mul_of_pos_left hcon.2 hell0⟩
    have hyN : (y 0).val < ncNu M R := nc_lt hM y 0
    have hy'N : (y' 0).val < ncNu M R := nc_lt hM y' 0
    have e4 : ncNu M R = 5 * (R * M) + 17 * M := by simp only [ncNu]; ring
    have e5 : M * (2 * R + 2) = 2 * (R * M) + 2 * M := by ring
    have hMR : 0 < R * M := Nat.mul_pos (by omega) hM
    have hy1 := hy.1
    have hy2 := hy.2
    have hpd : R * M < pcd (ncNu M R) (y 0).val (y' 0).val := by
      rcases hcase with h | h
      · exact pcd_gt_right2 (by omega) (by omega)
      · exact pcd_gt_left2 (by omega) hy'N (by omega)
    unfold pdist
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (ncLu M R μ + 1) (y μ).val (y' μ).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
    simpa [ncLu_succ hM] using hpd

theorem lambdaOK2_nc {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK2 ell M R 1 (ncS ell M R) (ncLam M R) :=
  ⟨lambdaOK_nc hell hdvd hM hR, lamBlockSum_nc (by omega) hdvd hM⟩

/-! ## a nonzero `B̃ ∈ Λ̃` -/

def yNc {M R : ℕ} (hM : 0 < M) : PeriodicLatticeSite (ncLu M R) :=
  fun μ => ⟨if μ = 0 then M * (2 * R + 2) else 0, by
    rw [ncLu_succ hM]
    have : 0 < ncNu M R := ncNu_pos hM
    split_ifs
    · simp only [ncNu]; nlinarith
    · exact this⟩

noncomputable def BseedNc {M R : ℕ} (ell : ℕ) (hM : 0 < M) : Bond (ncLu M R) → SuTwo :=
  Pi.single (freeBond ell (yNc (R := R) hM)) suTwoWitness

theorem BseedNc_props {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    OnLambdaTildeIn (ncLam M R) ell (BseedNc (R := R) ell hM) ∧ OnLambdaT (ncLam M R) (BseedNc (R := R) ell hM) ∧
      0 < bondEnergy (BseedNc (R := R) ell hM) ∧ BseedNc (R := R) ell hM ≠ 0 := by
  have hell2 : 2 ≤ ell := by omega
  have hdvd' : ∀ μ : Fin 3, ell ∣ ncLu M R μ + 1 := fun μ => by
    rw [ncLu_succ hM]; exact Dvd.dvd.mul_right hdvd _
  have hy : yNc (R := R) hM ∈ CoarseLattice (ncLu M R) ell := by
    rw [mem_CoarseLattice]
    intro μ
    show (if μ = 0 then M * (2 * R + 2) else 0) % ell = 0
    split_ifs
    · exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right hdvd _)
    · simp
  have hoff : ∀ b : Bond (ncLu M R), b ≠ freeBond ell (yNc (R := R) hM) → BseedNc (R := R) ell hM b = 0 :=
    fun b hb => Pi.single_eq_of_ne hb _
  have hOn : OnLambdaT (ncLam M R) (BseedNc (R := R) ell hM) := by
    intro b hb
    by_cases hbe : b = freeBond ell (yNc (R := R) hM)
    · exfalso
      apply hb
      have hy0 : ((yNc (R := R) hM) 0).val = M * (2 * R + 2) := by simp [yNc]
      have hfit : ((yNc (R := R) hM) 0).val + ell ≤ ncLu M R 0 + 1 := by
        rw [hy0, ncLu_succ hM]
        have : ell ≤ M := Nat.le_of_dvd hM hdvd
        have e : ncNu M R = M * (2 * R + 2) + M * (3 * R + 15) := by simp only [ncNu]; ring
        have : M ≤ M * (3 * R + 15) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have h0 := freeBond_coord_zero (yNc (R := R) hM) hfit hell2
      subst hbe
      left
      show M * (2 * R + 2) ≤ ((freeBond ell (yNc (R := R) hM)).1 0).val ∧
        ((freeBond ell (yNc (R := R) hM)).1 0).val < M * (2 * R + 2) + M
      have : ell ≤ M := Nat.le_of_dvd hM hdvd
      omega
    · exact hoff b hbe
  have hne : ‖BseedNc (R := R) ell hM (freeBond ell (yNc (R := R) hM))‖ ^ 2 > 0 := by
    have : BseedNc (R := R) ell hM (freeBond ell (yNc (R := R) hM)) = suTwoWitness := Pi.single_eq_same _ _
    rw [this]
    have : suTwoWitness ≠ 0 := suTwoWitness_ne_zero
    positivity
  refine ⟨⟨?_, ?_⟩, hOn, ?_, ?_⟩
  · intro y hy' x hx b hb
    refine hoff b ?_
    rintro rfl
    exact freeBond_not_mem_staircase hell2 hdvd' (yNc (R := R) hM) hy y hy'.1 x hx hb
  · intro b hb
    refine hoff b ?_
    rintro rfl
    obtain ⟨c, hc1, hc2⟩ := hb
    exact freeBond_not_dropped hell2 hdvd' (yNc (R := R) hM) hy ⟨c, hc2⟩
  · have hle : ‖BseedNc (R := R) ell hM (freeBond ell (yNc (R := R) hM))‖ ^ 2
        ≤ ∑ b : Bond (ncLu M R), ‖BseedNc (R := R) ell hM b‖ ^ 2 :=
      Finset.single_le_sum (f := fun b : Bond (ncLu M R) => ‖BseedNc (R := R) ell hM b‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ _)
    unfold bondEnergy
    linarith
  · intro h
    have : BseedNc (R := R) ell hM (freeBond ell (yNc (R := R) hM)) = 0 := by rw [h]; rfl
    rw [this] at hne
    simp at hne

#print axioms nc_admissible
#print axioms torusOK_nc
#print axioms lambdaOK2_nc
#print axioms ncLam_nonempty
#print axioms BseedNc_props

end AdalyFormal.NoCover
