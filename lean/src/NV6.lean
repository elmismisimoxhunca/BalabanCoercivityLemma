import NV5
import ZT5D

/-!
# NV6 -- the unit torus, the slab `Λ`, `TorusOK`, `LambdaOK2`, a nonzero `B̃ ∈ Λ̃` (lane nonvac_20261015)

Unit torus `N_u = M (6R+2)` per direction; `Λ = {3RM ≤ y₀ < 3RM + M}` (one big block thick in direction 0, a union of `ell`-blocks since `ell ∣ M`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVac

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.FullReparamC (freeBond freeBond_not_mem_staircase freeBond_not_dropped freeBond_coord_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem pcd_gt_right2 {N a b D : ℕ} (hba : b + D < a) (hN : a + D < N) : D < pcd N a b := by
  unfold pcd; split_ifs <;> omega

theorem pcd_gt_left2 {N a b D : ℕ} (hab : a + D < b) (hb : b < N) (ha : D ≤ a) : D < pcd N a b := by
  unfold pcd; split_ifs <;> omega

def nvLu (M R : ℕ) : PeriodicLatticeExtent := fun _ => M * (6 * R + 2) - 1

theorem nvLu_succ {M R : ℕ} (hM : 0 < M) (μ : Fin 3) : nvLu M R μ + 1 = M * (6 * R + 2) := by
  have : 0 < M * (6 * R + 2) := Nat.mul_pos hM (by omega)
  simp only [nvLu]; omega

theorem nv_lt {M R : ℕ} (hM : 0 < M) (x : PeriodicLatticeSite (nvLu M R)) (μ : Fin 3) :
    (x μ).val < M * (6 * R + 2) := by
  have := (x μ).isLt
  have e := nvLu_succ (R := R) hM μ
  omega

theorem scaleUp_nv {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) (μ : Fin 3) :
    scaleUp ell 2 (nvLu M R) μ + 1 = nvN ell M R := by
  have h1 := nvLu_succ (R := R) hM μ
  have h2 : 0 < M * (6 * R + 2) * ell ^ 2 := Nat.mul_pos (Nat.mul_pos hM (by omega)) (pow_pos hell 2)
  simp only [scaleUp, h1, nvN]
  have : M * (6 * R + 2) * ell ^ 2 = M * ell ^ 2 * (6 * R + 2) := by ring
  omega

/-- the slab `Λ` on the unit torus. -/
def LamN (M R : ℕ) : Set (PeriodicLatticeSite (nvLu M R)) :=
  {y | M * (3 * R) ≤ (y 0).val ∧ (y 0).val < M * (3 * R) + M}

theorem torusOK_nv {ell M R : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    TorusOK ell M (nvLu M R) := by
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩ <;> rw [nvLu_succ hM]
  · exact Dvd.dvd.mul_right hdvd _
  · have : ell ≤ M := Nat.le_of_dvd hM hdvd
    nlinarith
  · exact Dvd.intro _ rfl

theorem blockClosed_lam {M R : ℕ} (hM : 0 < M) : BlockClosed M (LamN M R) := by
  intro x hx y hy
  have h := hy 0
  have hx' : M * (3 * R) ≤ (x 0).val ∧ (x 0).val < M * (3 * R + 1) := by
    refine ⟨hx.1, ?_⟩; have := hx.2; rw [mul_add, mul_one]; exact this
  rw [iv_iff hM] at hx'
  have : M * (3 * R) ≤ (y 0).val ∧ (y 0).val < M * (3 * R + 1) := by
    rw [iv_iff hM, h]; exact hx'
  refine ⟨this.1, ?_⟩
  have := this.2; rw [mul_add, mul_one] at this; exact this

theorem lamBlockSum_nv {ell M R : ℕ} (hell : 0 < ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    LamBlockSum ell (LamN M R) := by
  intro x hx
  obtain ⟨a, ha⟩ := hdvd
  have hxN : ∀ μ, (x μ).val < M * (6 * R + 2) := fun μ => nv_lt hM x μ
  let y : PeriodicLatticeSite (nvLu M R) := fun μ => ⟨ell * ((x μ).val / ell),
    lt_of_le_of_lt (Nat.mul_div_le _ _) (by have := nvLu_succ (R := R) hM μ; have := hxN μ; omega)⟩
  have hyv : ∀ μ, (y μ).val = ell * ((x μ).val / ell) := fun μ => rfl
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_CoarseLattice]; intro μ; rw [hyv]; exact Nat.mul_mod_right _ _
  · intro x' hx'
    rw [mem_blockOf] at hx'
    have h0 := hx' 0
    rw [hyv] at h0
    -- ell * (3R) * a ... M = ell * a
    have hx0 : ell * (a * (3 * R)) ≤ (x 0).val ∧ (x 0).val < ell * (a * (3 * R + 1)) := by
      have e1 : M * (3 * R) = ell * (a * (3 * R)) := by rw [ha]; ring
      have e2 : M * (3 * R) + M = ell * (a * (3 * R + 1)) := by rw [ha]; ring
      have := hx.1; have := hx.2; omega
    rw [iv_iff hell] at hx0
    have e1 : M * (3 * R) = ell * (a * (3 * R)) := by rw [ha]; ring
    have e2 : M * (3 * R) + M = ell * (a * (3 * R + 1)) := by rw [ha]; ring
    have hq1 : a * (3 * R) ≤ (x 0).val / ell := hx0.1
    have hq2 : (x 0).val / ell + 1 ≤ a * (3 * R + 1) := hx0.2
    have m1 : ell * (a * (3 * R)) ≤ ell * ((x 0).val / ell) := Nat.mul_le_mul_left ell hq1
    have m2 : ell * ((x 0).val / ell + 1) ≤ ell * (a * (3 * R + 1)) := Nat.mul_le_mul_left ell hq2
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

theorem lam_nonempty {M R : ℕ} (hM : 0 < M) : (LamN M R).Nonempty := by
  refine ⟨fun μ => ⟨if μ = 0 then M * (3 * R) else 0, ?_⟩, ?_⟩
  · rw [nvLu_succ hM]
    have : 0 < M * (6 * R + 2) := Nat.mul_pos hM (by omega)
    split_ifs
    · nlinarith
    · exact this
  · show M * (3 * R) ≤ (if (0 : Fin 3) = 0 then M * (3 * R) else 0) ∧ (if (0 : Fin 3) = 0 then M * (3 * R) else 0) < M * (3 * R) + M
    simp only [if_true]; omega

/-- the embedding `y ↦ ell² · y`. -/
def embNv (ell M R : ℕ) (hell : 0 < ell) (hM : 0 < M) (y : PeriodicLatticeSite (nvLu M R)) :
    PeriodicLatticeSite (scaleUp ell 2 (nvLu M R)) :=
  fun μ => ⟨ell ^ 2 * (y μ).val, by
    have h2 := scaleUp_nv (ell := ell) (R := R) hell hM μ
    have h3 : (y μ).val < M * (6 * R + 2) := nv_lt hM y μ
    have h4 : ell ^ 2 * (y μ).val < ell ^ 2 * (M * (6 * R + 2)) := Nat.mul_lt_mul_of_pos_left h3 (pow_pos hell 2)
    have h5 : ell ^ 2 * (M * (6 * R + 2)) = nvN ell M R := by simp only [nvN]; ring
    omega⟩

theorem lambdaOK_nv {ell M R : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK ell M R 2 (slab3 (scaleUp ell 2 (nvLu M R)) (nvP0 ell M R) (nvQ0 ell M R) (nvP1 ell M R) (nvQ1 ell M R)
      (nvP2 ell M R) (nvQ2 ell M R)) (LamN M R) := by
  have hell0 : 0 < ell := by omega
  have hee : 0 < ell ^ 2 := pow_pos hell0 2
  refine ⟨blockClosed_lam hM, embNv ell M R hell0 hM, fun y μ => rfl, ?_, ?_⟩
  · intro y hy
    rw [om2_mem]
    show nvP2 ell M R ≤ ell ^ 2 * (y 0).val ∧ ell ^ 2 * (y 0).val < nvQ2 ell M R
    simp only [nvP2, nvQ2]
    have h1 := hy.1; have h2 := hy.2
    constructor
    · calc M * ell ^ 2 * (2 * R) ≤ M * ell ^ 2 * (3 * R) := Nat.mul_le_mul_left _ (by omega)
        _ = ell ^ 2 * (M * (3 * R)) := by ring
        _ ≤ ell ^ 2 * (y 0).val := Nat.mul_le_mul_left _ h1
    · calc ell ^ 2 * (y 0).val < ell ^ 2 * (M * (3 * R) + M) := Nat.mul_lt_mul_of_pos_left h2 hee
        _ = M * ell ^ 2 * (3 * R + 1) := by ring
        _ ≤ M * ell ^ 2 * (4 * R + 1) := Nat.mul_le_mul_left _ (by omega)
  · intro y hy y' hy'
    rw [om2_mem] at hy'
    have hyN : (y 0).val < M * (6 * R + 2) := nv_lt hM y 0
    have hy'N : (y' 0).val < M * (6 * R + 2) := nv_lt hM y' 0
    have hcase : (y' 0).val < M * (2 * R) ∨ M * (4 * R + 1) ≤ (y' 0).val := by
      by_contra hcon
      push Not at hcon
      apply hy'
      show nvP2 ell M R ≤ ell ^ 2 * (y' 0).val ∧ ell ^ 2 * (y' 0).val < nvQ2 ell M R
      simp only [nvP2, nvQ2]
      constructor
      · calc M * ell ^ 2 * (2 * R) = ell ^ 2 * (M * (2 * R)) := by ring
          _ ≤ ell ^ 2 * (y' 0).val := Nat.mul_le_mul_left _ hcon.1
      · calc ell ^ 2 * (y' 0).val < ell ^ 2 * (M * (4 * R + 1)) := Nat.mul_lt_mul_of_pos_left hcon.2 hee
          _ = M * ell ^ 2 * (4 * R + 1) := by ring
    have hRM : R * M = M * R := by ring
    have e1 : M * (3 * R) = 3 * (M * R) := by ring
    have e2 : M * (2 * R) = 2 * (M * R) := by ring
    have e3 : M * (4 * R + 1) = 4 * (M * R) + M := by ring
    have e4 : M * (6 * R + 2) = 6 * (M * R) + 2 * M := by ring
    have hMR : 0 < M * R := Nat.mul_pos hM hR
    have hy1 := hy.1
    have hy2 := hy.2
    have hpd : R * M < pcd (M * (6 * R + 2)) (y 0).val (y' 0).val := by
      rw [hRM]
      rcases hcase with h | h
      · exact pcd_gt_right2 (by omega) (by omega)
      · exact pcd_gt_left2 (by omega) hy'N (by omega)
    unfold pdist
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (nvLu M R μ + 1) (y μ).val (y' μ).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
    simpa [nvLu_succ hM] using hpd

theorem lambdaOK2_nv {ell M R : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    LambdaOK2 ell M R 2 (slab3 (scaleUp ell 2 (nvLu M R)) (nvP0 ell M R) (nvQ0 ell M R) (nvP1 ell M R) (nvQ1 ell M R)
      (nvP2 ell M R) (nvQ2 ell M R)) (LamN M R) :=
  ⟨lambdaOK_nv hell hdvd hM hR, lamBlockSum_nv (by omega) hdvd hM⟩

/-! ### a nonzero `B̃ ∈ Λ̃` -/

def yNv {M R : ℕ} (hM : 0 < M) : PeriodicLatticeSite (nvLu M R) :=
  fun μ => ⟨if μ = 0 then M * (3 * R) else 0, by
    rw [nvLu_succ hM]
    have : 0 < M * (6 * R + 2) := Nat.mul_pos hM (by omega)
    split_ifs
    · nlinarith
    · exact this⟩

noncomputable def BseedNv {M R : ℕ} (ell : ℕ) (hM : 0 < M) : Bond (nvLu M R) → SuTwo :=
  Pi.single (freeBond ell (yNv (R := R) hM)) suTwoWitness

theorem BseedNv_props {ell M R : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) :
    OnLambdaTildeIn (LamN M R) ell (BseedNv (R := R) ell hM) ∧ OnLambdaT (LamN M R) (BseedNv (R := R) ell hM) ∧
      0 < bondEnergy (BseedNv (R := R) ell hM) ∧ BseedNv (R := R) ell hM ≠ 0 := by
  have hdvd' : ∀ μ : Fin 3, ell ∣ nvLu M R μ + 1 := fun μ => by
    rw [nvLu_succ hM]; exact Dvd.dvd.mul_right hdvd _
  have hy : yNv (R := R) hM ∈ CoarseLattice (nvLu M R) ell := by
    rw [mem_CoarseLattice]
    intro μ
    show (if μ = 0 then M * (3 * R) else 0) % ell = 0
    split_ifs
    · exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right hdvd _)
    · simp
  have hoff : ∀ b : Bond (nvLu M R), b ≠ freeBond ell (yNv (R := R) hM) → BseedNv (R := R) ell hM b = 0 :=
    fun b hb => Pi.single_eq_of_ne hb _
  have hOn : OnLambdaT (LamN M R) (BseedNv (R := R) ell hM) := by
    intro b hb
    by_cases hbe : b = freeBond ell (yNv (R := R) hM)
    · exfalso
      apply hb
      have hy0 : ((yNv (R := R) hM) 0).val = M * (3 * R) := by simp [yNv]
      have hfit : ((yNv (R := R) hM) 0).val + ell ≤ nvLu M R 0 + 1 := by
        rw [hy0, nvLu_succ hM]
        have : ell ≤ M := Nat.le_of_dvd hM hdvd
        have e : M * (6 * R + 2) = M * (3 * R) + M * (3 * R + 2) := by ring
        have : M ≤ M * (3 * R + 2) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have h0 := freeBond_coord_zero (yNv (R := R) hM) hfit hell
      subst hbe
      left
      show M * (3 * R) ≤ ((freeBond ell (yNv (R := R) hM)).1 0).val ∧ ((freeBond ell (yNv (R := R) hM)).1 0).val < M * (3 * R) + M
      have : ell ≤ M := Nat.le_of_dvd hM hdvd
      omega
    · exact hoff b hbe
  have hne : ‖BseedNv (R := R) ell hM (freeBond ell (yNv (R := R) hM))‖ ^ 2 > 0 := by
    have : BseedNv (R := R) ell hM (freeBond ell (yNv (R := R) hM)) = suTwoWitness := Pi.single_eq_same _ _
    rw [this]
    have : suTwoWitness ≠ 0 := suTwoWitness_ne_zero
    positivity
  refine ⟨⟨?_, ?_⟩, hOn, ?_, ?_⟩
  · intro y hy' x hx b hb
    refine hoff b ?_
    rintro rfl
    exact freeBond_not_mem_staircase hell hdvd' (yNv (R := R) hM) hy y hy'.1 x hx hb
  · intro b hb
    refine hoff b ?_
    rintro rfl
    obtain ⟨c, hc1, hc2⟩ := hb
    exact freeBond_not_dropped hell hdvd' (yNv (R := R) hM) hy ⟨c, hc2⟩
  · have hle : ‖BseedNv (R := R) ell hM (freeBond ell (yNv (R := R) hM))‖ ^ 2
        ≤ ∑ b : Bond (nvLu M R), ‖BseedNv (R := R) ell hM b‖ ^ 2 :=
      Finset.single_le_sum (f := fun b : Bond (nvLu M R) => ‖BseedNv (R := R) ell hM b‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ _)
    unfold bondEnergy
    linarith
  · intro h
    have : BseedNv (R := R) ell hM (freeBond ell (yNv (R := R) hM)) = 0 := by rw [h]; rfl
    rw [this] at hne
    simp at hne

end AdalyFormal.NonVac
