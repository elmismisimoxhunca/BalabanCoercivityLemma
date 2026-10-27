import NMX1c

/-!
# NMX2 -- right-shell cubes of large factor, and `Λ` for the mixed layout (lane nonvac_mixed_20261017)

`mx_right_cube`: for `2 ≤ g ≤ T` there is a class cube of factor `g` (index `0`) through the right-shell site `x₀ = Q₁` (the right component
`[Q₂, Q₀)` has width `≥ g M`), even when `g` exceeds the left width `w`.
`lambdaOK2_mx`: the unit-torus slab `Λ` (nvcLu, `LamN`) of nonvac_c is inside `Ω₂` with collar `R M` on the mixed layout (`w ≤ T`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVacMix

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.NonVacC

section right
variable {ell M R T q : ℕ}

theorem mx_right_cube (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hq : R ≤ q) (hT : 1 ≤ T)
    (hwT : R + ell * q ≤ T) {g : ℕ} (hg2 : 2 ≤ g) (hgT : g ≤ T) :
    ∃ (x : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T))) (sites : Set (PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)))) (j : ℕ),
      x ∈ (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q).Om 0 ∧
      IsClassCube ell M g 2 (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q) sites j ∧ x ∈ sites := by
  have hell0 : 0 < ell := by omega
  have hN : ∀ μ, scaleUp ell 2 (nvcLu M T) μ + 1 = nvcN ell M T := fun μ => scaleUp_nvc hell0 hM μ
  have G := slabGeo_mix hell hdvd hM hR hq hT hwT
  have hnest := (slab3_admissible G hN).1
  have hRT : R ≤ T := by nlinarith
  obtain ⟨-, w2, -, -, w5, -, w7, w8⟩ := nvc_widths (c := g) hell hM hR hRT hT (by omega)
  have g1 := G.nest01; have g2 := G.nest12; have g3 := G.nestw; have g4 := G.nest21; have g5 := G.nest10
  have g6 := G.QN
  have hRM : 0 < R * M := Nat.mul_pos (by omega) hM
  have hbs : bigSide M ell 0 = M := by simp [bigSide]
  have hM2 : M ∣ nvcQ2 ell M T := Dvd.dvd.trans (Dvd.intro _ rfl) G.b2Q
  have hQ1N : nvcQ1 ell M T < nvcN ell M T := by omega
  let x : PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T)) := siteAt0 (T := T) hell0 hM (nvcQ1 ell M T) hQ1N
  have hx0 : (x 0).val = nvcQ1 ell M T := siteAt0_val hell0 hM _ hQ1N
  have hx1 : (x 0).val + 1 < nvcN ell M T := by omega
  have hxOm : x ∈ (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q).Om 0 := by
    unfold mxS; rw [om0_mem, hx0]; omega
  obtain ⟨sites, hc, hall⟩ := cube_of_region hg2 (ell := ell) (M := M) (j := 0) hN hnest (by norm_num)
    (lo := nvcQ2 ell M T) (hi := nvcQ0 ell M R T)
    (by rw [hbs]; exact hM) (by rw [hbs]; exact hM2) (by rw [hbs]; exact G.b0Q) (by rw [hbs]; exact w2) G.QN
    x (min ((x 0).val + 1) (nvcQ0 ell M R T - 1)) (by omega) (by omega) (by omega) (by omega) hx1
    (by
      intro y h1 h2
      by_cases h3 : nvcQ1 ell M T ≤ (y 0).val
      · left; rw [bj0]; omega
      · right; rw [bj1]; omega)
    ⟨(x 0).val, Or.inl rfl, by omega, by intro y hy; rw [bj0]; omega⟩
  exact ⟨x, sites, 0, hxOm, hc, hall x (adj_refl _ x) (by omega)⟩

end right

section lam
variable {ell M R T q : ℕ}

theorem lambdaOK_mx (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hq : R ≤ q) (hT : 1 ≤ T)
    (hwT : R + ell * q ≤ T) :
    LambdaOK ell M R 2 (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q) (LamN M T) := by
  have hell0 : 0 < ell := by omega
  have hee : 0 < ell ^ 2 := pow_pos hell0 2
  have hRT : R ≤ T := by nlinarith
  unfold mxS
  refine ⟨blockClosed_lam hM, embNv ell M T hell0 hM, fun y μ => rfl, ?_, ?_⟩
  · intro y hy
    rw [om2_mem]
    show mxP2 ell M R q ≤ ell ^ 2 * (y 0).val ∧ ell ^ 2 * (y 0).val < nvcQ2 ell M T
    simp only [mxP2, nvcQ2]
    have h1 := hy.1; have h2 := hy.2
    constructor
    · calc M * ell ^ 2 * (R + ell * q) ≤ M * ell ^ 2 * (3 * T) := Nat.mul_le_mul_left _ (by omega)
        _ = ell ^ 2 * (M * (3 * T)) := by ring
        _ ≤ ell ^ 2 * (y 0).val := Nat.mul_le_mul_left _ h1
    · calc ell ^ 2 * (y 0).val < ell ^ 2 * (M * (3 * T) + M) := Nat.mul_lt_mul_of_pos_left h2 hee
        _ = M * ell ^ 2 * (3 * T + 1) := by ring
        _ ≤ M * ell ^ 2 * (4 * T + 1) := Nat.mul_le_mul_left _ (by omega)
  · intro y hy y' hy'
    rw [om2_mem] at hy'
    have hyN : (y 0).val < M * (6 * T + 2) := nvc_lt hM y 0
    have hy'N : (y' 0).val < M * (6 * T + 2) := nvc_lt hM y' 0
    have hcase : (y' 0).val < M * (R + ell * q) ∨ M * (4 * T + 1) ≤ (y' 0).val := by
      by_contra hcon
      push Not at hcon
      apply hy'
      show mxP2 ell M R q ≤ ell ^ 2 * (y' 0).val ∧ ell ^ 2 * (y' 0).val < nvcQ2 ell M T
      simp only [mxP2, nvcQ2]
      constructor
      · calc M * ell ^ 2 * (R + ell * q) = ell ^ 2 * (M * (R + ell * q)) := by ring
          _ ≤ ell ^ 2 * (y' 0).val := Nat.mul_le_mul_left _ hcon.1
      · calc ell ^ 2 * (y' 0).val < ell ^ 2 * (M * (4 * T + 1)) := Nat.mul_lt_mul_of_pos_left hcon.2 hee
          _ = M * ell ^ 2 * (4 * T + 1) := by ring
    have hRM : R * M ≤ M * T := by
      calc R * M ≤ T * M := Nat.mul_le_mul_right M hRT
        _ = M * T := by ring
    have hwM : M * (R + ell * q) ≤ M * T := Nat.mul_le_mul_left M hwT
    have e1 : M * (3 * T) = 3 * (M * T) := by ring
    have e3 : M * (4 * T + 1) = 4 * (M * T) + M := by ring
    have e4 : M * (6 * T + 2) = 6 * (M * T) + 2 * M := by ring
    have hMT : 0 < M * T := Nat.mul_pos hM hT
    have hy1 := hy.1
    have hy2 := hy.2
    have hpd : R * M < pcd (M * (6 * T + 2)) (y 0).val (y' 0).val := by
      rcases hcase with h | h
      · exact pcd_gt_right2 (by omega) (by omega)
      · exact pcd_gt_left2 (by omega) hy'N (by omega)
    unfold pdist
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (nvcLu M T μ + 1) (y μ).val (y' μ).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
    simpa [nvcLu_succ hM] using hpd

theorem lambdaOK2_mx (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hq : R ≤ q) (hT : 1 ≤ T)
    (hwT : R + ell * q ≤ T) :
    LambdaOK2 ell M R 2 (mxS (scaleUp ell 2 (nvcLu M T)) ell M R T q) (LamN M T) :=
  ⟨lambdaOK_mx hell hM hR hq hT hwT, lamBlockSum_nv (by omega) hdvd hM⟩

end lam

end AdalyFormal.NonVacMix
