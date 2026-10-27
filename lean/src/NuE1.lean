import NuZ1
import NuC2
import NtCvOI6
import NtCvOF1

/-!
# NuE1 -- the `Dpi` energy of a chain vector for the single negative edge (lane ncwdh_ell2_20261018)

`zprof_eq_BF1`: for the nested instance and a chain vector `e`, `zprof (omega1 ..) (fe P0 e)` at the slice `P0 + x` equals `BF1 (xs - P0) (cos 2t) e δ_x`;
`Dpi_energy1`: `<zfield (fe e), zfield (zprof ..)> = c0 T1 qF1 (xs - P0) (cos 2t) e`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)

/-- `BF1 e f = Σ_x f_x BF1 e δ_x`. -/
theorem BF1_eq_sum_single {n : ℕ} (C : ℕ) (c : ℝ) (e f : Fin n → ℝ) :
    BF1 C c e f = ∑ x : Fin n, f x * BF1 C c e (Pi.single x 1) := by
  let Φ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => BF1 C c e f
      map_add' := fun f g => BF1_add_right C c e f g
      map_smul' := fun r f => by simpa using BF1_smul_right C c r e f }
  have := LinearMap.pi_apply_eq_sum_univ Φ f
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] at this
  rw [this]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 2
  funext y
  simp [Pi.single_apply, eq_comm]

section
variable [CfData]
variable {ell M R : ℕ}

theorem ne_P0_pos_two (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : 1 ≤ neP0 ell M R := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  simp only [neP0, neP1, neA']; omega

theorem ne_Q0_lt_N_two (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : neQ0 ell M R + 1 ≤ neN ell M R := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  simp only [neQ0, neQ1, neB, neN]; omega

/-- the edge weight along the single-layer family, on the chain edges. -/
theorem omega1_edge (xs : ℕ) (hxs : neP0 ell M R ≤ xs) (t : ℝ) {N : ℕ} (hN : neQ0 ell M R ≤ N) (y : ℕ) (hy : y + 1 < nN ell M R) :
    omega1 (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N xs t (neP0 ell M R + y) =
      W1 (xs - neP0 ell M R) (Real.cos (2 * t)) (y : ℤ) := by
  classical
  have hnxt : nxt N (neP0 ell M R + y) = neP0 ell M R + y + 1 := by
    unfold nxt; rw [if_neg]; unfold nN at hy; omega
  unfold omega1
  rw [hnxt]
  have hJ : (neP0 ell M R ≤ neP0 ell M R + y ∧ neP0 ell M R + y < neQ0 ell M R) ∧
      (neP0 ell M R ≤ neP0 ell M R + y + 1 ∧ neP0 ell M R + y + 1 < neQ0 ell M R) := by
    unfold nN at hy; omega
  rw [if_pos hJ]
  unfold W1
  by_cases h : neP0 ell M R + y = xs
  · have h' : (y : ℤ) = ((xs - neP0 ell M R : ℕ) : ℤ) := by omega
    rw [if_pos h, if_pos h']
  · have h' : ¬ ((y : ℤ) = ((xs - neP0 ell M R : ℕ) : ℤ)) := by omega
    rw [if_neg h, if_neg h']

theorem omega1_off (xs : ℕ) (t : ℝ) {N : ℕ} (hN : neQ0 ell M R ≤ N) {u : ℕ}
    (hu : u < neP0 ell M R ∨ neQ0 ell M R ≤ u + 1) (huN : u ≠ N) :
    omega1 (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N xs t u = 0 := by
  classical
  unfold omega1
  rw [if_neg]
  unfold nxt
  rw [if_neg huN]
  omega

theorem zprof_eq_BF1 (hell2 : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {xs : ℕ} (hxs : neP0 ell M R ≤ xs)
    (hxs2 : xs + 1 < neQ0 ell M R) (t : ℝ)
    (e : Fin (nN ell M R) → ℝ) (x : Fin (nN ell M R)) :
    zprof (scaleUp ell 2 (neLu M R) 0) (omega1 (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (scaleUp ell 2 (neLu M R) 0) xs t)
        (fe (neP0 ell M R) e) (neP0 ell M R + x.val) =
      BF1 (xs - neP0 ell M R) (Real.cos (2 * t)) e (Pi.single x 1) := by
  have hg := nGeo_two hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  set N := scaleUp ell 2 (neLu M R) 0 with hNdef
  have hN1 : N + 1 = neN ell M R := ne_scaleUp hell hM 0
  have hQN : neQ0 ell M R ≤ N := by have := ne_Q0_lt_N_two hell2 hM hR; omega
  have hP0 := ne_P0_pos_two hell2 hM hR
  have hn' : nN ell M R = neQ0 ell M R - neP0 ell M R := rfl
  have hC : xs - neP0 ell M R + 1 < nN ell M R := by omega
  rw [BF1_single _ _ hC e x]
  set v := neP0 ell M R + x.val with hv
  have hxn : x.val < (nN ell M R) := x.2
  have hvQ : v < neQ0 ell M R := by omega
  have hv0 : v ≠ 0 := by omega
  have hvN : v ≠ N := by omega
  unfold zprof Wa
  have hprv : prv N v = v - 1 := by unfold prv; rw [if_neg hv0]
  have hnxt : nxt N v = v + 1 := by unfold nxt; rw [if_neg hvN]
  have hnxt' : nxt N (v - 1) = v := by unfold nxt; rw [if_neg (by omega)]; omega
  rw [hprv, hnxt', hnxt]
  have hnxe : ∀ k : ℕ, k < (nN ell M R) → nx e (k : ℤ) = fe (neP0 ell M R) e (neP0 ell M R + k) := by
    intro k hk
    rw [nx_nat e k hk]
    exact (fe_at (neP0 ell M R) e ⟨k, hk⟩).symm
  have hR2 : omega1 (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N xs t v *
      (fe (neP0 ell M R) e (v + 1) - fe (neP0 ell M R) e v) =
      W1 (xs - neP0 ell M R) (Real.cos (2 * t)) (x.val : ℤ) * (nx e ((x.val : ℤ) + 1) - nx e (x.val : ℤ)) := by
    by_cases hx1 : x.val + 1 < (nN ell M R)
    · rw [hv, omega1_edge xs hxs t hQN x.val hx1]
      have h1 : nx e ((x.val : ℤ) + 1) = fe (neP0 ell M R) e (neP0 ell M R + x.val + 1) := by
        have := hnxe (x.val + 1) hx1
        push_cast at this; rw [this]; congr 1
      have h2 : nx e (x.val : ℤ) = fe (neP0 ell M R) e (neP0 ell M R + x.val) := hnxe x.val hxn
      rw [h1, h2]
    · have hx2 : x.val + 1 = (nN ell M R) := by omega
      have hoff : omega1 (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N xs t v = 0 :=
        omega1_off xs t hQN (Or.inr (by omega)) hvN
      rw [hoff, zero_mul]
      have : nx e ((x.val : ℤ) + 1) - nx e (x.val : ℤ) = 0 := by
        have e1 : (x.val : ℤ) + 1 = ((nN ell M R) : ℤ) := by omega
        have e2 : (x.val : ℤ) = ((nN ell M R) : ℤ) - 1 := by omega
        rw [e1, nx_n e (by omega), ← e2]; ring
      rw [this, mul_zero]
  have hL2 : omega1 (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N xs t (v - 1) *
      (fe (neP0 ell M R) e v - fe (neP0 ell M R) e (v - 1)) =
      W1 (xs - neP0 ell M R) (Real.cos (2 * t)) ((x.val : ℤ) - 1) * (nx e (x.val : ℤ) - nx e ((x.val : ℤ) - 1)) := by
    by_cases hx0 : x.val = 0
    · have hoff : omega1 (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N xs t (v - 1) = 0 :=
        omega1_off xs t hQN (Or.inl (by omega)) (by omega)
      rw [hoff, zero_mul]
      have : nx e (x.val : ℤ) - nx e ((x.val : ℤ) - 1) = 0 := by
        rw [hx0]
        have := nx_neg_one e (by omega : 0 < (nN ell M R))
        simp only [Nat.cast_zero, zero_sub]
        rw [this]; ring
      rw [this, mul_zero]
    · have hy : x.val - 1 + 1 < (nN ell M R) := by omega
      have hvv : v - 1 = neP0 ell M R + (x.val - 1) := by omega
      rw [hvv, omega1_edge xs hxs t hQN (x.val - 1) hy]
      have e1 : (((x.val - 1 : ℕ)) : ℤ) = (x.val : ℤ) - 1 := by omega
      rw [e1]
      have h1 : nx e (x.val : ℤ) = fe (neP0 ell M R) e (neP0 ell M R + x.val) := hnxe x.val hxn
      have h2 : nx e ((x.val : ℤ) - 1) = fe (neP0 ell M R) e (neP0 ell M R + (x.val - 1)) := by
        have := hnxe (x.val - 1) (by omega)
        rw [← this]; congr 1; omega
      rw [h1, h2, ← hv]
  rw [hL2, hR2]

theorem Dpi_energy1 (hell2 : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {xs : ℕ} (hxs : neP0 ell M R ≤ xs)
    (hxs2 : xs + 1 < neQ0 ell M R) (t : ℝ) (e : Fin (nN ell M R) → ℝ) :
    (inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R)))
        (zfield (zprof (scaleUp ell 2 (neLu M R) 0)
          (omega1 (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (scaleUp ell 2 (neLu M R) 0) xs t) (fe (neP0 ell M R) e))) : ℝ) =
      c0 * ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) *
        qF1 (xs - neP0 ell M R) (Real.cos (2 * t)) e := by
  have hell : 0 < ell := by omega
  rw [inner_zfield_zfield]
  congr 1
  set N := scaleUp ell 2 (neLu M R) 0 with hN
  have hN1 : N + 1 = neN ell M R := ne_scaleUp hell hM 0
  have hQ := ne_Q0_lt_N_two hell2 hM hR
  have hP0 := ne_P0_pos_two hell2 hM hR
  have hsub : ∀ v ∈ range (N + 1), v ∉ (Finset.univ : Finset (Fin (nN ell M R))).image (fun x => neP0 ell M R + x.val) →
      fe (neP0 ell M R) e v * zprof N (omega1 (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N xs t) (fe (neP0 ell M R) e) v = 0 := by
    intro v hv hvn
    have hfv : fe (neP0 ell M R) e v = 0 := by
      by_cases h1 : v < neP0 ell M R
      · exact fe_lt _ e h1
      · apply fe_ge
        by_contra h2
        apply hvn
        have h2' : v < neP0 ell M R + nN ell M R := by omega
        exact Finset.mem_image.mpr ⟨⟨v - neP0 ell M R, by omega⟩, Finset.mem_univ _, by simp; omega⟩
    rw [hfv, zero_mul]
  have himg : (Finset.univ : Finset (Fin (nN ell M R))).image (fun x => neP0 ell M R + x.val) ⊆ range (N + 1) := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
    have := x.2; unfold nN at this
    simp only [Finset.mem_range]; omega
  rw [← Finset.sum_subset himg (fun v hv hvn => hsub v hv hvn)]
  rw [Finset.sum_image (fun x _ y _ h => Fin.ext (by simpa using h))]
  rw [show qF1 (xs - neP0 ell M R) (Real.cos (2 * t)) e = BF1 (xs - neP0 ell M R) (Real.cos (2 * t)) e e from (BF1_self _ _ _).symm]
  rw [BF1_eq_sum_single]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [fe_at, zprof_eq_BF1 hell2 hdvd hM hR hxs hxs2 t e x]

end

end AdalyFormal.NcwdhTwo
