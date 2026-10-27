import MF3
import DLR1

/-!
# DL2 -- the D-layer pairings on the GENUINE objects (any `IngrBParams`; full tower for the slice step)

* `psiD P = H* J ∈ F` (the print's `H*J`, CMP99b p.422: "|(H*J)(b)| ≤ O(1)Mα₀(L^jη)⁻³"), `psi1u P = H₁in* Jf` (unit bonds).
* `delta2_pair` : `⟪A, Δ⁽²⁾A⟫ = 2 Σ_c ⟪C₂(A)(c), ψ(c)⟫`  (R2Algebra `Delta2_spec` + adjoint), so `Δ⁽²⁾` is NOT a fine-scale multiplication
  operator: `C₂(A) = C2fullOf(W A)` (W = 1 − DG'RD* non-local).
* `delta2_abs_le` : `|⟪A,Δ⁽²⁾A⟫| ≤ 2 (sup‖ψ‖) Σ_c ‖C₂(A)(c)‖`.
* `wA_le` (full tower) : `‖W ιA‖² ≤ C0 ⟪A, G⁻¹A⟫` from coercivity of `G⁻¹` at the slice point `x = W ιA` (T x = 0, Q x = Q ιA by B0,
  ⟪x,Dpi x⟫ = ⟪A,Dpi A⟫).  NO bound on ‖W‖ is used.
* `formD2` : the FORM bound `|⟪A,Δ⁽²⁾A⟫| ≤ 2 S K2n C0 ⟪A,G⁻¹A⟫` from `‖ψ(c)‖ ≤ S` and the quadratic ℓ¹ bound `Σ_c ‖C2fullOf z c‖ ≤ K2n ‖z‖²`.
* `psi_le_of_col`, `psi1u_le_of_col` : `‖ψ(c)‖ ≤ C_H · S_J` from the ℓ¹ column bound of `H` (resp. `H₁in`) and `sup‖Jf‖ ≤ S_J`.
* `hJ_le` : `|⟪H₁in(D2in B), Jf⟫| ≤ S₁ Σ_e ‖(D2in B)(e)‖` from `‖ψ₁(e)‖ ≤ S₁`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M0Finish (Wop_apply Wop_idem Qfull_Wop)

/-- `ψ = H* J` on `𝔅` -/
noncomputable def psiD (P : IngrBParams) : FSp P.G := ContinuousLinearMap.adjoint P.data.H P.data.J

/-- `ψ₁ = H₁in* Jf` on unit bonds -/
noncomputable def psi1u (P : IngrBParams) : BondFnL2 P.Lu := ContinuousLinearMap.adjoint P.H1in P.Jf

theorem delta2_pair (P : IngrBParams) (A : ↥(bondSupp P.G)) :
    ⟪A, P.data.Delta2 P.data_laws A⟫ = 2 * ∑ p, ⟪(P.data.C2 A) p, psiD P p⟫ := by
  rw [(P.data.Delta2_spec P.data_laws).2 A, ← ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  rfl

theorem delta2_abs_le (P : IngrBParams) (S : ℝ) (hψ : ∀ p, ‖psiD P p‖ ≤ S) (A : ↥(bondSupp P.G)) :
    |⟪A, P.data.Delta2 P.data_laws A⟫| ≤ 2 * S * ∑ p, ‖(P.data.C2 A) p‖ := by
  rw [delta2_pair, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), mul_assoc, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [mul_comm S]
  exact mul_le_mul_of_nonneg_left (hψ p) (norm_nonneg _)

/-- membership in `E₀` when `Ω₀` is the whole torus -/
theorem mem_bondSupp_univ (P : IngrBParams) (hOm : P.G.Om0 = Set.univ) (x : BondFnL2 P.Lf) :
    x ∈ bondSupp P.G := by
  intro b hb
  exact absurd (Or.inl (by rw [hOm]; trivial)) hb

/-- `‖W ιA‖² ≤ C0 ⟪A, G⁻¹ A⟫` (`Ω₀` = torus): coercivity at the slice point, no bound on ‖W‖. -/
theorem wA_le (P : IngrBParams) (hOm : P.G.Om0 = Set.univ)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hB0 : ∀ ν ∈ NQp P.G P.U, P.sector.Qfull (gradL2 P.U ν) = 0)
    (C0 : ℝ) (hC0 : 0 ≤ C0) (hcoer : ∀ y : ↥(bondSupp P.G), ‖y‖ ^ 2 ≤ C0 * ⟪y, P.data.Ginv y⟫)
    (A : ↥(bondSupp P.G)) :
    ‖Wop P.G P.U P.a (iE P.G A)‖ ^ 2 ≤ C0 * ⟪A, P.data.Ginv A⟫ := by
  set x : BondFnL2 P.Lf := Wop P.G P.U P.a (iE P.G A) with hx
  have hWW : Wop P.G P.U P.a x = x := Wop_idem P.G hOm P.U P.a hu _
  set x' : ↥(bondSupp P.G) := ⟨x, mem_bondSupp_univ P hOm x⟩ with hx'
  have hix : iE P.G x' = x := rfl
  have hD : ∀ z : ↥(bondSupp P.G), ⟪z, P.data.Dpi z⟫ = ⟪iE P.G z, DpiFull P.G P.U P.a (iE P.G z)⟫ := by
    intro z
    show ⟪z, (pE P.G) (DpiFull P.G P.U P.a (iE P.G z))⟫ = _
    rw [pE_inner_right]
  have hW : ∀ y : BondFnL2 P.Lf, ⟪y, DpiFull P.G P.U P.a y⟫ = ⟪Wop P.G P.U P.a y, Delta P.G P.U (Wop P.G P.U P.a y)⟫ := by
    intro y
    rw [inner_DpiFull, Wop_apply]
  have hDpiA : ⟪A, P.data.Dpi A⟫ = ⟪x, Delta P.G P.U x⟫ := by rw [hD, hW]
  have hDpix : ⟪x', P.data.Dpi x'⟫ = ⟪x, Delta P.G P.U x⟫ := by rw [hD, hix, hW, hWW]
  have hTx : P.data.T x' = 0 := by
    show Tfull P.G P.U (iE P.G x') = 0
    rw [hix, hx]
    exact AdalyFormal.SliceCoerc.slice_of_Wop P.G hOm P.U P.a hu _
  have hM : ∀ z : ↥(bondSupp P.G), ⟪z, P.data.Mass z⟫ = ⟪iE P.G z, MassFull P.G P.a P.sector (iE P.G z)⟫ := by
    intro z
    show ⟪z, (pE P.G) ((MassFull P.G P.a P.sector) ((iE P.G) z))⟫ = _
    rw [pE_inner_right]
  have hq : P.sector.Qfull x = P.sector.Qfull (iE P.G A) := Qfull_Wop P.G P.U P.a P.sector hu hB0 _
  have hMx : ⟪x', P.data.Mass x'⟫ = ⟪A, P.data.Mass A⟫ := by
    rw [hM, hM, inner_MassFull, inner_MassFull, hix, hq]
  have hGx : ⟪x', P.data.Ginv x'⟫ = ⟪x, Delta P.G P.U x⟫ + ⟪A, P.data.Mass A⟫ := by
    rw [BaseDataS.inner_Ginv, hDpix, hTx, hMx, norm_zero]; ring
  have hGA : ⟪A, P.data.Ginv A⟫ = ⟪x, Delta P.G P.U x⟫ + ‖P.data.T A‖ ^ 2 + ⟪A, P.data.Mass A⟫ := by
    rw [BaseDataS.inner_Ginv, hDpiA]
  have hc := hcoer x'
  have hn : ‖x'‖ = ‖x‖ := rfl
  rw [hn, hGx] at hc
  have hT := sq_nonneg ‖P.data.T A‖
  have h2 : C0 * (⟪x, Delta P.G P.U x⟫ + ⟪A, P.data.Mass A⟫) ≤ C0 * ⟪A, P.data.Ginv A⟫ := by
    rw [hGA]; exact mul_le_mul_of_nonneg_left (by linarith) hC0
  exact hc.trans h2

/-- **the D-layer FORM bound** (`Ω₀` = torus): `|⟪A,Δ⁽²⁾A⟫| ≤ (2 S K2n C0) ⟪A,G⁻¹A⟫` from `‖ψ‖ ≤ S` and the quadratic ℓ¹ bound. -/
theorem formD2 (P : IngrBParams) (hOm : P.G.Om0 = Set.univ)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hB0 : ∀ ν ∈ NQp P.G P.U, P.sector.Qfull (gradL2 P.U ν) = 0)
    (C0 : ℝ) (hC0 : 0 ≤ C0) (hcoer : ∀ y : ↥(bondSupp P.G), ‖y‖ ^ 2 ≤ C0 * ⟪y, P.data.Ginv y⟫)
    (S K2n : ℝ) (hS : 0 ≤ S) (hK2n : 0 ≤ K2n) (hψ : ∀ p, ‖psiD P p‖ ≤ S)
    (hK2 : ∀ z : BondFnL2 P.Lf, ∑ p, ‖C2fullOf P.G P.U z p‖ ≤ K2n * ‖z‖ ^ 2)
    (A : ↥(bondSupp P.G)) :
    |⟪A, P.data.Delta2 P.data_laws A⟫| ≤ (2 * S * K2n * C0) * ⟪A, P.data.Ginv A⟫ := by
  have h1 := delta2_abs_le P S hψ A
  have hC2 : P.data.C2 A = C2fullOf P.G P.U (Wop P.G P.U P.a (iE P.G A)) := rfl
  rw [hC2] at h1
  have h2 := hK2 (Wop P.G P.U P.a (iE P.G A))
  have h3 := wA_le P hOm hu hB0 C0 hC0 hcoer A
  calc |⟪A, P.data.Delta2 P.data_laws A⟫|
        ≤ 2 * S * ∑ p, ‖C2fullOf P.G P.U (Wop P.G P.U P.a (iE P.G A)) p‖ := h1
    _ ≤ 2 * S * (K2n * ‖Wop P.G P.U P.a (iE P.G A)‖ ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 * S * (K2n * (C0 * ⟪A, P.data.Ginv A⟫)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hK2n) (by positivity)
    _ = (2 * S * K2n * C0) * ⟪A, P.data.Ginv A⟫ := by ring

/-- inner product against a single-site field -/
theorem inner_single_right {ι : Type*} [Fintype ι] [DecidableEq ι] (f : PiLp 2 (fun _ : ι => SuTwo)) (p : ι) (v : SuTwo) :
    ⟪f, (WithLp.toLp 2 (Pi.single p v) : PiLp 2 (fun _ : ι => SuTwo))⟫ = ⟪f p, v⟫ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single p]
  · simp [PiLp.toLp_apply]
  · intro q _ hq
    simp [PiLp.toLp_apply, Pi.single_apply, hq]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- norm bound from a bound on all pairings -/
theorem norm_le_of_pair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (w : V) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ v : V, ⟪w, v⟫ ≤ K * ‖v‖) : ‖w‖ ≤ K := by
  by_cases hw : w = 0
  · rw [hw, norm_zero]; exact hK
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h1 := h w
  rw [real_inner_self_eq_norm_sq] at h1
  have : ‖w‖ * ‖w‖ ≤ K * ‖w‖ := by nlinarith
  exact le_of_mul_le_mul_right this hpos

/-- **ψ from the ℓ¹ column bound of H and the sup of J** (`|(H*J)(b)| ≤ (Σ_b' ‖H(b',b)‖)·sup‖J‖`). -/
theorem psi_le_of_col (P : IngrBParams) (CH SJ : ℝ) (hCH : 0 ≤ CH) (hSJ : 0 ≤ SJ)
    (hcol : ∀ (p : BIdx P.G) (v : SuTwo),
      ∑ b, ‖(iE P.G (P.data.H (WithLp.toLp 2 (Pi.single p v) : FSp P.G))) b‖ ≤ CH * ‖v‖)
    (hJ : ∀ b, ‖P.Jf b‖ ≤ SJ) (p : BIdx P.G) : ‖psiD P p‖ ≤ CH * SJ := by
  classical
  refine norm_le_of_pair _ _ (mul_nonneg hCH hSJ) (fun v => ?_)
  set z : FSp P.G := WithLp.toLp 2 (Pi.single p v) with hz
  have h1 : ⟪psiD P p, v⟫ = ⟪psiD P, z⟫ := (inner_single_right (psiD P) p v).symm
  have h2 : ⟪psiD P, z⟫ = ⟪P.data.J, P.data.H z⟫ := by
    unfold psiD; rw [ContinuousLinearMap.adjoint_inner_left]
  have h3 : ⟪P.data.J, P.data.H z⟫ = ⟪P.Jf, iE P.G (P.data.H z)⟫ := by
    show ⟪pE P.G P.Jf, _⟫ = _
    rw [pE_inner_left]
  rw [h1, h2, h3, PiLp.inner_apply]
  calc ∑ b, ⟪P.Jf b, (iE P.G (P.data.H z)) b⟫ ≤ ∑ b, ‖P.Jf b‖ * ‖(iE P.G (P.data.H z)) b‖ :=
        Finset.sum_le_sum (fun b _ => real_inner_le_norm _ _)
    _ ≤ ∑ b, SJ * ‖(iE P.G (P.data.H z)) b‖ :=
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right (hJ b) (norm_nonneg _))
    _ = SJ * ∑ b, ‖(iE P.G (P.data.H z)) b‖ := by rw [Finset.mul_sum]
    _ ≤ SJ * (CH * ‖v‖) := mul_le_mul_of_nonneg_left (hcol p v) hSJ
    _ = CH * SJ * ‖v‖ := by ring

/-- the same for `ψ₁ = H₁in* Jf` -/
theorem psi1u_le_of_col (P : IngrBParams) (CH SJ : ℝ) (hCH : 0 ≤ CH) (hSJ : 0 ≤ SJ)
    (hcol : ∀ (e : Bond P.Lu) (v : SuTwo),
      ∑ b, ‖(P.H1in (WithLp.toLp 2 (Pi.single e v) : BondFnL2 P.Lu)) b‖ ≤ CH * ‖v‖)
    (hJ : ∀ b, ‖P.Jf b‖ ≤ SJ) (e : Bond P.Lu) : ‖psi1u P e‖ ≤ CH * SJ := by
  classical
  refine norm_le_of_pair _ _ (mul_nonneg hCH hSJ) (fun v => ?_)
  set z : BondFnL2 P.Lu := WithLp.toLp 2 (Pi.single e v) with hz
  have h1 : ⟪psi1u P e, v⟫ = ⟪psi1u P, z⟫ := (inner_single_right (psi1u P) e v).symm
  have h2 : ⟪psi1u P, z⟫ = ⟪P.Jf, P.H1in z⟫ := by
    unfold psi1u; rw [ContinuousLinearMap.adjoint_inner_left]
  rw [h1, h2, PiLp.inner_apply]
  calc ∑ b, ⟪P.Jf b, (P.H1in z) b⟫ ≤ ∑ b, ‖P.Jf b‖ * ‖(P.H1in z) b‖ :=
        Finset.sum_le_sum (fun b _ => real_inner_le_norm _ _)
    _ ≤ ∑ b, SJ * ‖(P.H1in z) b‖ :=
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right (hJ b) (norm_nonneg _))
    _ = SJ * ∑ b, ‖(P.H1in z) b‖ := by rw [Finset.mul_sum]
    _ ≤ SJ * (CH * ‖v‖) := mul_le_mul_of_nonneg_left (hcol e v) hSJ
    _ = CH * SJ * ‖v‖ := by ring

/-- **the J cross term from ψ₁**: `|⟪H₁in(D2in B), Jf⟫| ≤ S₁ Σ_e ‖(D2in B)(e)‖`. -/
theorem hJ_le (P : IngrBParams) (S1 : ℝ) (hψ1 : ∀ e, ‖psi1u P e‖ ≤ S1) (B : BondFnL2 P.Lu) :
    |⟪P.H1in (P.D2in B), P.Jf⟫| ≤ S1 * ∑ e, ‖(P.D2in B) e‖ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun e _ => ?_))
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [mul_comm S1]
  exact mul_le_mul_of_nonneg_left (hψ1 e) (norm_nonneg _)

#print axioms psiD
#print axioms psi1u
#print axioms delta2_pair
#print axioms delta2_abs_le
#print axioms mem_bondSupp_univ
#print axioms wA_le
#print axioms formD2
#print axioms inner_single_right
#print axioms norm_le_of_pair
#print axioms psi_le_of_col
#print axioms psi1u_le_of_col
#print axioms hJ_le

end AdalyFormal.DLayer
