import RI1

/-!
# RI2 -- the twisted-source operator `T = Q_U ∘ EU` is invertible with a `k`-free `nD` bound (lane m2_rightinv_20261015)

`SrcOK hell U γ cS cT` : the W6 per-source bounds (chart defect `Dvec`, full vector `Tvec`) in the `F` weight, for EVERY row.
From it (W6 `Tlin_row`, `Nlin_Nlin`, `card_inter`, RI1):
* `nD_Sfun` : `nD(S y) ≤ sD nD y`, `sD = mult0 ℓ² cS`;  `nD_Tlin` : `nD(T y) ≤ mult0 ℓ² cT nD y`;  `nD_Nlin` : `nD(N y) ≤ AD nD y`;
* **`Tlin_rightInv`** : if `4 sD (1 + AD) ≤ 1/2` then for every `u` there is `v` with `T v = u`, `nD v ≤ 8 (1 + AD) nD u`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2RightInv

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.W6 (nD wD wD_pos nD_nonneg nD_add_le nF wF)
open AdalyFormal.M2W6 (Inter Dvec Tvec Sfun Tlin Nlin Slin Dfun Tlin_row T_split Slin_apply Nlin_Nlin Sfun_eq_sum
  Tlin_eq_sum card_inter Tvec_eq Qfull_zero_of_not_inter mult0)

/-- the `D`-norm constant of the defect part -/
def sD (ell : ℕ) (cS : ℝ) : ℝ := mult0 ell * ((ell : ℝ) ^ 2 * cS)

/-- the `D`-norm constant of the cross-level part -/
def AD (ell : ℕ) (cS cT : ℝ) : ℝ := 4 * (mult0 ell * ((ell : ℝ) ^ 2 * cT)) + 4 + 2 * sD ell cS

theorem mult0_nonneg (ell : ℕ) : 0 ≤ mult0 ell := by unfold mult0; positivity

theorem sD_nonneg (ell : ℕ) {cS : ℝ} (h : 0 ≤ cS) : 0 ≤ sD ell cS := by
  unfold sD; have := mult0_nonneg ell; positivity

theorem AD_nonneg (ell : ℕ) {cS cT : ℝ} (hS : 0 ≤ cS) (hT : 0 ≤ cT) : 0 ≤ AD ell cS cT := by
  unfold AD; have := mult0_nonneg ell; have := sD_nonneg ell hS; positivity

section src
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **per-source bounds for every row** -/
def SrcOK (hell : 0 < ell) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (cS cT : ℝ) : Prop :=
  ∀ (p : BIdx (geomOf ell k S)) (w : SuTwo), nF (Dvec hell U γ p w) ≤ cS * (wF p * ‖w‖ ^ 2) ∧
    nF (Tvec hell U γ p w) ≤ cT * (wF p * ‖w‖ ^ 2)

variable (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hroom : 17 * ell ≤ R * M)

include hell2 hS hM hroom in
theorem Dvec_supp (U : LinkCfg (scaleUp ell k Lu)) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (p p' : BIdx (geomOf ell k S)) (hI : ¬ Inter p' p) (w : SuTwo) : Dvec (by omega) U γ p w p' = 0 := by
  show RMap _ ((Dfun (by omega) U γ p (RMap ((γ p) p.2.1.1) w)) p') = 0
  unfold Dfun
  rw [PiLp.sub_apply, Qfull_zero_of_not_inter hell2 hS hM hroom (periodicGaugeTransform (γ p) U) p p' hI _,
    Qfull_zero_of_not_inter hell2 hS hM hroom (trivialU _) p p' hI _, sub_zero, map_zero]

include hell2 hS hM hroom in
theorem Tvec_supp (U : LinkCfg (scaleUp ell k Lu)) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (p p' : BIdx (geomOf ell k S)) (hI : ¬ Inter p' p) (w : SuTwo) : Tvec (by omega) U γ p w p' = 0 := by
  rw [Tvec_eq, Qfull_zero_of_not_inter hell2 hS hM hroom (periodicGaugeTransform (γ p) U) p p' hI _, map_zero]

include hell2 hS hM hroom in
theorem nD_Sfun (U : LinkCfg (scaleUp ell k Lu)) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) {cS cT : ℝ}
    (hok : SrcOK (by omega) U γ cS cT) (hcS : 0 ≤ cS) (y : FSp (geomOf ell k S)) :
    nD (Sfun (by omega) U γ y) ≤ sD ell cS * nD y := by
  classical
  have hell : 0 < ell := by omega
  rw [Sfun_eq_sum]
  have hsp := nD_sum_sparse hell (9 * (24 * ell + 1) ^ 3) (fun p => Dvec hell U γ p (y p))
    (fun p p' hI => Dvec_supp hell2 hS hM hroom U γ p p' hI (y p)) (fun p' => card_inter hell p')
  refine hsp.trans ?_
  have hc : (((9 * (24 * ell + 1) ^ 3 : ℕ)) : ℝ) = mult0 ell := by unfold mult0; push_cast; ring
  rw [hc]
  have h1 : ∑ p, nD (Dvec hell U γ p (y p)) ≤ (ell : ℝ) ^ 2 * cS * nD y := by
    calc ∑ p, nD (Dvec hell U γ p (y p)) ≤ ∑ p, (ell : ℝ) ^ 2 * cS * (wD p * ‖y p‖ ^ 2) :=
          Finset.sum_le_sum (fun p _ => nD_src hell p _ (fun p' hI => Dvec_supp hell2 hS hM hroom U γ p p' hI (y p))
            cS (y p) (hok p (y p)).1)
      _ = (ell : ℝ) ^ 2 * cS * nD y := by rw [← Finset.mul_sum]; rfl
  have hm := mult0_nonneg ell
  calc mult0 ell * ∑ p, nD (Dvec hell U γ p (y p)) ≤ mult0 ell * ((ell : ℝ) ^ 2 * cS * nD y) :=
        mul_le_mul_of_nonneg_left h1 hm
    _ = sD ell cS * nD y := by unfold sD; ring

include hell2 hS hM hroom in
theorem nD_Tlin (U : LinkCfg (scaleUp ell k Lu)) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) {cS cT : ℝ}
    (hok : SrcOK (by omega) U γ cS cT) (y : FSp (geomOf ell k S)) :
    nD (Tlin (by omega) U γ y) ≤ mult0 ell * ((ell : ℝ) ^ 2 * cT) * nD y := by
  classical
  have hell : 0 < ell := by omega
  rw [Tlin_eq_sum]
  have hsp := nD_sum_sparse hell (9 * (24 * ell + 1) ^ 3) (fun p => Tvec hell U γ p (y p))
    (fun p p' hI => Tvec_supp hell2 hS hM hroom U γ p p' hI (y p)) (fun p' => card_inter hell p')
  refine hsp.trans ?_
  have hc : (((9 * (24 * ell + 1) ^ 3 : ℕ)) : ℝ) = mult0 ell := by unfold mult0; push_cast; ring
  rw [hc]
  have h1 : ∑ p, nD (Tvec hell U γ p (y p)) ≤ (ell : ℝ) ^ 2 * cT * nD y := by
    calc ∑ p, nD (Tvec hell U γ p (y p)) ≤ ∑ p, (ell : ℝ) ^ 2 * cT * (wD p * ‖y p‖ ^ 2) :=
          Finset.sum_le_sum (fun p _ => nD_src hell p _ (fun p' hI => Tvec_supp hell2 hS hM hroom U γ p p' hI (y p))
            cT (y p) (hok p (y p)).2)
      _ = (ell : ℝ) ^ 2 * cT * nD y := by rw [← Finset.mul_sum]; rfl
  have hm := mult0_nonneg ell
  calc mult0 ell * ∑ p, nD (Tvec hell U γ p (y p)) ≤ mult0 ell * ((ell : ℝ) ^ 2 * cT * nD y) :=
        mul_le_mul_of_nonneg_left h1 hm
    _ = mult0 ell * ((ell : ℝ) ^ 2 * cT) * nD y := by ring

include hell2 hS hM hroom in
theorem nD_Nlin (hR : 8 * ell ≤ R) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) {cS cT : ℝ}
    (hok : SrcOK (by omega) U γ cS cT) (hcS : 0 ≤ cS) (y : FSp (geomOf ell k S)) :
    nD (Nlin (by omega) γ y) ≤ AD ell cS cT * nD y := by
  have hell : 0 < ell := by omega
  have hM1 : 1 ≤ M := hM
  have e : Nlin hell γ y = Tlin hell U γ y + -y + -(Sfun hell U γ y) := by
    have := Tlin_row hell hell2 hS hM1 hR U γ y
    rw [this]; abel
  rw [e]
  have h1 := nD_add_le hell (Tlin hell U γ y + -y) (-(Sfun hell U γ y))
  have h2 := nD_add_le hell (Tlin hell U γ y) (-y)
  rw [nD_neg] at h1 h2
  have h3 := nD_Tlin hell2 hS hM hroom U γ hok y
  have h4 := nD_Sfun hell2 hS hM hroom U γ hok hcS y
  have h0 := nD_nonneg hell y
  unfold AD
  nlinarith

include hell2 hS hM hroom in
/-- **the twisted-source operator is onto, with a `k`-free inverse bound** -/
theorem Tlin_rightInv (hR : 8 * ell ≤ R) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) {cS cT : ℝ}
    (hok : SrcOK (by omega) U γ cS cT) (hcS : 0 ≤ cS) (hcT : 0 ≤ cT)
    (hsmall : 4 * sD ell cS * (1 + AD ell cS cT) ≤ 1 / 2) (u : FSp (geomOf ell k S)) :
    ∃ v : FSp (geomOf ell k S), Tlin (by omega) U γ v = u ∧ nD v ≤ 8 * (1 + AD ell cS cT) * nD u := by
  have hell : 0 < ell := by omega
  have hM1 : 1 ≤ M := hM
  have hSb : ∀ y, nD (Slin hell U γ y) ≤ sD ell cS * nD y := fun y => by
    rw [Slin_apply hell hell2 hS hM1 hR U γ y]
    exact nD_Sfun hell2 hS hM hroom U γ hok hcS y
  have hNb : ∀ y, nD (Nlin hell γ y) ≤ AD ell cS cT * nD y := fun y => nD_Nlin hell2 hS hM hroom hR U γ hok hcS y
  have hbd : ∀ y, nD y ≤ 8 * (1 + AD ell cS cT) * nD (Tlin hell U γ y) := fun y =>
    bound_of_perturbed (fun y : FSp (geomOf ell k S) => nD y) (fun y => nD_nonneg hell y) (nD_add_le hell) nD_neg
      (Nlin hell γ) (Slin hell U γ) (Tlin hell U γ) (fun y => T_split hell U γ y)
      (fun y => Nlin_Nlin hell hell2 hS hM1 hR γ y) (AD ell cS cT) (sD ell cS) hNb hSb (sD_nonneg ell hcS)
      (AD_nonneg ell hcS hcT) hsmall y
  have hinj : Function.Injective (Tlin hell U γ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := hbd y
    rw [hy] at h1
    have h0 : nD (0 : FSp (geomOf ell k S)) = 0 := by unfold nD; simp
    rw [h0, mul_zero] at h1
    exact eq_zero_of_nD hell y h1
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) u
  refine ⟨v, hv, ?_⟩
  have := hbd v
  rw [hv] at this
  exact this

end src

end AdalyFormal.M2RightInv

#print axioms AdalyFormal.M2RightInv.sD
#print axioms AdalyFormal.M2RightInv.AD
#print axioms AdalyFormal.M2RightInv.mult0_nonneg
#print axioms AdalyFormal.M2RightInv.sD_nonneg
#print axioms AdalyFormal.M2RightInv.AD_nonneg
#print axioms AdalyFormal.M2RightInv.SrcOK
#print axioms AdalyFormal.M2RightInv.Dvec_supp
#print axioms AdalyFormal.M2RightInv.Tvec_supp
#print axioms AdalyFormal.M2RightInv.nD_Sfun
#print axioms AdalyFormal.M2RightInv.nD_Tlin
#print axioms AdalyFormal.M2RightInv.nD_Nlin
#print axioms AdalyFormal.M2RightInv.Tlin_rightInv
