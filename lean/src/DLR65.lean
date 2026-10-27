import DLR64
import DLR29
import R2Raw3
import R2Flat3
import RKL2

/-!
# DL65 -- even-part bounds for the AXIAL-GAUGE pieces of the raw step (63)/(89): `rProd`, `log rProd`, `sBlock`, `exp(±sBlock)`

Setting: background `V0` (any), stride `s > 0`, blocking `ell ≥ 1`, `N = 3 ell`; three configurations `V1p, V1m` (the field at
`±t`) and `V1z = 1` (at `t = 0`) with link-wise `EvQ (V1p e) (V1m e) 1 6 4 τ` (`EvQ.base`).  Every path used has length `≤ N`
(`DL29.gamma_len_le`).  Constants (`Ke`, `Kd` at scale `τ`):
* `hol` of `V1·V0` along a path of length `≤ N` : `(38N², 4N)`;  `rProd` : `(38N², 4N)`;
* `log rProd` (base `rProd(V0,1) = 1`) : `(1036N², 8N)`;  `sBlock` (average, weight `ell⁻³`, `#block ≤ ell³`) : `(1036N², 8N)`;
* `exp(±sBlock)` (base `exp 0 = 1`) : `(4912N², 56N)`.
Smallness used: `4Nτ ≤ 1/4`, `8Nτ ≤ 1/2`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp su2Angle su2NegOne coe_mul coe_inv coe_one
  su2Log_one su2Exp_zero)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.IngredientFamilyR2 (rProd rProd_eq rProd_one_right sBlock qsmul_real Wt rat_cast_Wt su2Log_mem_suTwo)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

/-- the hypothesis on the three configurations -/
def LinkEv (V1p V1m : PeriodicLinkConfiguration SU2 L) (τ : ℝ) : Prop :=
  ∀ e, EvQ ((V1p e : SU2) : Mt) ((V1m e : SU2) : Mt) ((1 : SU2) : Mt) 6 4 τ

theorem linkEv_prod {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ} (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ)
    (V0 : PeriodicLinkConfiguration SU2 L) (e : PeriodicLatticeEdge L) :
    EvQ ((V1p e * V0 e : SU2) : Mt) ((V1m e * V0 e : SU2) : Mt) (((fun _ => (1 : SU2)) e * V0 e : SU2) : Mt) 6 4 τ := by
  have := (h e).mul (EvQ.const1 (V0 e) τ)
  exact this.mono hτ (by norm_num) (by norm_num)

/-- holonomy of `V1·V0` along a path of length `≤ N` -/
theorem ev_hol (s : ℕ) {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ} (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ)
    (V0 : PeriodicLinkConfiguration SU2 L) (N : ℝ) (hN : 1 ≤ N) (y : PeriodicLatticeSite L) (p : List (Fin 3))
    (hp : (p.length : ℝ) ≤ N) :
    EvQ ((coarsePathHolonomy s (fun b => V1p b * V0 b) y p : SU2) : Mt)
      ((coarsePathHolonomy s (fun b => V1m b * V0 b) y p : SU2) : Mt)
      ((coarsePathHolonomy s (fun b => (fun _ => (1 : SU2)) b * V0 b) y p : SU2) : Mt) (38 * N ^ 2) (4 * N) τ := by
  have hh := EvQ.hol s (fun b => V1p b * V0 b) (fun b => V1m b * V0 b) (fun b => (fun _ => (1 : SU2)) b * V0 b)
    6 4 τ (by norm_num) (by norm_num) hτ (fun e => linkEv_prod hτ h V0 e) p y
  have hn0 : (0 : ℝ) ≤ p.length := Nat.cast_nonneg _
  refine hh.mono hτ ?_ ?_
  · nlinarith
  · nlinarith

theorem ev_rProd (s : ℕ) {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ} (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ)
    (V0 : PeriodicLinkConfiguration SU2 L) (N : ℝ) (hN : 1 ≤ N) (y : PeriodicLatticeSite L) (p : List (Fin 3))
    (hp : (p.length : ℝ) ≤ N) :
    EvQ ((rProd s V0 V1p y p : SU2) : Mt) ((rProd s V0 V1m y p : SU2) : Mt)
      ((rProd s V0 (fun _ => (1 : SU2)) y p : SU2) : Mt) (38 * N ^ 2) (4 * N) τ := by
  rw [rProd_eq, rProd_eq, rProd_eq]
  have := (ev_hol s hτ h V0 N hN y p hp).mul (EvQ.const1 ((coarsePathHolonomy s V0 y p)⁻¹) τ)
  exact this.mono hτ (by norm_num) (by norm_num)

theorem ev_log_rProd (s : ℕ) {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ} (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ)
    (V0 : PeriodicLinkConfiguration SU2 L) (N : ℝ) (hN : 1 ≤ N) (hsm : 4 * N * τ ≤ 1 / 4)
    (y : PeriodicLatticeSite L) (p : List (Fin 3)) (hp : (p.length : ℝ) ≤ N) :
    EvQ (su2Log (rProd s V0 V1p y p)) (su2Log (rProd s V0 V1m y p))
      (su2Log (rProd s V0 (fun _ => (1 : SU2)) y p)) (1036 * N ^ 2) (8 * N) τ := by
  have h1 := ev_rProd s hτ h V0 N hN y p hp
  have hb : rProd s V0 (fun _ => (1 : SU2)) y p = 1 := rProd_one_right s V0 y p
  have hg0 : frobNorm (((rProd s V0 (fun _ => (1 : SU2)) y p : SU2) : Mt) - 1) ≤ 1 := by
    rw [hb, coe_one, sub_self, fN_zero]; norm_num
  have hE : 2 * (Real.exp (Real.sqrt 2 * frobNorm (su2Log (rProd s V0 (fun _ => (1 : SU2)) y p))) - 1) ≤ 1 / 2 := by
    rw [hb, su2Log_one, fN_zero, mul_zero, Real.exp_zero]; norm_num
  have := EvQ.log hτ h1 hsm hg0 hE
  exact this.mono hτ (by nlinarith) (by nlinarith)

theorem sBlock_eq_Wt (s ell : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) :
    sBlock s ell V0 V1 y
      = ∑ x ∈ stepBlockOf y s ell, Wt ell • su2Log (rProd s V0 V1 y (coarseGammaPath s y x)) := by
  unfold sBlock
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [qsmul_real, rat_cast_Wt]

theorem Wt_card (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (y : PeriodicLatticeSite L) :
    Wt ell * ((stepBlockOf y s ell).card : ℝ) ≤ 1 := by
  have hc := AdalyFormal.RegBgKU.card_le_real y (ell := ell) hs
  have hl : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  unfold Wt
  rw [inv_mul_le_iff₀ hl]; linarith

theorem Wt_nonneg (ell : ℕ) : 0 ≤ Wt ell := by unfold Wt; positivity

theorem ev_sBlock (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ}
    (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ) (V0 : PeriodicLinkConfiguration SU2 L) (N : ℝ)
    (hN : 3 * (ell : ℝ) ≤ N) (hsm : 4 * N * τ ≤ 1 / 4) (y : PeriodicLatticeSite L) :
    EvQ (sBlock s ell V0 V1p y) (sBlock s ell V0 V1m y) (sBlock s ell V0 (fun _ => (1 : SU2)) y)
      (1036 * N ^ 2) (8 * N) τ := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hN1 : 1 ≤ N := by linarith
  rw [sBlock_eq_Wt, sBlock_eq_Wt, sBlock_eq_Wt]
  refine EvQ.avg _ (Wt ell) (Wt_nonneg ell) (Wt_card s ell hs hell y) _ _ _ _ _ τ (by positivity) (by positivity)
    (fun x hx => ?_) hτ
  have hlen := gamma_len_le s ell hs y x hx
  have hlen' : ((coarseGammaPath s y x).length : ℝ) ≤ N := by
    have : ((coarseGammaPath s y x).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
      have h3 : ((3 * (ell - 1) : ℕ) : ℝ) = 3 * ((ell : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; norm_num
      rw [← h3]; exact_mod_cast hlen
    linarith
  exact ev_log_rProd s hτ h V0 N hN1 hsm y _ hlen'

theorem sBlock_one (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) :
    sBlock s ell V0 (fun _ => (1 : SU2)) y = 0 := by
  unfold sBlock
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [rProd_one_right, su2Log_one, smul_zero]

theorem sBlock_mem (s ell : ℕ) (V0 V1 : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L) :
    sBlock s ell V0 V1 y ∈ AdalyFormal.Balaban.CovariantOperators.suTwo := by
  rw [sBlock_eq_Wt]
  exact Submodule.sum_mem _ (fun x _ => Submodule.smul_mem _ _ (su2Log_mem_suTwo _))

theorem su2Exp_coe {X : Mt} (hX : X ∈ AdalyFormal.Balaban.CovariantOperators.suTwo) :
    ((su2Exp X : SU2) : Mt) = NormedSpace.exp X :=
  AdalyFormal.Balaban.SmoothLog.su2Exp_coe_of_mem_suTwo hX.1 hX.2

/-- `exp(σ·sBlock)`, `σ = ±1` -/
theorem ev_exp_sBlock (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ}
    (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ) (V0 : PeriodicLinkConfiguration SU2 L) (N : ℝ)
    (hN : 3 * (ell : ℝ) ≤ N) (hsm : 4 * N * τ ≤ 1 / 4) (y : PeriodicLatticeSite L) (σ : ℝ) (hσ : |σ| = 1) :
    EvQ ((su2Exp (σ • sBlock s ell V0 V1p y) : SU2) : Mt) ((su2Exp (σ • sBlock s ell V0 V1m y) : SU2) : Mt)
      ((su2Exp (σ • sBlock s ell V0 (fun _ => (1 : SU2)) y) : SU2) : Mt) (4912 * N ^ 2) (56 * N) τ := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hN1 : 1 ≤ N := by linarith
  have h1 := (ev_sBlock s ell hs hell hτ h V0 N hN hsm y).smul σ
  rw [hσ, one_mul, one_mul] at h1
  have m1 := Submodule.smul_mem _ σ (sBlock_mem s ell V0 V1p y)
  have m2 := Submodule.smul_mem _ σ (sBlock_mem s ell V0 V1m y)
  have m3 := Submodule.smul_mem _ σ (sBlock_mem s ell V0 (fun _ => (1 : SU2)) y)
  rw [su2Exp_coe m1, su2Exp_coe m2, su2Exp_coe m3]
  have hE : Real.exp (Real.sqrt 2 * frobNorm (σ • sBlock s ell V0 (fun _ => (1 : SU2)) y)) ≤ 2 := by
    rw [sBlock_one, smul_zero, fN_zero, mul_zero, Real.exp_zero]; norm_num
  have h2 := EvQ.exp hτ h1 (by nlinarith) hE
  exact h2.mono hτ (by nlinarith) (by nlinarith)

#print axioms ev_hol
#print axioms ev_rProd
#print axioms ev_log_rProd
#print axioms ev_sBlock
#print axioms ev_exp_sBlock

end AdalyFormal.DLayer
