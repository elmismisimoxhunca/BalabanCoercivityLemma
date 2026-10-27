import W2G

/-!
# W2H -- the EXACT patch-side input of W2: local W3 (`W3LocAt`), with no decay assumption (M1 lane W2, 2026-10-13)

The decay defect is the only non-local piece of the comparison.  Writing it out, `G0_patch − defK = locG0` where
  `locG0 S U a K A = ‖χ_P curl_U A‖² + ‖P_{V_K} D_U* A‖² + ‖√w Q A‖²`,  `V_K = lapDir(N(Q') ∩ supp K)`
(`G0_sub_defK`).  Hence the weakest patch-side statement W2 needs is
* `W3LocAt ell L U a cW d` : on every two-stratum patch tower, for `A` supported on bonds touching `Ball w s`,
  `cW · ‖A‖_w² ≤ locG0(K = Ball w (s + d ell^i))(A)` — W3 for the decoupled form with the gauge-fixing projection restricted to
  constraint-null fields supported `d` lower-stratum blocks around the support of `A`.
* `W3LocAt_of` : `W3G0At … cW ∧ OptDecayAt … δ d → W3LocAt … (cW − δ) d`;
* **`patchCoercive_W2loc`** : lane E's `PatchCoercive` from `W3LocAt` alone (same constant shape, `min(a, cW)`), EXACT: no decay
  hypothesis appears.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1W2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower BlockClosed Admissible bigSide pdist scaleUp)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLaneR6 (plaqMask)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle)
open AdalyFormal.M1Patch (patchTower)
open AdalyFormal.M1IMS (G0form Fform Ymass HatPack HolRegime etaC nuC sandwich N_le_wnorm PatchCoercive ginvForm wN ginv_form)
open AdalyFormal.M1 (IsPatch gsp patch gsp_pos wnormSq)

variable {L : PeriodicLatticeExtent}

/-- the decoupled form with the gauge-fixing projection restricted to `V_K`. -/
noncomputable def locG0 (S : Tower L) (ell k : ℕ) (U : Cfg L) (a : ℝ) (K : Set (PeriodicLatticeSite L)) (A : BondFnL2 L) : ℝ :=
  ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U A)‖ ^ 2
    + ‖(VK (geomOf ell k S) U K).starProjection (gradAdj U A)‖ ^ 2 + ‖Ymass (geomOf ell k S) U a A‖ ^ 2

theorem G0_sub_defK (S : Tower L) (ell k : ℕ) (U : Cfg L) (a : ℝ) (K : Set (PeriodicLatticeSite L)) (A : BondFnL2 L) :
    G0form S ell k U a A - defK (geomOf ell k S) U K A = locG0 S ell k U a K A := by
  unfold G0form locG0 defK
  rw [Tfull_apply, proj_split (VK (geomOf ell k S) U K) (RImage (geomOf ell k S) U) (VK_le_RImage _ _ _) (gradAdj U A)]
  unfold Rproj
  ring

/-- **local W3** (the exact patch-side input of W2). -/
def W3LocAt (ell : ℕ) (L : PeriodicLatticeExtent) (U : Cfg L) (a cW : ℝ) (d : ℕ) : Prop :=
  ∀ (i : ℕ) (Rg : Set (PeriodicLatticeSite L)), BlockClosed (ell ^ (i + 1)) Rg → (∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1) →
    ∀ (w : PeriodicLatticeSite L) (s : ℕ) (A : BondFnL2 L),
      (∀ b : Bond L, (WithLp.ofLp A) b ≠ 0 → b.1 ∈ Ball w s ∨ periodicLatticeShift b.1 b.2 ∈ Ball w s) →
      cW * wnormSq (patchTower i Rg) ell (i + 1) A ≤ locG0 (patchTower i Rg) ell (i + 1) U a (Ball w (s + d * ell ^ i)) A

theorem W3LocAt_of (ell : ℕ) (L : PeriodicLatticeExtent) (U : Cfg L) (a cW δ : ℝ) (d : ℕ)
    (hW3 : W3G0At ell L U a cW) (hDec : OptDecayAt ell L U δ d) : W3LocAt ell L U a (cW - δ) d := by
  intro i Rg hRg hdiv w s A hA
  have h1 := hW3 i Rg hRg hdiv A
  have h2 := hDec i Rg hRg hdiv w s A hA
  rw [← G0_sub_defK]
  nlinarith

open AdalyFormal.Balaban.CoarseCurl (coarseShift)

section cases
variable {ell M R k κ c : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
  (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdM : d + 32 * ell ^ 2 ≤ κ * M)

include hS hell hroom hdM in
theorem g0_caseB_loc {i j : ℕ} (hij : i ≤ j) (hik : i + 1 ≤ k) {w : PeriodicLatticeSite L}
    (hZi : Ball w ((c + 1) * gsp ell M κ j) ⊆ S.Om i)
    (hZ2 : ∀ z ∈ Ball w ((c + 1) * gsp ell M κ j), z ∉ S.Om (i + 2))
    (U Up : Cfg L) (hU : ∀ e : Bond L, pdist w e.1 ≤ (c + 1) * gsp ell M κ j → U e = Up e)
    (a cW : ℝ) (ha : 0 ≤ a) (hW3 : W3LocAt ell L Up a cW d)
    (B : BondFnL2 L)
    (hB : ∀ b : Bond L, (WithLp.ofLp B) b ≠ 0 → b.1 ∈ Ball w (c * gsp ell M κ j) ∨
      periodicLatticeShift b.1 b.2 ∈ Ball w (c * gsp ell M κ j)) :
    cW * wnormSq S ell k B ≤ G0form S ell k U a B := by
  have hell0 : 0 < ell := by omega
  have hRg : BlockClosed (ell ^ (i + 1)) (S.Om (i + 1)) :=
    blockClosed_of_mul (by have := hS.2.2.2.1 (i + 1) hik; unfold bigSide at this; exact this)
  set Z := Ball w ((c + 1) * gsp ell M κ j) with hZdef
  set K := Ball w (c * gsp ell M κ j + d * ell ^ i) with hKdef
  set X := Ball w (c * gsp ell M κ j) with hXdef
  have hpj : ell ^ (i + 2) ≤ ell ^ 2 * ell ^ j := by
    rw [← pow_add]; exact Nat.pow_le_pow_right hell0 (by omega)
  have hpi : ell ^ i ≤ ell ^ j := Nat.pow_le_pow_right hell0 hij
  have hK : ∀ x ∈ K, Ball x (32 * ell ^ (i + 2)) ⊆ Z := by
    intro x hx y hy
    have hx' : pdist w x ≤ c * gsp ell M κ j + d * ell ^ i := hx
    have hy' : pdist x y ≤ 32 * ell ^ (i + 2) := hy
    show pdist w y ≤ (c + 1) * gsp ell M κ j
    have := pdist_triangle w x y
    have hg : (d + 32 * ell ^ 2) * ell ^ j ≤ gsp ell M κ j := by
      unfold gsp bigSide
      have := Nat.mul_le_mul_right (ell ^ j) hdM
      nlinarith
    have : d * ell ^ i ≤ d * ell ^ j := Nat.mul_le_mul_left d hpi
    nlinarith
  have hXK : X ⊆ K := fun x hx => le_trans hx (Nat.le_add_right _ _)
  have hUZ : ∀ e : Bond L, e.1 ∈ Z → U e = Up e := fun e he => hU e he
  have hcmp := G0_real_ge_patch hS hell hroom hik hZi hZ2 hK hXK U Up hUZ B hB a ha
  have hw := wnorm_real_eq_patch hS hell hik hZi hZ2 hK hXK B hB
  have hdiv : ∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1 := fun μ =>
    (dvd_mul_left (ell ^ (i + 1)) M).trans (hS.2.2.1 (i + 1) hik μ)
  have h3 := hW3 i (S.Om (i + 1)) hRg hdiv w (c * gsp ell M κ j) B hB
  rw [← G0_sub_defK] at h3
  rw [hw]
  linarith

end cases

section main
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR4 : (c + 4) * κ * ell ≤ R) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdM : d + 32 * ell ^ 2 ≤ κ * M)
  {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
include hell0 hS hκ hM hell hR1 hR4 hroom hdM hW hWR

/-- **W2, exact form**: `PatchCoercive` from local W3 on the patch towers (no decay hypothesis). -/
theorem patchCoercive_W2loc (U : LinkCfg (scaleUp ell k Lu)) (a cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ) (ε1 : ℝ) (hε1 : 0 < ε1) (hη : etaC ell W cs ρ ε1 < 1)
    (Up : ℕ → PeriodicLatticeSite (scaleUp ell k Lu) → Cfg (scaleUp ell k Lu))
    (hUp : ∀ j w, IsPatch ell M k κ S j w → ∀ e : Bond (scaleUp ell k Lu),
      pdist w e.1 ≤ (c + 1) * gsp ell M κ j → U e = Up j w e)
    (cW : ℝ)
    (hW3 : ∀ j w, IsPatch ell M k κ S j w → W3LocAt ell (scaleUp ell k Lu) (Up j w) a cW d) :
    PatchCoercive ell M k κ c Lu hell0 S U a Lam ((1 - etaC ell W cs ρ ε1) * min a cW - 2 * nuC ell ρ) := by
  intro j w hpj A hA
  have ha0 : 0 ≤ a := hp.ha.le
  set B : BondFnL2 (scaleUp ell k Lu) := (A : BondFnL2 (scaleUp ell k Lu)) with hBdef
  have hFA : ginvForm ell k Lu hell0 S U a Lam A = Fform S ell k U a B := by
    unfold ginvForm
    rw [ginv_form hell0 S U a Lam ha0 hp.hu]
    rfl
  have hsand := (sandwich hS hell hR1 (by omega) hW hWR U a cs hp ρ hρ hreg ε1 hε1 B).1
  have hN := N_le_wnorm hS hell0 B
  have hBsupp : ∀ b : Bond (scaleUp ell k Lu), (WithLp.ofLp B) b ≠ 0 →
      b.1 ∈ Ball w (c * gsp ell M κ j) ∨ periodicLatticeShift b.1 b.2 ∈ Ball w (c * gsp ell M κ j) := hA
  have hOm0 : ∀ b : Bond (scaleUp ell k Lu), (WithLp.ofLp B) b ≠ 0 →
      b.1 ∈ S.Om 0 ∨ periodicLatticeShift b.1 b.2 ∈ S.Om 0 := by
    intro b hb
    by_contra hn
    exact hb (A.2 b hn)
  have hw0 : 0 ≤ wnormSq S ell k B := by unfold wnormSq; exact Finset.sum_nonneg (fun b _ => by positivity)
  have hG0 : min a cW * wnormSq S ell k B ≤ G0form S ell k U a B := by
    by_cases hB : ∃ y ∈ Ball w ((c + 1) * gsp ell M κ j), y ∈ S.Om (j + 1)
    · obtain ⟨hjk, hZi, hZ2⟩ := caseB_up hS hell hκ hM hR4 hpj hB
      have h := g0_caseB_loc hS hell hroom hdM (le_refl j) hjk hZi hZ2 U (Up j w) (hUp j w hpj) a cW ha0
        (hW3 j w hpj) B hBsupp
      have hm := min_le_right a cW
      nlinarith
    · by_cases hj : 1 ≤ j
      · have hZi := caseB_down hS hell hκ hM hR4 hpj hj
        have hZ2 : ∀ z ∈ Ball w ((c + 1) * gsp ell M κ j), z ∉ S.Om (j - 1 + 2) := by
          rw [show j - 1 + 2 = j + 1 by omega]
          intro z hz hz1
          exact hB ⟨z, hz, hz1⟩
        have h := g0_caseB_loc hS hell hroom hdM (i := j - 1) (by omega) (by have := hpj.1; omega) hZi hZ2 U (Up j w)
          (hUp j w hpj) a cW ha0 (hW3 j w hpj) B hBsupp
        have hm := min_le_right a cW
        nlinarith
      · have hj0 : j = 0 := by omega
        have hg := gsp_pos hκ hM hell0 (ell := ell) j
        have hZ1 : ∀ z ∈ Ball w (c * gsp ell M κ j + 1), z ∉ S.Om 1 := by
          intro z hz hz1
          refine hB ⟨z, ?_, by rw [hj0]; exact hz1⟩
          have hz' : pdist w z ≤ c * gsp ell M κ j + 1 := hz
          show pdist w z ≤ (c + 1) * gsp ell M κ j
          nlinarith
        have h := g0_caseA hS hell hκ hM hZ1 U a ha0 B hOm0 hBsupp
        have hm := min_le_left a cW
        nlinarith
  rw [hFA]
  show ((1 - etaC ell W cs ρ ε1) * min a cW - 2 * nuC ell ρ) * wnormSq S ell k B ≤ Fform S ell k U a B
  have hη1 : 0 ≤ 1 - etaC ell W cs ρ ε1 := by linarith
  have hν : 0 ≤ nuC ell ρ := by
    unfold nuC; have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num); positivity
  have hs' : (1 - etaC ell W cs ρ ε1) * G0form S ell k U a B
      - 2 * nuC ell ρ * ‖AdalyFormal.DLayer.bondWt (-AdalyFormal.M1IMS.sigG (geomOf ell k S)) B‖ ^ 2
      ≤ Fform S ell k U a B := hsand
  have h1 := mul_le_mul_of_nonneg_left hG0 hη1
  have h2 := mul_le_mul_of_nonneg_left hN (by linarith : (0 : ℝ) ≤ 2 * nuC ell ρ)
  nlinarith

end main

end AdalyFormal.M1W2

#print axioms AdalyFormal.M1W2.locG0
#print axioms AdalyFormal.M1W2.G0_sub_defK
#print axioms AdalyFormal.M1W2.W3LocAt
#print axioms AdalyFormal.M1W2.W3LocAt_of
#print axioms AdalyFormal.M1W2.g0_caseB_loc
#print axioms AdalyFormal.M1W2.patchCoercive_W2loc
