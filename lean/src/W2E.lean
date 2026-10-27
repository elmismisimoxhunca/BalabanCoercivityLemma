import W2D

/-!
# W2E -- **W2 closed as a reduction**: lane E's `PatchCoercive` from W3 on the decoupled form + the decay defect bound
(M1 lane W2, 2026-10-13)

* **`patchCoercive_W2`** : on `G = geomOf ell k S` (admissible), with lane E's sandwich hypotheses (`HatPack`, `HolRegime`, `ε₁ > 0`,
  `etaC < 1` -- the W4 hypotheses), room `(c+4) κ ell ≤ R`, `17 ell ≤ R M`, `d + 32 ell² ≤ κ M`, and for every patch `(j, w)` a
  configuration `Up j w` equal to `U` on the bonds based within `(c+1) G_j` of `w` satisfying `W3G0At … cW` and
  `OptDecayAt … δ d` (W2D), lane E's interface holds:
    `PatchCoercive … U … ((1 − etaC) · min(a, cW − δ) − 2 · nuC)`.
  The constant loss is explicit and free of `k`, `Lu`, `S`, `U`.
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
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle)
open AdalyFormal.M1IMS (G0form Fform HatPack HolRegime etaC nuC sandwich N_le_wnorm PatchCoercive ginvForm wN ginv_form)
open AdalyFormal.M1 (IsPatch gsp patch gsp_pos wnormSq)

section main
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR4 : (c + 4) * κ * ell ≤ R) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdM : d + 32 * ell ^ 2 ≤ κ * M)
  {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
include hell0 hS hκ hM hell hR1 hR4 hroom hdM hW hWR

theorem wnormSq_nonneg' (S' : Tower (scaleUp ell k Lu)) (B : BondFnL2 (scaleUp ell k Lu)) : 0 ≤ wnormSq S' ell k B := by
  unfold wnormSq; exact Finset.sum_nonneg (fun b _ => by positivity)

/-- **W2 (`ginv_locality`) as the W4 interface**: `PatchCoercive` from the patch-tower inputs. -/
theorem patchCoercive_W2 (U : LinkCfg (scaleUp ell k Lu)) (a cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ) (ε1 : ℝ) (hε1 : 0 < ε1) (hη : etaC ell W cs ρ ε1 < 1)
    (Up : ℕ → PeriodicLatticeSite (scaleUp ell k Lu) → Cfg (scaleUp ell k Lu))
    (hUp : ∀ j w, IsPatch ell M k κ S j w → ∀ e : Bond (scaleUp ell k Lu),
      pdist w e.1 ≤ (c + 1) * gsp ell M κ j → U e = Up j w e)
    (cW δ : ℝ)
    (hW3 : ∀ j w, IsPatch ell M k κ S j w → W3G0At ell (scaleUp ell k Lu) (Up j w) a cW)
    (hDec : ∀ j w, IsPatch ell M k κ S j w → OptDecayAt ell (scaleUp ell k Lu) (Up j w) δ d) :
    PatchCoercive ell M k κ c Lu hell0 S U a Lam ((1 - etaC ell W cs ρ ε1) * min a (cW - δ) - 2 * nuC ell ρ) := by
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
  have hw0 := wnormSq_nonneg' hell0 hS hκ hM hell hR1 hR4 hroom hdM hW hWR S B
  have hG0 : min a (cW - δ) * wnormSq S ell k B ≤ G0form S ell k U a B := by
    by_cases hB : ∃ y ∈ Ball w ((c + 1) * gsp ell M κ j), y ∈ S.Om (j + 1)
    · obtain ⟨hjk, hZi, hZ2⟩ := caseB_up hS hell hκ hM hR4 hpj hB
      have h := g0_caseB hS hell hκ hM hroom hdM (le_refl j) hjk hZi hZ2 U (Up j w) (hUp j w hpj) a cW δ ha0
        (hW3 j w hpj) (hDec j w hpj) B hBsupp
      have hm := min_le_right a (cW - δ)
      nlinarith
    · by_cases hj : 1 ≤ j
      · have hZi := caseB_down hS hell hκ hM hR4 hpj hj
        have hZ2 : ∀ z ∈ Ball w ((c + 1) * gsp ell M κ j), z ∉ S.Om (j - 1 + 2) := by
          rw [show j - 1 + 2 = j + 1 by omega]
          intro z hz hz1
          exact hB ⟨z, hz, hz1⟩
        have h := g0_caseB hS hell hκ hM hroom hdM (i := j - 1) (by omega) (by have := hpj.1; omega) hZi hZ2 U (Up j w)
          (hUp j w hpj) a cW δ ha0 (hW3 j w hpj) (hDec j w hpj) B hBsupp
        have hm := min_le_right a (cW - δ)
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
        have hm := min_le_left a (cW - δ)
        nlinarith
  rw [hFA]
  show ((1 - etaC ell W cs ρ ε1) * min a (cW - δ) - 2 * nuC ell ρ) * wnormSq S ell k B ≤ Fform S ell k U a B
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

#print axioms AdalyFormal.M1W2.wnormSq_nonneg'
#print axioms AdalyFormal.M1W2.patchCoercive_W2
