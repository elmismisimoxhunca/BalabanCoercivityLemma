import NP11
import LV10

/-!
# NP12 -- `PatchCoercive` at NON-FLAT `U` in lane B's M1 regime (m1_patch_nonflat, 2026-10-14)

* `g0_caseB_nf` : W2H `g0_caseB_loc` with (a) the agreement set `Z' = Ball w (c G_j + d ell^i + 32 ell^{i+2})` passed to
  W2C3 `G0_real_ge_patch` (its `Z` is a free set) instead of `Ball w ((c+1) G_j)`, and (b) the local-W3 input at ONE
  instance (the real patch, level `i`) instead of W2H's all-levels `W3LocAt`.
* **`patchCoercive_nonflat`** : for `2 ≤ ell`, `0 < a` there are `cW > 0`, `a₀ > 0` and `D` (depending on `ell`, `a` only),
  with `epsNF ell (PkA a) (thetaN ell) d ≤ cW/2` for `d ≥ D`, such that for every admissible tower, room
  `(c+4)κ ell ≤ R`, `17 ell ≤ R M`, `D ≤ d`, `d + 64 ell² ≤ κ M`, lane E's sandwich hypotheses, and every `U` in lane B's
  regime `M1Regular ell M 12 k S α₀ (ell^k)⁻¹ U` with `0 < α₀`, `12 M α₀ ≤ a₀`:
  `PatchCoercive … U a Lam ((1 − etaC)·min a (cW − epsNF ell (PkA a) (thetaN ell) d) − 2 nuC)`.
  `cW = 1/(ell² KG0 a (CS·KV))` (lane D's `lemIFlat` constant).  No named input.
  Difference from DG `patchCoercive_flat`: room `d + 64 ell² ≤ κM` (was `+ 32 ell²`), the flatness hypothesis `_hflat`
  replaced by `M1Regular` with `12 M α₀ ≤ a₀`, and the decay constant `epsNF` in place of `epsD`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane (Tower BlockClosed Admissible bigSide pdist scaleUp)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle)
open AdalyFormal.M1Patch (patchTower LemIFlat Kflat)
open AdalyFormal.RegBgKU (KUSmall kapHat)
open AdalyFormal.W3NF (lamC ThetaP KG0 KG0_pos rhoM1)
open AdalyFormal.M1IMS (G0form Fform HatPack HolRegime etaC nuC sandwich N_le_wnorm PatchCoercive ginvForm wN ginv_form)
open AdalyFormal.M1 (IsPatch gsp patch gsp_pos wnormSq)
open AdalyFormal.M1W2 (locG0 G0_sub_defK G0_real_ge_patch wnorm_real_eq_patch blockClosed_of_mul caseB_up caseB_down
  g0_caseA)

variable {L : PeriodicLatticeExtent}

section cases
variable {ell M R k κ c : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
  (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdM : d + 64 * ell ^ 2 ≤ κ * M)

include hS hell hroom hdM in
theorem g0_caseB_nf {i j : ℕ} (hij : i ≤ j) (hik : i + 1 ≤ k) {w : PeriodicLatticeSite L}
    (hZi : Ball w ((c + 1) * gsp ell M κ j) ⊆ S.Om i)
    (hZ2 : ∀ z ∈ Ball w ((c + 1) * gsp ell M κ j), z ∉ S.Om (i + 2))
    (U Up : Cfg L)
    (hU : ∀ e : Bond L, pdist w e.1 ≤ c * gsp ell M κ j + d * ell ^ i + 32 * ell ^ (i + 2) → U e = Up e)
    (a cW : ℝ) (ha : 0 ≤ a)
    (hW3 : ∀ B : BondFnL2 L, (∀ b : Bond L, (WithLp.ofLp B) b ≠ 0 →
          b.1 ∈ Ball w (c * gsp ell M κ j) ∨ periodicLatticeShift b.1 b.2 ∈ Ball w (c * gsp ell M κ j)) →
        cW * wnormSq (patchTower i (S.Om (i + 1))) ell (i + 1) B
          ≤ locG0 (patchTower i (S.Om (i + 1))) ell (i + 1) Up a (Ball w (c * gsp ell M κ j + d * ell ^ i)) B)
    (B : BondFnL2 L)
    (hB : ∀ b : Bond L, (WithLp.ofLp B) b ≠ 0 → b.1 ∈ Ball w (c * gsp ell M κ j) ∨
      periodicLatticeShift b.1 b.2 ∈ Ball w (c * gsp ell M κ j)) :
    cW * wnormSq S ell k B ≤ G0form S ell k U a B := by
  have hell0 : 0 < ell := by omega
  set Z' := Ball w (c * gsp ell M κ j + d * ell ^ i + 32 * ell ^ (i + 2)) with hZ'def
  set K := Ball w (c * gsp ell M κ j + d * ell ^ i) with hKdef
  set X := Ball w (c * gsp ell M κ j) with hXdef
  have hpi : ell ^ i ≤ ell ^ j := Nat.pow_le_pow_right hell0 hij
  have hZ'Z : Z' ⊆ Ball w ((c + 1) * gsp ell M κ j) := by
    intro y hy
    have hy' : pdist w y ≤ c * gsp ell M κ j + d * ell ^ i + 32 * ell ^ (i + 2) := hy
    show pdist w y ≤ (c + 1) * gsp ell M κ j
    have hg : (d + 64 * ell ^ 2) * ell ^ i ≤ gsp ell M κ j := by
      unfold gsp bigSide
      have h3 := Nat.mul_le_mul_right (ell ^ i) hdM
      have h4 : κ * M * ell ^ i ≤ κ * M * ell ^ j := Nat.mul_le_mul_left _ hpi
      nlinarith
    have e2 : ell ^ (i + 2) = ell ^ 2 * ell ^ i := by ring
    rw [e2] at hy'
    nlinarith
  have hK : ∀ x ∈ K, Ball x (32 * ell ^ (i + 2)) ⊆ Z' := by
    intro x hx y hy
    have hx' : pdist w x ≤ c * gsp ell M κ j + d * ell ^ i := hx
    have hy' : pdist x y ≤ 32 * ell ^ (i + 2) := hy
    show pdist w y ≤ c * gsp ell M κ j + d * ell ^ i + 32 * ell ^ (i + 2)
    have := pdist_triangle w x y
    omega
  have hXK : X ⊆ K := fun x hx => le_trans hx (Nat.le_add_right _ _)
  have hZi' : Z' ⊆ S.Om i := hZ'Z.trans hZi
  have hZ2' : ∀ z ∈ Z', z ∉ S.Om (i + 2) := fun z hz => hZ2 z (hZ'Z hz)
  have hUZ : ∀ e : Bond L, e.1 ∈ Z' → U e = Up e := fun e he => hU e he
  have hcmp := G0_real_ge_patch hS hell hroom hik hZi' hZ2' hK hXK U Up hUZ B hB a ha
  have hw := wnorm_real_eq_patch hS hell hik hZi' hZ2' hK hXK B hB
  have h3 := hW3 B hB
  rw [← G0_sub_defK] at h3
  rw [hw]
  linarith

end cases

section main
variable {ell M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR4 : (c + 4) * κ * ell ≤ R) (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdM : d + 64 * ell ^ 2 ≤ κ * M)
  {W : ℕ} (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
include hell0 hS hκ hM hell hR1 hR4 hroom hdM hW hWR

/-- **`PatchCoercive` from the per-patch local inputs** (W2H `patchCoercive_W2loc`, one instance per case). -/
theorem patchCoercive_inst (U : LinkCfg (scaleUp ell k Lu)) (a cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ) (ε1 : ℝ) (hε1 : 0 < ε1) (hη : etaC ell W cs ρ ε1 < 1)
    (cW : ℝ)
    (hinst : ∀ j w, IsPatch ell M k κ S j w → ∀ i, i ≤ j → i + 1 ≤ k →
      Ball w ((c + 1) * gsp ell M κ j) ⊆ S.Om i →
      ∃ Up : Cfg (scaleUp ell k Lu),
        (∀ e : Bond (scaleUp ell k Lu), pdist w e.1 ≤ c * gsp ell M κ j + d * ell ^ i + 32 * ell ^ (i + 2) → U e = Up e) ∧
        ∀ B : BondFnL2 (scaleUp ell k Lu), (∀ b : Bond (scaleUp ell k Lu), (WithLp.ofLp B) b ≠ 0 →
            b.1 ∈ Ball w (c * gsp ell M κ j) ∨ periodicLatticeShift b.1 b.2 ∈ Ball w (c * gsp ell M κ j)) →
          cW * wnormSq (patchTower i (S.Om (i + 1))) ell (i + 1) B
            ≤ locG0 (patchTower i (S.Om (i + 1))) ell (i + 1) Up a (Ball w (c * gsp ell M κ j + d * ell ^ i)) B) :
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
  have hdM32 : d + 32 * ell ^ 2 ≤ κ * M := by nlinarith
  have hG0 : min a cW * wnormSq S ell k B ≤ G0form S ell k U a B := by
    by_cases hB : ∃ y ∈ Ball w ((c + 1) * gsp ell M κ j), y ∈ S.Om (j + 1)
    · obtain ⟨hjk, hZi, hZ2⟩ := caseB_up hS hell hκ hM hR4 hpj hB
      obtain ⟨Up, hUp, hW3⟩ := hinst j w hpj j le_rfl hjk hZi
      have h := g0_caseB_nf hS hell hroom hdM (le_refl j) hjk hZi hZ2 U Up hUp a cW ha0 hW3 B hBsupp
      have hm := min_le_right a cW
      nlinarith
    · by_cases hj : 1 ≤ j
      · have hZi := caseB_down hS hell hκ hM hR4 hpj hj
        have hZ2 : ∀ z ∈ Ball w ((c + 1) * gsp ell M κ j), z ∉ S.Om (j - 1 + 2) := by
          rw [show j - 1 + 2 = j + 1 by omega]
          intro z hz hz1
          exact hB ⟨z, hz, hz1⟩
        obtain ⟨Up, hUp, hW3⟩ := hinst j w hpj (j - 1) (by omega) (by have := hpj.1; omega) hZi
        have h := g0_caseB_nf hS hell hroom hdM (i := j - 1) (by omega) (by have := hpj.1; omega) hZi hZ2 U Up
          hUp a cW ha0 hW3 B hBsupp
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

/-- **`PatchCoercive` at non-flat `U` in lane B's M1 regime, with no named input.** -/
theorem patchCoercive_nonflat {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) :
    ∃ cW : ℝ, 0 < cW ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ D : ℕ, 12 * ell + 10 ≤ D ∧
    (∀ d, D ≤ d → epsNF ell (PkA a) (thetaN ell) d ≤ cW / 2) ∧
    ∀ {M R k κ c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
      {S : Tower (scaleUp ell k Lu)} (_hS : Admissible ell M R k S) (_hκ : 0 < κ) (_hM : 0 < M) (_hR1 : 1 ≤ R)
      (_hR4 : (c + 4) * κ * ell ≤ R) (_hroom : 17 * ell ≤ R * M) {d : ℕ} (_hdD : D ≤ d)
      (_hdM : d + 64 * ell ^ 2 ≤ κ * M)
      {W : ℕ} (_hW : 1 ≤ W) (_hWR : W ≤ R * M * ell)
      (U : LinkCfg (scaleUp ell k Lu)) (cs : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
      (_hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs)
      (ρ : ℝ) (_hρ : 0 ≤ ρ) (_hreg : HolRegime S ell k U ρ) (ε1 : ℝ) (_hε1 : 0 < ε1) (_hη : etaC ell W cs ρ ε1 < 1)
      (α₀ : ℝ) (_hα0 : 0 < α₀) (_hαa : (12 : ℝ) * M * α₀ ≤ a₀)
      (_hM1 : AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U),
      PatchCoercive ell M k κ c Lu hell0 S U a Lam
        ((1 - etaC ell W cs ρ ε1) * min a (cW - epsNF ell (PkA a) (thetaN ell) d) - 2 * nuC ell ρ) := by
  set Ci := AdalyFormal.LemIFlat.CS ell a * AdalyFormal.LemIFlat.KV ell a with hCi
  have hCi0 : 0 ≤ Ci := AdalyFormal.W3NF.CSKV_nonneg ell ha
  have hI : LemIFlat ell a Ci := AdalyFormal.LemIFlat.lemIFlat ell (by omega) a ha
  have hKG := KG0_pos ha hCi0
  set cW : ℝ := 1 / ((ell : ℝ) ^ 2 * KG0 a Ci) with hcW
  have hcW0 : 0 < cW := by
    have : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
    positivity
  obtain ⟨a₀, ha₀, ha₀1, hsmall⟩ := smallA ell hell a Ci ha hCi0
  obtain ⟨D, hD, hDle⟩ := epsNF_small ell (by omega) (PkA_ge_one a) (thetaN_nonneg ell) (cW / 2) (by linarith)
  refine ⟨cW, hcW0, a₀, ha₀, D, hD, hDle, ?_⟩
  intro M R k κ c Lu hell0 S hS hκ hM hR1 hR4 hroom d hdD hdM W hW hWR U cs Lam hp ρ hρ hreg ε1 hε1 hη α₀ hα0 hαa hM1
  have hd : 12 * ell + 10 ≤ d := le_trans hD hdD
  have hηk : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    positivity
  exact patchCoercive_inst hell0 hS hκ hM hell hR1 hR4 hroom hdM hW hWR U a cs Lam hp ρ hρ hreg ε1 hε1 hη _
    (fun j w _ i hij hik hZi => inst_local hell ha hCi0 hI a₀ ha₀1 hsmall hS hM i j hij hik w hZi d hd hdM
      ((ell : ℝ) ^ k)⁻¹ hηk α₀ hα0 hαa U hM1)

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.g0_caseB_nf
#print axioms AdalyFormal.M1NonFlat.patchCoercive_inst
#print axioms AdalyFormal.M1NonFlat.patchCoercive_nonflat
