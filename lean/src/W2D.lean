import W2C3

/-!
# W2D -- W2 (`ginv_locality`) as consumed by W4: lane E's `PatchCoercive` from the patch-tower inputs (M1 lane W2, 2026-10-13)

The two patch-tower inputs (Props, NOT assumed anywhere else; `L` any fine torus, `U` a configuration on it):
* `W3G0At ell L U a cW` : on every two-stratum patch tower `patchTower i Rg` (`Rg` a union of `ell^{i+1}`-blocks) of the torus `L`
  (whose sides are multiples of `ell^{i+1}`),
  `cW · ‖A‖_w² ≤ G0_patch(U)(A)` for every bond field `A` (W3 stated for the DECOUPLED form `G0 = curl² + ‖R D*‖² + mass`;
  at flat `U` it is lane D's `W3FlatStmt`, see W2F);
* `OptDecayAt ell L U δ d` : on every such patch tower (torus sides multiples of `ell^{i+1}`), for `A` supported on bonds
  touching `Ball w s`, the decay defect relative
  to `Ball w (s + d ell^i)` (`d` blocks of the lower stratum) is at most `δ · ‖A‖_w²`.

Main result (`patchCoercive_W2`): on an admissible real tower, with lane E's sandwich hypotheses (exactly those of W4: `HatPack`,
`HolRegime`, `ε₁ > 0`, `η < 1`), the room conditions `(c+4) κ ell ≤ R`, `17 ell ≤ R M`, `d + 32 ell² ≤ κ M`, and for every patch
`(j, w)` a configuration `Up j w` that agrees with `U` on the bonds based in the ball of radius `(c+1) G_j` around `w` and satisfies
the two inputs, lane E's `PatchCoercive` holds with
  `cP = (1 − η) · min(a, cW − δ) − 2ν`,  `η = etaC ell W cs ρ ε₁`, `ν = nuC ell ρ` (lane E's constants; no `k`).
Patch cases: a stratum-`(j+1)` point within `(c+1)G_j` → compare with `patchTower j Ω_{j+1}`; none and `j ≥ 1` → `patchTower (j−1) Ω_j`;
none and `j = 0` → every bond of `A` is a level-`0` constraint bond and `G0 ≥ a ‖A‖²` (the mass term; covers the patches at `∂Ω₀`).
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
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLaneR8 (Ball mem_Ball_self Ball_sub Ball_mono pdist_comm pdist_triangle pdist_self pdist_shift_le)
open AdalyFormal.M1Patch (patchTower)
open AdalyFormal.StatementLaneR6 (plaqMask)
open AdalyFormal.M1IMS (G0form Fform Ymass HatPack HolRegime etaC nuC sandwich N_le_wnorm PatchCoercive ginvForm wN
  ginv_form)
open AdalyFormal.M1 (IsPatch gsp patch gsp_pos wnormSq)

variable {L : PeriodicLatticeExtent}

/-- **W3 for the decoupled form** on the two-stratum patch towers of the torus `L` at configuration `U`. -/
def W3G0At (ell : ℕ) (L : PeriodicLatticeExtent) (U : Cfg L) (a cW : ℝ) : Prop :=
  ∀ (i : ℕ) (Rg : Set (PeriodicLatticeSite L)), BlockClosed (ell ^ (i + 1)) Rg → (∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1) →
    ∀ A : BondFnL2 L, cW * wnormSq (patchTower i Rg) ell (i + 1) A ≤ G0form (patchTower i Rg) ell (i + 1) U a A

/-- **decay of the gauge-fixing optimizer** on the two-stratum patch towers: the defect relative to `d` lower-stratum blocks. -/
def OptDecayAt (ell : ℕ) (L : PeriodicLatticeExtent) (U : Cfg L) (δ : ℝ) (d : ℕ) : Prop :=
  ∀ (i : ℕ) (Rg : Set (PeriodicLatticeSite L)), BlockClosed (ell ^ (i + 1)) Rg → (∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1) →
    ∀ (w : PeriodicLatticeSite L) (s : ℕ) (A : BondFnL2 L),
      (∀ b : Bond L, (WithLp.ofLp A) b ≠ 0 → b.1 ∈ Ball w s ∨ periodicLatticeShift b.1 b.2 ∈ Ball w s) →
      defK (geomOf ell (i + 1) (patchTower i Rg)) U (Ball w (s + d * ell ^ i)) A
        ≤ δ * wnormSq (patchTower i Rg) ell (i + 1) A

/-! ## 1. patch geometry: which comparison tower -/

section geom
variable {ell M R k κ c : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hκ : 0 < κ) (hM : 0 < M)
  (hR4 : (c + 4) * κ * ell ≤ R)
include hS hell hκ hM hR4

theorem caseB_up {j : ℕ} {w : PeriodicLatticeSite L} (hp : IsPatch ell M k κ S j w)
    (hB : ∃ y ∈ Ball w ((c + 1) * gsp ell M κ j), y ∈ S.Om (j + 1)) :
    j + 1 ≤ k ∧ Ball w ((c + 1) * gsp ell M κ j) ⊆ S.Om j ∧
      ∀ z ∈ Ball w ((c + 1) * gsp ell M κ j), z ∉ S.Om (j + 2) := by
  obtain ⟨y, hyZ, hy⟩ := hB
  have hjk : j + 1 ≤ k := by
    by_contra h
    rw [hS.2.1 (j + 1) (by omega)] at hy
    exact hy
  have hbs : 0 < bigSide M ell j := Nat.mul_pos hM (pow_pos (by omega) j)
  obtain ⟨x₀, hx0j, hs0, hd0⟩ := hp.anchor hκ hM (by omega)
  refine ⟨hjk, fun z hz => ?_, fun z hz hz2 => ?_⟩
  · by_contra hzn
    have hcol := hS.2.2.2.2.1 j (by omega) z hzn y hy
    have h1 : pdist w z ≤ (c + 1) * gsp ell M κ j := hz
    have h2 : pdist w y ≤ (c + 1) * gsp ell M κ j := hyZ
    have h3 := pdist_triangle z w y
    rw [pdist_comm z w] at h3
    unfold gsp at h1 h2
    have h4 : 2 * ((c + 1) * κ) ≤ R := by nlinarith
    have : R * bigSide M ell j < 2 * ((c + 1) * (κ * bigSide M ell j)) := by omega
    nlinarith
  · have hx0n : x₀ ∉ S.Om (j + 1) := by
      intro h
      have := AdalyFormal.M1.le_strat_of_mem (k := k) hjk h
      omega
    have hcol := hS.2.2.2.2.1 (j + 1) hjk x₀ hx0n z hz2
    have h1 : pdist w z ≤ (c + 1) * gsp ell M κ j := hz
    have h3 := pdist_triangle x₀ w z
    unfold gsp at h1 hd0
    have e : bigSide M ell (j + 1) = bigSide M ell j * ell := AdalyFormal.M1.bigSide_succ M ell j
    rw [e] at hcol
    have key : 3 * (κ * bigSide M ell j) + (c + 1) * (κ * bigSide M ell j) ≤ R * (bigSide M ell j * ell) := by
      calc 3 * (κ * bigSide M ell j) + (c + 1) * (κ * bigSide M ell j) = (c + 4) * κ * bigSide M ell j := by ring
        _ ≤ (c + 4) * κ * bigSide M ell j * ell := Nat.le_mul_of_pos_right _ (by omega)
        _ = (c + 4) * κ * ell * bigSide M ell j := by ring
        _ ≤ R * bigSide M ell j := Nat.mul_le_mul_right _ hR4
        _ ≤ R * bigSide M ell j * ell := Nat.le_mul_of_pos_right _ (by omega)
        _ = R * (bigSide M ell j * ell) := by ring
    linarith

theorem caseB_down {j : ℕ} {w : PeriodicLatticeSite L} (hp : IsPatch ell M k κ S j w) (hj : 1 ≤ j) :
    Ball w ((c + 1) * gsp ell M κ j) ⊆ S.Om (j - 1) := by
  obtain ⟨x₀, hx0j, -, hd0⟩ := hp.anchor hκ hM (by omega)
  intro z hz
  by_contra hzn
  have hx0 : x₀ ∈ S.Om (j - 1 + 1) := by rw [Nat.sub_add_cancel hj]; exact hx0j
  have hcol := hS.2.2.2.2.1 (j - 1) (by have := hp.1; omega) z hzn x₀ hx0
  have h1 : pdist w z ≤ (c + 1) * gsp ell M κ j := hz
  have h3 := pdist_triangle z w x₀
  rw [pdist_comm z w, pdist_comm w x₀] at h3
  rw [pdist_comm x₀ w] at hd0
  unfold gsp at h1 hd0
  have e : bigSide M ell j = bigSide M ell (j - 1) * ell := by
    rw [← AdalyFormal.M1.bigSide_succ, Nat.sub_add_cancel hj]
  rw [e] at h1 hd0
  have key : (c + 1) * (κ * (bigSide M ell (j - 1) * ell)) + 3 * (κ * (bigSide M ell (j - 1) * ell))
      ≤ R * bigSide M ell (j - 1) := by
    calc (c + 1) * (κ * (bigSide M ell (j - 1) * ell)) + 3 * (κ * (bigSide M ell (j - 1) * ell))
        = (c + 4) * κ * ell * bigSide M ell (j - 1) := by ring
      _ ≤ R * bigSide M ell (j - 1) := Nat.mul_le_mul_right _ hR4
  rw [pdist_comm x₀ w] at h3
  linarith

end geom

/-! ## 2. the mass bound for an all-stratum-0 patch -/

theorem rvU_zero_level (ell : ℕ) (U : Cfg L) (A : BondFnL2 L) (b : Bond L) : rvU ell U A 0 b = (WithLp.ofLp A) b := by
  have h := QlinB_zero (geomOf ell 0 (⟨fun _ => ∅⟩ : Tower L)) U A
  rw [QlinB_apply] at h
  unfold rvU
  have h2 : WithLp.ofLp (suCoordInv (QlinCompL ell (AdalyFormal.Balaban.UbarTowerCov.UbarTower
      AdalyFormal.Balaban.SuTwoLogExp.su2LogExp ell U) 0 (suCoord A))) = WithLp.ofLp A := congrArg WithLp.ofLp h
  rw [h2]
  simp

open Classical in
theorem ymass_ge_lvl0 (ell k : ℕ) (S : Tower L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a) (A : BondFnL2 L)
    (h0 : ∀ b : Bond L, (WithLp.ofLp A) b ≠ 0 → b ∈ bondsLam (geomOf ell k S) 0) :
    a * ‖A‖ ^ 2 ≤ ‖Ymass (geomOf ell k S) U a A‖ ^ 2 := by
  rw [ymass_sq_eq ell k S U a ha A]
  have hnn : ∀ m ∈ Finset.range (k + 1), 0 ≤ ∑ b : Bond L,
      (if b ∈ bondsLam (geomOf ell k S) m then a * (ell : ℝ) ^ m * ‖rvU ell U A m b‖ ^ 2 else 0) :=
    fun m _ => Finset.sum_nonneg (fun b _ => by split_ifs <;> positivity)
  refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_range.mpr (Nat.succ_pos k)))
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  by_cases hb : (WithLp.ofLp A) b = 0
  · rw [hb, norm_zero]; split_ifs <;> simp [rvU_zero_level, hb]
  · rw [if_pos (h0 b hb), rvU_zero_level, pow_zero, mul_one]

theorem wnorm_le_sq (S : Tower L) (ell k : ℕ) (hell : 0 < ell) (A : BondFnL2 L) : wnormSq S ell k A ≤ ‖A‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold wnormSq
  refine Finset.sum_le_sum (fun b _ => ?_)
  have h1 : (1 : ℝ) ≤ (ell : ℝ) ^ AdalyFormal.M1.bstrat S k b := one_le_pow₀ (by exact_mod_cast hell)
  have h2 : (((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹) ^ 2 ≤ 1 := by
    have h3 : ((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have h4 : 0 ≤ ((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹ := by positivity
    nlinarith
  have := sq_nonneg ‖(WithLp.ofLp A) b‖
  nlinarith

/-! ## 3. the two cases on the decoupled form -/

section cases
variable {ell M R k κ c : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hκ : 0 < κ) (hM : 0 < M)
  (hroom : 17 * ell ≤ R * M) {d : ℕ} (hdM : d + 32 * ell ^ 2 ≤ κ * M)

include hS hell hκ hM hroom hdM in
theorem g0_caseB {i j : ℕ} (hij : i ≤ j) (hik : i + 1 ≤ k) {w : PeriodicLatticeSite L}
    (hZi : Ball w ((c + 1) * gsp ell M κ j) ⊆ S.Om i)
    (hZ2 : ∀ z ∈ Ball w ((c + 1) * gsp ell M κ j), z ∉ S.Om (i + 2))
    (U Up : Cfg L) (hU : ∀ e : Bond L, pdist w e.1 ≤ (c + 1) * gsp ell M κ j → U e = Up e)
    (a cW δ : ℝ) (ha : 0 ≤ a) (hW3 : W3G0At ell L Up a cW) (hDec : OptDecayAt ell L Up δ d)
    (B : BondFnL2 L)
    (hB : ∀ b : Bond L, (WithLp.ofLp B) b ≠ 0 → b.1 ∈ Ball w (c * gsp ell M κ j) ∨
      periodicLatticeShift b.1 b.2 ∈ Ball w (c * gsp ell M κ j)) :
    (cW - δ) * wnormSq S ell k B ≤ G0form S ell k U a B := by
  have hell0 : 0 < ell := by omega
  have hRg : BlockClosed (ell ^ (i + 1)) (S.Om (i + 1)) :=
    blockClosed_of_mul (by have := hS.2.2.2.1 (i + 1) hik; unfold bigSide at this; exact this)
  set Z := Ball w ((c + 1) * gsp ell M κ j) with hZdef
  set K := Ball w (c * gsp ell M κ j + d * ell ^ j) with hKdef
  set X := Ball w (c * gsp ell M κ j) with hXdef
  have hpj : ell ^ (i + 2) ≤ ell ^ 2 * ell ^ j := by
    rw [← pow_add]; exact Nat.pow_le_pow_right hell0 (by omega)
  have hK : ∀ x ∈ K, Ball x (32 * ell ^ (i + 2)) ⊆ Z := by
    intro x hx y hy
    have hx' : pdist w x ≤ c * gsp ell M κ j + d * ell ^ j := hx
    have hy' : pdist x y ≤ 32 * ell ^ (i + 2) := hy
    show pdist w y ≤ (c + 1) * gsp ell M κ j
    have := pdist_triangle w x y
    have hg : (d + 32 * ell ^ 2) * ell ^ j ≤ gsp ell M κ j := by
      unfold gsp bigSide
      have := Nat.mul_le_mul_right (ell ^ j) hdM
      nlinarith
    nlinarith
  have hXK : X ⊆ K := fun x hx => le_trans hx (Nat.le_add_right _ _)
  have hUZ : ∀ e : Bond L, e.1 ∈ Z → U e = Up e := fun e he => hU e he
  have hcmp := G0_real_ge_patch hS hell hroom hik hZi hZ2 hK hXK U Up hUZ B hB a ha
  have hw := wnorm_real_eq_patch hS hell hik hZi hZ2 hK hXK B hB
  have hdiv : ∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1 := fun μ =>
    (dvd_mul_left (ell ^ (i + 1)) M).trans (hS.2.2.1 (i + 1) hik μ)
  have h3 := hW3 i (S.Om (i + 1)) hRg hdiv B
  have h4 := hDec i (S.Om (i + 1)) hRg hdiv w (c * gsp ell M κ j) B hB
  have h5 : defK (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) Up K B
      ≤ defK (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) Up (Ball w (c * gsp ell M κ j + d * ell ^ i)) B := by
    refine defK_anti _ _ (fun x hx => ?_) B
    have hx' : pdist w x ≤ c * gsp ell M κ j + d * ell ^ i := hx
    show pdist w x ≤ c * gsp ell M κ j + d * ell ^ j
    have : ell ^ i ≤ ell ^ j := Nat.pow_le_pow_right hell0 hij
    have : d * ell ^ i ≤ d * ell ^ j := Nat.mul_le_mul_left d this
    omega
  rw [hw]
  rw [← hw] at h3 h4
  rw [hw] at h3 h4
  nlinarith

open Classical in
include hS hell hκ hM in
theorem g0_caseA {j : ℕ} {w : PeriodicLatticeSite L}
    (hZ1 : ∀ z ∈ Ball w (c * gsp ell M κ j + 1), z ∉ S.Om 1)
    (U : Cfg L) (a : ℝ) (ha : 0 ≤ a) (B : BondFnL2 L)
    (hsupp : ∀ b : Bond L, (WithLp.ofLp B) b ≠ 0 → b.1 ∈ S.Om 0 ∨ periodicLatticeShift b.1 b.2 ∈ S.Om 0)
    (hB : ∀ b : Bond L, (WithLp.ofLp B) b ≠ 0 → b.1 ∈ Ball w (c * gsp ell M κ j) ∨
      periodicLatticeShift b.1 b.2 ∈ Ball w (c * gsp ell M κ j)) :
    a * wnormSq S ell k B ≤ G0form S ell k U a B := by
  have hell0 : 0 < ell := by omega
  have hnear : ∀ b : Bond L, (WithLp.ofLp B) b ≠ 0 →
      b.1 ∈ Ball w (c * gsp ell M κ j + 1) ∧ periodicLatticeShift b.1 b.2 ∈ Ball w (c * gsp ell M κ j + 1) := by
    intro b hb
    have hs := pdist_shift_le b.1 b.2
    rcases hB b hb with h | h
    · have h' : pdist w b.1 ≤ c * gsp ell M κ j := h
      have := pdist_triangle w b.1 (periodicLatticeShift b.1 b.2)
      exact ⟨show pdist w b.1 ≤ _ by omega, show pdist w _ ≤ _ by omega⟩
    · have h' : pdist w (periodicLatticeShift b.1 b.2) ≤ c * gsp ell M κ j := h
      have := pdist_triangle w (periodicLatticeShift b.1 b.2) b.1
      rw [pdist_comm (periodicLatticeShift b.1 b.2) b.1] at this
      exact ⟨show pdist w b.1 ≤ _ by omega, show pdist w _ ≤ _ by omega⟩
  have h0 : ∀ b : Bond L, (WithLp.ofLp B) b ≠ 0 → b ∈ bondsLam (geomOf ell k S) 0 := by
    intro b hb
    obtain ⟨n1, n2⟩ := hnear b hb
    have hc : coarseShift b.1 ((geomOf ell k S).ell ^ 0) b.2 = periodicLatticeShift b.1 b.2 := by
      rw [pow_zero]; rfl
    refine ⟨?_, ?_⟩
    · rw [hc]
      rcases hsupp b hb with h | h
      · exact Or.inl ⟨fun μ => by rw [pow_zero]; exact one_dvd _, h, hZ1 _ n1⟩
      · exact Or.inr ⟨fun μ => by rw [pow_zero]; exact one_dvd _, h, hZ1 _ n2⟩
    · rw [hc]
      rintro (h | h)
      · exact hZ1 _ n1 ((omGe_iff_om ell M R k hell0 S hS 1 _).mp h)
      · exact hZ1 _ n2 ((omGe_iff_om ell M R k hell0 S hS 1 _).mp h)
  have hm := ymass_ge_lvl0 ell k S U a ha B h0
  have hw := wnorm_le_sq S ell k hell0 B
  have hG : ‖Ymass (geomOf ell k S) U a B‖ ^ 2 ≤ G0form S ell k U a B := by
    unfold G0form
    have := sq_nonneg ‖plaqMask (plaqIn (S.Om 0)) (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U B)‖
    have := sq_nonneg ‖Tfull (geomOf ell k S) U B‖
    linarith
  nlinarith

end cases

end AdalyFormal.M1W2

#print axioms AdalyFormal.M1W2.W3G0At
#print axioms AdalyFormal.M1W2.OptDecayAt
#print axioms AdalyFormal.M1W2.caseB_up
#print axioms AdalyFormal.M1W2.caseB_down
#print axioms AdalyFormal.M1W2.rvU_zero_level
#print axioms AdalyFormal.M1W2.ymass_ge_lvl0
#print axioms AdalyFormal.M1W2.wnorm_le_sq
#print axioms AdalyFormal.M1W2.g0_caseB
#print axioms AdalyFormal.M1W2.g0_caseA
