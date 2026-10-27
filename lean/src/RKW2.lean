import RKW
/-!
# RKW2 -- a CURVED witness FAMILY over EVERY k at ONE fixed smallness parameter (the point of k-uniformity).

`ell = 2`, `Lu = (3,3,3)`, fine torus `(4·2^k)³`, `U_k = torusCfg f`, `f = ε_k` on the single bond `(0, direction 0)`,
`ε_k = epsB / 4^k` (class scaling: fine link `√2 ε_k ~ ρ 2^{-k}·2^{-k}`, plaquettes `4√2 ε_k ~ ρ 4^{-k}`).
`rho_family_le : ρ_k ≤ 59 epsB` for EVERY k; `KU_of_le`: `KUSmall 2 ρ` whenever `0 ≤ ρ ≤ 230 epsB`;
`witnessKU_family k : M0RegimeR 2 k Lu3 (UK k) 1 1 (√2 ε_k) (4√2 ε_k) ∧ KUSmall 2 ρ_k ∧ ∃ plaquette with dv > 0`;
`witnessKU_family_coercive k`: `ginv_coercive_M0_kuniform` applied, for every `k`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
noncomputable section
namespace AdalyFormal.RegBgKU

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2 (Cfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 torus torus_add)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.AbelianBlockingRate (torusCfg torus_inv frobNorm_torus_sub_one)
open AdalyFormal.CurvBlock (dv pw curlS dv_torus_le plaq_of_pw_one shift_self)
open AdalyFormal.NonflatJet (r0 r0_pos)
open AdalyFormal.AsmM0 (rhoM0 M0RegimeR Lu3 Theta_num)
open AdalyFormal.StatementLane (scaleUp)

variable {L : PeriodicLatticeExtent}

theorem pw_torusCfg_gen (s : ℕ) (f : PeriodicLatticeEdge L → ℝ) (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    pw s (torusCfg f) y ν μ = torus (curlS s f y ν μ) := by
  unfold pw curlS torusCfg
  rw [torus_inv, torus_inv, ← torus_add, ← torus_add, ← torus_add]
  simp only [sub_eq_add_neg]

def oK (k : ℕ) : PeriodicLatticeSite (scaleUp 2 k Lu3) := fun _ => 0

def fK (k : ℕ) (ε : ℝ) (b : PeriodicLatticeEdge (scaleUp 2 k Lu3)) : ℝ := if b = (oK k, 0) then ε else 0

def UK (k : ℕ) (ε : ℝ) : Cfg (scaleUp 2 k Lu3) := torusCfg (fK k ε)

def epsK (k : ℕ) : ℝ := epsB / 4 ^ k

theorem fK_abs (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (b : PeriodicLatticeEdge (scaleUp 2 k Lu3)) : |fK k ε b| ≤ ε := by
  unfold fK; split_ifs <;> simp [abs_of_nonneg hε, hε]

theorem UK_link (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (b : PeriodicLatticeEdge (scaleUp 2 k Lu3)) :
    dv (UK k ε b) ≤ Real.sqrt 2 * ε :=
  (dv_torus_le (fK k ε b)).trans (mul_le_mul_of_nonneg_left (fK_abs k ε hε b) (Real.sqrt_nonneg _))

theorem UK_plaq (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) : ∀ y ν μ, dv (pw 1 (UK k ε) y ν μ) ≤ 4 * Real.sqrt 2 * ε := by
  intro y ν μ
  unfold UK; rw [pw_torusCfg_gen]
  refine le_trans (dv_torus_le _) ?_
  have h1 := fK_abs k ε hε (y, ν); have h2 := fK_abs k ε hε (coarseShift y 1 ν, μ)
  have h3 := fK_abs k ε hε (coarseShift y 1 μ, ν); have h4 := fK_abs k ε hε (y, μ)
  have : |curlS 1 (fK k ε) y ν μ| ≤ 4 * ε := by
    unfold curlS
    obtain ⟨a1, b1⟩ := abs_le.mp h1; obtain ⟨a2, b2⟩ := abs_le.mp h2
    obtain ⟨a3, b3⟩ := abs_le.mp h3; obtain ⟨a4, b4⟩ := abs_le.mp h4
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

theorem UK_nonflat (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hπ : ε < Real.pi) : 0 < dv (pw 1 (UK k ε) (oK k) 0 1) := by
  unfold UK; rw [pw_torusCfg_gen]
  have hc : curlS 1 (fK k ε) (oK k) 0 1 = ε := by
    unfold curlS fK
    have e1 : ((coarseShift (oK k) 1 0, (1 : Fin 3)) = (oK k, (0 : Fin 3))) = False := by
      apply propext; constructor
      · intro h; have h2 := congrArg Prod.snd h; simp at h2
      · intro h; exact h.elim
    have e2 : ((coarseShift (oK k) 1 1, (0 : Fin 3)) = (oK k, (0 : Fin 3))) = False := by
      apply propext; constructor
      · intro h
        have h' := congrArg (fun p => (p.1 1).val) h
        simp only at h'
        rw [shift_self] at h'
        have hN : 1 < scaleUp 2 k Lu3 1 + 1 := by
          show 1 < (3 + 1) * 2 ^ k - 1 + 1
          have := Nat.one_le_two_pow (n := k); omega
        have : ((oK k 1 + AdalyFormal.CurvBlock.finK (scaleUp 2 k Lu3 1) 1 : Fin _)).val = 1 := by
          rw [Fin.val_add]
          show (0 + 1 % (scaleUp 2 k Lu3 1 + 1)) % (scaleUp 2 k Lu3 1 + 1) = 1
          rw [Nat.mod_eq_of_lt hN, Nat.zero_add, Nat.mod_eq_of_lt hN]
        rw [this] at h'
        exact absurd h' (by show (1 : ℕ) ≠ (0 : Fin _).val; simp)
      · intro h; exact h.elim
    have e3 : ((oK k, (1 : Fin 3)) = (oK k, (0 : Fin 3))) = False := by
      apply propext; constructor
      · intro h; have h2 := congrArg Prod.snd h; simp at h2
      · intro h; exact h.elim
    simp only [e1, e2, e3, if_true, if_false]
    ring
  rw [hc]
  unfold dv
  rw [frobNorm_torus_sub_one]
  apply Real.sqrt_pos.mpr
  have hc1 : Real.cos ε < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ.le hε
    rwa [Real.cos_zero] at this
  linarith

theorem rho_family_le (k : ℕ) :
    rhoM0 2 k (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k) ≤ 59 * epsB := by
  have hε := epsB_pos
  have hs2 : Real.sqrt 2 ≤ 1.5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs2' : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  set n : ℝ := (2 : ℝ) ^ k with hn
  have hn1 : 1 ≤ n := one_le_pow₀ (by norm_num)
  have h4 : (4 : ℝ) ^ k = n ^ 2 := by rw [hn, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
  unfold rhoM0 epsK
  push_cast
  rw [← hn, h4]
  have e1 : n * (Real.sqrt 2 * (epsB / n ^ 2) + 3 * Real.pi * (n * (4 * Real.sqrt 2 * (epsB / n ^ 2))))
      = Real.sqrt 2 * epsB / n + 12 * Real.pi * Real.sqrt 2 * epsB := by
    field_simp; ring
  rw [e1]
  have h5 : Real.sqrt 2 * epsB / n ≤ Real.sqrt 2 * epsB := div_le_self (by positivity) hn1
  have h6 : 12 * Real.pi * Real.sqrt 2 ≤ 57 := by nlinarith [mul_le_mul hpi.le hs2 hs2' (by norm_num)]
  nlinarith

theorem KU_of_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ230 : ρ ≤ 230 * epsB) : KUSmall 2 ρ := by
  have hε := epsB_pos
  have hε1 := epsB_le1
  have hε2 := epsB_le2
  have hr0 := r0_pos
  have hpi3 := Real.pi_gt_three
  have hpi := Real.pi_lt_d2
  have hρs : ρ ≤ 3e-11 := hρ230.trans (by nlinarith)
  have hK := Kc_two_le
  have hK0 : 0 < Kc 2 := Kc_pos 2 le_rfl
  have hq : ρ / (3 * Real.pi) ≤ ρ / 9 := div_le_div_of_nonneg_left hρ0 (by norm_num) (by linarith)
  have hρ2 : ρ ^ 2 ≤ 3e-11 * ρ := by nlinarith
  have hinner : ρ / (3 * Real.pi) + ρ ^ 2 ≤ ρ / 8 := by nlinarith
  have hkap : kapHat 2 ρ ≤ 50001 * ρ := by
    unfold kapHat
    have := mul_le_mul hK hinner (by positivity) (by norm_num)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have : 8 * ((2 : ℕ) : ℝ) * kapHat 2 ρ ≤ 16 * (50001 * (230 * (1 / 10 ^ 13))) := by
      push_cast; nlinarith
    refine this.trans ?_
    rw [le_div_iff₀ (by positivity)]; nlinarith
  · have h1 : Kc 2 ^ 2 ≤ 400000 ^ 2 := pow_le_pow_left₀ hK0.le hK 2
    have h2 : ρ / (3 * Real.pi) + ρ ^ 2 ≤ 3e-11 / 8 := by nlinarith
    have h3 : 0 ≤ ρ / (3 * Real.pi) + ρ ^ 2 := by positivity
    nlinarith [mul_le_mul h1 h2 h3 (by positivity)]
  · have : (8 * ((2 : ℕ) : ℝ) - 6) * kapHat 2 ρ ≤ 10 * (50001 * (230 * (r0 / 10 ^ 10))) := by
      push_cast; nlinarith
    refine lt_of_le_of_lt this ?_
    nlinarith

theorem witnessKU_family (k : ℕ) :
    M0RegimeR 2 k Lu3 (UK k (epsK k)) 1 1 (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k) ∧
    KUSmall 2 (rhoM0 2 k (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k)) ∧
    ∃ p : PeriodicLatticePlaquette (scaleUp 2 k Lu3), 0 < dv (periodicPlaquetteHolonomy (UK k (epsK k)) p) := by
  have hε := epsB_pos
  have hε1 := epsB_le1
  have hs2 : Real.sqrt 2 ≤ 1.5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs2' : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have h4k : (0 : ℝ) < 4 ^ k := by positivity
  have hek : 0 < epsK k := by unfold epsK; positivity
  have hek1 : epsK k ≤ epsB := by unfold epsK; exact div_le_self hε.le (one_le_pow₀ (by norm_num))
  have hρ := rho_family_le k
  have hρ0 : 0 ≤ rhoM0 2 k (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k) := by unfold rhoM0; positivity
  have hρs : rhoM0 2 k (Real.sqrt 2 * epsK k) (4 * Real.sqrt 2 * epsK k) ≤ 3e-11 := hρ.trans (by nlinarith)
  refine ⟨⟨le_refl _, one_pos, one_pos, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    KU_of_le _ hρ0 (hρ.trans (by nlinarith)), ?_⟩
  · intro _; show 2 * 2 ^ k < (3 + 1) * 2 ^ k - 1 + 1
    have := Nat.one_le_two_pow (n := k); omega
  · intro b; exact UK_link k (epsK k) hek.le b
  · exact plaq_of_pw_one (UK k (epsK k)) _ (UK_plaq k (epsK k) hek.le)
  · have e1 : ((2 : ℝ) ^ 2) ^ k * (4 * Real.sqrt 2 * epsK k) = 4 * Real.sqrt 2 * epsB := by
      unfold epsK; rw [show ((2 : ℝ) ^ 2) = 4 by norm_num]; field_simp
    push_cast
    rw [e1]; nlinarith
  · nlinarith
  · refine hρs.trans ?_; push_cast; norm_num
  · exact Theta_num _ hρ0 hρs
  · refine ⟨(oK k, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩), ?_⟩
    exact UK_nonflat k (epsK k) hek (by have := Real.pi_gt_three; linarith)

/-- the k-uniform headline theorem along the curved family, for EVERY `k`. -/
def witnessKU_family_coercive (k : ℕ) (Lam : Set (PeriodicLatticeSite Lu3))
    (x : ↥(AdalyFormal.IngredientFamilyR2.bondSupp (AdalyFormal.SliceCoerc.GF 2 k Lu3))) :=
  ginv_coercive_M0_kuniform 2 k Lu3 (UK k (epsK k)) 1 1 _ _ (witnessKU_family k).1 (witnessKU_family k).2.1 Lam x

#print axioms pw_torusCfg_gen
#print axioms UK_nonflat
#print axioms rho_family_le
#print axioms KU_of_le
#print axioms witnessKU_family
#print axioms witnessKU_family_coercive

#print axioms UK_link
#print axioms UK_plaq
#print axioms fK_abs
end AdalyFormal.RegBgKU
