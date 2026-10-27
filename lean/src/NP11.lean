import NP10

/-!
# NP11 -- the instance at a real patch: the comparison configuration from lane B's `M1Regular` (m1_patch_nonflat, 2026-10-14)

**`inst_local`** (statement in NP10's header): from `M1Regular ell M 12 k S α₀ η U` with `0 < α₀`, `12 M α₀ ≤ a₀`
(`a₀` from `smallA`), a level `i ≤ j`, `i + 1 ≤ k`, `Ball w ((c+1) G_j) ⊆ Ω_i`, room `d + 64 ell² ≤ κ M`,
`12 ell + 10 ≤ d`: a configuration `Up`, equal to `U` on bonds based within `c G_j + d ell^i + 32 ell^{i+2}` of `w`, with
`(1/(ell² KG0 a Ci) − epsNF ell (PkA a) (thetaN ell) d) · wnormSq_patch B ≤ locG0(patch_i, Up, Ball w (c G_j + d ell^i))(B)`
for every `B` supported on bonds touching `Ball w (c G_j)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.StatementLane (Tower BlockClosed Admissible bigSide pdist scaleUp)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le)
open AdalyFormal.M1Patch (patchTower LemIFlat Kflat)
open AdalyFormal.CurvBlock (dv pw)
open AdalyFormal.RegBgKU (KUSmall kapHat)
open AdalyFormal.AsmM0 (rhoM0)
open AdalyFormal.W3NF (lamC ThetaP KG0 rhoM1 rho_M1_eq)
open AdalyFormal.M1W2 (locG0 blockClosed_of_mul)
open AdalyFormal.M1 (gsp)
open AdalyFormal.M1Decay (ramp ramp_nonneg ramp_le_one ramp_one ramp_zero ramp_lip pdist_back_le)

variable {L : PeriodicLatticeExtent}

theorem inst_local {ell : ℕ} (hell : 2 ≤ ell) {a Ci : ℝ} (ha : 0 < a) (hCi : 0 ≤ Ci) (hI : LemIFlat ell a Ci)
    (a₀ : ℝ) (ha₀1 : a₀ ≤ 1 / 2)
    (hsmall : ∀ a' : ℝ, 0 ≤ a' → a' ≤ a₀ →
      KUSmall ell (rhoM1 ell (2 * a')) ∧
      432 * kapHat ell (rhoM1 ell (2 * a')) ^ 2 ≤ 1 ∧
      kapHat ell (rhoM1 ell (2 * a')) ≤ 1 / (1000 * (ell : ℝ) ^ 3) ∧
      kapHat ell (rhoM1 ell (2 * a')) ≤ 1 ∧
      324 * lamC ell * kapHat ell (rhoM1 ell (2 * a')) ≤ 1 ∧
      2 * ThetaP ell a (kapHat ell (rhoM1 ell (2 * a'))) ≤ 1 / Kflat a Ci ∧
      8 * (272 * (kapHat ell (rhoM1 ell (2 * a')) / (3 * Real.pi)) / (4 * Real.sqrt 2)) ≤ 1 / Kflat a Ci)
    {M R k κ c : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 0 < M)
    (i j : ℕ) (hij : i ≤ j) (hik : i + 1 ≤ k) (w : PeriodicLatticeSite L)
    (hZi : Ball w ((c + 1) * gsp ell M κ j) ⊆ S.Om i)
    (d : ℕ) (hd : 12 * ell + 10 ≤ d) (hdM : d + 64 * ell ^ 2 ≤ κ * M)
    (η : ℝ) (hη : 0 < η) (α₀ : ℝ) (hα0 : 0 < α₀) (hαa : (12 : ℝ) * M * α₀ ≤ a₀) (U : Cfg L)
    (hM1 : AdalyFormal.M1.M1Regular ell M 12 k S α₀ η U) :
    ∃ Up : Cfg L,
      (∀ e : Bond L, pdist w e.1 ≤ c * gsp ell M κ j + d * ell ^ i + 32 * ell ^ (i + 2) → U e = Up e) ∧
      ∀ B : BondFnL2 L, (∀ b : Bond L, (WithLp.ofLp B) b ≠ 0 →
          b.1 ∈ Ball w (c * gsp ell M κ j) ∨ periodicLatticeShift b.1 b.2 ∈ Ball w (c * gsp ell M κ j)) →
        (1 / ((ell : ℝ) ^ 2 * KG0 a Ci) - epsNF ell (PkA a) (thetaN ell) d)
            * AdalyFormal.M1.wnormSq (patchTower i (S.Om (i + 1))) ell (i + 1) B
          ≤ locG0 (patchTower i (S.Om (i + 1))) ell (i + 1) Up a (Ball w (c * gsp ell M κ j + d * ell ^ i)) B := by
  have hell0 : 0 < ell := by omega
  have hlR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hlpos : (0 : ℝ) < ell := by linarith
  have hpi := Real.pi_pos
  obtain ⟨g, A, hUA, hHT, h1, h2, -⟩ := hM1
  set G := gsp ell M κ j with hGdef
  set a' : ℝ := ((12 : ℕ) : ℝ) * M * α₀ with ha'
  have ha'0 : 0 < a' := by
    have : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  have ha'a : a' ≤ a₀ := by rw [ha']; push_cast; linarith
  have ha'h : a' ≤ 1 / 2 := ha'a.trans ha₀1
  set ni : ℝ := (ell : ℝ) ^ i with hni
  have hni1 : 1 ≤ ni := one_le_pow₀ (by linarith)
  have hni0 : 0 < ni := by linarith
  set c1 : ℝ := a' * ((ni * η)⁻¹ ^ 1) with hc1
  set c2 : ℝ := a' * ((ni * η)⁻¹ ^ 2) with hc2
  have hc10 : 0 < c1 := by positivity
  have hc20 : 0 < c2 := by positivity
  -- the region
  set Zr : Set (PeriodicLatticeSite L) := {x | pdist w x + 1 ≤ (c + 1) * G} with hZr
  have hbst : ∀ e : Bond L, e.1 ∈ Zr → i ≤ AdalyFormal.M1.bstrat S k e := by
    intro e he
    have he' : pdist w e.1 + 1 ≤ (c + 1) * G := he
    refine AdalyFormal.M1.le_bstrat_of_mem (by omega) e (hZi (by show pdist w e.1 ≤ _; omega)) (hZi ?_)
    show pdist w (periodicLatticeShift e.1 e.2) ≤ _
    have := pdist_triangle w e.1 (periodicLatticeShift e.1 e.2)
    have := pdist_shift_le e.1 e.2
    omega
  have hZ1 : ∀ e : Bond L, e.1 ∈ Zr → frobNorm (A e) < c1 := by
    intro e he
    have := h1 e i (hbst e he)
    rw [hc1, ha']; exact this
  have hZ2 : ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L), x ∈ Zr → periodicLatticeShift x μ ∈ Zr →
      frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) < c2 := by
    intro μ ν x hx hx'
    have := h2 μ ν x i (hbst (x, ν) hx) (hbst (periodicLatticeShift x μ, ν) hx')
    rw [hc2, ha']; exact this
  -- the cut-off
  set r1 : ℕ := c * G + d * ell ^ i + 32 * ell ^ (i + 2) with hr1
  set Wc : ℕ := 32 * ell ^ (i + 2) - 4 with hWc
  have hpow : 4 * ell ^ i ≤ ell ^ (i + 2) := by
    have h4 : 4 ≤ ell ^ 2 := by nlinarith
    calc 4 * ell ^ i ≤ ell ^ 2 * ell ^ i := Nat.mul_le_mul_right _ h4
      _ = ell ^ (i + 2) := by ring
  have hpi1 : 1 ≤ ell ^ i := Nat.one_le_pow _ _ hell0
  have hWcpos : 0 < Wc := by omega
  have hWci : ell ^ i ≤ Wc := by omega
  have hGroom : d * ell ^ i + 64 * ell ^ (i + 2) ≤ G := by
    have hij' : ell ^ i ≤ ell ^ j := Nat.pow_le_pow_right hell0 hij
    have e2 : ell ^ (i + 2) = ell ^ 2 * ell ^ i := by ring
    have h3 : (d + 64 * ell ^ 2) * ell ^ i ≤ κ * M * ell ^ i := Nat.mul_le_mul_right _ hdM
    have h4 : κ * M * ell ^ i ≤ κ * M * ell ^ j := Nat.mul_le_mul_left _ hij'
    rw [hGdef]; unfold gsp bigSide
    rw [e2]; nlinarith
  set χ : PeriodicLatticeSite L → ℝ := ramp w r1 Wc with hχ
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => ramp_nonneg w r1 Wc x
  have hχ1 : ∀ x, χ x ≤ 1 := fun x => ramp_le_one w r1 Wc x
  have hsupp : ∀ x, χ x ≠ 0 → x ∈ Zr ∧ ∀ μ : Fin 3, periodicLatticeShift x μ ∈ Zr ∧ periodicLatticeShiftBack x μ ∈ Zr := by
    intro x hx
    have hxw : pdist w x + 1 ≤ r1 + Wc := by
      by_contra hc; exact hx (ramp_zero w r1 Wc hWcpos x (by omega))
    have hcG : (c + 1) * G = c * G + G := by ring
    have hRW : r1 + Wc + 4 ≤ (c + 1) * G := by
      rw [hcG, hr1, hWc]; omega
    refine ⟨show pdist w x + 1 ≤ (c + 1) * G by omega, fun μ => ⟨?_, ?_⟩⟩
    · show pdist w (periodicLatticeShift x μ) + 1 ≤ (c + 1) * G
      have := pdist_triangle w x (periodicLatticeShift x μ)
      have := pdist_shift_le x μ
      omega
    · show pdist w (periodicLatticeShiftBack x μ) + 1 ≤ (c + 1) * G
      have := pdist_triangle w x (periodicLatticeShiftBack x μ)
      have := pdist_back_le x μ
      omega
  set lip : ℝ := 1 / (Wc : ℝ) with hlipdef
  have hWcR : (0 : ℝ) < Wc := by exact_mod_cast hWcpos
  have hlip0 : 0 ≤ lip := by positivity
  have hlip : ∀ x (μ : Fin 3), |χ (periodicLatticeShift x μ) - χ x| ≤ lip := by
    intro x μ
    have h := ramp_lip w r1 Wc hWcpos (periodicLatticeShift x μ) x
    have hp : (pdist (periodicLatticeShift x μ) x : ℝ) ≤ 1 := by
      rw [pdist_comm]; exact_mod_cast pdist_shift_le x μ
    calc |χ (periodicLatticeShift x μ) - χ x| ≤ 1 / Wc * (pdist (periodicLatticeShift x μ) x : ℝ) := h
      _ ≤ 1 / Wc * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = lip := by rw [mul_one]
  refine ⟨Upc η g A χ, fun e he => ?_, fun B hB => ?_⟩
  · exact (Upc_eq η hη U g A hHT hUA χ e (ramp_one w r1 Wc hWcpos e.1 he)).symm
  -- the chart bounds
  have hηc1 : η * c1 = a' / ni := by rw [hc1]; field_simp
  have hηc2 : η ^ 2 * (c2 + lip * c1 / η) = a' / ni ^ 2 + lip * (a' / ni) := by
    rw [hc2, ← hηc1]; field_simp
  have hWni : ni ≤ (Wc : ℝ) := by
    calc ni = ((ell ^ i : ℕ) : ℝ) := by rw [hni]; push_cast; ring
      _ ≤ (Wc : ℝ) := by exact_mod_cast hWci
  have hlipni : lip * (a' / ni) ≤ a' / ni ^ 2 := by
    have h1 : lip ≤ 1 / ni := by rw [hlipdef]; exact one_div_le_one_div_of_le hni0 hWni
    calc lip * (a' / ni) ≤ (1 / ni) * (a' / ni) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = a' / ni ^ 2 := by ring
  have hsmallη : η * c1 ≤ 1 := by
    rw [hηc1, div_le_one hni0]; linarith
  have hlink := Vchi_link η hη g A hHT χ hχ0 hχ1 Zr c1 c2 lip hc10 hc20 hlip0 hZ1 hZ2 hsupp hlip
  have hplaq := Vchi_plaq η hη g A hHT χ hχ0 hχ1 Zr c1 c2 lip hc10 hc20 hlip0 hZ1 hZ2 hsupp hlip hsmallη
  have hdif := Vchi_diff η hη g A hHT χ hχ0 hχ1 Zr c1 c2 lip hc10 hc20 hlip0 hZ1 hZ2 hsupp hlip hsmallη
  set α : ℝ := 2 * a' with hα
  set e' : ℝ := α / (ell : ℝ) ^ i with he'
  set q0' : ℝ := 2 * (α / ((ell : ℝ) ^ i) ^ 2) + (4 * Real.pi + 2) * (α / (ell : ℝ) ^ i) ^ 2 with hq0'
  have he'0 : 0 ≤ e' := by positivity
  have hq0'0 : 0 ≤ q0' := by positivity
  have hlinks' : ∀ b, dv (Vchi η A χ b) ≤ e' := by
    intro b
    refine (hlink b).trans ?_
    rw [hηc1, he', hα, ← hni]
    exact div_le_div_of_nonneg_right (by linarith) hni0.le
  have h0' : ∀ y ν μ, dv (pw 1 (Vchi η A χ) y ν μ) ≤ q0' := by
    intro y ν μ
    refine (hplaq y ν μ).trans ?_
    rw [hηc2, hηc1, hq0', hα, ← hni]
    have hsq : (a' / ni) ^ 2 ≤ (2 * a' / ni) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (by linarith) hni0.le) 2
    have h4 : (0 : ℝ) ≤ 4 * Real.pi + 2 := by positivity
    have e1 : 2 * (2 * a' / ni ^ 2) = 2 * (a' / ni ^ 2) + 2 * (a' / ni ^ 2) := by ring
    nlinarith [mul_le_mul_of_nonneg_left hsq h4]
  have hθ : e' ≤ thetaN ell / (ell : ℝ) ^ (i + 1) := by
    have h1 : e' ≤ 1 / (ell : ℝ) ^ i := by
      rw [he', hα]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : 1 / (ell : ℝ) ^ i ≤ thetaN ell / (ell : ℝ) ^ (i + 1) := by
      rw [pow_succ, thetaN, div_le_div_iff₀ (by positivity) (by positivity)]
      have hl : (ell : ℝ) ≤ (3 + 2 * Real.pi) * (ell : ℝ) ^ 2 := by nlinarith [Real.pi_pos]
      have := mul_le_mul_of_nonneg_left hl (pow_nonneg hlpos.le i)
      nlinarith
    exact h1.trans h2
  have hdiff' : ∀ (x : PeriodicLatticeSite L) (μ : Fin 3),
      frobNorm (((Vchi η A χ (x, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
        - ((Vchi η A χ (periodicLatticeShiftBack x μ, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ))
        ≤ thetaN ell / ((ell : ℝ) ^ (i + 1)) ^ 2 := by
    intro x μ
    refine (hdif x μ).trans ?_
    rw [hηc2, hηc1, thetaN]
    have e1 : (3 + 2 * Real.pi) * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ (i + 1)) ^ 2 = (3 + 2 * Real.pi) / ni ^ 2 := by
      rw [hni, pow_succ]; field_simp; ring
    rw [e1]
    have hb : a' / ni ^ 2 + lip * (a' / ni) + 2 * Real.pi * (a' / ni) ^ 2 ≤ (1 + 2 * Real.pi * (1 / 4)) / ni ^ 2 := by
      have hsq : (a' / ni) ^ 2 = a' ^ 2 / ni ^ 2 := by ring
      rw [hsq]
      have ha2 : a' ^ 2 ≤ 1 / 4 := by nlinarith
      have : a' / ni ^ 2 + a' / ni ^ 2 + 2 * Real.pi * (a' ^ 2 / ni ^ 2) ≤ (1 + 2 * Real.pi * (1 / 4)) / ni ^ 2 := by
        have e2 : a' / ni ^ 2 + a' / ni ^ 2 + 2 * Real.pi * (a' ^ 2 / ni ^ 2) = (2 * a' + 2 * Real.pi * a' ^ 2) / ni ^ 2 := by
          ring
        rw [e2]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [Real.pi_pos]
      linarith
    refine hb.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    nlinarith
  have hρ := rho_M1_eq ell i hell0 α
  obtain ⟨hKU, hs1, hs2, hs3, hs4, hs5, hs6⟩ := hsmall a' ha'0.le ha'a
  rw [← hα, ← hρ] at hKU hs1 hs2 hs3 hs4 hs5 hs6
  have hdvd : ∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1 := fun μ =>
    (dvd_mul_left (ell ^ (i + 1)) M).trans (hS.2.2.1 (i + 1) hik μ)
  have hRg : BlockClosed (ell ^ (i + 1)) (S.Om (i + 1)) :=
    blockClosed_of_mul (by have := hS.2.2.2.1 (i + 1) hik; unfold bigSide at this; exact this)
  have hB' : ∀ b : Bond L, (WithLp.ofLp (AdalyFormal.GaugeCov.adBL g B)) b ≠ 0 →
      b.1 ∈ Ball w (c * G) ∨ periodicLatticeShift b.1 b.2 ∈ Ball w (c * G) :=
    fun b hb => hB b ((supp_adBL g B b).mp hb)
  have hmain := w3loc_any hell ha hCi hI i hdvd (S.Om (i + 1)) hRg (Vchi η A χ) e' q0' (thetaN ell) he'0 hq0'0
    (thetaN_nonneg ell) hlinks' h0' hθ hdiff' hKU hs1 hs2 hs3 hs4 hs5 hs6 d hd w (c * G)
    (AdalyFormal.GaugeCov.adBL g B) hB'
  rw [AdalyFormal.W3NF.wnormSq_gauge, ← gauge_Upc η g A χ, locG0_gauge] at hmain
  exact hmain

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.inst_local
