import GV12

/-!
# GV13 -- `gchart_at_bad_vertex` (InterfaceCharts item (a)) (m2_glue3, 2026-10-15)

Six half-space charts around a lattice site `v` (`g σ b` a `GChart` at `(t₁, t₂)` on
`lift v (Hraw R σ b) = ι_v(Box(R+2) ∩ {p_σ ≥ 0})` resp. `{p_σ ≤ −1}`) give ONE gauge `gv` with
* `GChart U gv (ι_v(Box R)) (KT1·(3R+2)·s) (KT2·s)`, `s = t₂ + 43 t₁²`, `KT1 = KT1 4 1152`, `KT2 = KT2 4 1152`
  universal numbers (independent of `R`, `L`, `t₁`, `t₂`, `U`, the RG scale);
* closeness: for each input chart a constant `n σ b ∈ SU(2)` with
  `|gv(x)·g_{σ,b}(x)⁻¹ − n σ b| ≤ cB 1152 5 · ρ² s + 15 ρ t₁` on its half-space (`ρ = ρ(p)`, `x = ι_v p`).
Hypotheses: `1 ≤ R`, non-wrap `InjOn (iota v) (Box (R+3))`, `0 ≤ t₁ ≤ 2`, `0 ≤ t₂`,
smallness `(4 cB 1152 5 + 1)(3R+2)² s ≤ 1`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace AdalyFormal.M2Glue3

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.M2Glue2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul)

variable {L : PeriodicLatticeExtent}

theorem KT1_nonneg : 0 ≤ KT1 4 1152 := by
  unfold KT1 eS
  have := cA_ge (A0 := 4) (B0 := 1152) (by norm_num) (by norm_num) 5
  have := cB_nonneg (B0 := 1152) (by norm_num) 5
  positivity

theorem KT2_nonneg : 0 ≤ KT2 4 1152 := by
  unfold KT2 eS
  have := cC_ge (A0 := 4) (B0 := 1152) (by norm_num) (by norm_num) 5
  have := cB_nonneg (B0 := 1152) (by norm_num) 5
  positivity

theorem frob_flatY_le {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hR : 1 ≤ R)
    (hinj : Set.InjOn (iota v) (Box (R + 3))) {g : Fin 3 → Bool → PeriodicLatticeSite L → SU2} {t1 t2 : ℝ}
    (ht12 : t1 ≤ 2) (hg : ∀ σ b, GChart U (g σ b) (lift v (Hraw R σ b)) t1 t2) (σ : Fin 3) (b : Bool)
    {p : Z3} (hp : p ∈ Box (R + 2)) :
    frobNorm (flatY U (g σ b) (iota v (baseP σ b)) (phiA v R σ b) (iota v p)) ≤ (rho p + 7 / 2) * t1 := by
  have hinj2 : Set.InjOn (iota v) (Box (R + 2)) := hinj.mono (Box_mono (Nat.le_succ _))
  have hb := baseP_mem hR σ b
  have hB : ∀ σ', frobNorm (flatB U (g σ b) (iota v (baseP σ b)) σ') ≤ t1 := by
    intro σ'
    refine frobNorm_flatB_le ((hg σ b).1 _ σ' (iota_mem_lift hb.1) ?_) ht12
    rw [iota_shift]; exact iota_mem_lift (hb.2 σ')
  have ht1 : 0 ≤ t1 := (frobNorm_nonneg _).trans (hB 0)
  have hφ : ∀ σ', |phiA v R σ b σ' (iota v p)| ≤ |qc p σ'| + 1 / 2 + |((baseP σ b σ' : ℤ) : ℝ)| := by
    intro σ'
    unfold phiA qc
    rw [coord_iota hinj2 hp]
    have h1 := abs_sub ((p σ' : ℝ) + 1 / 2) ((baseP σ b σ' : ℤ) : ℝ)
    have h2 : ((p σ' : ℤ) : ℝ) - ((baseP σ b σ' : ℤ) : ℝ) = (((p σ' : ℝ) + 1 / 2) - ((baseP σ b σ' : ℤ) : ℝ)) - 1 / 2 := by
      ring
    rw [h2]
    have h3 := abs_sub (((p σ' : ℝ) + 1 / 2) - ((baseP σ b σ' : ℤ) : ℝ)) (1 / 2 : ℝ)
    have h4 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    linarith
  have hbs : |((baseP σ b 0 : ℤ) : ℝ)| + |((baseP σ b 1 : ℤ) : ℝ)| + |((baseP σ b 2 : ℤ) : ℝ)| ≤ 2 := by
    unfold baseP; cases b <;> fin_cases σ <;> simp
  unfold flatY
  rw [Fin.sum_univ_three]
  have t : ∀ σ', frobNorm (phiA v R σ b σ' (iota v p) • flatB U (g σ b) (iota v (baseP σ b)) σ')
      ≤ (|qc p σ'| + 1 / 2 + |((baseP σ b σ' : ℤ) : ℝ)|) * t1 := by
    intro σ'
    rw [frobNorm_smul]
    exact mul_le_mul (hφ σ') (hB σ') (frobNorm_nonneg _) (by positivity)
  have a := frobNorm_add_le (phiA v R σ b 0 (iota v p) • flatB U (g σ b) (iota v (baseP σ b)) 0
      + phiA v R σ b 1 (iota v p) • flatB U (g σ b) (iota v (baseP σ b)) 1)
    (phiA v R σ b 2 (iota v p) • flatB U (g σ b) (iota v (baseP σ b)) 2)
  have c := frobNorm_add_le (phiA v R σ b 0 (iota v p) • flatB U (g σ b) (iota v (baseP σ b)) 0)
    (phiA v R σ b 1 (iota v p) • flatB U (g σ b) (iota v (baseP σ b)) 1)
  have t0 := t 0; have t1' := t 1; have t2' := t 2
  unfold rho
  nlinarith

/-- **the chart at a bad vertex.** -/
theorem gchart_at_bad_vertex {U : LinkCfg L} (v : PeriodicLatticeSite L) {R : ℕ} (hR : 1 ≤ R)
    (hinj : Set.InjOn (iota v) (Box (R + 3)))
    (g : Fin 3 → Bool → PeriodicLatticeSite L → SU2) {t1 t2 : ℝ} (ht1 : 0 ≤ t1) (ht12 : t1 ≤ 2) (ht2 : 0 ≤ t2)
    (hg : ∀ σ b, GChart U (g σ b) (lift v (Hraw R σ b)) t1 t2)
    (hsmall : (4 * cB 1152 5 + 1) * (3 * (R : ℝ) + 2) ^ 2 * (t2 + 43 * t1 ^ 2) ≤ 1) :
    ∃ gv : PeriodicLatticeSite L → SU2,
      GChart U gv (lift v (Box R)) (KT1 4 1152 * (3 * R + 2) * (t2 + 43 * t1 ^ 2)) (KT2 4 1152 * (t2 + 43 * t1 ^ 2)) ∧
      ∃ n : Fin 3 → Bool → SU2, ∀ σ b p, p ∈ Box R → hsP σ b p →
        frobNorm (((gv (iota v p) * (g σ b (iota v p))⁻¹ : SU2) : M2) - (n σ b : M2))
          ≤ cB 1152 5 * rho p ^ 2 * (t2 + 43 * t1 ^ 2) + 15 * rho p * t1 := by
  set s := t2 + 43 * t1 ^ 2 with hsdef
  have hs : 0 ≤ s := by positivity
  have hinj2 : Set.InjOn (iota v) (Box (R + 2)) := hinj.mono (Box_mono (Nat.le_succ _))
  have hinj1 : Set.InjOn (iota v) (Box (R + 1)) := hinj2.mono (Box_mono (Nat.le_succ _))
  have hcB := cB_nonneg (B0 := 1152) (by norm_num) 5
  have hsm : ∀ p ∈ Box R, (4 * cB 1152 5 + 1) * rho p ^ 2 * s ≤ 1 := by
    intro p hp
    have h1 := rho_le_box hp
    have h0 := rho_pos p
    have : rho p ^ 2 ≤ (3 * (R : ℝ) + 2) ^ 2 := by nlinarith
    have : (4 * cB 1152 5 + 1) * rho p ^ 2 * s ≤ (4 * cB 1152 5 + 1) * (3 * (R : ℝ) + 2) ^ 2 * s := by
      have : 0 ≤ (4 * cB 1152 5 + 1) * s := by positivity
      nlinarith
    linarith
  obtain ⟨hZ, hcl⟩ := vertex_core (U := U) hinj2 (A0 := 4) (B0 := 1152) (by norm_num) (by norm_num) hs
    (prepZ hR hinj ht1 ht12 ht2 hg (nrm U v R g)) (pairs_all hR hinj ht1 ht12 ht2 hg) hsm
  refine ⟨Aseq v R (gsN (nrm U v R g) U v R g) 5, ?_, nrm U v R g, ?_⟩
  · refine gchart_lift hinj1 (fun _ h => h) hZ (fun p hp => ⟨?_, le_rfl⟩)
    have h1 := rho_le_box hp
    have : 0 ≤ KT1 4 1152 * s := mul_nonneg KT1_nonneg hs
    show KT1 4 1152 * rho p * s ≤ KT1 4 1152 * (3 * R + 2) * s
    nlinarith
  · intro σ b p hp hsp
    have hpa : p ∈ Hd R σ b := ⟨Box_mono (Nat.le_succ R) hp, hsp⟩
    have hT := hcl p hp σ b hpa
    set T := trans (gsN (nrm U v R g) U v R g σ b) (Aseq v R (gsN (nrm U v R g) U v R g) 5) (iota v p)
    set C := cay (flatY U (g σ b) (iota v (baseP σ b)) (phiA v R σ b) (iota v p))
    have e : Aseq v R (gsN (nrm U v R g) U v R g) 5 (iota v p) * (g σ b (iota v p))⁻¹ = T * (nrm U v R g σ b * C) := by
      simp only [T, C, M2Glue2.trans, gsN, flA, flatten]; group
    rw [e, coe_mul, coe_mul]
    have e2 : (T : M2) * ((nrm U v R g σ b : M2) * (C : M2)) - (nrm U v R g σ b : M2)
        = ((T : M2) - 1) * ((nrm U v R g σ b : M2) * (C : M2)) + (nrm U v R g σ b : M2) * ((C : M2) - 1) := by
      noncomm_ring
    rw [e2]
    refine (frobNorm_add_le _ _).trans ?_
    have m1 : frobNorm (((T : M2) - 1) * ((nrm U v R g σ b : M2) * (C : M2))) = frobNorm ((T : M2) - 1) := by
      rw [← coe_mul, frobNorm_mul_su2]
    rw [m1, frobNorm_su2_mul]
    have hC : frobNorm ((C : M2) - 1) ≤ (9 / 2) * ((rho p + 7 / 2) * t1) :=
      (frobNorm_cay_sub_one_le (isSu2_flatY _ _ _ _ _)).trans
        (mul_le_mul_of_nonneg_left (frob_flatY_le hR hinj ht12 hg σ b (Box_mono (by omega) hp)) (by norm_num))
    have hρ := rho_ge p
    have : (9 / 2) * ((rho p + 7 / 2) * t1) ≤ 15 * rho p * t1 := by nlinarith
    linarith

end AdalyFormal.M2Glue3
