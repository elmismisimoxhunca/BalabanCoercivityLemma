import GV11

/-!
# GV12 -- the chart at a bad vertex (InterfaceCharts item (a)) (m2_glue3, 2026-10-15)

`gchart_at_bad_vertex`: six half-space charts around a lattice site `v` (one per half-space
`p_σ ≥ 0` / `p_σ ≤ −1` of the coordinate box of radius `R+2`), each a `GChart` at `(t₁, t₂)`, give ONE gauge on the
coordinate box of radius `R` around `v` which is a `GChart` at `(KT1·(3R+2)·s, KT2·s)`, `s = t₂ + 43 t₁²`, with
universal numerical constants `KT1 4 1152`, `KT2 4 1152` (no dependence on `R`, `L`, `t₁`, `t₂`, the scale `k`),
under the smallness condition `(4 cB 1152 5 + 1)(3R+2)² s ≤ 1` and the non-wrap condition `InjOn (iota v) (Box (R+3))`;
moreover it is `cB·ρ²s + 15ρt₁`-close (after a constant) to each input chart on its half-space.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AdalyFormal.M2Glue3

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.M2Glue2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul)

variable {L : PeriodicLatticeExtent}

theorem corner_hd {R : ℕ} {z : Z3} (hz : isCorner z) {σ : Fin 3} {b : Bool} (hs : hsP σ b z) : z ∈ Hd R σ b := by
  refine ⟨fun i => ?_, hs⟩
  rcases hz i with h | h <;> rw [h] <;> simp <;> omega

instance hsP_dec (σ : Fin 3) (b : Bool) (p : Z3) : Decidable (hsP σ b p) := by
  unfold hsP; infer_instance

theorem prepZ {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hR : 1 ≤ R)
    (hinj : Set.InjOn (iota v) (Box (R + 3))) {g : Fin 3 → Bool → PeriodicLatticeSite L → SU2} {t1 t2 : ℝ}
    (ht1 : 0 ≤ t1) (ht12 : t1 ≤ 2) (ht2 : 0 ≤ t2) (hg : ∀ σ b, GChart U (g σ b) (lift v (Hraw R σ b)) t1 t2)
    (n : Fin 3 → Bool → SU2) (σ : Fin 3) (b : Bool) :
    ZCh U (gsN n U v R g σ b) v (Hd R σ b) (fun p => 4 * rho p * (t2 + 43 * t1 ^ 2)) (fun _ => t2 + 43 * t1 ^ 2) := by
  have hG := (flA_gchart hinj hR ht1 ht12 hg σ b).const_mul (n σ b)
  refine flat_prepared hR (by positivity) hG (fun σ' => ?_)
  show periodicGaugeTransform (fun x => n σ b * flA U v R g σ b x) U (iota v (baseP σ b), σ') = 1
  rw [gauge_const_mul, flA_base hinj hR ht12 hg σ b σ']; group

/-- all twelve non-opposite pairs, for an abstract family normalised at the corner sites. -/
theorem pairs_abstract {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ}
    (hinj2 : Set.InjOn (iota v) (Box (R + 2))) {G : Fin 3 → Bool → PeriodicLatticeSite L → SU2} {s : ℝ} (hs : 0 ≤ s)
    (Z : ∀ σ b, ZCh U (G σ b) v (Hd R σ b) (fun p => 4 * rho p * s) (fun _ => s))
    (n0t : trans (G 2 true) (G 0 true) (iota v (zc 0 true)) = 1)
    (n0f : trans (G 2 true) (G 0 false) (iota v (zc 0 false)) = 1)
    (n1t : trans (G 2 true) (G 1 true) (iota v (zc 1 true)) = 1)
    (n1f : trans (G 2 true) (G 1 false) (iota v (zc 1 false)) = 1)
    (n2f : trans (G 0 true) (G 2 false) (iota v (zc 2 false)) = 1) :
    ∀ σ b σ' b' p, p ∈ Hd R σ b → p ∈ Hd R σ' b' →
      frobNorm (((trans (G σ b) (G σ' b') (iota v p) : SU2) : M2) - 1) ≤ 1152 * rho p ^ 2 * s := by
  -- direct pairs
  have direct : ∀ σ b σ' b' (z : Z3), isCorner z → hsP σ b z → hsP σ' b' z →
      trans (G σ b) (G σ' b') (iota v z) = 1 →
      ∀ p, p ∈ Hd R σ b → p ∈ Hd R σ' b' →
        frobNorm (((trans (G σ b) (G σ' b') (iota v p) : SU2) : M2) - 1) ≤ 128 * rho p ^ 2 * s := by
    intro σ b σ' b' z hz h1 h2 he p hp1 hp2
    have hE : frobNorm (((trans (G σ b) (G σ' b') (iota v z) : SU2) : M2) - 1) ≤ 0 := by
      rw [he]; simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]
    have := pair_growth hinj2 hs (Z σ b) (Z σ' b') hz (corner_hd hz h1) (corner_hd hz h2) hp1 hp2 hE
    linarith
  have symm : ∀ σ b σ' b' (B : ℝ), (∀ p, p ∈ Hd R σ b → p ∈ Hd R σ' b' →
      frobNorm (((trans (G σ b) (G σ' b') (iota v p) : SU2) : M2) - 1) ≤ B * rho p ^ 2 * s) →
      ∀ p, p ∈ Hd R σ' b' → p ∈ Hd R σ b →
      frobNorm (((trans (G σ' b') (G σ b) (iota v p) : SU2) : M2) - 1) ≤ B * rho p ^ 2 * s := by
    intro σ b σ' b' B h p h1 h2
    rw [frob_trans_symm]; exact h p h2 h1
  have cz : ∀ (z : Z3), (∀ i, z i = 0 ∨ z i = -1) → isCorner z := fun z h => h
  -- the five normalised pairs
  have D1 := direct 2 true 0 true (zc 0 true) (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP, zc]) (by simp [hsP, zc]) n0t
  have D2 := direct 2 true 0 false (zc 0 false) (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP, zc]) (by simp [hsP, zc]) n0f
  have D3 := direct 2 true 1 true (zc 1 true) (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP, zc]) (by simp [hsP, zc]) n1t
  have D4 := direct 2 true 1 false (zc 1 false) (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP, zc]) (by simp [hsP, zc]) n1f
  have D5 := direct 0 true 2 false (zc 2 false) (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP, zc]) (by simp [hsP, zc]) n2f
  have h128 : (0 : ℝ) ≤ 128 := by norm_num
  -- pairs through a third chart
  have V6 := pair_via hinj2 hs h128 h128 (Z 0 true) (Z 1 true) (symm _ _ _ _ _ D1) D3 (z := ![0, 0, 0])
    (cz _ (by intro i; fin_cases i <;> simp [zc])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
    (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
  have V7 := pair_via hinj2 hs h128 h128 (Z 0 true) (Z 1 false) (symm _ _ _ _ _ D1) D4 (z := ![0, -1, 0])
    (cz _ (by intro i; fin_cases i <;> simp [zc])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
    (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
  have V8 := pair_via hinj2 hs h128 h128 (Z 0 false) (Z 1 true) (symm _ _ _ _ _ D2) D3 (z := ![-1, 0, 0])
    (cz _ (by intro i; fin_cases i <;> simp [zc])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
    (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
  have V9 := pair_via hinj2 hs h128 h128 (Z 0 false) (Z 1 false) (symm _ _ _ _ _ D2) D4 (z := ![-1, -1, 0])
    (cz _ (by intro i; fin_cases i <;> simp [zc])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
    (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
  have h384 : (0 : ℝ) ≤ 128 + 128 + 128 := by norm_num
  have V10 := pair_via hinj2 hs h384 h128 (Z 1 true) (Z 2 false) (symm _ _ _ _ _ V6) D5 (z := ![0, 0, -1])
    (cz _ (by intro i; fin_cases i <;> simp [zc])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
    (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
  have V11 := pair_via hinj2 hs h384 h128 (Z 1 false) (Z 2 false) (symm _ _ _ _ _ V7) D5 (z := ![0, -1, -1])
    (cz _ (by intro i; fin_cases i <;> simp [zc])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
    (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
  have h640 : (0 : ℝ) ≤ 128 + (128 + 128 + 128) + 128 := by norm_num
  have V12 := pair_via hinj2 hs h384 h640 (Z 0 false) (Z 2 false) V8 V10 (z := ![-1, 0, -1])
    (cz _ (by intro i; fin_cases i <;> simp [zc])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP])) (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
    (corner_hd (cz _ (by intro i; fin_cases i <;> simp [zc])) (by simp [hsP]))
  -- weaken everything to 1152
  have W : ∀ σ b σ' b' (B : ℝ), B ≤ 1152 → (∀ p, p ∈ Hd R σ b → p ∈ Hd R σ' b' →
      frobNorm (((trans (G σ b) (G σ' b') (iota v p) : SU2) : M2) - 1) ≤ B * rho p ^ 2 * s) →
      ∀ p, p ∈ Hd R σ b → p ∈ Hd R σ' b' →
      frobNorm (((trans (G σ b) (G σ' b') (iota v p) : SU2) : M2) - 1) ≤ 1152 * rho p ^ 2 * s := by
    intro σ b σ' b' B hB h p h1 h2
    refine (h p h1 h2).trans ?_
    have : 0 ≤ rho p ^ 2 * s := by positivity
    nlinarith
  have same : ∀ σ b p, frobNorm (((trans (G σ b) (G σ b) (iota v p) : SU2) : M2) - 1) ≤ 1152 * rho p ^ 2 * s := by
    intro σ b p
    have e : trans (G σ b) (G σ b) (iota v p) = 1 := by simp [M2Glue2.trans]
    rw [e]
    have : 0 ≤ 1152 * rho p ^ 2 * s := by positivity
    simpa [AdalyFormal.Balaban.RMapLipschitz.frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq] using this
  have opp : ∀ σ p, p ∈ Hd R σ true → p ∈ Hd R σ false → False := by
    intro σ p h1 h2
    have a := h1.2; have c := h2.2
    unfold hsP at a c; simp at a c; omega
  intro σ b σ' b' p h1 h2
  match σ, b, σ', b' with
  | 0, false, 0, false => exact same _ _ p
  | 0, false, 0, true => exact (opp _ p h2 h1).elim
  | 0, false, 1, false => exact W _ _ _ _ _ (by norm_num) V9 p h1 h2
  | 0, false, 1, true => exact W _ _ _ _ _ (by norm_num) V8 p h1 h2
  | 0, false, 2, false => exact W _ _ _ _ _ (by norm_num) V12 p h1 h2
  | 0, false, 2, true => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ D2) p h1 h2
  | 0, true, 0, false => exact (opp _ p h1 h2).elim
  | 0, true, 0, true => exact same _ _ p
  | 0, true, 1, false => exact W _ _ _ _ _ (by norm_num) V7 p h1 h2
  | 0, true, 1, true => exact W _ _ _ _ _ (by norm_num) V6 p h1 h2
  | 0, true, 2, false => exact W _ _ _ _ _ (by norm_num) D5 p h1 h2
  | 0, true, 2, true => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ D1) p h1 h2
  | 1, false, 0, false => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ V9) p h1 h2
  | 1, false, 0, true => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ V7) p h1 h2
  | 1, false, 1, false => exact same _ _ p
  | 1, false, 1, true => exact (opp _ p h2 h1).elim
  | 1, false, 2, false => exact W _ _ _ _ _ (by norm_num) V11 p h1 h2
  | 1, false, 2, true => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ D4) p h1 h2
  | 1, true, 0, false => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ V8) p h1 h2
  | 1, true, 0, true => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ V6) p h1 h2
  | 1, true, 1, false => exact (opp _ p h1 h2).elim
  | 1, true, 1, true => exact same _ _ p
  | 1, true, 2, false => exact W _ _ _ _ _ (by norm_num) V10 p h1 h2
  | 1, true, 2, true => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ D3) p h1 h2
  | 2, false, 0, false => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ V12) p h1 h2
  | 2, false, 0, true => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ D5) p h1 h2
  | 2, false, 1, false => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ V11) p h1 h2
  | 2, false, 1, true => exact W _ _ _ _ _ (by norm_num) (symm _ _ _ _ _ V10) p h1 h2
  | 2, false, 2, false => exact same _ _ p
  | 2, false, 2, true => exact (opp _ p h2 h1).elim
  | 2, true, 0, false => exact W _ _ _ _ _ (by norm_num) D2 p h1 h2
  | 2, true, 0, true => exact W _ _ _ _ _ (by norm_num) D1 p h1 h2
  | 2, true, 1, false => exact W _ _ _ _ _ (by norm_num) D4 p h1 h2
  | 2, true, 1, true => exact W _ _ _ _ _ (by norm_num) D3 p h1 h2
  | 2, true, 2, false => exact (opp _ p h1 h2).elim
  | 2, true, 2, true => exact same _ _ p

theorem pairs_all {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hR : 1 ≤ R)
    (hinj : Set.InjOn (iota v) (Box (R + 3))) {g : Fin 3 → Bool → PeriodicLatticeSite L → SU2} {t1 t2 : ℝ}
    (ht1 : 0 ≤ t1) (ht12 : t1 ≤ 2) (ht2 : 0 ≤ t2) (hg : ∀ σ b, GChart U (g σ b) (lift v (Hraw R σ b)) t1 t2) :
    ∀ σ b σ' b' p, p ∈ Hd R σ b → p ∈ Hd R σ' b' →
      frobNorm (((trans (gsN (nrm U v R g) U v R g σ b) (gsN (nrm U v R g) U v R g σ' b') (iota v p) : SU2) : M2) - 1)
        ≤ 1152 * rho p ^ 2 * (t2 + 43 * t1 ^ 2) :=
  pairs_abstract (hinj.mono (Box_mono (Nat.le_succ _))) (by positivity)
    (prepZ hR hinj ht1 ht12 ht2 hg (nrm U v R g))
    (norm_2t U v R g 0 (by decide) true) (norm_2t U v R g 0 (by decide) false)
    (norm_2t U v R g 1 (by decide) true) (norm_2t U v R g 1 (by decide) false) (norm_2f U v R g)

end AdalyFormal.M2Glue3
