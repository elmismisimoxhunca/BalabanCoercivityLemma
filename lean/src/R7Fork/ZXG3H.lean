import R7Fork.ZXG3G
import R7Fork.ZR2B3

/-!
# G3H -- the genuine class lives inside `𝔅`: for `B̃` in the touching class, `C B̃` is supported on unit
bonds that are (embeddings of) level-`k` bonds of `𝔅`.  Consequently the first term of (3.156), which
sees `B` only through `τ* B`, loses nothing, and the `a⟨B,B⟩` term has no off-`𝔅` part.
Also: `‖τ* B‖ = ‖B‖` for `B` supported on the image.  No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)

theorem pcd_comm (N a b : ℕ) : pcd N a b = pcd N b a := by
  unfold pcd; split_ifs <;> omega

theorem pcd_succ_le (N a : ℕ) (ha : a < N) : pcd N a ((a + 1) % N) ≤ 1 := by
  unfold pcd
  by_cases h : a + 1 < N
  · rw [Nat.mod_eq_of_lt h]; split_ifs <;> omega
  · have : a + 1 = N := by omega
    rw [this, Nat.mod_self]; split_ifs <;> omega

theorem pdist_shift_le {L : PeriodicLatticeExtent} (hN : ∀ μ, 1 ≤ L μ) (y : PeriodicLatticeSite L)
    (μ : Fin 3) : pdist y (periodicLatticeShift y μ) ≤ 1 := by
  unfold pdist
  have hz : ∀ ν : Fin 3, ν ≠ μ →
      pcd (L ν + 1) (y ν).val ((periodicLatticeShift y μ) ν).val = 0 := by
    intro ν h
    rw [shift_apply]
    simp only [h, if_false]
    unfold pcd; split_ifs <;> omega
  rw [Finset.sum_eq_single μ (fun ν _ h => hz ν h) (fun h => absurd (Finset.mem_univ _) h)]
  rw [shift_apply]
  simp only [if_true]
  rw [fin_succ_val μ (hN μ)]
  exact pcd_succ_le _ _ (y μ).isLt

theorem pdist_comm {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) : pdist x y = pdist y x := by
  unfold pdist
  exact Finset.sum_congr rfl (fun μ _ => pcd_comm _ _ _)

/-- `coarseShift` of an embedded site is the embedding of the unit shift -/
theorem coarseShift_embY (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (hN : ∀ μ, 1 ≤ Lu μ) (y : PeriodicLatticeSite Lu) (μ : Fin 3) :
    coarseShift (embY ell k Lu hell y) (ell ^ k) μ = embY ell k Lu hell (periodicLatticeShift y μ) := by
  funext ν
  apply Fin.ext
  by_cases h : ν = μ
  · subst h
    rw [coarseShift_val_eq]
    show ((ell ^ k * (y ν).val) + ell ^ k) % (scaleUp ell k Lu ν + 1) = ell ^ k * ((periodicLatticeShift y ν) ν).val
    have hsu : scaleUp ell k Lu ν + 1 = (Lu ν + 1) * ell ^ k := scaleUp_succ ell k Lu hell ν
    rw [hsu]
    have hs : ((periodicLatticeShift y ν) ν).val = ((y ν).val + 1) % (Lu ν + 1) := by
      rw [shift_apply]; simp only [if_true]
      exact fin_succ_val ν (hN ν) (y ν)
    rw [hs, show (Lu ν + 1) * ell ^ k = ell ^ k * (Lu ν + 1) from mul_comm _ _,
      show ell ^ k * (y ν).val + ell ^ k = ell ^ k * ((y ν).val + 1) by ring, Nat.mul_mod_mul_left]
  · rw [coarseShift_apply_ne _ _ _ _ h]
    show ell ^ k * (y ν).val = ell ^ k * ((periodicLatticeShift y μ) ν).val
    rw [shift_apply]; simp [h]

#print axioms coarseShift_embY
#print axioms pdist_shift_le
#print axioms pdist_comm


open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.FullReparamC (pathSite_mem_block)

/-- the unit-torus site `emb` is the embedding of the statement lane's `LambdaOK` -/
theorem lambdaOK_embY {ell M R k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent}
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)}
    (hL : LambdaOK ell M R k S Lam) :
    (∀ y ∈ Lam, embY ell k Lu hell y ∈ S.Om k) ∧
    (∀ y ∈ Lam, ∀ y' : PeriodicLatticeSite Lu, embY ell k Lu hell y' ∉ S.Om k → R * M < pdist y y') := by
  obtain ⟨-, emb, hemb, hin, hfar⟩ := hL
  have h : emb = embY ell k Lu hell := by
    funext y μ
    exact Fin.ext (hemb y μ)
  subst h
  exact ⟨hin, hfar⟩

/-- **a bond touching `Λ` is an embedded level-`k` bond of `𝔅`** (`Λ ⊂ Λ_k` with `RM ≥ 1` collar) -/
theorem touching_in_frakB {ell M R k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent}
    (hN : ∀ μ, 1 ≤ Lu μ) (hMR : 1 ≤ R * M) {S : Tower (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) {Lam : Set (PeriodicLatticeSite Lu)}
    (hL : LambdaOK ell M R k S Lam) (e : Bond Lu)
    (he : e.1 ∈ Lam ∨ periodicLatticeShift e.1 e.2 ∈ Lam) :
    unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k := by
  obtain ⟨hin, hfar⟩ := lambdaOK_embY hell hL
  have hnear : ∀ y ∈ Lam, ∀ y' : PeriodicLatticeSite Lu, pdist y y' ≤ R * M →
      embY ell k Lu hell y' ∈ S.Om k := by
    intro y hy y' hd
    by_contra hn
    exact absurd (hfar y hy y' hn) (not_lt.mpr hd)
  have h1 : pdist e.1 (periodicLatticeShift e.1 e.2) ≤ R * M :=
    le_trans (pdist_shift_le hN e.1 e.2) hMR
  have h2 : pdist (periodicLatticeShift e.1 e.2) e.1 ≤ R * M := by rw [pdist_comm]; exact h1
  have hOm : embY ell k Lu hell e.1 ∈ S.Om k ∧
      embY ell k Lu hell (periodicLatticeShift e.1 e.2) ∈ S.Om k := by
    rcases he with h | h
    · exact ⟨hin _ h, hnear _ h _ h1⟩
    · exact ⟨hnear _ h _ h2, hin _ h⟩
  have hLamk : ∀ y : PeriodicLatticeSite Lu, embY ell k Lu hell y ∈ S.Om k →
      embY ell k Lu hell y ∈ (geomOf ell k S).Lam k := by
    intro y hy
    refine ⟨fun μ => dvd_mul_right _ _, hy, ?_⟩
    have : S.Om (k + 1) = ∅ := hS.2.1 (k + 1) (Nat.lt_succ_self k)
    rw [this]; exact Set.notMem_empty _
  exact ⟨Or.inl (hLamk _ hOm.1),
    fun hh => hh.elim (not_OmGe_of_lt (by show k < k + 1; omega) _) (not_OmGe_of_lt (by show k < k + 1; omega) _)⟩

/-- a dropped bond TOUCHES `Λ` (r5 (3): rows touch `Λ'` through `c₋` or `c₊`; the bond `b₀ = (c₋ + (ell-1)e, μ)` has base in
`B(c₋)` and target `c₊`) -/
theorem dropped_touches_lam {ell : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent}
    (hdvd : ∀ μ, ell ∣ Lu μ + 1) {Lam : Set (PeriodicLatticeSite Lu)} {b : Bond Lu}
    (hb : IsDroppedIn Lam ell b) : b.1 ∈ Lam ∨ periodicLatticeShift b.1 b.2 ∈ Lam := by
  obtain ⟨c, hc, rfl⟩ := hb
  rcases hc with ⟨hcl, hblk⟩ | ⟨hcl, hblk⟩
  · left
    have hfit : (c.1.1 c.2).val + ell ≤ Lu c.2 + 1 := by
      have h0 := (mem_CoarseLattice.mp c.1.2) c.2
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h0
      obtain ⟨r, hr⟩ := hdvd c.2
      have hlt := (c.1.1 c.2).isLt
      have hqr : q < r := by
        by_contra hn
        push_neg at hn
        have : ell * r ≤ ell * q := Nat.mul_le_mul_left ell hn
        omega
      have : ell * (q + 1) ≤ ell * r := Nat.mul_le_mul_left ell hqr
      nlinarith
    exact hblk _ (pathSite_mem_block hell c.1.1 c.2 (ell - 1) (by omega) hfit)
  · right
    have hsh : periodicLatticeShift (droppedBondLast ell c).1 (droppedBondLast ell c).2 =
        coarseShift c.1.1 ell c.2 := by
      show periodicLatticeShift (pathSite c.1.1 c.2 (ell - 1)) c.2 = coarseShift c.1.1 ell c.2
      unfold pathSite coarseShift
      rw [← Function.iterate_succ_apply' (fun z => periodicLatticeShift z c.2)]
      congr 1
      omega
    rw [hsh]
    refine hblk (coarseShift c.1.1 ell c.2) ?_
    rw [AdalyFormal.Balaban.AdmissibleSubspace.mem_blockOf]
    intro ν; omega

/-- **SUPPORT of `C B̃`**: for `B̃` in the touching class, `(C B̃)(e) ≠ 0` forces `e` to be an embedded
`𝔅`-bond (so `τ τ* (C B̃) = C B̃`). -/
theorem Cop_support {ell M R k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent}
    (hdvd : ∀ μ, ell ∣ Lu μ + 1) (hN : ∀ μ, 1 ≤ Lu μ) (hMR : 1 ≤ R * M)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) {Lam : Set (PeriodicLatticeSite Lu)}
    (hL : LambdaOK ell M R k S Lam)
    (Q : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo)) (Bt : Bond Lu → SuTwo)
    (hBt : OnLambdaT Lam Bt) (e : Bond Lu) (hne : Cop Lam Q Bt e ≠ 0) :
    unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k := by
  refine touching_in_frakB hell hN hMR hS hL e ?_
  by_cases hd : IsDroppedIn Lam ell e
  · exact dropped_touches_lam hell hdvd hd
  · rw [Cop_id Lam Q Bt e hd] at hne
    by_contra hnt
    exact hne (hBt e hnt)

#print axioms touching_in_frakB
#print axioms dropped_touches_lam
#print axioms Cop_support


/-! ### `τ τ* B = B` for `B` supported on the image of `𝔅` -/

section tau
variable (P : IngrBParams)

/-- the level-`k` index of an embedded unit bond -/
def pe (e : Bond P.Lu) (h : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam P.G P.k) : BIdx P.G :=
  ⟨Fin.last P.k, ⟨unitBondEmb P.ell P.k P.Lu P.hell e, h⟩⟩

theorem tau_apply_mem (f : FSp P.G) (e : Bond P.Lu)
    (h : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam P.G P.k) :
    (WithLp.ofLp (P.tau f)) e = (WithLp.ofLp f) (pe P e h) := by
  classical
  show (if hb : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam (geomOf P.ell P.k P.S) P.k
      then WithLp.ofLp f ⟨Fin.last P.k, ⟨unitBondEmb P.ell P.k P.Lu P.hell e, hb⟩⟩ else 0) = _
  rw [dif_pos h]; rfl

theorem tau_apply_not_mem (f : FSp P.G) (e : Bond P.Lu)
    (h : unitBondEmb P.ell P.k P.Lu P.hell e ∉ bondsLam P.G P.k) :
    (WithLp.ofLp (P.tau f)) e = 0 := by
  classical
  show (if hb : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam (geomOf P.ell P.k P.S) P.k
      then WithLp.ofLp f ⟨Fin.last P.k, ⟨unitBondEmb P.ell P.k P.Lu P.hell e, hb⟩⟩ else 0) = 0
  rw [dif_neg h]

theorem pe_injective (e e' : Bond P.Lu) (h : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam P.G P.k)
    (h' : unitBondEmb P.ell P.k P.Lu P.hell e' ∈ bondsLam P.G P.k) (hee : pe P e h = pe P e' h') : e = e' := by
  have := congrArg (fun p : BIdx P.G => p.2.1) hee
  exact unitBondEmb_injective P.ell P.k P.Lu P.hell this

/-- `(τ* B)(p_e) = B e` -/
theorem tauAdj_apply (B : BondFnL2 P.Lu) (e : Bond P.Lu)
    (h : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam P.G P.k) :
    (WithLp.ofLp (ContinuousLinearMap.adjoint P.tau B)) (pe P e h) = (WithLp.ofLp B) e := by
  classical
  refine ext_inner_left ℝ (fun v => ?_)
  -- ⟨v, (τ*B)(p_e)⟩ = ⟨single p_e v, τ* B⟩ = ⟨τ (single p_e v), B⟩ = ⟨v, B e⟩
  have h1 : ⟪v, (WithLp.ofLp (ContinuousLinearMap.adjoint P.tau B)) (pe P e h)⟫ =
      ⟪(WithLp.toLp 2 (Pi.single (pe P e h) v) : FSp P.G), ContinuousLinearMap.adjoint P.tau B⟫ := by
    rw [PiLp.inner_apply, Finset.sum_eq_single (pe P e h)]
    · simp
    · intro p _ hp; simp [Pi.single_apply, hp]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  have h2 : P.tau (WithLp.toLp 2 (Pi.single (pe P e h) v) : FSp P.G) =
      WithLp.toLp 2 (Pi.single e v) := by
    refine PiLp.ext (fun e' => ?_)
    by_cases hm : unitBondEmb P.ell P.k P.Lu P.hell e' ∈ bondsLam P.G P.k
    · rw [tau_apply_mem P _ e' hm]
      by_cases hee : e' = e
      · subst hee; simp
      · have : pe P e' hm ≠ pe P e h := fun hh => hee (pe_injective P e' e hm h hh)
        simp [Pi.single_apply, this, hee]
    · rw [tau_apply_not_mem P _ e' hm]
      have hee : e' ≠ e := fun hh => hm (hh ▸ h)
      simp [Pi.single_apply, hee]
  rw [h1, ContinuousLinearMap.adjoint_inner_right, h2, PiLp.inner_apply, Finset.sum_eq_single e]
  · simp
  · intro p _ hp; simp [Pi.single_apply, hp]
  · intro hh; exact absurd (Finset.mem_univ _) hh

/-- **`τ τ* B = B` when `B` is supported on the embedded `𝔅`-bonds**; hence `‖τ*B‖ = ‖B‖` there. -/
theorem tau_tauAdj_of_supp (B : BondFnL2 P.Lu)
    (hB : ∀ e : Bond P.Lu, unitBondEmb P.ell P.k P.Lu P.hell e ∉ bondsLam P.G P.k → (WithLp.ofLp B) e = 0) :
    P.tau (ContinuousLinearMap.adjoint P.tau B) = B := by
  refine PiLp.ext (fun e => ?_)
  by_cases hm : unitBondEmb P.ell P.k P.Lu P.hell e ∈ bondsLam P.G P.k
  · rw [tau_apply_mem P _ e hm, tauAdj_apply P B e hm]
  · rw [tau_apply_not_mem P _ e hm, hB e hm]

theorem inner_tauAdj_of_supp (B : BondFnL2 P.Lu)
    (hB : ∀ e : Bond P.Lu, unitBondEmb P.ell P.k P.Lu P.hell e ∉ bondsLam P.G P.k → (WithLp.ofLp B) e = 0) :
    ⟪ContinuousLinearMap.adjoint P.tau B, ContinuousLinearMap.adjoint P.tau B⟫ = ⟪B, B⟫ := by
  rw [ContinuousLinearMap.adjoint_inner_right, tau_tauAdj_of_supp P B hB]

end tau

#print axioms tauAdj_apply
#print axioms tau_tauAdj_of_supp
#print axioms inner_tauAdj_of_supp

end AdalyFormal.StatementLaneG
