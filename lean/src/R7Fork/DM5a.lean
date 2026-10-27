import R7Fork.DM4b

/-!
# DM5a -- glue lemmas: masked curl norm as a plaquette sum; embedded `Omega_k`-bonds lie in `frakB`; the curl of a touching-supported field
vanishes on plaquettes whose unit box is not inside `Omega_k` (uses `LambdaOK` with `3 <= R M`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.DirichletMono

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlCovariantLM)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

open Classical in
theorem masked_curl_norm_sq {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L)) (x : BondFnL2 L) :
    ‖AdalyFormal.StatementLaneR6.plaqMask P
        (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) x)‖ ^ 2
      = ∑ p ∈ (Finset.univ : Finset (PeriodicLatticePlaquette L)).filter (fun p => p ∈ P),
          ‖flatCurlValue (WithLp.ofLp x) p‖ ^ 2 := by
  have hx : x = WithLp.toLp 2 (WithLp.ofLp x) := rfl
  have hpt : ∀ p, (curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) x) p = flatCurlValue (WithLp.ofLp x) p := by
    intro p
    rw [hx, curlCovariantCLM_L2_toLp]
    have hc : curlCovariantLM (trivialU L) (WithLp.ofLp (WithLp.toLp 2 (WithLp.ofLp x))) = flatCurlValue (WithLp.ofLp x) := by
      rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
    exact congrFun hc p
  rw [PiLp.norm_sq_eq_of_L2, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [AdalyFormal.StatementLaneR6.plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]; rw [hpt p]
  · simp [hp]

theorem emb_lam_k {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (y : PeriodicLatticeSite Lu)
    (hy : embY ell k Lu hell y ∈ S.Om k) : embY ell k Lu hell y ∈ (geomOf ell k S).Lam k := by
  refine ⟨fun μ => dvd_mul_right _ _, hy, ?_⟩
  have : S.Om (k + 1) = ∅ := hS.2.1 (k + 1) (Nat.lt_succ_self k)
  rw [this]; exact Set.notMem_empty _

theorem emb_bondsLam {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (e : Bond Lu)
    (h : embY ell k Lu hell e.1 ∈ S.Om k) : unitBondEmb ell k Lu hell e ∈ bondsLam (geomOf ell k S) k :=
  ⟨Or.inl (emb_lam_k hell hS e.1 h),
    fun hh => hh.elim (not_OmGe_of_lt (by show k < k + 1; omega) _) (not_OmGe_of_lt (by show k < k + 1; omega) _)⟩

theorem pcd_self' (N a : ℕ) : pcd N a a = 0 := by unfold pcd; simp

theorem pcd_box_le {Lu : PeriodicLatticeExtent} (hu : ∀ ρ, 1 ≤ Lu ρ) {z c c' : PeriodicLatticeSite Lu}
    (h : InBox z c) (h' : InBox z c') (ρ : Fin 3) : pcd (Lu ρ + 1) (c ρ).val (c' ρ).val ≤ 1 := by
  have hs : ∀ (w : Fin (Lu ρ + 1)), (w + 1).val = (w.val + 1) % (Lu ρ + 1) := fun w => AdalyFormal.StatementLane2.fin_succ_val ρ (hu ρ) w
  have key : pcd (Lu ρ + 1) (z ρ).val (z ρ + 1).val ≤ 1 := by
    rw [hs]; exact pcd_succ_le _ _ (z ρ).isLt
  rcases h ρ with h1 | h1 <;> rcases h' ρ with h2 | h2 <;> rw [h1, h2]
  · rw [pcd_self']; omega
  · exact key
  · rw [pcd_comm]; exact key
  · rw [pcd_self']; omega

theorem pdist_box_le {Lu : PeriodicLatticeExtent} (hu : ∀ ρ, 1 ≤ Lu ρ) {z c c' : PeriodicLatticeSite Lu}
    (h : InBox z c) (h' : InBox z c') : pdist c c' ≤ 3 := by
  unfold pdist
  rw [Fin.sum_univ_three]
  have := pcd_box_le hu h h' 0
  have := pcd_box_le hu h h' 1
  have := pcd_box_le hu h h' 2
  omega

theorem curl_zero_of_not_good {ell M R k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent}
    (hu : ∀ ρ, 1 ≤ Lu ρ) (hRM : 3 ≤ R * M) {S : Tower (scaleUp ell k Lu)}
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK ell M R k S Lam)
    (Bf : Bond Lu → SuTwo)
    (hsup : ∀ e : Bond Lu, Bf e ≠ 0 → e.1 ∈ Lam ∨ periodicLatticeShift e.1 e.2 ∈ Lam)
    (q : PeriodicLatticePlaquette Lu)
    (hq : ¬ ∀ c, InBox q.1 c → embY ell k Lu hell c ∈ S.Om k) :
    AdalyFormal.Balaban.CovU1Reduction.flatCurlValue Bf q = 0 := by
  obtain ⟨-, hfar⟩ := lambdaOK_embY hell hL
  have hμν : q.2.1.1 ≠ q.2.1.2 := ne_of_lt q.2.2
  -- any bond of the plaquette with nonzero value would put all of the box into `Om k`
  have hbond : ∀ e : Bond Lu, (InBox q.1 e.1 ∧ InBox q.1 (periodicLatticeShift e.1 e.2)) → Bf e = 0 := by
    intro e ⟨h1, h2⟩
    by_contra hne
    apply hq
    intro c hc
    rcases hsup e hne with hy | hy
    · by_contra hn
      have := hfar _ hy c hn
      have h3 := pdist_box_le hu h1 hc
      omega
    · by_contra hn
      have := hfar _ hy c hn
      have h3 := pdist_box_le hu h2 hc
      omega
  unfold AdalyFormal.Balaban.CovU1Reduction.flatCurlValue
  have e1 := hbond (q.1, q.2.1.1) ⟨self_inBox _, shift_inBox _ _⟩
  have e2 := hbond (periodicLatticeShift q.1 q.2.1.1, q.2.1.2) ⟨shift_inBox _ _, shift_shift_inBox _ _ _ hμν⟩
  have e3 := hbond (periodicLatticeShift q.1 q.2.1.2, q.2.1.1)
    ⟨shift_inBox _ _, shift_shift_inBox _ _ _ (Ne.symm hμν)⟩
  have e4 := hbond (q.1, q.2.1.2) ⟨self_inBox _, shift_inBox _ _⟩
  simp only [e1, e2, e3, e4]; simp

#print axioms masked_curl_norm_sq
#print axioms emb_bondsLam
#print axioms pdist_box_le
#print axioms curl_zero_of_not_good

end AdalyFormal.DirichletMono
