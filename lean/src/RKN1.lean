import RKL3
/-!
# RKN1 -- one level of the NONABELIAN towers in the given gauge, linearised at EVERY bond.

Notation: `bg l = ubarTowerSU2 ell U l` (the tree's genuine blocked tower, truncated blocks at junk bonds),
`st l = strT ell U l` (straight tower, CB3), `Alog V b = su2Log (V b)`.
* `step_bg`: chart `‖Alog (bg l)‖ ≤ k`, `8 ell k ≤ 1/(8π)` ⇒ at every bond `c`:
  `exp (Alog (bg (l+1)) c) = bg (l+1) c` and `‖Alog (bg (l+1)) c − blkM (ell^l) ell (Alog (bg l)) c‖ ≤ 200π ell² k²` (NB7).
* `step_st`: chart `‖Alog (st l)‖ ≤ k`, `ell k ≤ 1/(2π)` ⇒ `‖Alog (st (l+1)) c − bondM (ell^l) ell (Alog (st l)) c‖ ≤ 2π (ell k)²` (NB1).
* `src_st`: `‖blkM (Alog (st l)) c − bondM (Alog (st l)) c‖ ≤ 3(ell−1) ell (P + P³/8 + 32π k²)`, `P = (ell²)^l q0`
  (curvature of the straight tower, CB3 `pw_strT_le`, through NB2 ladders and NB8 `curlM_le_plaq`).
Kernel-checked; standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.RegBgKU
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathEndpoint coarsePathHolonomy)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq coarseBondVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarTowerSU2)
open AdalyFormal.Balaban.ClassPropagationUbar (gammaPath_length_le)
open AdalyFormal.Balaban.Bch2 (IsSu2)
open AdalyFormal.CurvBlock (pathM bondM loopM blkM ladAM curlM off gamma_end endpoint_rep pathBonds Chart
  hol_eq_prod sum_pathBonds length_pathBonds multi_bch log_ubar_lin curlM_le_plaq ladAM_le strT pw_strT_le dv pw
  ladPlaqs)

variable {L : PeriodicLatticeExtent}

/-- the Lie-algebra field of a configuration. -/
def Alog (V : PeriodicLinkConfiguration SU2 L) : Fld L := fun b => su2Log (V b)

theorem step_bg (ell l : ℕ) (hell : 0 < ell) (U : PeriodicLinkConfiguration SU2 L) (k : ℝ) (hk : 0 ≤ k)
    (hsm : 8 * (ell : ℝ) * k ≤ 1 / (8 * Real.pi))
    (hch : ∀ b, Chart (ubarTowerSU2 ell U l) (Alog (ubarTowerSU2 ell U l)) k b) (c : PeriodicLatticeEdge L) :
    su2Exp (Alog (ubarTowerSU2 ell U (l + 1)) c) = ubarTowerSU2 ell U (l + 1) c ∧
    frobNorm (Alog (ubarTowerSU2 ell U (l + 1)) c - blkM (ell ^ l) ell (Alog (ubarTowerSU2 ell U l)) c)
      ≤ 200 * Real.pi * ((ell : ℝ) ^ 2 * k ^ 2) := by
  have h := log_ubar_lin (ell ^ l) ell (by positivity) hell (ubarTowerSU2 ell U l) (Alog (ubarTowerSU2 ell U l)) k hk hsm c
    (fun x _ b _ => hch b) (fun b _ => hch b)
  exact h

theorem step_st (ell l : ℕ) (U : PeriodicLinkConfiguration SU2 L) (k : ℝ) (hk : 0 ≤ k)
    (hsm : (ell : ℝ) * k ≤ 1 / (2 * Real.pi))
    (hch : ∀ b, Chart (strT ell U l) (Alog (strT ell U l)) k b) (c : PeriodicLatticeEdge L) :
    frobNorm (Alog (strT ell U (l + 1)) c - bondM (ell ^ l) ell (Alog (strT ell U l)) c)
      ≤ 2 * Real.pi * ((ell : ℝ) * k) ^ 2 := by
  set s := ell ^ l
  set as : List M2 := (pathBonds s c.1 (List.replicate ell c.2)).map (Alog (strT ell U l)) with has
  have hprod : strT ell U (l + 1) c = (as.map su2Exp).prod := by
    show coarseBondVar s ell (strT ell U l) c = _
    unfold coarseBondVar
    rw [hol_eq_prod s (strT ell U l) (Alog (strT ell U l)) _ _ (fun b _ => (hch b).1)]
  have hsu : ∀ a ∈ as, IsSu2 a := by
    intro a ha; rw [has, List.mem_map] at ha; obtain ⟨b, _, rfl⟩ := ha; exact (hch b).2.1
  have hlen : as.length = ell := by rw [has, List.length_map, length_pathBonds, List.length_replicate]
  have hn : (as.map frobNorm).sum ≤ (ell : ℝ) * k := by
    have : ∀ a ∈ as.map frobNorm, a ≤ k := by
      intro a ha; rw [List.mem_map] at ha; obtain ⟨x, hx, rfl⟩ := ha
      rw [has, List.mem_map] at hx; obtain ⟨b, _, rfl⟩ := hx; exact (hch b).2.2
    have h := List.sum_le_card_nsmul (as.map frobNorm) k this
    rw [List.length_map, hlen, nsmul_eq_mul] at h; exact h
  have hn0 : 0 ≤ (as.map frobNorm).sum := List.sum_nonneg (fun a ha => by
    rw [List.mem_map] at ha; obtain ⟨x, _, rfl⟩ := ha; exact frobNorm_nonneg _)
  obtain ⟨_, hb⟩ := multi_bch as hsu (hn.trans hsm)
  have hsum : as.sum = bondM s ell (Alog (strT ell U l)) c := by
    rw [has, sum_pathBonds]; rfl
  have e : Alog (strT ell U (l + 1)) c = su2Log ((as.map su2Exp).prod) := by
    unfold Alog; rw [hprod]
  rw [e, ← hsum]
  refine hb.trans ?_
  have := mul_le_mul hn hn hn0 (by positivity)
  nlinarith [Real.pi_pos]

theorem loopM_eq_ladAM (s ell : ℕ) (A : Fld L) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 s ell) :
    loopM s ell A c x = ladAM s A c.1 (coarseGammaPath s c.1 x) c.2 ell := by
  have hx' := mem_stepBlockOf.mp hx
  have hoff : ∀ σ, s ∣ off c.1 x σ := by
    intro σ; have h := hx' σ; unfold off; rw [Fin.sub_val_of_le h.1]; exact h.2.2
  unfold loopM ladAM bondM
  rw [gamma_end s c.1 x hoff, cPlusS_eq]

theorem src_st (ell l : ℕ) (hell : 0 < ell) (U : PeriodicLinkConfiguration SU2 L) (q0 k : ℝ) (hk : 0 ≤ k)
    (hk4 : 4 * k ≤ 1 / (2 * Real.pi)) (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0)
    (hP : ((ell : ℝ) ^ 2) ^ l * q0 ≤ 1)
    (hch : ∀ b, Chart (strT ell U l) (Alog (strT ell U l)) k b) (c : PeriodicLatticeEdge L) :
    frobNorm (blkM (ell ^ l) ell (Alog (strT ell U l)) c - bondM (ell ^ l) ell (Alog (strT ell U l)) c)
      ≤ 3 * ((ell : ℝ) - 1) * (ell : ℝ) *
        (((ell : ℝ) ^ 2) ^ l * q0 + (((ell : ℝ) ^ 2) ^ l * q0) ^ 3 / 8 + 32 * Real.pi * k ^ 2) := by
  set s := ell ^ l with hs
  have hs0 : 0 < s := by positivity
  set P := ((ell : ℝ) ^ 2) ^ l * q0
  set Q := P + P ^ 3 / 8 + 32 * Real.pi * k ^ 2
  have hQ0 : 0 ≤ Q := by
    have hP0 : 0 ≤ P := le_trans (AdalyFormal.CurvBlock.dv_nonneg _) (pw_strT_le ell U q0 h0 l c.1 0 0)
    positivity
  have hcurl : ∀ t : PeriodicLatticeSite L × Fin 3 × Fin 3, frobNorm (curlM s (Alog (strT ell U l)) t.1 t.2.1 t.2.2) ≤ Q :=
    fun t => curlM_le_plaq s (strT ell U l) (Alog (strT ell U l)) k P hk hk4 hP t.1 t.2.1 t.2.2
      (hch _) (hch _) (hch _) (hch _) (pw_strT_le ell U q0 h0 l t.1 t.2.1 t.2.2)
  have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hdiff : blkM s ell (Alog (strT ell U l)) c - bondM s ell (Alog (strT ell U l)) c
      = ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ • loopM s ell (Alog (strT ell U l)) c x := by
    unfold blkM; abel
  rw [hdiff]
  have hterm : ∀ x ∈ stepBlockOf c.1 s ell,
      frobNorm (((ell : ℝ) ^ 3)⁻¹ • loopM s ell (Alog (strT ell U l)) c x)
        ≤ ((ell : ℝ) ^ 3)⁻¹ * (3 * ((ell : ℝ) - 1) * (ell : ℝ) * Q) := by
    intro x hx
    rw [frob_smul, abs_of_nonneg (by positivity), loopM_eq_ladAM s ell _ c x hx]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := ladAM_le s (Alog (strT ell U l)) c.2 ell Q (coarseGammaPath s c.1 x) c.1 (fun t _ => hcurl t)
    have hlen := gammaPath_length_le c.1 x hs0 hx
    have hlenR : ((coarseGammaPath s c.1 x).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
      have h' : ((coarseGammaPath s c.1 x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by exact_mod_cast hlen
      rw [Nat.cast_mul, Nat.cast_sub (by omega)] at h'; simpa using h'
    calc _ ≤ ((coarseGammaPath s c.1 x).length : ℝ) * ((ell : ℝ) * Q) := h1
      _ ≤ 3 * ((ell : ℝ) - 1) * ((ell : ℝ) * Q) := mul_le_mul_of_nonneg_right hlenR (by positivity)
      _ = _ := by ring
  refine (frob_sum _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := card_le_real c.1 (ell := ell) hs0
  have h3 : 0 ≤ 3 * ((ell : ℝ) - 1) * (ell : ℝ) * Q := by
    have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    positivity
  calc ((stepBlockOf c.1 s ell).card : ℝ) * (((ell : ℝ) ^ 3)⁻¹ * (3 * ((ell : ℝ) - 1) * (ell : ℝ) * Q))
      ≤ (ell : ℝ) ^ 3 * (((ell : ℝ) ^ 3)⁻¹ * (3 * ((ell : ℝ) - 1) * (ell : ℝ) * Q)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

#print axioms step_bg
#print axioms step_st
#print axioms loopM_eq_ladAM
#print axioms src_st

end AdalyFormal.RegBgKU
