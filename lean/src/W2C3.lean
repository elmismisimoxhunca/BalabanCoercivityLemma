import W2C2

/-!
# W2C3 -- the decoupled form of the real tower dominates the patch form up to the decay defect (M1 lane W2, 2026-10-13)

Setting of W2C2 plus: `K` a set of deep points of `Z` (`Ball x (32 ell^{i+2}) ⊆ Z` for `x ∈ K`), `X ⊆ K`, two configurations
`U₁` (real) and `U₂` (patch) agreeing on every bond based in `Z`, and a bond field `A` whose nonzero bonds have an endpoint in `X`.
* `hD_of`, `hC_of`, `hL_of`, `hN_of`, `hM_of` : the five hypotheses of `G0_cmp` (W2B), each an EXACT locality statement;
* **`G0_real_ge_patch`** : `G0_patch(U₂)(A) − defK_patch(U₂, K)(A) ≤ G0_real(U₁)(A)`;
* `wnorm_real_eq_patch` : the stratum-weighted norms of `A` agree.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1W2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower BlockClosed Admissible bigSide pdist)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt AgreeX mem_Ball_self Ball_sub Ball_mono rhoT rhoT_le rhoT_mono pdist_comm
  pdist_triangle pdist_self pdist_coarseShift_le pdist_shift_le admissible_ball lapFull_zero_of_ball QlinCompL_congr_in
  QlinCompL_congr_U Qcomposite_congr suCoordInv_apply_congr)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply edge_mem)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (curlCovariantLM_L2_toLp)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.M1Patch (patchTower om_le om_succ om_gt sum_BIdx)
open AdalyFormal.M1IMS (G0form Ymass inner_MassFull_eq)

variable {L : PeriodicLatticeExtent}

theorem pdist_shiftBack_le' (x : PeriodicLatticeSite L) (μ : Fin 3) : pdist x (periodicLatticeShiftBack x μ) ≤ 1 :=
  AdalyFormal.StatementLaneR8.pdist_shiftBack_le x μ

/-- every boundary bond of a plaquette is based within distance `1` of its base point. -/
theorem bdry_near (p : PeriodicLatticePlaquette L) (e : PeriodicLatticeEdge L)
    (he : e ∈ periodicPlaquetteBoundaryEdges p) : pdist p.1 e.1 ≤ 1 := by
  rcases (edge_mem p e).mp he with h | h | h | h <;> subst h
  · rw [pdist_self]; omega
  · exact pdist_shift_le _ _
  · exact pdist_shift_le _ _
  · rw [pdist_self]; omega

/-- the row value at level `m`, bond `b`, of the bond `Q` at `U` (depends on the geometry only through `ell`). -/
noncomputable def rvU (ell : ℕ) (U : Cfg L) (A : BondFnL2 L) (m : ℕ) (b : Bond L) : SuTwo :=
  (((ell : ℝ) ^ m)⁻¹) • (WithLp.ofLp (suCoordInv (QlinCompL ell (UbarTower su2LogExp ell U) m (suCoord A)))) b

theorem rvU_zero_of (ell : ℕ) (hell : 0 < ell) (U : Cfg L) (A : BondFnL2 L) (m : ℕ) (b : Bond L)
    (h : ∀ e : Bond L, e.1 ∈ Ball b.1 (rhoT ell m) → (WithLp.ofLp A) e = 0) : rvU ell U A m b = 0 := by
  unfold rvU
  have h1 : QlinCompL ell (UbarTower su2LogExp ell U) m (suCoord A) b
      = QlinCompL ell (UbarTower su2LogExp ell U) m 0 b :=
    QlinCompL_congr_in ell hell _ m b (fun e he => by
      rw [AdalyFormal.DLayer.suCoord_zero_of A e (h e he)]; rfl)
  have h2 : (WithLp.ofLp (suCoordInv (QlinCompL ell (UbarTower su2LogExp ell U) m (suCoord A)))) b
      = (WithLp.ofLp (suCoordInv (0 : AdalyFormal.IngredientFamilyR2.XS L))) b := by
    refine suCoordInv_apply_congr ?_
    rw [h1, map_zero]
  rw [h2, map_zero]
  simp

theorem rvU_congr_U (ell : ℕ) (hell : 0 < ell) (U₁ U₂ : Cfg L) (A : BondFnL2 L) (m : ℕ) (b : Bond L)
    (h : AgreeAt (Ball b.1 (2 * rhoT ell m)) U₁ U₂) : rvU ell U₁ A m b = rvU ell U₂ A m b := by
  unfold rvU
  congr 1
  refine suCoordInv_apply_congr ?_
  exact QlinCompL_congr_U (L := L) ⟨ell, 0, ∅, fun _ => ∅⟩ hell (suCoord A) m b h

open Classical in
/-- the mass square as a level sum of row values. -/
theorem ymass_sq_eq (ell k : ℕ) (S : Tower L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a) (A : BondFnL2 L) :
    ‖Ymass (geomOf ell k S) U a A‖ ^ 2 = ∑ m ∈ Finset.range (k + 1), ∑ b : Bond L,
      if b ∈ bondsLam (geomOf ell k S) m then a * (ell : ℝ) ^ m * ‖rvU ell U A m b‖ ^ 2 else 0 := by
  rw [← inner_MassFull_eq (geomOf ell k S) U a ha A, inner_MassFull]
  have h := sum_BIdx (geomOf ell k S) (fun m b => a * (ell : ℝ) ^ m * ‖rvU ell U A m b‖ ^ 2)
  refine h.trans ?_
  rw [← Fin.sum_univ_eq_sum_range (fun m => ∑ b : Bond L,
      if b ∈ bondsLam (geomOf ell k S) m then a * (ell : ℝ) ^ m * ‖rvU ell U A m b‖ ^ 2 else 0) (k + 1)]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_filter]

section region
variable {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
  {i : ℕ} (hik : i + 1 ≤ k) {Z : Set (PeriodicLatticeSite L)} (hZi : Z ⊆ S.Om i) (hZ2 : ∀ z ∈ Z, z ∉ S.Om (i + 2))
  {K X : Set (PeriodicLatticeSite L)} (hK : ∀ x ∈ K, Ball x (32 * ell ^ (i + 2)) ⊆ Z) (hXK : X ⊆ K)
  (U₁ U₂ : Cfg L) (hU : ∀ e : Bond L, e.1 ∈ Z → U₁ e = U₂ e)
  (A : BondFnL2 L) (hA : ∀ b : Bond L, (WithLp.ofLp A) b ≠ 0 → b.1 ∈ X ∨ periodicLatticeShift b.1 b.2 ∈ X)

include hK in
theorem deep_mem {x : PeriodicLatticeSite L} (hx : x ∈ K) {y : PeriodicLatticeSite L} {r : ℕ} (hr : r ≤ 32 * ell ^ (i + 2))
    (hxy : pdist x y ≤ r) : y ∈ Z := hK x hx (le_trans hxy hr)

include hXK hA in
/-- a nonzero bond of `A` is based within distance `1` of a point of `K`. -/
theorem near_of_ne {b : Bond L} (hb : (WithLp.ofLp A) b ≠ 0) : ∃ x ∈ K, pdist x b.1 ≤ 1 := by
  rcases hA b hb with h | h
  · exact ⟨b.1, hXK h, by rw [pdist_self]; omega⟩
  · refine ⟨_, hXK h, ?_⟩
    rw [pdist_comm]; exact pdist_shift_le _ _

include hell hK hXK hU hA in
theorem hD_of : gradAdj U₁ A = gradAdj U₂ A := by
  have hpos : 0 < ell ^ (i + 2) := pow_pos (by omega) _
  refine gradAdj_congr U₁ U₂ A (fun b hb => hU b ?_)
  obtain ⟨x, hx, hxb⟩ := near_of_ne hXK A hA hb
  exact deep_mem hK hx (show 1 ≤ 32 * ell ^ (i + 2) by omega) hxb

open Classical in
include hS hell hZi hK hXK hU hA in
theorem hC_of :
    plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 U₁ A)
      = plaqMask (plaqIn ((patchTower i (S.Om (i + 1))).Om 0)) (curlCovariantLM_L2 U₂ A) := by
  have hpos : 0 < ell ^ (i + 2) := pow_pos (by omega) _
  refine PiLp.ext (fun p => ?_)
  rw [plaqMask_apply, plaqMask_apply]
  have hA' : A = WithLp.toLp 2 (WithLp.ofLp A) := rfl
  rw [hA', curlCovariantLM_L2_toLp, curlCovariantLM_L2_toLp]
  show (if p ∈ plaqIn (S.Om 0) then curlValueCovariant U₁ (WithLp.ofLp A) p else 0)
    = (if p ∈ plaqIn ((patchTower i (S.Om (i + 1))).Om 0) then curlValueCovariant U₂ (WithLp.ofLp A) p else 0)
  by_cases hex : ∃ e ∈ periodicPlaquetteBoundaryEdges p, (WithLp.ofLp A) e ≠ 0
  · obtain ⟨e, he, hne⟩ := hex
    obtain ⟨x, hx, hxe⟩ := near_of_ne hXK A hA hne
    have hpe := bdry_near p e he
    -- every bond of the plaquette is based within 3 of x, its far end within 4
    have hnear : ∀ e' ∈ periodicPlaquetteBoundaryEdges p, e'.1 ∈ Z ∧ periodicLatticeShift e'.1 e'.2 ∈ Z := by
      intro e' he'
      have h1 := bdry_near p e' he'
      have d1 : pdist x e'.1 ≤ 3 := by
        have t1 := pdist_triangle x e.1 p.1
        have t2 := pdist_triangle x p.1 e'.1
        rw [pdist_comm e.1 p.1] at t1
        omega
      have d2 : pdist x (periodicLatticeShift e'.1 e'.2) ≤ 4 := by
        have := pdist_triangle x e'.1 (periodicLatticeShift e'.1 e'.2)
        have := pdist_shift_le e'.1 e'.2
        omega
      exact ⟨deep_mem hK hx (show 3 ≤ 32 * ell ^ (i + 2) by omega) d1,
        deep_mem hK hx (show 4 ≤ 32 * ell ^ (i + 2) by omega) d2⟩
    have hP1 : p ∈ plaqIn (S.Om 0) := fun e' he' =>
      ⟨AdalyFormal.M1.om_anti hS (Nat.zero_le i) (hZi (hnear e' he').1),
       AdalyFormal.M1.om_anti hS (Nat.zero_le i) (hZi (hnear e' he').2)⟩
    have hP2 : p ∈ plaqIn ((patchTower i (S.Om (i + 1))).Om 0) := by
      rw [om_le i _ (Nat.zero_le i)]
      exact fun e' _ => ⟨Set.mem_univ _, Set.mem_univ _⟩
    rw [if_pos hP1, if_pos hP2]
    exact curl_congr_U U₁ U₂ _ p (fun e' he' => hU e' (hnear e' he').1)
  · push Not at hex
    rw [curl_zero_of U₁ _ p hex, curl_zero_of U₂ _ p hex]
    split_ifs <;> rfl

theorem siteMask_eq_self_of (Sset : Set (PeriodicLatticeSite L)) (f : SiteL2 L) (h : ∀ x, x ∉ Sset → f x = 0) :
    siteMask Sset f = f := by
  classical
  refine PiLp.ext (fun x => ?_)
  show (siteMask Sset f) x = f x
  rw [siteMask_apply]
  split_ifs with hx
  · rfl
  · exact (h x hx).symm

include hS hell hZi hK hU in
theorem hL_of (f : SiteL2 L) (hf : f ∈ NK (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) U₂ K) :
    lapDir (geomOf ell k S) U₁ f = lapDir (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) U₂ f := by
  classical
  have hpos : 0 < ell ^ (i + 2) := pow_pos (by omega) _
  have hfK : ∀ x, x ∉ K → f x = 0 := (Submodule.mem_inf.mp hf).2
  have hKZ : ∀ x ∈ K, x ∈ S.Om 0 := fun x hx =>
    AdalyFormal.M1.om_anti hS (Nat.zero_le i) (hZi (deep_mem hK hx (Nat.zero_le _) (by rw [pdist_self])))
  have hm1 : siteMask (S.Om 0) f = f := siteMask_eq_self_of _ f (fun x hx => hfK x (fun hk => hx (hKZ x hk)))
  have hu2 : ∀ g : SiteL2 L, siteMask ((patchTower i (S.Om (i + 1))).Om 0) g = g := fun g =>
    siteMask_eq_self_of _ g (fun x hx => absurd (by rw [om_le i _ (Nat.zero_le i)]; trivial) hx)
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  show siteMask (S.Om 0) (lapFull U₁ (siteMask (S.Om 0) f))
    = siteMask ((patchTower i (S.Om (i + 1))).Om 0) (lapFull U₂ (siteMask ((patchTower i (S.Om (i + 1))).Om 0) f))
  rw [hm1, hu2, hu2]
  refine PiLp.ext (fun x => ?_)
  show (siteMask (S.Om 0) (lapFull U₁ f)) x = (lapFull U₂ f) x
  rw [siteMask_apply]
  by_cases hx : ∃ z ∈ K, pdist z x ≤ 1
  · obtain ⟨z, hz, hzx⟩ := hx
    have hxZ : x ∈ Z := deep_mem hK hz (show 1 ≤ 32 * ell ^ (i + 2) by omega) hzx
    rw [if_pos (AdalyFormal.M1.om_anti hS (Nat.zero_le i) (hZi hxZ))]
    refine lapFull_congr_at U₁ U₂ f x (fun μ => hU (x, μ) hxZ) (fun μ => hU _ ?_)
    show periodicLatticeShiftBack x μ ∈ Z
    have := pdist_triangle z x (periodicLatticeShiftBack x μ)
    have := pdist_shiftBack_le' x μ
    exact deep_mem hK hz (show 2 ≤ 32 * ell ^ (i + 2) by omega) (by omega)
  · push Not at hx
    have h0 : ∀ y ∈ Ball x 1, f y = 0 := fun y hy => hfK y (fun hyK => by
      have := hx y hyK
      have hy' : pdist x y ≤ 1 := hy
      rw [pdist_comm] at hy'
      omega)
    rw [lapFull_zero_of_ball U₁ f x h0, lapFull_zero_of_ball U₂ f x h0]
    split_ifs <;> rfl

include hS hell hroom hik hZi hZ2 hK hU in
theorem hN_of (f : SiteL2 L) (hf : f ∈ NK (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) U₂ K) :
    f ∈ NQp (geomOf ell k S) U₁ := by
  have hpos : 0 < ell ^ (i + 2) := pow_pos (by omega) _
  have hell0 : 0 < ell := by omega
  have hfN : f ∈ NQp (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) U₂ := (Submodule.mem_inf.mp hf).1
  have hfK : ∀ x, x ∉ K → f x = 0 := (Submodule.mem_inf.mp hf).2
  refine ⟨fun x hx => ?_, fun m hm y hy => ?_⟩
  · by_contra hfx
    have hxK : x ∈ K := by
      by_contra h; exact hfx (hfK x h)
    exact hx (AdalyFormal.M1.om_anti hS (Nat.zero_le i) (hZi (deep_mem hK hxK (Nat.zero_le _) (by rw [pdist_self]))))
  · rw [Qlev_apply]
    by_cases hz : ∃ z ∈ Ball y (rhoT ell m), f z ≠ 0
    · obtain ⟨z, hzy, hfz⟩ := hz
      have hzK : z ∈ K := by by_contra h; exact hfz (hfK z h)
      have hrho := rhoT_le ell hell m
      have hzy' : pdist z y ≤ 9 * ell ^ m := by
        have : pdist y z ≤ rhoT ell m := hzy
        rw [pdist_comm]; omega
      have hlev := lam_near hS hell hroom hZi hZ2 z (hK z hzK) m hm y hy hzy'
      have hmi : m ≤ i + 1 := by omega
      have hpm : ell ^ m ≤ ell ^ (i + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have hyZ : y ∈ Z := deep_mem hK hzK (show 9 * ell ^ m ≤ 32 * ell ^ (i + 2) by omega) hzy'
      have hy2 : y ∈ (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))).Lam m :=
        (lam_agree hS hZi hZ2 y hyZ m).mp hy
      have h0 := hfN.2 m hmi y hy2
      rw [Qlev_apply] at h0
      have hag : AgreeAt (Ball y (2 * rhoT ell m)) U₁ U₂ := by
        intro w hw μ
        refine hU (w, μ) (show w ∈ Z from deep_mem hK hzK (show 9 * ell ^ m + 2 * rhoT ell m ≤ 32 * ell ^ (i + 2) by omega) ?_)
        have := pdist_triangle z y w
        have hw' : pdist y w ≤ 2 * rhoT ell m := hw
        omega
      have hc := Qcomposite_congr (geomOf ell k S) hell0 (WithLp.ofLp f) m y hag
      exact hc.trans h0
    · push Not at hz
      exact Qcomposite_zero_of _ ell hell0 m y _ hz

theorem rvU_near (ell : ℕ) (hell : 0 < ell) (U : Cfg L) (A : BondFnL2 L) (m : ℕ) (b : Bond L)
    (hr : rvU ell U A m b ≠ 0) : ∃ e : Bond L, e.1 ∈ Ball b.1 (rhoT ell m) ∧ (WithLp.ofLp A) e ≠ 0 := by
  by_contra h
  push Not at h
  exact hr (rvU_zero_of ell hell U A m b h)

include hXK hA in
theorem row_near (ell : ℕ) (hell : 0 < ell) (U : Cfg L) (m : ℕ) (b : Bond L) (hr : rvU ell U A m b ≠ 0) :
    ∃ x ∈ K, pdist x b.1 ≤ 1 + rhoT ell m := by
  obtain ⟨e, he, hne⟩ := rvU_near ell hell U A m b hr
  obtain ⟨x, hx, hxe⟩ := near_of_ne hXK A hA hne
  refine ⟨x, hx, ?_⟩
  have := pdist_triangle x e.1 b.1
  have he' : pdist b.1 e.1 ≤ rhoT ell m := he
  rw [pdist_comm b.1 e.1] at he'
  omega

open Classical in
include hS hell hroom hik hZi hZ2 hK hXK hU hA in
theorem hM_of (a : ℝ) (ha : 0 ≤ a) :
    ‖Ymass (geomOf ell k S) U₁ a A‖ = ‖Ymass (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) U₂ a A‖ := by
  have hell0 : 0 < ell := by omega
  have hpos : 0 < ell ^ (i + 2) := pow_pos (by omega) _
  have hsq : ‖Ymass (geomOf ell k S) U₁ a A‖ ^ 2
      = ‖Ymass (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) U₂ a A‖ ^ 2 := by
    rw [ymass_sq_eq ell k S U₁ a ha A, ymass_sq_eq ell (i + 1) _ U₂ a ha A]
    rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 + 1 ≤ k + 1 by omega)]
    have hhigh : ∑ m ∈ Finset.Ico (i + 1 + 1) (k + 1), ∑ b : Bond L,
        (if b ∈ bondsLam (geomOf ell k S) m then a * (ell : ℝ) ^ m * ‖rvU ell U₁ A m b‖ ^ 2 else 0) = 0 := by
      refine Finset.sum_eq_zero (fun m hm => Finset.sum_eq_zero (fun b _ => ?_))
      rw [Finset.mem_Ico] at hm
      by_cases hr : rvU ell U₁ A m b = 0
      · rw [hr, norm_zero]; simp
      · rw [if_neg]
        intro hb
        obtain ⟨x, hx, hxb⟩ := row_near hXK A hA ell hell0 U₁ m b hr
        have hrho := rhoT_le ell hell m
        rcases hb.1 with hy | hy
        · have := lam_near hS hell hroom hZi hZ2 x (hK x hx) m (by omega) b.1 hy (by omega)
          omega
        · have hy' : coarseShift b.1 (ell ^ m) b.2 ∈ (geomOf ell k S).Lam m := hy
          have hc := pdist_coarseShift_le b.1 (ell ^ m) b.2
          have := pdist_triangle x b.1 (coarseShift b.1 (ell ^ m) b.2)
          have := lam_near hS hell hroom hZi hZ2 x (hK x hx) m (by omega) _ hy' (by omega)
          omega
    rw [hhigh, add_zero]
    refine Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Finset.mem_range] at hm
    by_cases h0 : rvU ell U₁ A m b = 0 ∧ rvU ell U₂ A m b = 0
    · rw [h0.1, h0.2, norm_zero]; simp
    · have hnz : ∃ U, rvU ell U A m b ≠ 0 := by
        by_contra hn; push Not at hn; exact h0 ⟨hn U₁, hn U₂⟩
      obtain ⟨U, hU0⟩ := hnz
      obtain ⟨x, hx, hxb⟩ := row_near hXK A hA ell hell0 U m b hU0
      have hrho := rhoT_le ell hell m
      have hpm : ell ^ m ≤ ell ^ (i + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h1 : b.1 ∈ Z := deep_mem hK hx (show 1 + rhoT ell m ≤ 32 * ell ^ (i + 2) by omega) hxb
      have h2 : coarseShift b.1 (ell ^ m) b.2 ∈ Z := by
        have hc := pdist_coarseShift_le b.1 (ell ^ m) b.2
        have := pdist_triangle x b.1 (coarseShift b.1 (ell ^ m) b.2)
        exact deep_mem hK hx (show 1 + rhoT ell m + ell ^ m ≤ 32 * ell ^ (i + 2) by omega) (by omega)
      have hiff := bondsLam_agree hS hell hik hZi hZ2 m b h1 h2
      have hag : AgreeAt (Ball b.1 (2 * rhoT ell m)) U₁ U₂ := by
        intro w hw μ
        refine hU (w, μ) (show w ∈ Z from deep_mem hK hx (show 1 + rhoT ell m + 2 * rhoT ell m ≤ 32 * ell ^ (i + 2) by omega) ?_)
        have := pdist_triangle x b.1 w
        have hw' : pdist b.1 w ≤ 2 * rhoT ell m := hw
        omega
      rw [rvU_congr_U ell hell0 U₁ U₂ A m b hag]
      by_cases hb : b ∈ bondsLam (geomOf ell k S) m
      · rw [if_pos hb, if_pos (hiff.mp hb)]
      · rw [if_neg hb, if_neg (fun h => hb (hiff.mpr h))]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

include hS hell hroom hik hZi hZ2 hK hXK hU hA in
/-- **the real decoupled form dominates the patch form, up to the patch decay defect.** -/
theorem G0_real_ge_patch (a : ℝ) (ha : 0 ≤ a) :
    G0form (patchTower i (S.Om (i + 1))) ell (i + 1) U₂ a A
        - defK (geomOf ell (i + 1) (patchTower i (S.Om (i + 1)))) U₂ K A
      ≤ G0form S ell k U₁ a A :=
  G0_cmp (ell := ell) S (patchTower i (S.Om (i + 1))) U₁ U₂ a K A
    (hC_of hS hell hZi hK hXK U₁ U₂ hU A hA)
    (hM_of hS hell hroom hik hZi hZ2 hK hXK U₁ U₂ hU A hA a ha)
    (fun f hf => hN_of hS hell hroom hik hZi hZ2 hK U₁ U₂ hU f hf)
    (fun f hf => hL_of hS hell hZi hK U₁ U₂ hU f hf)
    (hD_of hell hK hXK U₁ U₂ hU A hA)

include hS hell hik hZi hZ2 hK hXK hA in
theorem wnorm_real_eq_patch :
    AdalyFormal.M1.wnormSq S ell k A = AdalyFormal.M1.wnormSq (patchTower i (S.Om (i + 1))) ell (i + 1) A := by
  have hpos : 0 < ell ^ (i + 2) := pow_pos (by omega) _
  refine wnorm_agree hS hik hZi hZ2 A (fun b hb => ?_)
  obtain ⟨x, hx, hxb⟩ := near_of_ne hXK A hA hb
  refine ⟨deep_mem hK hx (show 1 ≤ 32 * ell ^ (i + 2) by omega) hxb, ?_⟩
  have := pdist_triangle x b.1 (periodicLatticeShift b.1 b.2)
  have := pdist_shift_le b.1 b.2
  exact deep_mem hK hx (show 2 ≤ 32 * ell ^ (i + 2) by omega) (by omega)

end region

end AdalyFormal.M1W2

#print axioms AdalyFormal.M1W2.bdry_near
#print axioms AdalyFormal.M1W2.rvU
#print axioms AdalyFormal.M1W2.rvU_zero_of
#print axioms AdalyFormal.M1W2.rvU_congr_U
#print axioms AdalyFormal.M1W2.ymass_sq_eq
#print axioms AdalyFormal.M1W2.deep_mem
#print axioms AdalyFormal.M1W2.near_of_ne
#print axioms AdalyFormal.M1W2.hD_of
#print axioms AdalyFormal.M1W2.hC_of
#print axioms AdalyFormal.M1W2.siteMask_eq_self_of
#print axioms AdalyFormal.M1W2.hL_of
#print axioms AdalyFormal.M1W2.hN_of
#print axioms AdalyFormal.M1W2.rvU_near
#print axioms AdalyFormal.M1W2.row_near
#print axioms AdalyFormal.M1W2.hM_of
#print axioms AdalyFormal.M1W2.G0_real_ge_patch
#print axioms AdalyFormal.M1W2.wnorm_real_eq_patch
#print axioms AdalyFormal.M1W2.pdist_shiftBack_le'
