import ZR8Geo
import ZR8Mask
import ZLocJet
import R2Ops1

/-!
# ZR8Read -- r8 locality, read sets of the derivative-free objects

Every object below is a finite product/sum over transport paths of stride `s`; each reads its configuration only at bonds based in
an explicit `ℓ¹` ball:
 * `coarsePathHolonomy s V y p`            : ball `(y, s·|p|)`;
 * `stridedBlockedGauge P s ell V c` (CMP98 (43) at stride `s`) : ball `(c₋, 4 s ell)`;
 * the background tower `Ū^l` (`UbarTower`, `bgTower`) at `(y, μ)` : ball `(y, rhoT ell l)`, `rhoT ell l = Σ_{i<l} 4 ell^{i+1}`;
 * the raw one-step map `rawStep s ell V₀ V₁ c` (CMP98 (63)/(89)) : ball `(c₋, 4 s ell)` in BOTH `V₀` and `V₁`;
 * hence the component `a ↦ qStepX s ell V₀ a c`: in `V₀` and in `a`, ball `(c₋, 4 s ell)`;
 * `stepAverage s V ell λ y` (the factor of `Q'_j`, (3.19)) : ball `(y, 3 s ell)` in `V` and `λ`;
 * `Q'_j = Qcomposite (bgTower U) ell j` at `y` : `U` in ball `(y, 2·rhoT ell j)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.StatementLaneR8

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage Qcomposite)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS cPlusS_eq coarseBondVar gammaVarStrided loopVar UbarTower)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)

variable {L : PeriodicLatticeExtent}

/-! ## 1. holonomy -/

theorem coarsePathHolonomy_congr {G : Type*} [Group G] (s : ℕ) {V V' : PeriodicLinkConfiguration G L}
    (p : List (Fin 3)) : ∀ (y : PeriodicLatticeSite L), AgreeAt (Ball y (s * p.length)) V V' →
      coarsePathHolonomy s V y p = coarsePathHolonomy s V' y p := by
  induction p with
  | nil => intro y _; rfl
  | cons μ rest ih =>
      intro y h
      show V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) rest
        = V' (y, μ) * coarsePathHolonomy s V' (coarseShift y s μ) rest
      rw [h y (mem_Ball_self _ _) μ]
      congr 1
      refine ih _ (h.mono (Ball_sub (pdist_coarseShift_le y s μ) ?_))
      simp only [List.length_cons]; rw [Nat.mul_succ]; omega

/-! ## 2. the strided blocking `Ū` (CMP98 (43)) -/

theorem stridedBlockedGauge_congr {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : AdalyFormal.Balaban.BlockedGauge.LogExpAd G 𝔤) (s ell : ℕ) (hs : 0 < s)
    {V V' : PeriodicLinkConfiguration G L} (c : PeriodicLatticeEdge L)
    (h : AgreeAt (Ball c.1 (4 * (s * ell))) V V') :
    stridedBlockedGauge P s ell V c = stridedBlockedGauge P s ell V' c := by
  have hbond : coarseBondVar s ell V c = coarseBondVar s ell V' c := by
    unfold coarseBondVar
    refine coarsePathHolonomy_congr s _ _ (h.mono (Ball_mono ?_))
    simp only [List.length_replicate]; nlinarith
  have hloop : ∀ x ∈ stepBlockOf c.1 s ell, loopVar s ell V c x = loopVar s ell V' c x := by
    intro x hx
    have hlen := length_coarseGammaPath_le hs hx
    have hdx := pdist_stepBlock_le hx
    unfold loopVar gammaVarStrided
    rw [hbond]
    congr 2
    · congr 1
      · refine coarsePathHolonomy_congr s _ _ (h.mono (Ball_mono ?_))
        have : s * (coarseGammaPath s c.1 x).length ≤ s * (3 * ell) := Nat.mul_le_mul_left _ hlen
        nlinarith
      · refine coarsePathHolonomy_congr s _ _ (h.mono (Ball_sub hdx ?_))
        simp only [List.length_replicate]; nlinarith
    · congr 1
      have hc := pdist_coarseShift_le c.1 (s * ell) c.2
      rw [← cPlusS_eq] at hc
      refine coarsePathHolonomy_congr s _ _ (h.mono (Ball_sub hc ?_))
      have : s * (coarseGammaPath s c.1 x).length ≤ s * (3 * ell) := Nat.mul_le_mul_left _ hlen
      nlinarith
  have hsum : (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell V c x))
      = ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell V' c x) :=
    Finset.sum_congr rfl (fun x hx => by rw [hloop x hx])
  unfold stridedBlockedGauge
  rw [hbond, hsum]

/-- the radius of the background tower. -/
def rhoT (ell : ℕ) : ℕ → ℕ
  | 0 => 0
  | l + 1 => rhoT ell l + 4 * (ell ^ l * ell)

theorem rhoT_succ (ell l : ℕ) : rhoT ell (l + 1) = rhoT ell l + 4 * (ell ^ l * ell) := rfl

theorem rhoT_le (ell : ℕ) (hell : 2 ≤ ell) (l : ℕ) : rhoT ell l + 8 ≤ 8 * ell ^ l := by
  induction l with
  | zero => simp [rhoT]
  | succ l ih =>
      rw [rhoT_succ, pow_succ]
      have : 8 * ell ^ l ≤ 4 * (ell ^ l * ell) := by nlinarith [pow_pos (show 0 < ell by omega) l]
      nlinarith

theorem rhoT_mono (ell : ℕ) {l l' : ℕ} (h : l ≤ l') : rhoT ell l ≤ rhoT ell l' := by
  induction l' with
  | zero => have : l = 0 := by omega
            subst this; exact le_rfl
  | succ l' ih =>
      rcases Nat.eq_or_lt_of_le h with e | e
      · rw [e]
      · rw [rhoT_succ]; have := ih (by omega); omega

/-- **the background tower reads `U` only in the ball of radius `rhoT ell l`.** -/
theorem UbarTower_congr {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : AdalyFormal.Balaban.BlockedGauge.LogExpAd G 𝔤) (ell : ℕ) (hell : 0 < ell)
    {U U' : PeriodicLinkConfiguration G L} (l : ℕ) :
    ∀ y : PeriodicLatticeSite L, AgreeAt (Ball y (rhoT ell l)) U U' →
      ∀ μ, UbarTower P ell U l (y, μ) = UbarTower P ell U' l (y, μ) := by
  induction l with
  | zero => intro y h μ; exact h y (mem_Ball_self _ _) μ
  | succ l ih =>
      intro y h μ
      show stridedBlockedGauge P (ell ^ l) ell (UbarTower P ell U l) (y, μ)
        = stridedBlockedGauge P (ell ^ l) ell (UbarTower P ell U' l) (y, μ)
      refine stridedBlockedGauge_congr P _ ell (pow_pos hell l) _ ?_
      intro z hz ν
      refine ih z (h.mono (Ball_sub hz ?_)) ν
      rw [rhoT_succ]; omega

theorem bgTower_congr (G : TowerGeom L) (hell : 0 < G.ell) {U U' : Cfg L} (l : ℕ) (y : PeriodicLatticeSite L)
    (h : AgreeAt (Ball y (rhoT G.ell l)) U U') (μ : Fin 3) :
    bgTower G U l (y, μ) = bgTower G U' l (y, μ) :=
  UbarTower_congr su2LogExp G.ell hell l y h μ

/-- the tower agrees at every bond based in a ball, if `U` agrees in the enlarged ball. -/
theorem bgTower_agreeAt (G : TowerGeom L) (hell : 0 < G.ell) {U U' : Cfg L} (l : ℕ) (y : PeriodicLatticeSite L) (r : ℕ)
    (h : AgreeAt (Ball y (r + rhoT G.ell l)) U U') :
    AgreeAt (Ball y r) (bgTower G U l) (bgTower G U' l) :=
  fun z hz μ => bgTower_congr G hell l z (h.mono (Ball_sub hz le_rfl)) μ

/-! ## 3. the raw one-step map and its components -/

theorem rProd_congr (s : ℕ) {V0 V0' V1 V1' : PeriodicLinkConfiguration SU2 L} (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) (h0 : AgreeAt (Ball y (s * p.length)) V0 V0') (h1 : AgreeAt (Ball y (s * p.length)) V1 V1') :
    rProd s V0 V1 y p = rProd s V0' V1' y p := by
  rw [rProd_eq, rProd_eq]
  have h01 : AgreeAt (Ball y (s * p.length)) (fun b => V1 b * V0 b) (fun b => V1' b * V0' b) :=
    fun z hz μ => by simp only [h0 z hz μ, h1 z hz μ]
  rw [coarsePathHolonomy_congr s p y h01, coarsePathHolonomy_congr s p y h0]

theorem sBlock_congr (s ell : ℕ) (hs : 0 < s) {V0 V0' V1 V1' : PeriodicLinkConfiguration SU2 L} (y : PeriodicLatticeSite L)
    (h0 : AgreeAt (Ball y (3 * (s * ell))) V0 V0') (h1 : AgreeAt (Ball y (3 * (s * ell))) V1 V1') :
    sBlock s ell V0 V1 y = sBlock s ell V0' V1' y := by
  unfold sBlock
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hlen := length_coarseGammaPath_le hs hx
  have hb : s * (coarseGammaPath s y x).length ≤ 3 * (s * ell) := by
    have := Nat.mul_le_mul_left s hlen; nlinarith
  rw [rProd_congr s y _ (h0.mono (Ball_mono hb)) (h1.mono (Ball_mono hb))]

/-- **the raw one-step map reads `V₀, V₁` only in the ball `(c₋, 4 s ell)`.** -/
theorem rawStep_congr (s ell : ℕ) (hs : 0 < s) {V0 V0' V1 V1' : PeriodicLinkConfiguration SU2 L} (c : PeriodicLatticeEdge L)
    (h0 : AgreeAt (Ball c.1 (4 * (s * ell))) V0 V0') (h1 : AgreeAt (Ball c.1 (4 * (s * ell))) V1 V1') :
    rawStep s ell V0 V1 c = rawStep s ell V0' V1' c := by
  have hc := pdist_coarseShift_le c.1 (s * ell) c.2
  rw [← cPlusS_eq] at hc
  have hsub : Ball (cPlusS s ell c) (3 * (s * ell)) ⊆ Ball c.1 (4 * (s * ell)) := Ball_sub hc (by omega)
  have hsub0 : Ball c.1 (3 * (s * ell)) ⊆ Ball c.1 (4 * (s * ell)) := Ball_mono (by omega)
  have h01 : AgreeAt (Ball c.1 (4 * (s * ell))) (fun b => V1 b * V0 b) (fun b => V1' b * V0' b) :=
    fun z hz μ => by simp only [h0 z hz μ, h1 z hz μ]
  unfold rawStep
  rw [sBlock_congr s ell hs c.1 (h0.mono hsub0) (h1.mono hsub0),
    sBlock_congr s ell hs (cPlusS s ell c) (h0.mono hsub) (h1.mono hsub),
    stridedBlockedGauge_congr su2LogExp s ell hs c h01, stridedBlockedGauge_congr su2LogExp s ell hs c h0]

open Classical in
/-- bonds based in a set of sites, as a mask on coordinate fields. -/
noncomputable def maskX (W : Set (PeriodicLatticeSite L)) : XS L →L[ℝ] XS L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a e => if e.1 ∈ W then a e else 0
      map_add' := fun a b => by funext e; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun r a => by funext e; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }

open Classical in
theorem maskX_apply (W : Set (PeriodicLatticeSite L)) (a : XS L) (e : PeriodicLatticeEdge L) :
    maskX W a e = if e.1 ∈ W then a e else 0 := rfl

theorem maskX_idem (W : Set (PeriodicLatticeSite L)) (a : XS L) : maskX W (maskX W a) = maskX W a := by
  funext e; rw [maskX_apply, maskX_apply]; split_ifs <;> simp

theorem maskX_eq_of_agree (W : Set (PeriodicLatticeSite L)) {a a' : XS L} (h : ∀ e : PeriodicLatticeEdge L, e.1 ∈ W → a e = a' e) :
    maskX W a = maskX W a' := by
  funext e; rw [maskX_apply, maskX_apply]; split_ifs with he
  · exact h e he
  · rfl

/-- **component `c` of the raw map reads the background only in the ball `(c₋, 4 s ell)`** (as a function of `a`). -/
theorem qStepComp_congr_bg (s ell : ℕ) (hs : 0 < s) {V0 V0' : PeriodicLinkConfiguration SU2 L} (c : PeriodicLatticeEdge L)
    (h : AgreeAt (Ball c.1 (4 * (s * ell))) V0 V0') : qStepComp s ell V0 c = qStepComp s ell V0' c := by
  funext a
  show fromM2 (su2Log (rawStep s ell V0 (expCfgX a) c)) = fromM2 (su2Log (rawStep s ell V0' (expCfgX a) c))
  rw [rawStep_congr s ell hs c h (fun _ _ _ => rfl)]

/-- **component `c` of the raw map reads the coordinate field only at bonds based in the ball `(c₋, 4 s ell)`.** -/
theorem qStepComp_mask (s ell : ℕ) (hs : 0 < s) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) (a : XS L) :
    qStepComp s ell V0 c a = qStepComp s ell V0 c (maskX (Ball c.1 (4 * (s * ell))) a) := by
  show fromM2 (su2Log (rawStep s ell V0 (expCfgX a) c)) = fromM2 (su2Log (rawStep s ell V0 (expCfgX (maskX _ a)) c))
  rw [rawStep_congr s ell hs c (V1 := expCfgX a) (V1' := expCfgX (maskX (Ball c.1 (4 * (s * ell))) a))
    (fun _ _ _ => rfl) (fun z hz μ => by
    show su2Exp (toM2 (a (z, μ))) = su2Exp (toM2 (maskX (Ball c.1 (4 * (s * ell))) a (z, μ)))
    rw [maskX_apply, if_pos hz])]

/-! ## 4. the site averaging `Q'_j` -/

theorem stepAverage_congr (s ell : ℕ) (hs : 0 < s) {V V' : PeriodicLinkConfiguration SU2 L}
    {lam lam' : PeriodicLatticeSite L → SuTwo} (y : PeriodicLatticeSite L)
    (hV : AgreeAt (Ball y (3 * (s * ell))) V V') (hl : ∀ x ∈ Ball y (3 * (s * ell)), lam x = lam' x) :
    stepAverage s V ell lam y = stepAverage s V' ell lam' y := by
  unfold stepAverage
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hlen := length_coarseGammaPath_le hs hx
  have hb : s * (coarseGammaPath s y x).length ≤ 3 * (s * ell) := by
    have := Nat.mul_le_mul_left s hlen; nlinarith
  rw [coarsePathHolonomy_congr s _ y (hV.mono (Ball_mono hb)), hl x (pdist_stepBlock_le hx)]

/-- **`Q'_j(U)` at `y` reads `U` only in the ball `(y, 2 rhoT ell j)`.** -/
theorem Qcomposite_congr (G : TowerGeom L) (hell : 0 < G.ell) {U U' : Cfg L} (lam : PeriodicLatticeSite L → SuTwo) (j : ℕ) :
    ∀ y : PeriodicLatticeSite L, AgreeAt (Ball y (2 * rhoT G.ell j)) U U' →
      Qcomposite (bgTower G U) G.ell j lam y = Qcomposite (bgTower G U') G.ell j lam y := by
  induction j with
  | zero => intro y _; rfl
  | succ j ih =>
      intro y h
      show stepAverage (G.ell ^ j) (bgTower G U j) G.ell (Qcomposite (bgTower G U) G.ell j lam) y
        = stepAverage (G.ell ^ j) (bgTower G U' j) G.ell (Qcomposite (bgTower G U') G.ell j lam) y
      refine stepAverage_congr _ _ (pow_pos hell j) y ?_ ?_
      · refine bgTower_agreeAt G hell j y _ (h.mono (Ball_mono ?_))
        rw [rhoT_succ]; generalize G.ell ^ j * G.ell = X; generalize rhoT G.ell j = r; omega
      · intro x hx
        refine ih x (h.mono (Ball_sub hx ?_))
        rw [rhoT_succ]; omega

#print axioms coarsePathHolonomy_congr
#print axioms stridedBlockedGauge_congr
#print axioms rhoT_le
#print axioms UbarTower_congr
#print axioms bgTower_agreeAt
#print axioms rawStep_congr
#print axioms qStepComp_congr_bg
#print axioms qStepComp_mask
#print axioms stepAverage_congr
#print axioms Qcomposite_congr

end AdalyFormal.StatementLaneR8
