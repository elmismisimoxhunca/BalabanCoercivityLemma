import CJ1
import ZR8Jet
import NB30

/-!
# CJ2 -- the ALIGNED read set of a row, and the GENUINE derivatives of the level composite

`ZR8Read.qStepComp_mask` shows that the component `c` of the stride-`s` raw step reads its argument at bonds based in the ball
`(c₋, 4 s ell)`.  When `c₋` is `s`-aligned (and `s ∣ N`) every transport path of the step starts at an `s`-aligned site and moves
by multiples of `s`, so the component reads its argument only at bonds based at `s`-ALIGNED sites of that ball
(`qStepComp_maskA`).  Hence the level-`j` composite row `b` (`b₋` `ell^j`-aligned) is a function of the aligned rows of the
level-`(j-1)` composite only, recursively.

**Main theorem `comp_genuine`** (hypotheses: `0 < ell`, `ell^J ∣ N_ρ` for all `ρ`, `j ≤ J`, `b₋ ∈ CoarseLattice (ell^j)`).
If every aligned row `e` that the level-`j` row `b` reads (at every level `l < j`:
`e₋ ∈ CoarseLattice (ell^(l+1))`, `|b₋ − e₋| ≤ rhoT j − rhoT (l+1)`) has an analytic component `qStepComp (ell^l) ell (bg l) e`,
then `a ↦ qCompX ell bg j a b` (the printed composite (3.13), component `b`) is `C^∞` at `0`, its derivative is row `b` of
`QlinCompL ell bg j` (the r8 jet), and its second derivative is row `b` of `D2CompL ell bg j` (so `C2CompL` row `b` is
`½ D²`).  No junk value can enter row `b`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.ClassJets

open scoped Matrix
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS cPlusS_eq coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)

variable {L : PeriodicLatticeExtent}

/-! ## 1. aligned balls -/

/-- the `s`-aligned sites of the `ℓ¹` ball. -/
def BallA (y : PeriodicLatticeSite L) (r s : ℕ) : Set (PeriodicLatticeSite L) :=
  {z | pdist y z ≤ r ∧ z ∈ CoarseLattice L s}

theorem mem_BallA_self {y : PeriodicLatticeSite L} {s : ℕ} (r : ℕ) (hy : y ∈ CoarseLattice L s) : y ∈ BallA y r s :=
  ⟨by rw [pdist_self]; exact Nat.zero_le _, hy⟩

theorem BallA_sub {y y' : PeriodicLatticeSite L} {d r R s : ℕ} (hd : pdist y y' ≤ d) (hR : d + r ≤ R) :
    BallA y' r s ⊆ BallA y R s :=
  fun z hz => ⟨le_trans (pdist_triangle y y' z) (by have := hz.1; omega), hz.2⟩

theorem BallA_mono {y : PeriodicLatticeSite L} {r R s : ℕ} (h : r ≤ R) : BallA y r s ⊆ BallA y R s :=
  BallA_sub (y' := y) (d := 0) (by rw [pdist_self]) (by omega)

/-- shifting an `s`-aligned site by a multiple of `s` keeps it aligned (`s ∣ N`). -/
theorem coarseShift_mem_CL_of_dvd {s : ℕ} (hd : ∀ ρ : Fin 3, s ∣ L ρ + 1) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L s) (μ : Fin 3) : ∀ m : ℕ, coarseShift y (s * m) μ ∈ CoarseLattice L s := by
  intro m
  induction m with
  | zero => simpa [coarseShift] using hy
  | succ m ih =>
      have e : coarseShift y (s * (m + 1)) μ = coarseShift (coarseShift y (s * m) μ) s μ := by
        rw [Nat.mul_succ, Nat.add_comm, AdalyFormal.CurvBlock.shift_add]
      rw [e]; exact coarseShift_mem_coarseLattice hd ih μ

/-- a strided-block site of an `s`-aligned base is `s`-aligned. -/
theorem block_alignedS (s ell : ℕ) {y x : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L s) (hx : x ∈ stepBlockOf y s ell) : x ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice] at hy ⊢
  intro ν
  have h := (mem_stepBlockOf.mp hx) ν
  have h1 : s ∣ (y ν).val := Nat.dvd_of_mod_eq_zero (hy ν)
  have h2 : s ∣ (x ν).val := by
    have := Nat.dvd_add h1 h.2.2
    rwa [Nat.add_sub_cancel' h.1] at this
  exact Nat.mod_eq_zero_of_dvd h2

theorem cPlusS_aligned {s ell : ℕ} (hd : ∀ ρ : Fin 3, s ∣ L ρ + 1) (c : PeriodicLatticeEdge L)
    (hc : c.1 ∈ CoarseLattice L s) : cPlusS s ell c ∈ CoarseLattice L s := by
  rw [cPlusS_eq]; exact coarseShift_mem_CL_of_dvd hd hc c.2 ell

/-! ## 2. read sets restricted to aligned sites -/

theorem coarsePathHolonomy_congrA {G : Type*} [Group G] (s : ℕ) (hd : ∀ ρ : Fin 3, s ∣ L ρ + 1)
    {V V' : PeriodicLinkConfiguration G L} (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, y ∈ CoarseLattice L s → AgreeAt (BallA y (s * p.length) s) V V' →
      coarsePathHolonomy s V y p = coarsePathHolonomy s V' y p := by
  induction p with
  | nil => intro y _ _; rfl
  | cons μ rest ih =>
      intro y hy h
      show V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) rest
        = V' (y, μ) * coarsePathHolonomy s V' (coarseShift y s μ) rest
      rw [h y (mem_BallA_self _ hy) μ]
      congr 1
      refine ih _ (coarseShift_mem_coarseLattice hd hy μ) (h.mono (BallA_sub (pdist_coarseShift_le y s μ) ?_))
      simp only [List.length_cons]; rw [Nat.mul_succ]; omega

theorem stridedBlockedGauge_congrA {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : AdalyFormal.Balaban.BlockedGauge.LogExpAd G 𝔤) (s ell : ℕ) (hs : 0 < s) (hd : ∀ ρ : Fin 3, s ∣ L ρ + 1)
    {V V' : PeriodicLinkConfiguration G L} (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L s)
    (h : AgreeAt (BallA c.1 (4 * (s * ell)) s) V V') :
    stridedBlockedGauge P s ell V c = stridedBlockedGauge P s ell V' c := by
  have hbond : coarseBondVar s ell V c = coarseBondVar s ell V' c := by
    unfold coarseBondVar
    refine coarsePathHolonomy_congrA s hd _ _ hc (h.mono (BallA_mono ?_))
    simp only [List.length_replicate]; nlinarith
  have hloop : ∀ x ∈ stepBlockOf c.1 s ell, loopVar s ell V c x = loopVar s ell V' c x := by
    intro x hx
    have hlen := length_coarseGammaPath_le hs hx
    have hdx := pdist_stepBlock_le hx
    have hxa := block_alignedS s ell hc hx
    unfold loopVar gammaVarStrided
    rw [hbond]
    congr 2
    · congr 1
      · refine coarsePathHolonomy_congrA s hd _ _ hc (h.mono (BallA_mono ?_))
        have : s * (coarseGammaPath s c.1 x).length ≤ s * (3 * ell) := Nat.mul_le_mul_left _ hlen
        nlinarith
      · refine coarsePathHolonomy_congrA s hd _ _ hxa (h.mono (BallA_sub hdx ?_))
        simp only [List.length_replicate]; nlinarith
    · congr 1
      have hcp := pdist_coarseShift_le c.1 (s * ell) c.2
      rw [← cPlusS_eq] at hcp
      refine coarsePathHolonomy_congrA s hd _ _ (cPlusS_aligned hd c hc) (h.mono (BallA_sub hcp ?_))
      have : s * (coarseGammaPath s c.1 x).length ≤ s * (3 * ell) := Nat.mul_le_mul_left _ hlen
      nlinarith
  have hsum : (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell V c x))
      = ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell V' c x) :=
    Finset.sum_congr rfl (fun x hx => by rw [hloop x hx])
  unfold stridedBlockedGauge
  rw [hbond, hsum]

theorem rProd_congrA (s : ℕ) (hd : ∀ ρ : Fin 3, s ∣ L ρ + 1) {V0 V0' V1 V1' : PeriodicLinkConfiguration SU2 L}
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s) (p : List (Fin 3))
    (h0 : AgreeAt (BallA y (s * p.length) s) V0 V0') (h1 : AgreeAt (BallA y (s * p.length) s) V1 V1') :
    rProd s V0 V1 y p = rProd s V0' V1' y p := by
  rw [rProd_eq, rProd_eq]
  have h01 : AgreeAt (BallA y (s * p.length) s) (fun b => V1 b * V0 b) (fun b => V1' b * V0' b) :=
    fun z hz μ => by simp only [h0 z hz μ, h1 z hz μ]
  rw [coarsePathHolonomy_congrA s hd p y hy h01, coarsePathHolonomy_congrA s hd p y hy h0]

theorem sBlock_congrA (s ell : ℕ) (hs : 0 < s) (hd : ∀ ρ : Fin 3, s ∣ L ρ + 1)
    {V0 V0' V1 V1' : PeriodicLinkConfiguration SU2 L} (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s)
    (h0 : AgreeAt (BallA y (3 * (s * ell)) s) V0 V0') (h1 : AgreeAt (BallA y (3 * (s * ell)) s) V1 V1') :
    sBlock s ell V0 V1 y = sBlock s ell V0' V1' y := by
  unfold sBlock
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hlen := length_coarseGammaPath_le hs hx
  have hb : s * (coarseGammaPath s y x).length ≤ 3 * (s * ell) := by
    have := Nat.mul_le_mul_left s hlen; nlinarith
  rw [rProd_congrA s hd y hy _ (h0.mono (BallA_mono hb)) (h1.mono (BallA_mono hb))]

/-- **the raw one-step map reads `V₀, V₁` only at `s`-aligned sites of the ball `(c₋, 4 s ell)`** (`c₋` aligned). -/
theorem rawStep_congrA (s ell : ℕ) (hs : 0 < s) (hd : ∀ ρ : Fin 3, s ∣ L ρ + 1)
    {V0 V0' V1 V1' : PeriodicLinkConfiguration SU2 L} (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L s)
    (h0 : AgreeAt (BallA c.1 (4 * (s * ell)) s) V0 V0') (h1 : AgreeAt (BallA c.1 (4 * (s * ell)) s) V1 V1') :
    rawStep s ell V0 V1 c = rawStep s ell V0' V1' c := by
  have hcp := pdist_coarseShift_le c.1 (s * ell) c.2
  rw [← cPlusS_eq] at hcp
  have hsub : BallA (cPlusS s ell c) (3 * (s * ell)) s ⊆ BallA c.1 (4 * (s * ell)) s := BallA_sub hcp (by omega)
  have hsub0 : BallA c.1 (3 * (s * ell)) s ⊆ BallA c.1 (4 * (s * ell)) s := BallA_mono (by omega)
  have h01 : AgreeAt (BallA c.1 (4 * (s * ell)) s) (fun b => V1 b * V0 b) (fun b => V1' b * V0' b) :=
    fun z hz μ => by simp only [h0 z hz μ, h1 z hz μ]
  unfold rawStep
  rw [sBlock_congrA s ell hs hd c.1 hc (h0.mono hsub0) (h1.mono hsub0),
    sBlock_congrA s ell hs hd (cPlusS s ell c) (cPlusS_aligned hd c hc) (h0.mono hsub) (h1.mono hsub),
    stridedBlockedGauge_congrA su2LogExp s ell hs hd c hc h01, stridedBlockedGauge_congrA su2LogExp s ell hs hd c hc h0]

/-- **the component `c` reads the coordinate field only at bonds based at `s`-aligned sites of the ball `(c₋, 4 s ell)`.** -/
theorem qStepComp_maskA (s ell : ℕ) (hs : 0 < s) (hd : ∀ ρ : Fin 3, s ∣ L ρ + 1) (V0 : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L s) (a : XS L) :
    qStepComp s ell V0 c a = qStepComp s ell V0 c (maskX (BallA c.1 (4 * (s * ell)) s) a) := by
  show fromM2 (su2Log (rawStep s ell V0 (expCfgX a) c)) = fromM2 (su2Log (rawStep s ell V0 (expCfgX (maskX _ a)) c))
  rw [rawStep_congrA s ell hs hd c hc (V1 := expCfgX a) (V1' := expCfgX (maskX (BallA c.1 (4 * (s * ell)) s) a))
    (fun _ _ _ => rfl) (fun z hz μ => by
    show su2Exp (toM2 (a (z, μ))) = su2Exp (toM2 (maskX (BallA c.1 (4 * (s * ell)) s) a (z, μ)))
    rw [maskX_apply, if_pos hz])]

/-! ## 3. derivatives of maps into `XS L`, componentwise -/

theorem fderiv_apply_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : E → XS L) (x : E)
    (hH : DifferentiableAt ℝ H x) (v : E) (e : PeriodicLatticeEdge L) :
    fderiv ℝ H x v e = fderiv ℝ (fun y => H y e) x v := by
  have h := fderiv_apply (Φ := H) hH e
  rw [h]; rfl

theorem fderiv2_apply_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (H : E → XS L) (x : E)
    (hH : ContDiffAt ℝ 2 H x) (v w : E) (e : PeriodicLatticeEdge L) :
    fderiv ℝ (fderiv ℝ H) x v w e = fderiv ℝ (fderiv ℝ (fun y => H y e)) x v w := by
  have hP : ContDiffAt ℝ 2 (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) e)
      (H x) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) e).contDiff (n := 2)).contDiffAt
  have hc := AdalyFormal.Balaban.SmoothLog.fderiv_fderiv_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) e) H x hP hH v w
  have hcomp : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) e) ∘ H)
      = fun y => H y e := rfl
  rw [hcomp] at hc
  have h2 : fderiv ℝ (fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) e))
      (H x) = 0 := by
    have : fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) e)
        = fun _ => ContinuousLinearMap.proj e := by
      funext y; exact ContinuousLinearMap.fderiv _
    rw [this]; exact fderiv_const_apply _
  rw [h2, ContinuousLinearMap.fderiv] at hc
  simp only [zero_apply, zero_add, ContinuousLinearMap.proj_apply] at hc
  exact hc.symm

open Classical in
/-- the masked composite `a ↦ (e ↦ [e₋ ∈ W] · qCompX j a e)`. -/
noncomputable def maskComp (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) (W : Set (PeriodicLatticeSite L))
    (a : XS L) : XS L :=
  fun e => if e.1 ∈ W then qCompX ell bg j a e else 0

theorem maskComp_eq (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) (W : Set (PeriodicLatticeSite L))
    (a : XS L) : maskComp ell bg j W a = maskX W (qCompX ell bg j a) := by
  funext e; rw [maskX_apply]; rfl

/-! ## 4. the genuine composite -/

/-- the aligned rows read by the level-`j` row `b`, at level `l < j` (rows of the level-`(l+1)` composite). -/
def ReadRow (ell j : ℕ) (b : PeriodicLatticeEdge L) (l : ℕ) (e : PeriodicLatticeEdge L) : Prop :=
  l < j ∧ e.1 ∈ CoarseLattice L (ell ^ (l + 1)) ∧ pdist b.1 e.1 ≤ rhoT ell j - rhoT ell (l + 1)

/-- the conclusion: component `b` of the level-`j` composite is `C^∞` at `0` with first and second derivatives the
r8 local jets. -/
def Genuine (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) (b : PeriodicLatticeEdge L) : Prop :=
  ContDiffAt ℝ ⊤ (fun a : XS L => qCompX ell bg j a b) 0 ∧
  (∀ v : XS L, fderiv ℝ (fun a : XS L => qCompX ell bg j a b) 0 v = QlinCompL ell bg j v b) ∧
  (∀ v w : XS L, fderiv ℝ (fderiv ℝ (fun a : XS L => qCompX ell bg j a b)) 0 v w = D2CompL ell bg j v w b)

theorem rhoT_mono' (ell : ℕ) {l l' : ℕ} (h : l ≤ l') : rhoT ell l ≤ rhoT ell l' := rhoT_mono ell h

/-- **GENUINE COMPOSITE.**  Every aligned row read is analytic ⇒ the level-`j` row `b` of the jets is the genuine
first/second derivative of component `b` of the printed composite. -/
theorem comp_genuine (ell : ℕ) (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hd : ∀ ρ : Fin 3, ell ^ J ∣ L ρ + 1) :
    ∀ j, j ≤ J → ∀ b : PeriodicLatticeEdge L, b.1 ∈ CoarseLattice L (ell ^ j) →
      (∀ l e, ReadRow ell j b l e → ContDiffAt ℝ ⊤ (qStepComp (ell ^ l) ell (bg l) e) 0) →
      Genuine ell bg j b := by
  intro j
  induction j with
  | zero =>
      intro _ b _ _
      have hP := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) b)
      have hf : (fun a : XS L => qCompX ell bg 0 a b)
          = ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) b := rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hf]; exact (ContinuousLinearMap.contDiff _).contDiffAt
      · intro v; rw [hf, ContinuousLinearMap.fderiv]; rfl
      · intro v w
        rw [hf]
        have : fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) b)
            = fun _ => ContinuousLinearMap.proj b := by
          funext y; exact ContinuousLinearMap.fderiv _
        rw [this, fderiv_const_apply]
        show (0 : XS L) b = ((0 : XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L) v w) b
        rfl
  | succ j ih =>
      intro hjJ b hb hread
      set s := ell ^ j with hsdef
      have hs : 0 < s := pow_pos hell j
      have hdj : ∀ ρ : Fin 3, s ∣ L ρ + 1 := fun ρ => Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (hd ρ)
      have hbs : b.1 ∈ CoarseLattice L s := by
        rw [mem_CoarseLattice] at hb ⊢
        intro ν
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (Nat.dvd_of_mod_eq_zero (hb ν)))
      set W := BallA b.1 (4 * (s * ell)) s with hW
      set g := qStepComp s ell (bg j) b with hg
      -- the outer row is analytic
      have hgood : ContDiffAt ℝ ⊤ g 0 := by
        refine hread j b ⟨by omega, hb, ?_⟩
        rw [pdist_self]; exact Nat.zero_le _
      -- inner rows are genuine
      have hinner : ∀ e : PeriodicLatticeEdge L, e.1 ∈ W → Genuine ell bg j e := by
        intro e he
        refine ih (by omega) e he.2 (fun l e' hr => hread l e' ⟨by have := hr.1; omega, hr.2.1, ?_⟩)
        have h1 := pdist_triangle b.1 e.1 e'.1
        have h2 := he.1
        have h3 := hr.2.2
        have h4 : rhoT ell (l + 1) ≤ rhoT ell j := rhoT_mono ell (by have := hr.1; omega)
        rw [rhoT_succ]
        have h5 : s * ell = ell ^ j * ell := rfl
        omega
      -- the masked inner map
      set h := maskComp ell bg j W with hh
      have hgm : ∀ x, g x = g (maskX W x) := fun x => qStepComp_maskA s ell hs hdj (bg j) b hbs x
      have hcomp : (fun a : XS L => qCompX ell bg (j + 1) a b) = g ∘ h := by
        funext a
        show g (qCompX ell bg j a) = g (h a)
        rw [hgm (qCompX ell bg j a), hh, maskComp_eq]
      have hin : ∀ e : PeriodicLatticeEdge L, e.1 ∈ W → (fun a => h a e) = fun a => qCompX ell bg j a e := by
        intro e he; funext a; simp only [hh, maskComp, if_pos he]
      have hout : ∀ e : PeriodicLatticeEdge L, e.1 ∉ W → (fun a => h a e) = fun _ => (0 : Fin 3 → ℝ) := by
        intro e he; funext a; simp only [hh, maskComp, if_neg he]
      have hh0 : h 0 = 0 := by
        rw [hh, maskComp_eq, qCompX_zero]; funext e; rw [maskX_apply]; split_ifs <;> rfl
      have hhC : ContDiffAt ℝ ⊤ h 0 := by
        refine contDiffAt_pi.mpr (fun e => ?_)
        by_cases he : e.1 ∈ W
        · rw [hin e he]; exact (hinner e he).1
        · rw [hout e he]; exact contDiffAt_const
      have hgC : ContDiffAt ℝ ⊤ g (h 0) := by rw [hh0]; exact hgood
      have hgD : DifferentiableAt ℝ g (h 0) := hgC.differentiableAt (by simp)
      have hhD : DifferentiableAt ℝ h 0 := hhC.differentiableAt (by simp)
      -- derivative of the masked inner map
      have hDh : ∀ v, fderiv ℝ h 0 v = maskX W (QlinCompL ell bg j v) := by
        intro v; funext e
        rw [fderiv_apply_comp h 0 hhD v e, maskX_apply]
        by_cases he : e.1 ∈ W
        · rw [if_pos he, hin e he]; exact (hinner e he).2.1 v
        · rw [if_neg he, hout e he, fderiv_const_apply]; rfl
      have hD2h : ∀ v w, fderiv ℝ (fderiv ℝ h) 0 v w = maskX W (D2CompL ell bg j v w) := by
        intro v w; funext e
        rw [fderiv2_apply_comp h 0 (hhC.of_le (by simp)) v w e, maskX_apply]
        by_cases he : e.1 ∈ W
        · rw [if_pos he, hin e he]; exact (hinner e he).2.2 v w
        · rw [if_neg he, hout e he]
          have : fderiv ℝ (fun _ : XS L => (0 : Fin 3 → ℝ)) = fun _ => 0 := by
            funext y; exact fderiv_const_apply _
          rw [this, fderiv_const_apply]; rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hcomp]; exact hgC.comp (0 : XS L) hhC
      · intro v
        rw [hcomp, fderiv_comp (0 : XS L) hgD hhD, ContinuousLinearMap.comp_apply, hDh, hh0]
        rw [← fderiv_mask (maskX W) g hgm (QlinCompL ell bg j v)]
        rfl
      · intro v w
        rw [hcomp, AdalyFormal.Balaban.SmoothLog.fderiv_fderiv_comp g h 0 (hgC.of_le (by simp)) (hhC.of_le (by simp)) v w,
          hDh, hDh, hD2h, hh0]
        rw [← fderiv2_mask (maskX W) (maskX_idem W) g hgm (QlinCompL ell bg j v) (QlinCompL ell bg j w),
          ← fderiv_mask (maskX W) g hgm (D2CompL ell bg j v w)]
        show _ = QlinStepL (ell ^ j) ell (bg j) (D2CompL ell bg j v w) b
            + D2StepL (ell ^ j) ell (bg j) (QlinCompL ell bg j v) (QlinCompL ell bg j w) b
        rw [QlinStepL_apply, D2StepL_apply, add_comm]

/-- the second-order jet row is half the genuine second derivative. -/
theorem C2CompL_genuine (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) (b : PeriodicLatticeEdge L)
    (hG : Genuine ell bg j b) (a : XS L) :
    C2CompL ell bg j a b = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (fun a : XS L => qCompX ell bg j a b)) 0 a a := by
  rw [hG.2.2 a a]; rfl

/-- the first-order jet row is the genuine Fréchet derivative (`HasFDerivAt` form). -/
theorem QlinCompL_hasFDerivAt (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) (b : PeriodicLatticeEdge L)
    (hG : Genuine ell bg j b) :
    HasFDerivAt (fun a : XS L => qCompX ell bg j a b)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) b).comp
        (QlinCompL ell bg j)) 0 := by
  have hD : DifferentiableAt ℝ (fun a : XS L => qCompX ell bg j a b) 0 := hG.1.differentiableAt (by simp)
  have : fderiv ℝ (fun a : XS L => qCompX ell bg j a b) 0
      = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) b).comp
        (QlinCompL ell bg j) := by
    ext1 v; rw [hG.2.1 v]; rfl
  rw [← this]; exact hD.hasFDerivAt

#print axioms qStepComp_maskA
#print axioms fderiv2_apply_comp
#print axioms comp_genuine
#print axioms C2CompL_genuine
#print axioms QlinCompL_hasFDerivAt

end AdalyFormal.ClassJets
