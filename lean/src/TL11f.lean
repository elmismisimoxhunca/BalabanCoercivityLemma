import TL11e
import CJ2

/-!
# TL11f -- READ-RESTRICTED naturality of the jets.

The class supplies regularity of the averaging components only at the rows READ by a bond-sector row
(`ClassJets.ReadRow`, CJ4) -- at the UR point a class configuration has an unread non-differentiable aligned row (CJ6).
Locality of a component (`qStepComp_maskA`: it reads the coordinate field only on the ball `BallA c.1 (4 s ell) s`) lets the
naturality induction use regularity only on `ReadRow`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist)
open AdalyFormal.StatementLaneR8 (maskX maskX_apply rhoT rhoT_succ rhoT_mono pdist_triangle pdist_self)
open AdalyFormal.ClassJets (ReadRow BallA qStepComp_maskA)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp SU2 M2)
open AdalyFormal.IngredientFamilyR2

section rowT
variable {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s ell : ℕ}

theorem fderiv_comp_T {Lx : PeriodicLatticeExtent} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : XS Lx → F) (T : XS Lx →L[ℝ] XS Lx) (hf : DifferentiableAt ℝ f 0) (hP : ∀ x, f x = f (T x)) :
    fderiv ℝ f 0 = (fderiv ℝ f 0).comp T := by
  have h1 : HasFDerivAt f (fderiv ℝ f 0) (T 0) := by rw [map_zero]; exact hf.hasFDerivAt
  have h2 := h1.comp (0 : XS Lx) T.hasFDerivAt
  have h3 : (f ∘ T) = f := by funext x; exact (hP x).symm
  rw [h3] at h2
  exact h2.fderiv

theorem QlinStepL_row_natT (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {V0t : PeriodicLinkConfiguration SU2 Lt} {V0 : PeriodicLinkConfiguration SU2 L} (h0 : AgreeAligned h o s V0t V0)
    {c : PeriodicLatticeEdge Lt} (hc : Aligned (s * ell) c.1) (hdiff : DifferentiableAt ℝ (qStepComp s ell V0t c) 0)
    (T : XS Lt →L[ℝ] XS Lt) (hT : ∀ z, qStepComp s ell V0t c z = qStepComp s ell V0t c (T z))
    (x : XS Lt) (a : XS L) (hxa : T x = T (ellX h o a)) :
    QlinStepL s ell V0t x c = QlinStepL s ell V0 a (phiE h o c) := by
  classical
  rw [QlinStepL_apply, QlinStepL_apply]
  have hd1 := fderiv_comp_T _ T hdiff hT
  have step1 : fderiv ℝ (qStepComp s ell V0t c) 0 x = fderiv ℝ (qStepComp s ell V0t c) 0 (ellX h o a) := by
    conv_lhs => rw [hd1]
    conv_rhs => rw [hd1]
    simp only [ContinuousLinearMap.comp_apply, hxa]
  rw [step1]
  have hfun : qStepComp s ell V0 (phiE h o c) = (qStepComp s ell V0t c) ∘ (ellX h o) := by
    funext a'; exact (qStepComp_ell hp hs hell h0 hc a').symm
  have h1 : HasFDerivAt (qStepComp s ell V0t c) (fderiv ℝ (qStepComp s ell V0t c) 0) ((ellX h o) 0) := by
    rw [map_zero]; exact hdiff.hasFDerivAt
  have h2 := h1.comp (0 : XS L) (ellX h o).hasFDerivAt
  rw [← hfun] at h2
  rw [h2.fderiv]
  rfl

theorem D2StepL_row_natT (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {V0t : PeriodicLinkConfiguration SU2 Lt} {V0 : PeriodicLinkConfiguration SU2 L} (h0 : AgreeAligned h o s V0t V0)
    {c : PeriodicLatticeEdge Lt} (hc : Aligned (s * ell) c.1) (hC2 : ContDiffAt ℝ 2 (qStepComp s ell V0t c) 0)
    (T : XS Lt →L[ℝ] XS Lt) (hT : ∀ z, qStepComp s ell V0t c z = qStepComp s ell V0t c (T z))
    (x y : XS Lt) (a b : XS L) (hxa : T x = T (ellX h o a)) (hyb : T y = T (ellX h o b)) :
    D2StepL s ell V0t x y c = D2StepL s ell V0 a b (phiE h o c) := by
  classical
  rw [D2StepL_apply, D2StepL_apply]
  have hfun1 : (qStepComp s ell V0t c) ∘ T = qStepComp s ell V0t c := by
    funext z; exact (hT z).symm
  have A : ∀ u v : XS Lt, fderiv ℝ (fderiv ℝ (qStepComp s ell V0t c)) 0 u v =
      fderiv ℝ (fderiv ℝ (qStepComp s ell V0t c)) 0 (T u) (T v) := by
    intro u v
    have := fderiv2_comp_clm (qStepComp s ell V0t c) T hC2 u v
    rw [hfun1] at this
    exact this
  rw [A x y, hxa, hyb, ← A]
  have hfun2 : qStepComp s ell V0 (phiE h o c) = (qStepComp s ell V0t c) ∘ (ellX h o) := by
    funext a'; exact (qStepComp_ell hp hs hell h0 hc a').symm
  rw [hfun2, fderiv2_comp_clm (qStepComp s ell V0t c) (ellX h o) hC2 a b]

theorem aligned_of_mem_coarse {L' : PeriodicLatticeExtent} {s : ℕ} {x : PeriodicLatticeSite L'}
    (hx : x ∈ CoarseLattice L' s) : Aligned s x :=
  fun μ => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hx μ)

theorem mem_coarse_of_aligned {L' : PeriodicLatticeExtent} {s : ℕ} {x : PeriodicLatticeSite L'}
    (hx : Aligned s x) : x ∈ CoarseLattice L' s :=
  mem_CoarseLattice.mpr (fun μ => Nat.mod_eq_zero_of_dvd (hx μ))

/-- read rows of a row inside the ball of an inner row are read rows of the outer row -/
theorem readRow_mono {ell j : ℕ} {e e' : PeriodicLatticeEdge Lt} (hee : pdist e.1 e'.1 ≤ 4 * (ell ^ j * ell))
    {l : ℕ} {e'' : PeriodicLatticeEdge Lt} (hr : ReadRow ell j e' l e'') : ReadRow ell (j + 1) e l e'' := by
  obtain ⟨hl, ha, hd⟩ := hr
  refine ⟨by omega, ha, ?_⟩
  have h1 := pdist_triangle e.1 e'.1 e''.1
  have h4 : rhoT ell (l + 1) ≤ rhoT ell j := rhoT_mono ell (by omega)
  rw [rhoT_succ]
  omega

theorem QlinCompL_natR (hell : 0 < ell) (bgt : ℕ → PeriodicLinkConfiguration SU2 Lt) (bg : ℕ → PeriodicLinkConfiguration SU2 L) :
    ∀ j : ℕ, PhiOK h o (ell ^ j) →
      (∀ l, l < j → AgreeAligned h o (ell ^ l) (bgt l) (bg l)) →
      ∀ (e : PeriodicLatticeEdge Lt), Aligned (ell ^ j) e.1 →
      (∀ l e', ReadRow ell j e l e' → DifferentiableAt ℝ (qStepComp (ell ^ l) ell (bgt l) e') 0) →
      ∀ (a : XS L), QlinCompL ell bgt j (ellX h o a) e = QlinCompL ell bg j a (phiE h o e) := by
  intro j
  induction j with
  | zero => intro _ _ e _ _ a; rfl
  | succ j ih =>
    intro hp hbg e he hread a
    have hpos : 0 < ell ^ j := pow_pos hell j
    have hp' : PhiOK h o (ell ^ j * ell) := by rw [← pow_succ]; exact hp
    have he' : Aligned (ell ^ j * ell) e.1 := by rw [← pow_succ]; exact he
    have hpj : PhiOK h o (ell ^ j) := hp.mono (pow_dvd_pow ell (Nat.le_succ j))
    have hbg' : ∀ l, l < j → AgreeAligned h o (ell ^ l) (bgt l) (bg l) := fun l hl => hbg l (Nat.lt_succ_of_lt hl)
    have hs_al : Aligned (ell ^ j) e.1 := fun μ => (Dvd.intro _ rfl).trans (he' μ)
    have hdd : ∀ ρ : Fin 3, ell ^ j ∣ Lt ρ + 1 := fun ρ => (hpj.side ρ).trans (h ρ)
    have hdiff_e : DifferentiableAt ℝ (qStepComp (ell ^ j) ell (bgt j) e) 0 :=
      hread j e ⟨by omega, mem_coarse_of_aligned he, by rw [pdist_self]; exact Nat.zero_le _⟩
    rw [QlinCompL_succ, QlinCompL_succ]
    simp only [ContinuousLinearMap.comp_apply]
    refine QlinStepL_row_natT hp' hpos hell (hbg j (Nat.lt_succ_self j)) he' hdiff_e
      (maskX (BallA e.1 (4 * (ell ^ j * ell)) (ell ^ j)))
      (fun z => qStepComp_maskA (ell ^ j) ell hpos hdd (bgt j) e (mem_coarse_of_aligned hs_al) z) _ _ ?_
    funext e'
    rw [maskX_apply, maskX_apply]
    split_ifs with hW
    · have hal' : Aligned (ell ^ j) e'.1 := aligned_of_mem_coarse hW.2
      have hr' : ∀ l e'', ReadRow ell j e' l e'' → DifferentiableAt ℝ (qStepComp (ell ^ l) ell (bgt l) e'') 0 :=
        fun l e'' hr => hread l e'' (readRow_mono hW.1 hr)
      exact ih hpj hbg' e' hal' hr' a
    · rfl

theorem D2CompL_natR (hell : 0 < ell) (bgt : ℕ → PeriodicLinkConfiguration SU2 Lt) (bg : ℕ → PeriodicLinkConfiguration SU2 L) :
    ∀ j : ℕ, PhiOK h o (ell ^ j) →
      (∀ l, l < j → AgreeAligned h o (ell ^ l) (bgt l) (bg l)) →
      ∀ (e : PeriodicLatticeEdge Lt), Aligned (ell ^ j) e.1 →
      (∀ l e', ReadRow ell j e l e' → ContDiffAt ℝ 2 (qStepComp (ell ^ l) ell (bgt l) e') 0) →
      ∀ (a b : XS L), D2CompL ell bgt j (ellX h o a) (ellX h o b) e = D2CompL ell bg j a b (phiE h o e) := by
  intro j
  induction j with
  | zero => intro _ _ e _ _ a b; rfl
  | succ j ih =>
    intro hp hbg e he hread a b
    have hpos : 0 < ell ^ j := pow_pos hell j
    have hp' : PhiOK h o (ell ^ j * ell) := by rw [← pow_succ]; exact hp
    have he' : Aligned (ell ^ j * ell) e.1 := by rw [← pow_succ]; exact he
    have hpj : PhiOK h o (ell ^ j) := hp.mono (pow_dvd_pow ell (Nat.le_succ j))
    have hbg' : ∀ l, l < j → AgreeAligned h o (ell ^ l) (bgt l) (bg l) := fun l hl => hbg l (Nat.lt_succ_of_lt hl)
    have hs_al : Aligned (ell ^ j) e.1 := fun μ => (Dvd.intro _ rfl).trans (he' μ)
    have hdd : ∀ ρ : Fin 3, ell ^ j ∣ Lt ρ + 1 := fun ρ => (hpj.side ρ).trans (h ρ)
    have hC2e : ContDiffAt ℝ 2 (qStepComp (ell ^ j) ell (bgt j) e) 0 :=
      hread j e ⟨by omega, mem_coarse_of_aligned he, by rw [pdist_self]; exact Nat.zero_le _⟩
    have hT := fun z => qStepComp_maskA (ell ^ j) ell hpos hdd (bgt j) e (mem_coarse_of_aligned hs_al) z
    have hr' : ∀ e' : PeriodicLatticeEdge Lt, e'.1 ∈ BallA e.1 (4 * (ell ^ j * ell)) (ell ^ j) →
        ∀ l e'', ReadRow ell j e' l e'' → ContDiffAt ℝ 2 (qStepComp (ell ^ l) ell (bgt l) e'') 0 :=
      fun e' hW l e'' hr => hread l e'' (readRow_mono hW.1 hr)
    simp only [D2CompL, LinearMap.mk₂_apply]
    rw [Pi.add_apply, Pi.add_apply]
    congr 1
    · refine QlinStepL_row_natT hp' hpos hell (hbg j (Nat.lt_succ_self j)) he' (hC2e.differentiableAt (by norm_num))
        (maskX (BallA e.1 (4 * (ell ^ j * ell)) (ell ^ j))) hT _ _ ?_
      funext e'
      rw [maskX_apply, maskX_apply]
      split_ifs with hW
      · exact ih hpj hbg' e' (aligned_of_mem_coarse hW.2) (hr' e' hW) a b
      · rfl
    · refine D2StepL_row_natT hp' hpos hell (hbg j (Nat.lt_succ_self j)) he' hC2e
        (maskX (BallA e.1 (4 * (ell ^ j * ell)) (ell ^ j))) hT _ _ _ _ ?_ ?_
      · funext e'
        rw [maskX_apply, maskX_apply]
        split_ifs with hW
        · exact QlinCompL_natR hell bgt bg j hpj hbg' e' (aligned_of_mem_coarse hW.2)
            (fun l e'' hr => (hr' e' hW l e'' hr).differentiableAt (by norm_num)) a
        · rfl
      · funext e'
        rw [maskX_apply, maskX_apply]
        split_ifs with hW
        · exact QlinCompL_natR hell bgt bg j hpj hbg' e' (aligned_of_mem_coarse hW.2)
            (fun l e'' hr => (hr' e' hW l e'' hr).differentiableAt (by norm_num)) b
        · rfl

end rowT

end AdalyFormal.Thin
