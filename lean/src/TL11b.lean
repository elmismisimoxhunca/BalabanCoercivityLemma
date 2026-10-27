import TL11a
import ZLocJet

/-!
# TL11b -- first-order jets of the one-step averaging: rows at aligned bonds
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp SU2 M2)
open AdalyFormal.IngredientFamilyR2

section jets
variable {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s ell : ℕ}

theorem phiS_refl_zero (x : PeriodicLatticeSite Lt) : phiS (Covers.refl Lt) (fun _ => 0) x = x := by
  funext μ; apply Fin.ext; simp [phiS_val, Nat.mod_eq_of_lt (x μ).isLt]

theorem phiE_refl_zero (e : PeriodicLatticeEdge Lt) : phiE (Covers.refl Lt) (fun _ => 0) e = e := by
  simp [phiE, phiS_refl_zero]

/-- pullback of coordinate fields along `phiE` -/
noncomputable def ellX (h : Covers Lt L) (o : Fin 3 → ℕ) : XS L →L[ℝ] XS Lt :=
  LinearMap.toContinuousLinearMap (LinearMap.funLeft ℝ (Fin 3 → ℝ) (phiE h o))

theorem ellX_apply (a : XS L) (e : PeriodicLatticeEdge Lt) : ellX h o a e = a (phiE h o e) := rfl

open Classical in
/-- truncation to the `s`-aligned bonds -/
noncomputable def truncX (Lx : PeriodicLatticeExtent) (s : ℕ) : XS Lx →L[ℝ] XS Lx :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x e => if Aligned s e.1 then x e else 0
      map_add' := fun x y => by funext e; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by funext e; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }

open Classical in
theorem truncX_apply (Lx : PeriodicLatticeExtent) (s : ℕ) (x : XS Lx) (e : PeriodicLatticeEdge Lx) :
    truncX Lx s x e = if Aligned s e.1 then x e else 0 := rfl

theorem phiOK_refl_zero (hp : PhiOK h o (s * ell)) : PhiOK (Covers.refl Lt) (fun _ => 0) (s * ell) :=
  ⟨fun μ => (hp.side μ).trans (h μ), fun μ => dvd_zero _⟩

theorem qStepComp_trunc (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell) (V0t : PeriodicLinkConfiguration SU2 Lt)
    {c : PeriodicLatticeEdge Lt} (hc : Aligned (s * ell) c.1) (x : XS Lt) :
    qStepComp s ell V0t c x = qStepComp s ell V0t c (truncX Lt s x) := by
  classical
  have h0 : AgreeAligned (Covers.refl Lt) (fun _ => 0) s V0t V0t := by
    intro e _; rw [phiE_refl_zero]
  have := qStepX_nat (phiOK_refl_zero hp) hs hell h0 x (truncX Lt s x) (c := c) (fun e he => by
    rw [phiE_refl_zero, truncX_apply, if_pos he]) hc
  rw [phiE_refl_zero] at this
  exact this

theorem qStepComp_ell (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {V0t : PeriodicLinkConfiguration SU2 Lt} {V0 : PeriodicLinkConfiguration SU2 L} (h0 : AgreeAligned h o s V0t V0)
    {c : PeriodicLatticeEdge Lt} (hc : Aligned (s * ell) c.1) (a : XS L) :
    qStepComp s ell V0t c (ellX h o a) = qStepComp s ell V0 (phiE h o c) a :=
  qStepX_nat hp hs hell h0 (ellX h o a) a (fun e _ => rfl) hc

theorem fderiv_comp_trunc {Lx : PeriodicLatticeExtent} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : XS Lx → F) (s : ℕ) (hf : DifferentiableAt ℝ f 0) (hP : ∀ x, f x = f (truncX Lx s x)) :
    fderiv ℝ f 0 = (fderiv ℝ f 0).comp (truncX Lx s) := by
  have h1 : HasFDerivAt f (fderiv ℝ f 0) ((truncX Lx s) 0) := by rw [map_zero]; exact hf.hasFDerivAt
  have h2 := h1.comp (0 : XS Lx) (truncX Lx s).hasFDerivAt
  have h3 : (f ∘ truncX Lx s) = f := by funext x; exact (hP x).symm
  rw [h3] at h2
  exact h2.fderiv

theorem QlinStepL_row_nat (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {V0t : PeriodicLinkConfiguration SU2 Lt} {V0 : PeriodicLinkConfiguration SU2 L} (h0 : AgreeAligned h o s V0t V0)
    {c : PeriodicLatticeEdge Lt} (hc : Aligned (s * ell) c.1) (hdiff : DifferentiableAt ℝ (qStepComp s ell V0t c) 0)
    (x : XS Lt) (a : XS L) (hxa : ∀ e : PeriodicLatticeEdge Lt, Aligned s e.1 → x e = a (phiE h o e)) :
    QlinStepL s ell V0t x c = QlinStepL s ell V0 a (phiE h o c) := by
  classical
  rw [QlinStepL_apply, QlinStepL_apply]
  have hP := qStepComp_trunc hp hs hell V0t hc
  have hd1 := fderiv_comp_trunc _ s hdiff hP
  have e1 : truncX Lt s x = truncX Lt s (ellX h o a) := by
    funext e
    rw [truncX_apply, truncX_apply]
    split_ifs with he
    · exact hxa e he
    · rfl
  have step1 : fderiv ℝ (qStepComp s ell V0t c) 0 x = fderiv ℝ (qStepComp s ell V0t c) 0 (ellX h o a) := by
    conv_lhs => rw [hd1]
    conv_rhs => rw [hd1]
    simp only [ContinuousLinearMap.comp_apply, e1]
  rw [step1]
  -- chain rule through `ellX`
  have hfun : qStepComp s ell V0 (phiE h o c) = (qStepComp s ell V0t c) ∘ (ellX h o) := by
    funext a'; exact (qStepComp_ell hp hs hell h0 hc a').symm
  have h1 : HasFDerivAt (qStepComp s ell V0t c) (fderiv ℝ (qStepComp s ell V0t c) 0) ((ellX h o) 0) := by
    rw [map_zero]; exact hdiff.hasFDerivAt
  have h2 := h1.comp (0 : XS L) (ellX h o).hasFDerivAt
  rw [← hfun] at h2
  rw [h2.fderiv]
  rfl

end jets


end AdalyFormal.Thin
