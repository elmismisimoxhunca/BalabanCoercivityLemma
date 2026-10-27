import TL11d

/-!
# TL11e -- second-order jets: rows at aligned bonds and the level composite `D2CompL`
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp SU2 M2)
open AdalyFormal.IngredientFamilyR2

section d2
variable {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s ell : ℕ}

theorem D2StepL_row_nat (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {V0t : PeriodicLinkConfiguration SU2 Lt} {V0 : PeriodicLinkConfiguration SU2 L} (h0 : AgreeAligned h o s V0t V0)
    {c : PeriodicLatticeEdge Lt} (hc : Aligned (s * ell) c.1) (hC2 : ContDiffAt ℝ 2 (qStepComp s ell V0t c) 0)
    (x y : XS Lt) (a b : XS L) (hxa : ∀ e : PeriodicLatticeEdge Lt, Aligned s e.1 → x e = a (phiE h o e))
    (hyb : ∀ e : PeriodicLatticeEdge Lt, Aligned s e.1 → y e = b (phiE h o e)) :
    D2StepL s ell V0t x y c = D2StepL s ell V0 a b (phiE h o c) := by
  classical
  rw [D2StepL_apply, D2StepL_apply]
  have hP := qStepComp_trunc hp hs hell V0t hc
  have hfun1 : (qStepComp s ell V0t c) ∘ (truncX Lt s) = qStepComp s ell V0t c := by
    funext z; exact (hP z).symm
  have A : ∀ u v : XS Lt, fderiv ℝ (fderiv ℝ (qStepComp s ell V0t c)) 0 u v =
      fderiv ℝ (fderiv ℝ (qStepComp s ell V0t c)) 0 (truncX Lt s u) (truncX Lt s v) := by
    intro u v
    have := fderiv2_comp_clm (qStepComp s ell V0t c) (truncX Lt s) hC2 u v
    rw [hfun1] at this
    exact this
  have ex : truncX Lt s x = truncX Lt s (ellX h o a) := by
    funext e; rw [truncX_apply, truncX_apply]; split_ifs with he
    · exact hxa e he
    · rfl
  have ey : truncX Lt s y = truncX Lt s (ellX h o b) := by
    funext e; rw [truncX_apply, truncX_apply]; split_ifs with he
    · exact hyb e he
    · rfl
  rw [A x y, ex, ey, ← A]
  have hfun2 : qStepComp s ell V0 (phiE h o c) = (qStepComp s ell V0t c) ∘ (ellX h o) := by
    funext a'; exact (qStepComp_ell hp hs hell h0 hc a').symm
  rw [hfun2, fderiv2_comp_clm (qStepComp s ell V0t c) (ellX h o) hC2 a b]

end d2

section comp2
variable {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {ell : ℕ}

theorem D2CompL_nat (hell : 0 < ell) (bgt : ℕ → PeriodicLinkConfiguration SU2 Lt) (bg : ℕ → PeriodicLinkConfiguration SU2 L) :
    ∀ j : ℕ, PhiOK h o (ell ^ j) →
      (∀ l, l < j → AgreeAligned h o (ell ^ l) (bgt l) (bg l)) →
      (∀ l, l < j → ∀ c : PeriodicLatticeEdge Lt, Aligned (ell ^ (l + 1)) c.1 →
        ContDiffAt ℝ 2 (qStepComp (ell ^ l) ell (bgt l) c) 0) →
      ∀ (a b : XS L) (e : PeriodicLatticeEdge Lt), Aligned (ell ^ j) e.1 →
        D2CompL ell bgt j (ellX h o a) (ellX h o b) e = D2CompL ell bg j a b (phiE h o e) := by
  intro j
  induction j with
  | zero => intro _ _ _ a b e _; rfl
  | succ j ih =>
    intro hp hbg hC2 a b e he
    have hpos : 0 < ell ^ j := pow_pos hell j
    have hp' : PhiOK h o (ell ^ j * ell) := by rw [← pow_succ]; exact hp
    have he' : Aligned (ell ^ j * ell) e.1 := by rw [← pow_succ]; exact he
    have hpj : PhiOK h o (ell ^ j) := hp.mono (pow_dvd_pow ell (Nat.le_succ j))
    have hbg' : ∀ l, l < j → AgreeAligned h o (ell ^ l) (bgt l) (bg l) := fun l hl => hbg l (Nat.lt_succ_of_lt hl)
    have hC2' : ∀ l, l < j → ∀ c : PeriodicLatticeEdge Lt, Aligned (ell ^ (l + 1)) c.1 →
        ContDiffAt ℝ 2 (qStepComp (ell ^ l) ell (bgt l) c) 0 := fun l hl => hC2 l (Nat.lt_succ_of_lt hl)
    have ih' := ih hpj hbg' hC2' a b
    have hdiff : ∀ l, l < j → ∀ c : PeriodicLatticeEdge Lt, Aligned (ell ^ (l + 1)) c.1 →
        DifferentiableAt ℝ (qStepComp (ell ^ l) ell (bgt l) c) 0 :=
      fun l hl c hc => (hC2' l hl c hc).differentiableAt (by norm_num)
    have hq := QlinCompL_nat (h := h) (o := o) hell bgt bg j hpj hbg' hdiff
    have hcj : ContDiffAt ℝ 2 (qStepComp (ell ^ j) ell (bgt j) e) 0 := hC2 j (Nat.lt_succ_self j) e (by rw [pow_succ]; exact he')
    simp only [D2CompL, LinearMap.mk₂_apply]
    rw [Pi.add_apply, Pi.add_apply]
    congr 1
    · exact QlinStepL_row_nat hp' hpos hell (hbg j (Nat.lt_succ_self j)) he'
        (hcj.differentiableAt (by norm_num)) _ _ (fun e' he'' => ih' e' he'')
    · exact D2StepL_row_nat hp' hpos hell (hbg j (Nat.lt_succ_self j)) he' hcj _ _ _ _
        (fun e' he'' => hq a e' he'') (fun e' he'' => hq b e' he'')

end comp2

end AdalyFormal.Thin
