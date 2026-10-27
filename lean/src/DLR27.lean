import DLR26

/-!
# DL27 -- locality of the raw one-step averaging: path congruence → `rawStep` → `qStepX`

* `OnPath s y p e` : the edge `e` is visited by the stride-`s` coarse path `p` from `y` (the factors `W(y_i, μ_i)` of
  `coarsePathHolonomy`).  `hol_congr` : the holonomy depends only on the visited edges.
* `VisStep s ell c e` : the edges read by the raw one-step map at the coarse bond `c` (the staircases `Γ_{c₋,x}` of `S₋`,
  `Γ_{c₊,x}` of `S₊`, the loop factors `V(Γ_{c,x})` and the bond `V(c)` of the strided blocking, CMP98 (63)/(89)).
* **`rawStep_congr`** : `rawStep s ell V0 V1 c` depends on `V1` only through `V1|_{VisStep c}`;
  **`qStepX_congr`** : `qStepX s ell V0 a c` depends on `a` only through `a|_{VisStep c}`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 su2Exp su2Log su2LogExp)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-- `e` is a factor of the stride-`s` coarse path `p` from `y` -/
def OnPath (s : ℕ) : PeriodicLatticeSite L → List (Fin 3) → PeriodicLatticeEdge L → Prop
  | _, [], _ => False
  | y, μ :: rest, e => e = (y, μ) ∨ OnPath s (coarseShift y s μ) rest e

theorem hol_congr {G : Type*} [Group G] (s : ℕ) (W W' : PeriodicLinkConfiguration G L) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), (∀ e, OnPath s y p e → W e = W' e) →
      coarsePathHolonomy s W y p = coarsePathHolonomy s W' y p := by
  intro p
  induction p with
  | nil => intro y _; rfl
  | cons μ rest ih =>
      intro y h
      show W (y, μ) * coarsePathHolonomy s W (coarseShift y s μ) rest
        = W' (y, μ) * coarsePathHolonomy s W' (coarseShift y s μ) rest
      rw [h (y, μ) (Or.inl rfl), ih (coarseShift y s μ) (fun e he => h e (Or.inr he))]

/-- the edges read by the raw one-step map at `c` -/
def VisStep (s ell : ℕ) (c : PeriodicLatticeEdge L) (e : PeriodicLatticeEdge L) : Prop :=
  (∃ x ∈ stepBlockOf c.1 s ell, OnPath s c.1 (coarseGammaPath s c.1 x) e)
  ∨ (∃ x ∈ stepBlockOf (cPlusS s ell c) s ell, OnPath s (cPlusS s ell c) (coarseGammaPath s (cPlusS s ell c) x) e)
  ∨ (∃ x ∈ stepBlockOf c.1 s ell, OnPath s x (List.replicate ell c.2) e)
  ∨ (∃ x ∈ stepBlockOf c.1 s ell, OnPath s (cPlusS s ell c) (coarseGammaPath s c.1 x) e)
  ∨ OnPath s c.1 (List.replicate ell c.2) e

theorem sBlock_congr (s ell : ℕ) (V0 V1 V1' : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    (h : ∀ x ∈ stepBlockOf y s ell, ∀ e, OnPath s y (coarseGammaPath s y x) e → V1 e = V1' e) :
    sBlock s ell V0 V1 y = sBlock s ell V0 V1' y := by
  unfold sBlock
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [rProd_eq, rProd_eq, hol_congr s (fun b => V1 b * V0 b) (fun b => V1' b * V0 b) _ y
    (fun e he => by simp only [h x hx e he])]

theorem loopVar_congr {G : Type*} [Group G] (s ell : ℕ) (W W' : PeriodicLinkConfiguration G L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (h1 : ∀ e, OnPath s c.1 (coarseGammaPath s c.1 x) e → W e = W' e)
    (h3 : ∀ e, OnPath s x (List.replicate ell c.2) e → W e = W' e)
    (h4 : ∀ e, OnPath s (cPlusS s ell c) (coarseGammaPath s c.1 x) e → W e = W' e)
    (h5 : ∀ e, OnPath s c.1 (List.replicate ell c.2) e → W e = W' e) :
    loopVar s ell W c x = loopVar s ell W' c x := by
  have hb : coarseBondVar s ell W c = coarseBondVar s ell W' c := hol_congr s W W' _ c.1 h5
  have hg : gammaVarStrided s ell W c x = gammaVarStrided s ell W' c x := by
    show coarsePathHolonomy s W c.1 (coarseGammaPath s c.1 x) * coarsePathHolonomy s W x (List.replicate ell c.2)
        * (coarsePathHolonomy s W (cPlusS s ell c) (coarseGammaPath s c.1 x))⁻¹
      = coarsePathHolonomy s W' c.1 (coarseGammaPath s c.1 x) * coarsePathHolonomy s W' x (List.replicate ell c.2)
        * (coarsePathHolonomy s W' (cPlusS s ell c) (coarseGammaPath s c.1 x))⁻¹
    rw [hol_congr s W W' _ c.1 h1, hol_congr s W W' _ x h3, hol_congr s W W' _ (cPlusS s ell c) h4]
  show gammaVarStrided s ell W c x * (coarseBondVar s ell W c)⁻¹
    = gammaVarStrided s ell W' c x * (coarseBondVar s ell W' c)⁻¹
  rw [hg, hb]

theorem sbg_eq_of {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : AdalyFormal.Balaban.BlockedGauge.LogExpAd G 𝔤) (s ell : ℕ)
    (W W' : PeriodicLinkConfiguration G L) (c : PeriodicLatticeEdge L)
    (hl : ∀ x ∈ stepBlockOf c.1 s ell, loopVar s ell W c x = loopVar s ell W' c x)
    (hb : coarseBondVar s ell W c = coarseBondVar s ell W' c) :
    stridedBlockedGauge P s ell W c = stridedBlockedGauge P s ell W' c := by
  have hs : (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell W c x))
      = ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell W' c x) :=
    Finset.sum_congr rfl (fun x hx => by rw [hl x hx])
  show P.exp (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell W c x)) * coarseBondVar s ell W c
    = P.exp (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell W' c x)) * coarseBondVar s ell W' c
  rw [hs, hb]

/-- **the raw one-step map is local** -/
theorem rawStep_congr (s ell : ℕ) (V0 V1 V1' : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L)
    (h : ∀ e, VisStep s ell c e → V1 e = V1' e) :
    rawStep s ell V0 V1 c = rawStep s ell V0 V1' c := by
  have hm : sBlock s ell V0 V1 c.1 = sBlock s ell V0 V1' c.1 :=
    sBlock_congr s ell V0 V1 V1' c.1 (fun x hx e he => h e (Or.inl ⟨x, hx, he⟩))
  have hp : sBlock s ell V0 V1 (cPlusS s ell c) = sBlock s ell V0 V1' (cPlusS s ell c) :=
    sBlock_congr s ell V0 V1 V1' (cPlusS s ell c) (fun x hx e he => h e (Or.inr (Or.inl ⟨x, hx, he⟩)))
  have hW : ∀ e, VisStep s ell c e → (fun b => V1 b * V0 b) e = (fun b => V1' b * V0 b) e := by
    intro e he
    show V1 e * V0 e = V1' e * V0 e
    rw [h e he]
  have hl : ∀ x ∈ stepBlockOf c.1 s ell, loopVar s ell (fun b => V1 b * V0 b) c x
      = loopVar s ell (fun b => V1' b * V0 b) c x := fun x hx =>
    loopVar_congr s ell _ _ c x
      (fun e he => hW e (Or.inl ⟨x, hx, he⟩))
      (fun e he => hW e (Or.inr (Or.inr (Or.inl ⟨x, hx, he⟩))))
      (fun e he => hW e (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hx, he⟩)))))
      (fun e he => hW e (Or.inr (Or.inr (Or.inr (Or.inr he)))))
  have hb : coarseBondVar s ell (fun b => V1 b * V0 b) c = coarseBondVar s ell (fun b => V1' b * V0 b) c :=
    hol_congr s _ _ _ c.1 (fun e he => hW e (Or.inr (Or.inr (Or.inr (Or.inr he)))))
  have hg := sbg_eq_of su2LogExp s ell _ _ c hl hb
  rw [rawStep_simp, rawStep_simp, hm, hp, hg]

/-- **the coordinate one-step map is local** -/
theorem qStepX_congr (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (a a' : XS L) (c : PeriodicLatticeEdge L)
    (h : ∀ e, VisStep s ell c e → a e = a' e) :
    qStepX s ell V0 a c = qStepX s ell V0 a' c := by
  have hr := rawStep_congr s ell V0 (expCfgX a) (expCfgX a') c (fun e he => by
    show su2Exp (toM2 (a e)) = su2Exp (toM2 (a' e))
    rw [h e he])
  show fromM2 (su2Log (rawStep s ell V0 (expCfgX a) c)) = fromM2 (su2Log (rawStep s ell V0 (expCfgX a') c))
  rw [hr]

#print axioms hol_congr
#print axioms sBlock_congr
#print axioms loopVar_congr
#print axioms sbg_eq_of
#print axioms rawStep_congr
#print axioms qStepX_congr

end AdalyFormal.DLayer
