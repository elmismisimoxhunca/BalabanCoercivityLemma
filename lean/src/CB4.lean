import CB3
/-!
# CB4 -- one blocking step of the defect `D = Ū · T⁻¹`

For level-`l` configurations `V` (genuine) and `T` (straight) at stride `s`, with
`dv (V b · (T b)⁻¹) ≤ d` on the bonds read and `dv (pw s T ·) ≤ q` on the enclosed plaquettes:

  `dv (ubarSU2 s ell V c · (coarseBondVar s ell T c)⁻¹) ≤ ell·d + (π/2)·((8 ell − 6)·d + 3(ell−1)·ell·q)`.

Ingredients (all tree lemmas except CB1/CB2): `Ū_c = exp(H)·V(c)` (`ubarSU2_eq_blockedLink`),
`‖exp H − 1‖ ≤ ‖H‖` (`frobNorm_su2Exp_sub_one_le_uncond`), `‖H‖ ≤ max ‖log W_x‖` (weights sum `≤ 1`,
`frobNorm_blockExponent_le'`, `weight_sum_le_one`), `‖log g‖ ≤ (π/2)‖g − 1‖` (CMP98 (25),
`frobNorm_su2Log_le_pi_div_two`), `|Γ| ≤ 3(ell−1)` (`gammaPath_length_le`); the block loop of `V`
equals (D-conjugates)·(block loop of `T`) (`four_cmp`), and the block loop of `T` is a strided ladder
(`loopVar_eq_ladS`, bounded by curvature via `ladS_le`).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf coarsePathEndpoint_coarseGammaPath)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_eq_blockedLink)
open AdalyFormal.Balaban.BlockingLinkEstimate (blockExponent frobNorm_su2Log_le_pi_div_two)
open AdalyFormal.Balaban.ClassPropagationUbar (blockExponent_antiHerm blockExponent_trace
  frobNorm_blockExponent_le' frobNorm_su2Exp_sub_one_le_uncond weight_sum_le_one gammaPath_length_le)

variable {L : PeriodicLatticeExtent}

/-- The block loop is a strided ladder over the staircase. -/
theorem loopVar_eq_ladS (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell) :
    loopVar s ell V c x = ladS s V c.1 (coarseGammaPath s c.1 x) c.2 ell := by
  have hmem := mem_stepBlockOf.mp hx
  have hend : coarsePathEndpoint s c.1 (coarseGammaPath s c.1 x) = x :=
    coarsePathEndpoint_coarseGammaPath (fun μ => ⟨(hmem μ).1, (hmem μ).2.2⟩)
  have hplus : cPlusS s ell c = coarseShift c.1 (s * ell) c.2 := cPlusS_eq s ell c
  unfold ladS
  rw [hend, ← hplus]
  rfl

/-- Bonds read by the block loop at `x`. -/
def loopBonds (s ell : ℕ) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    List (PeriodicLatticeEdge L) :=
  pathBonds s c.1 (coarseGammaPath s c.1 x) ++ pathBonds s x (List.replicate ell c.2)
    ++ pathBonds s (cPlusS s ell c) (coarseGammaPath s c.1 x)
    ++ pathBonds s c.1 (List.replicate ell c.2)

/-- **Block-loop comparison.** -/
theorem loop_cmp (s ell : ℕ) (hs : 0 < s) (V T : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell)
    (d q : ℝ) (hd0 : 0 ≤ d)
    (hd : ∀ b ∈ loopBonds s ell c x, dv (V b * (T b)⁻¹) ≤ d)
    (hq : ∀ t ∈ ladPlaqs s c.2 ell c.1 (coarseGammaPath s c.1 x),
      dv (pw s T t.1 t.2.1 t.2.2) ≤ q) (hq0 : 0 ≤ q) :
    dv (loopVar s ell V c x)
      ≤ (8 * (ell : ℝ) - 6) * d + 3 * ((ell : ℝ) - 1) * (ell : ℝ) * q := by
  have hell : 0 < ell := AdalyFormal.Balaban.ClassPropagationUbar.ell_pos_of_mem hs hx
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have hg := gammaPath_length_le c.1 x hs hx
  have hgR : ((coarseGammaPath s c.1 x).length : ℝ) ≤ 3 * (ell : ℝ) - 3 := by
    have h1 : ((coarseGammaPath s c.1 x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by
      exact_mod_cast hg
    have h3 : ((3 * (ell - 1) : ℕ) : ℝ) = 3 * (ell : ℝ) - 3 := by
      rw [Nat.cast_mul, Nat.cast_sub hell]; push_cast; ring
    linarith
  set G := coarseGammaPath s c.1 x
  set A := coarsePathHolonomy s V c.1 G
  set B := coarsePathHolonomy s V x (List.replicate ell c.2)
  set C := coarsePathHolonomy s V (cPlusS s ell c) G
  set E := coarseBondVar s ell V c
  set a := coarsePathHolonomy s T c.1 G
  set b := coarsePathHolonomy s T x (List.replicate ell c.2)
  set cc := coarsePathHolonomy s T (cPlusS s ell c) G
  set e := coarseBondVar s ell T c
  have hV : loopVar s ell V c x = A * B * C⁻¹ * E⁻¹ := rfl
  have hT : loopVar s ell T c x = a * b * cc⁻¹ * e⁻¹ := rfl
  have h4 := four_cmp (A * a⁻¹) (B * b⁻¹) (C * cc⁻¹) (E * e⁻¹) a b cc e
  simp only [inv_mul_cancel_right] at h4
  have h4' : dv (loopVar s ell V c x) ≤ dv (A * a⁻¹) + dv (B * b⁻¹) + dv (C * cc⁻¹) + dv (E * e⁻¹)
      + dv (ladS s T c.1 G c.2 ell) := by
    rw [hV, ← loopVar_eq_ladS s ell T c x hx, hT]; exact h4
  have hlad : dv (ladS s T c.1 G c.2 ell) ≤ (G.length : ℝ) * ((ell : ℝ) * q) :=
    ladS_le s T c.2 ell q G c.1 hq
  have b1 : dv (A * a⁻¹) ≤ (G.length : ℝ) * d := path_cmp s V T d G c.1 (fun b hb => hd b (by
    unfold loopBonds; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl hb))))
  have b2 : dv (B * b⁻¹) ≤ (ell : ℝ) * d := by
    have := path_cmp s V T d (List.replicate ell c.2) x (fun b hb => hd b (by
      unfold loopBonds; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr hb))))
    rw [List.length_replicate] at this; exact this
  have b3 : dv (C * cc⁻¹) ≤ (G.length : ℝ) * d := path_cmp s V T d G (cPlusS s ell c)
    (fun b hb => hd b (by
      unfold loopBonds; simp only [List.mem_append]; exact Or.inl (Or.inr hb)))
  have b4 : dv (E * e⁻¹) ≤ (ell : ℝ) * d := by
    have := path_cmp s V T d (List.replicate ell c.2) c.1 (fun b hb => hd b (by
      unfold loopBonds; simp only [List.mem_append]; exact Or.inr hb))
    rw [List.length_replicate] at this; exact this
  have hGd : (G.length : ℝ) * d ≤ (3 * (ell : ℝ) - 3) * d := mul_le_mul_of_nonneg_right hgR hd0
  have hGq : (G.length : ℝ) * ((ell : ℝ) * q) ≤ (3 * (ell : ℝ) - 3) * ((ell : ℝ) * q) :=
    mul_le_mul_of_nonneg_right hgR (by positivity)
  have hfin : (3 * (ell : ℝ) - 3) * ((ell : ℝ) * q) = 3 * ((ell : ℝ) - 1) * (ell : ℝ) * q := by ring
  linarith

/-- **One blocking step of the defect.** -/
theorem defect_step (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (V T : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) (d q : ℝ)
    (hd0 : 0 ≤ d) (hq0 : 0 ≤ q)
    (hd : ∀ x ∈ stepBlockOf c.1 s ell, ∀ b ∈ loopBonds s ell c x, dv (V b * (T b)⁻¹) ≤ d)
    (hdc : ∀ b ∈ pathBonds s c.1 (List.replicate ell c.2), dv (V b * (T b)⁻¹) ≤ d)
    (hq : ∀ x ∈ stepBlockOf c.1 s ell, ∀ t ∈ ladPlaqs s c.2 ell c.1 (coarseGammaPath s c.1 x),
      dv (pw s T t.1 t.2.1 t.2.2) ≤ q) :
    dv (ubarSU2 s ell V c * (coarseBondVar s ell T c)⁻¹)
      ≤ (ell : ℝ) * d
        + Real.pi / 2 * ((8 * (ell : ℝ) - 6) * d + 3 * ((ell : ℝ) - 1) * (ell : ℝ) * q) := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  set S := stepBlockOf c.1 s ell
  set w : PeriodicLatticeSite L → ℝ := fun _ => ((ell : ℝ) ^ 3)⁻¹
  set W : PeriodicLatticeSite L → SU2 := fun x => loopVar s ell V c x
  set bnd : ℝ := Real.pi / 2 * ((8 * (ell : ℝ) - 6) * d + 3 * ((ell : ℝ) - 1) * (ell : ℝ) * q)
  have hbnn : 0 ≤ bnd := by
    have h1 : (0 : ℝ) ≤ 8 * (ell : ℝ) - 6 := by linarith
    have h2 : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    have hpi := Real.pi_pos
    positivity
  have hlog : ∀ x ∈ S, frobNorm (su2Log (W x)) ≤ bnd := by
    intro x hx
    refine le_trans (frobNorm_su2Log_le_pi_div_two (W x)) ?_
    have hl := loop_cmp s ell hs V T c x hx d q hd0 (hd x hx) (hq x hx) hq0
    have hpi := Real.pi_pos
    exact mul_le_mul_of_nonneg_left hl (by positivity)
  have hE : frobNorm (blockExponent S w W) ≤ bnd :=
    frobNorm_blockExponent_le' S w W bnd (fun _ _ => by positivity)
      (weight_sum_le_one c.1 hs hell) hbnn hlog
  have hexp : dv (su2Exp (blockExponent S w W)) ≤ bnd :=
    le_trans (frobNorm_su2Exp_sub_one_le_uncond (blockExponent_antiHerm S w W)
      (blockExponent_trace S w W)) hE
  have hshape : ubarSU2 s ell V c = su2Exp (blockExponent S w W) * coarseBondVar s ell V c := by
    rw [ubarSU2_eq_blockedLink]; rfl
  have hcb := path_cmp s V T d (List.replicate ell c.2) c.1 hdc
  rw [List.length_replicate] at hcb
  have hid : ubarSU2 s ell V c * (coarseBondVar s ell T c)⁻¹
      = su2Exp (blockExponent S w W)
        * (coarseBondVar s ell V c * (coarseBondVar s ell T c)⁻¹) := by
    rw [hshape]; group
  rw [hid]
  have ht := dv_mul (su2Exp (blockExponent S w W))
    (coarseBondVar s ell V c * (coarseBondVar s ell T c)⁻¹)
  have hcb' : dv (coarseBondVar s ell V c * (coarseBondVar s ell T c)⁻¹) ≤ (ell : ℝ) * d := hcb
  linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.loopVar_eq_ladS
#print axioms AdalyFormal.CurvBlock.loop_cmp
#print axioms AdalyFormal.CurvBlock.defect_step
