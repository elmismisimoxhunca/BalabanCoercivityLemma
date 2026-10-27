import AdalyFormal.Balaban.Q1Real
import AdalyFormal.Balaban.BlockedBackground
import AdalyFormal.Balaban.SuTwoLogExpCore
import AdalyFormal.Balaban.BlockedGaugeGuardAlgebraExp
import AdalyFormal.Balaban.CovariantHjMinimizer
import AdalyFormal.Balaban.AdmissibleSubspace
import AdalyFormal.Balaban.QOne
import AdalyFormal.Balaban.Bch2

set_option autoImplicit false

open Matrix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.IngredientDeriv

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.Q1Real (GammaPath)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Exp_zero su2Log_one
  su2Exp_coe_of_antiHerm_traceless adMap adMap_apply coe_mul coe_inv)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

variable {L : PeriodicLatticeExtent}

/-! ## Ingredient 1 — `su2Exp` (and via §3 below, `su2Log`'s partner role): the fixed derivative

Astra's audit named the failure exactly: the seed file's own `HasDerivAt (fun t => NormedSpace.exp
(t•H)) H 0` step introduced a SECOND, independently-elaborated instance-sensitive goal, which
diverged from what `hasDerivAt_exp_smul_const'` itself produces (`Matrix.linftyOpNormedRing`'s own
`AddCommGroup`/`Module`/`TopologicalSpace` triple vs. a syntactically different default triple —
not a mathematical disagreement, an elaboration-order artifact). **The fix**: never re-state that
intermediate `HasDerivAt` goal; let its type be inferred ENTIRELY from the library lemma
application, then simplify in place. -/

theorem smul_conjTranspose_eq_neg {H : M2} (hah : Hᴴ = -H) (t : ℝ) : (t • H)ᴴ = -(t • H) := by
  rw [Matrix.conjTranspose_smul, hah, smul_neg]; simp

theorem smul_trace_eq_zero {H : M2} (htr : Matrix.trace H = 0) (t : ℝ) :
    Matrix.trace (t • H) = 0 := by
  rw [Matrix.trace_smul, htr, smul_zero]

theorem su2Exp_coe_smul_eq (H : M2) (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) (t : ℝ) :
    ((su2Exp (t • H) : SU2) : M2) = NormedSpace.exp (t • H) :=
  su2Exp_coe_of_antiHerm_traceless (smul_conjTranspose_eq_neg hah t) (smul_trace_eq_zero htr t)

/-- **PAID — Ingredient `su2Exp`/`su2Log` (the exponential half), instance-diamond fixed.**
`t ↦ ((su2Exp (t•H) : SU2) : M2)` has derivative exactly `H` at `t = 0`, on arbitrary traceless
anti-Hermitian `H` — a genuine closed-form coefficient identity, not a gradient. -/
theorem hasDerivAt_su2Exp_coe_smul {H : M2} (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    HasDerivAt (fun t : ℝ => ((su2Exp (t • H) : SU2) : M2)) H 0 := by
  have hraw := hasDerivAt_exp_smul_const' H (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, mul_one] at hraw
  exact hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => su2Exp_coe_smul_eq H hah htr t))

#print axioms smul_conjTranspose_eq_neg
#print axioms smul_trace_eq_zero
#print axioms su2Exp_coe_smul_eq
#print axioms hasDerivAt_su2Exp_coe_smul

/-! ## Ingredient 2 — blocked conjugation `R̄_{0,c}` / `groupConj` at a FIXED background point

CMP98 (59)'s `R̄_{0,c} = R((V̄₀)_c)` is conjugation by a group element that (for the derivative
w.r.t. `V₁` taken here) does not itself move: only the argument being conjugated moves. This is
exactly `adMap`, ALREADY compiled (`SuTwoLogExpCore.lean`) as the `ℚ`-linear derivative of
conjugation — reused here, not rebuilt, and now actually CONNECTED to a `HasDerivAt` fact. -/

def groupConj (g h : SU2) : SU2 := g * h * g⁻¹

/-- **PAID — Ingredient "blocked conjugation" `R̄_{0,c}`.** For a FIXED `g` (e.g. `g = (V̄₀)_c`,
CMP98's own raw average (15)), conjugating a near-identity curve `t ↦ su2Exp(t•H)` differentiates
to exactly `adMap g H` at `t = 0` — the coefficient CMP98's channels transport by, on arbitrary
`H`, not merely at one numeric instance. -/
theorem hasDerivAt_groupConj_coe_smul (g : SU2) {H : M2} (hah : Hᴴ = -H)
    (htr : Matrix.trace H = 0) :
    HasDerivAt (fun t : ℝ => ((groupConj g (su2Exp (t • H)) : SU2) : M2)) (adMap g H) 0 := by
  have hg : ∀ t : ℝ, ((groupConj g (su2Exp (t • H)) : SU2) : M2)
      = (g : M2) * ((su2Exp (t • H) : SU2) : M2) * (g : M2)ᴴ := by
    intro t
    show ((g * (su2Exp (t • H)) * g⁻¹ : SU2) : M2) = _
    rw [coe_mul, coe_mul, coe_inv]
  have hd : HasDerivAt (fun t : ℝ => (g : M2) * ((su2Exp (t • H) : SU2) : M2) * (g : M2)ᴴ)
      ((g : M2) * H * (g : M2)ᴴ) 0 :=
    ((hasDerivAt_su2Exp_coe_smul hah htr).const_mul (g : M2)).mul_const (g : M2)ᴴ
  have hEq : (g : M2) * H * (g : M2)ᴴ = adMap g H := (adMap_apply g H).symm
  rw [hEq] at hd
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hg)

#print axioms hasDerivAt_groupConj_coe_smul

/-! ## Ingredient 1b — `su2Log`, the LEFT-INVERSE half, on the near-identity curves this project
actually needs

Reuses the ALREADY-COMPILED `Bch2.log_exp` (an exact, not first-order, local inverse of `su2Exp`)
rather than re-deriving `su2Log`'s own analytic derivative from its `arccos`/`sin` closed form
(which has a genuine coordinate singularity in its own parametrization at the identity, cancelled
only after composing back with `su2Exp` — exactly the situation `log_exp` was built to avoid). -/

theorem hasDerivAt_su2Log_su2Exp_smul {H : M2} (hah : Hᴴ = -H) (htr : Matrix.trace H = 0) :
    HasDerivAt (fun t : ℝ => su2Log (su2Exp (t • H))) H 0 := by
  set R : ℝ := Real.pi / (AdalyFormal.Balaban.Bch2.nu H + 1) with hR
  have hRpos : 0 < R :=
    div_pos Real.pi_pos (by linarith [AdalyFormal.Balaban.Bch2.nu_nonneg H])
  have heq : ∀ t ∈ Metric.ball (0 : ℝ) R, su2Log (su2Exp (t • H)) = t • H := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    refine AdalyFormal.Balaban.Bch2.log_exp ⟨smul_conjTranspose_eq_neg hah t, smul_trace_eq_zero htr t⟩ ?_
    rw [AdalyFormal.Balaban.Bch2.nu_smul]
    have hnn : (0:ℝ) ≤ AdalyFormal.Balaban.Bch2.nu H := Real.sqrt_nonneg _
    have h1 : |t| * AdalyFormal.Balaban.Bch2.nu H ≤ |t| * (AdalyFormal.Balaban.Bch2.nu H + 1) := by
      have : AdalyFormal.Balaban.Bch2.nu H ≤ AdalyFormal.Balaban.Bch2.nu H + 1 := by linarith
      exact mul_le_mul_of_nonneg_left this (abs_nonneg t)
    have h2 : |t| * (AdalyFormal.Balaban.Bch2.nu H + 1) < Real.pi := by
      rw [hR] at ht
      have hpos1 : (0:ℝ) < AdalyFormal.Balaban.Bch2.nu H + 1 := by positivity
      calc |t| * (AdalyFormal.Balaban.Bch2.nu H + 1)
          < (Real.pi / (AdalyFormal.Balaban.Bch2.nu H + 1)) * (AdalyFormal.Balaban.Bch2.nu H + 1) :=
            mul_lt_mul_of_pos_right ht hpos1
        _ = Real.pi := by field_simp
    linarith
  have hlin := (hasDerivAt_id (0 : ℝ)).smul_const H
  simp only [one_smul] at hlin
  exact hlin.congr_of_eventuallyEq
    (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hRpos) heq)

#print axioms hasDerivAt_su2Log_su2Exp_smul

/-! ## Ingredient 3 — path products `rZeroPath` (CMP98 (58)), on the FORWARD-only paths this
project actually uses

`GammaPath` (`Q1Real.lean`'s own `straightSegment := List.replicate _ (μ, true)`) is built
ENTIRELY from `(μ, true)` steps — Astra's reverse-branch defect is never exercised on the paths
`endpointAvg`/`modifiedAverage` actually call `rZeroPath` on. So the genuine "path products"
derivative needed here is the FORWARD-only case, proved directly (not merely assumed absent). -/

def rZeroPathStep (V0 V1 : PeriodicLinkConfiguration SU2 L) :
    (PeriodicLatticeSite L × SU2 × SU2) → (Fin 3 × Bool) → (PeriodicLatticeSite L × SU2 × SU2) :=
  fun st step =>
    let x := st.1
    let transportSoFar := st.2.1
    let prod := st.2.2
    let next := periodicLatticeStep x step
    let bondFactor : SU2 := if step.2 then V1 (x, step.1) else (V1 (next, step.1))⁻¹
    let bgFactor : SU2 := if step.2 then V0 (x, step.1) else (V0 (next, step.1))⁻¹
    (next, transportSoFar * bgFactor, prod * groupConj transportSoFar bondFactor)

noncomputable def rZeroPath (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (base : PeriodicLatticeSite L) (steps : List (Fin 3 × Bool)) : SU2 :=
  (steps.foldl (rZeroPathStep V0 V1) (base, 1, 1)).2.2

theorem rZeroPathStep_forward (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (x : PeriodicLatticeSite L) (transport prod : SU2) (μ : Fin 3) :
    rZeroPathStep V0 V1 (x, transport, prod) (μ, true)
      = (periodicLatticeStep x (μ, true), transport * V0 (x, μ),
          prod * groupConj transport (V1 (x, μ))) := by
  simp [rZeroPathStep]

/-- `A`'s adjoint-transported contribution, summed along a forward-only path — the CLOSED FORM
coefficient `rZeroPath`'s derivative equals. Recursion mirrors `rZeroPathStep` exactly. -/
noncomputable def dirDeriv (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) :
    PeriodicLatticeSite L → List (Fin 3 × Bool) → SU2 → M2
  | _, [], _ => 0
  | x, s :: rest, transport =>
      adMap transport (A (x, s.1))
        + dirDeriv V0 A (periodicLatticeStep x s) rest (transport * V0 (x, s.1))

/-- **PAID — Ingredient "path products" `rZeroPath`, forward-only, arbitrary direction `A`.**
Along ANY forward-only path and ANY per-bond traceless anti-Hermitian direction `A`, the raw
relative tree-frame transport `rZeroPath V0 (fun e => su2Exp(t•A e)) base steps` differentiates at
`t = 0` to EXACTLY `dirDeriv V0 A base steps 1` — a sum of adjoint-transported per-bond generators,
not a gradient, on arbitrary `A`. -/
theorem hasDerivAt_rZeroPath_forward (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (base : PeriodicLatticeSite L)
    (steps : List (Fin 3 × Bool)) (hfwd : ∀ s ∈ steps, s.2 = true) :
    HasDerivAt
      (fun t : ℝ => ((rZeroPath V0 (fun e => su2Exp (t • A e)) base steps : SU2) : M2))
      (dirDeriv V0 A base steps 1) 0 := by
  suffices h : ∀ (steps : List (Fin 3 × Bool)), (∀ s ∈ steps, s.2 = true) →
      ∀ (site : PeriodicLatticeSite L) (transport : SU2) (P : ℝ → SU2) (D : M2),
        P 0 = 1 → HasDerivAt (fun t : ℝ => ((P t : SU2) : M2)) D 0 →
        HasDerivAt (fun t : ℝ =>
            (((steps.foldl (rZeroPathStep V0 (fun e => su2Exp (t • A e))) (site, transport, P t)).2.2
              : SU2) : M2))
          (D + dirDeriv V0 A site steps transport) 0 by
    have := h steps hfwd base 1 (fun _ => (1 : SU2)) 0 rfl
      (hasDerivAt_const (0 : ℝ) (((1 : SU2) : M2)))
    simpa [rZeroPath] using this
  intro steps
  induction steps with
  | nil =>
    intro _ site transport P D hP0 hPd
    simpa [dirDeriv] using hPd
  | cons s rest ih =>
    intro hfwd site transport P D hP0 hPd
    have hs : s.2 = true := hfwd s (by simp)
    obtain ⟨μ, hμ⟩ : ∃ μ, s = (μ, true) := ⟨s.1, by cases s; simp_all⟩
    subst hμ
    have hstep : ∀ t : ℝ,
        (rZeroPathStep V0 (fun e => su2Exp (t • A e)) (site, transport, P t) (μ, true))
          = (periodicLatticeStep site (μ, true), transport * V0 (site, μ),
              P t * groupConj transport (su2Exp (t • A (site, μ)))) :=
      fun t => rZeroPathStep_forward V0 (fun e => su2Exp (t • A e)) site transport (P t) μ
    have hQ0 : (fun t : ℝ => P t * groupConj transport (su2Exp (t • A (site, μ)))) 0 = 1 := by
      simp [hP0, groupConj]
    have hQd : HasDerivAt
        (fun t : ℝ => ((P t * groupConj transport (su2Exp (t • A (site, μ))) : SU2) : M2))
        (D + adMap transport (A (site, μ))) 0 := by
      have hcoe : ∀ t : ℝ, ((P t * groupConj transport (su2Exp (t • A (site, μ))) : SU2) : M2)
          = (P t : M2) * ((groupConj transport (su2Exp (t • A (site, μ))) : SU2) : M2) := by
        intro t; exact coe_mul (P t) _
      have hmul := hPd.mul (hasDerivAt_groupConj_coe_smul transport (hah (site, μ)) (htr (site, μ)))
      have hQval : ((groupConj transport (su2Exp ((0 : ℝ) • A (site, μ))) : SU2) : M2) = 1 := by
        simp [groupConj]
      simp only [hQval, hP0, Submonoid.coe_one, mul_one, one_mul] at hmul
      exact hmul.congr_of_eventuallyEq (Filter.Eventually.of_forall hcoe)
    have hrest := ih (fun s' hs' => hfwd s' (List.mem_cons_of_mem _ hs'))
      (periodicLatticeStep site (μ, true)) (transport * V0 (site, μ))
      (fun t => P t * groupConj transport (su2Exp (t • A (site, μ)))) (D + adMap transport (A (site, μ)))
      hQ0 hQd
    have hfold : ∀ t : ℝ,
        ((((μ, true) :: rest).foldl (rZeroPathStep V0 (fun e => su2Exp (t • A e))) (site, transport, P t)).2.2
          : M2)
          = ((rest.foldl (rZeroPathStep V0 (fun e => su2Exp (t • A e)))
              (periodicLatticeStep site (μ, true), transport * V0 (site, μ),
                P t * groupConj transport (su2Exp (t • A (site, μ))))).2.2 : M2) := by
      intro t; rw [List.foldl_cons, hstep t]
    have : D + adMap transport (A (site, μ))
        + dirDeriv V0 A (periodicLatticeStep site (μ, true)) rest (transport * V0 (site, μ))
        = D + dirDeriv V0 A site ((μ, true) :: rest) transport := by
      simp [dirDeriv, add_assoc]
    rw [this] at hrest
    exact hrest.congr_of_eventuallyEq (Filter.Eventually.of_forall hfold)

#print axioms rZeroPathStep_forward
#print axioms hasDerivAt_rZeroPath_forward

end AdalySI1.IngredientDeriv
