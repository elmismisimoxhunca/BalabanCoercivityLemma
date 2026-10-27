/-! ## Curved twist families with a free interior profile and a free exterior path

The class leaves the exterior field free and allows every bounded interior amplitude mask
(round 5 `maskedU`, `masked_regular`).  A counterexample may therefore use any continuous
one-parameter family `V` of exterior configurations (round 5 uses the frozen twist `Uth`)
and any interior profile `f` with `|f| ≤ 1`, scaled by the curvature `ε`.  At `ε = 0`
the interior is flat whatever `f` is, and the correction vanishes; only the first-order
correction depends on `f`. -/
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

/-- Interior amplitudes `ε • f` on every bond touching `Ω₀`, the exterior path `V t` on
the purely exterior bonds. -/
noncomputable def pathU (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (V t)

noncomputable def pathP (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (pathU q R V f ε t) a (dilLam q R)

/-- The actual all-plaquette carrier of the family. -/
noncomputable def pathA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (pathP q R V f ε a t)).Ginv

/-- The actual localized correction of the family. -/
noncomputable def pathD (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (pathP q R V f ε a t)).Delta2 (dataS_laws selIn selIn _)

theorem path_agrees (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε s t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    pathU q R V f ε s e = pathU q R V f ε t e := by
  classical
  simp only [pathU, maskedU, if_neg he]

theorem path_cont (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    AdalyFormal.D1Literal.ContFam (pathU q R V f ε) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact hV e
  · simp only [pathU, maskedU, if_neg he]
    exact continuous_const

/-- Continuity of the actual carrier in the path parameter (the proof of round 5's
`twistA_continuous`, through the exterior path identity). -/
theorem pathA_continuous {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) :
    Continuous (pathA q R V f ε a) := by
  let G := geomOf 2 1 (dilTower q R)
  let U := pathU q R V f ε
  have h : pathA q R V f ε a = fun t => pathA q R V f ε a 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wop G (U 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop G (U 0) a))).comp (iE G)) := by
    funext t
    exact exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      a (dilLam q R) U (fun s e he => path_agrees q R V f ε s 0 e he) selAll t
  rw [h]
  have hd : Continuous fun t => AdalyFormal.StatementLaneR6.deltaKLocCLM (U t)
      (Set.univ : Set (PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))) :=
    AdalyFormal.D1Literal.cont_deltaKLocCLM (path_cont q R hV f ε) _
  refine continuous_const.add
    (Continuous.clm_comp continuous_const (Continuous.clm_comp ?_ continuous_const))
  exact Continuous.clm_comp continuous_const
    (Continuous.clm_comp (hd.sub continuous_const) continuous_const)

/-- The localized data do not see the exterior. -/
theorem path_data_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    dataS selIn selIn (pathP q R V f ε a t) = dataS selIn selIn (pathP q R V f ε a 0) := by
  change (pathP q R V f ε a t).data = (pathP q R V f ε a 0).data
  exact AdalyFormal.M1IMS.data_congr_U (by norm_num) (dil_admissible hq hR)
    (by norm_num) hroom (pathU q R V f ε 0) (pathU q R V f ε t) a (dilLam q R)
    (fun e he => path_agrees q R V f ε 0 t e (fun hz => hz.1 he.1))

theorem pathD_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathD q R V f ε a t = pathD q R V f ε a 0 := by
  have hd := path_data_constant hq hR hroom V f ε a t
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- At zero curvature the correction vanishes, for every exterior path and profile (the
proof of round 6's `twistD_zero_amplitude`, `AHP/round6/limits-r2/Attempt.lean:2421`). -/
theorem pathD_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (h3 : 3 ≤ R * (2*q))
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (a t : ℝ) : pathD q R V f 0 a t = 0 := by
  classical
  let P := pathP q R V f 0 a t
  have hflat : ∀ e : Bond P.Lf, e.1 ∈ P.S.Om 0 → P.U e = 1 := by
    intro e he
    have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) :=
      fun h => h.1 he
    change pathU q R V f 0 t e = 1
    simp only [pathU, maskedU, zero_mul, AdalyFormal.StatementLane2.Ug_zero, ite_eq_right_iff]
    intro h
    exact (hz h).elim
  have hg := AdalyFormal.D1Guarded.G1invS_eq_Ginv_base
    selIn P selIn (dil_admissible hq hR) (by norm_num [P, pathP, gparams]) h3 hflat
  have hid := (dataS selIn selIn P).G1inv_unique
    (AdalyFormal.D1Literal.G1invS_spec selIn selIn P)
    ((dataS selIn selIn P).isG1inv_sub (dataS_laws selIn selIn P))
  have hh : (dataS selIn selIn P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) =
      (dataS selIn selIn P).Ginv := hid.symm.trans hg
  exact sub_eq_self.mp hh

/-- The frozen exterior twist as a path. -/
noncomputable def uthPath (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun t => AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t

theorem uthPath_cont (q R : ℕ) : AdalyFormal.D1Literal.ContFam (uthPath q R) :=
  AdalyFormal.D1Literal.contFam_Uth _

open Classical in
/-- The round-4 single defect line, as a profile. -/
noncomputable def dilMask (q R : ℕ) : Bond (scaleUp 2 1 (dilLu q R)) → ℝ :=
  fun e => if dilPattern q R e then 1 else 0

theorem dilMask_bound (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : |dilMask q R e| ≤ 1 := by
  simp only [dilMask]
  split_ifs <;> simp

/-- The round-4/5 curved twist family is the case `V = Uth`, `f = dilMask`. -/
theorem twistU_eq_path (q R : ℕ) (ε t : ℝ) :
    twistU q R ε t = pathU q R (uthPath q R) (dilMask q R) ε t := by
  classical
  funext e
  simp only [twistU, dilU, pathU, maskedU, uthPath, dilMask]
  split_ifs <;> simp

theorem twistA_eq_path (q R : ℕ) (ε a t : ℝ) :
    twistA q R ε a t = pathA q R (uthPath q R) (dilMask q R) ε a t := by
  unfold twistA twistP pathA pathP
  rw [twistU_eq_path]

theorem twistD_eq_path (q R : ℕ) (ε a t : ℝ) :
    twistD q R ε a t = pathD q R (uthPath q R) (dilMask q R) ε a t := by
  have hd : dataS selIn selIn (twistP q R ε a t) =
      dataS selIn selIn (pathP q R (uthPath q R) (dilMask q R) ε a t) := by
    unfold twistP pathP
    rw [twistU_eq_path]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-! ### Separation in a path family refutes the guarded reading -/

/-- Some path parameter has a unit carrier and a non-unit corrected carrier (mass `1`). -/
def PathSeparation (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : Prop :=
  ∃ t : ℝ, IsUnit (pathA q R V f ε 1 t) ∧ ¬ IsUnit (pathA q R V f ε 1 t - pathD q R V f ε 1 t)

/-- The cofinal premise with, for each scale and radius, a free continuous exterior path
and a free bounded interior profile (both chosen before the cap; only the amplitude `ε`
goes to zero).  NOT proved here. -/
def CofinalPathSeparation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ PathSeparation (2^j) R V f ε

/-- Bridge: the cofinal bookkeeping of round 8, with `masked_regular` in place of
`dil_regular` (the exterior is unconstrained by the class). -/
theorem goalNeg2_of_cofinalPathSeparation (h : CofinalPathSeparation) : GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  obtain ⟨j, hj, hRs⟩ := h m₀
  refine ⟨j+1, by omega, by omega, ?_⟩
  intro R₀
  obtain ⟨R, hRR, hR, hR18, V, -, f, hf1, hsep⟩ := hRs R₀
  refine ⟨R, hRR, ?_⟩
  intro a₀ ha₀
  let q := 2^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(j+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := min (a₀/(3840*q)) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε0, hεδ, t, hu, hnu⟩ := hsep δ hδ
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    dsimp [α]; push_cast; nlinarith
  have hmask : ∀ e, |ε * f e| ≤ α/80 := by
    intro e
    rw [abs_mul, abs_of_pos hε0]
    have h1 := hf1 e
    have h2 : ε * |f e| ≤ ε * 1 := mul_le_mul_of_nonneg_left h1 hε0.le
    dsimp [α]
    linarith
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (pathU q R V f ε t) :=
    ⟨dil_coverage hq hR (by omega), masked_regular hq hR hα (fun e => ε * f e) hmask _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    pathU q R V f ε t, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩

/-- Sign-free interval premise for a path family. -/
def PathSignChange (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : Prop :=
  ∃ t₀ t₁ : ℝ, t₀ ≤ t₁ ∧
    (∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (pathA q R V f ε 1 t)) ∧
    PSD (pathA q R V f ε 1 t₀ - pathD q R V f ε 1 0) ∧
    ∃ w : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      ⟪w, (pathA q R V f ε 1 t₁ - pathD q R V f ε 1 0) w⟫ < 0

theorem pathSeparation_of_signChange {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ} {ε : ℝ}
    (h : PathSignChange q R V f ε) : PathSeparation q R V f ε := by
  obtain ⟨t₀, t₁, h01, hguard, h₀, w, h₁⟩ := h
  have hsA : ∀ t x y, ⟪pathA q R V f ε 1 t x, y⟫ = ⟪x, pathA q R V f ε 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (pathP q R V f ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ x y, ⟪pathD q R V f ε 1 0 x, y⟫ = ⟪x, pathD q R V f ε 1 0 y⟫ := by
    intro x y
    exact ((dataS selIn selIn (pathP q R V f ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  obtain ⟨t, -, -, hu, hnu⟩ := separation_of_sign_change (pathA q R V f ε 1)
    (pathD q R V f ε 1 0) (pathA_continuous hq hR hroom hV f ε 1) hsA hsD t₀ t₁ h01 hguard
    h₀ w h₁
  refine ⟨t, hu, ?_⟩
  rwa [pathD_constant hq hR hroom V f ε 1 t]

/-! ### Vacuum nondegeneracy: the remaining premise, at zero curvature only -/

/-- **Vacuum nondegeneracy of a path family at `(q,R)`** (mass `1`).  Spectral content only
at zero curvature: the vacuum carrier `pathA q R V f 0 1 ts` (flat interior) vanishes on a
nonzero subspace `K` and is `≥ g > 0` on `Kᗮ` (a first crossing of the path).
Regularity: `(ε,t) ↦ pathA` is Fréchet differentiable at `(0,ts)` and `ε ↦ pathD` is
differentiable at `0`, with derivatives `At`, `Ae`, `De` acting on `K` as scalars
`σ < 0`, `α`, `c`.  Nondegeneracy: `c ≠ 0` (no sign, no size).  NOT proved here. -/
def PathVacuumNondegeneracy (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts : ℝ) (K : Submodule ℝ ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (g σ α c : ℝ)
    (At Ae De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    (∀ u ∈ K, pathA q R V f 0 1 ts u = 0) ∧ 0 < g ∧
    (∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, pathA q R V f 0 1 ts y⟫) ∧
    (∃ u ∈ K, u ≠ 0) ∧ σ < 0 ∧ c ≠ 0 ∧
    (∀ u ∈ K, ⟪u, At u⟫ = σ * ‖u‖ ^ 2) ∧
    (∀ u ∈ K, ⟪u, Ae u⟫ = α * ‖u‖ ^ 2) ∧
    (∀ u ∈ K, ⟪u, De u⟫ = c * ‖u‖ ^ 2) ∧
    HasFDerivAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Ae +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight At) ((0 : ℝ), ts) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0

/-- Vacuum nondegeneracy gives the sign-free interval premise at EVERY small curvature. -/
theorem pathSignChange_of_vacuum {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (h3 : 3 ≤ R * (2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : PathVacuumNondegeneracy q R V f) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSignChange q R V f ε := by
  obtain ⟨ts, K, g, σ, α, c, At, Ae, De, hker, hg, hgap, hne, hσ, hc, hAt, hAe, hDe,
    hA, hD⟩ := h
  have hsA : ∀ ε t x y, ⟪pathA q R V f ε 1 t x, y⟫ = ⟪x, pathA q R V f ε 1 t y⟫ := by
    intro ε t x y
    exact (dataS selAll selAll (pathP q R V f ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ ε x y, ⟪pathD q R V f ε 1 0 x, y⟫ = ⟪x, pathD q R V f ε 1 0 y⟫ := by
    intro ε x y
    exact ((dataS selIn selIn (pathP q R V f ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  exact perturbative_sign_change (fun ε t => pathA q R V f ε 1 t) (fun ε => pathD q R V f ε 1 0)
    hsA hsD ts K g σ α c At Ae De hker hg hgap hne hσ hc hAt hAe hDe
    (expansion_of_hasFDerivAt (fun ε t => pathA q R V f ε 1 t) ts Ae At hA)
    (expansion_of_hasDerivAt (fun ε => pathD q R V f ε 1 0) De (pathD_zero hq hR h3 V f 1 0) hD)

/-- The cofinal vacuum premise: infinitely many dyadic scales, for each infinitely many
even radii `R ≥ 18`, each with SOME continuous exterior path and SOME bounded interior
profile whose first-order correction is visible on a first vacuum crossing kernel.
NOT proved here. -/
def CofinalPathVacuum : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      PathVacuumNondegeneracy (2^j) R V f

theorem cofinalPathSeparation_of_cofinalPathVacuum (h : CofinalPathVacuum) :
    CofinalPathSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hV, f, hf, hv⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, V, hV, f, hf, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have h3 : 3 ≤ R * (2 * 2^j) := by nlinarith
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨ε₀, hε₀, hall⟩ := pathSignChange_of_vacuum hq hR h3 hv
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  refine ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀], ?_⟩
  exact pathSeparation_of_signChange hq hR hroom hV
    (hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀]))

/-- **Main reduction of this route.**  Cofinal vacuum nondegeneracy (zero-curvature data,
first-order regularity and `c ≠ 0` for some exterior path and bounded interior profile)
refutes the guarded all-plaquette reading. -/
theorem goalNeg2_of_cofinalPathVacuum (h : CofinalPathVacuum) : GoalNeg2 :=
  goalNeg2_of_cofinalPathSeparation (cofinalPathSeparation_of_cofinalPathVacuum h)

/-- The positive reading forbids it. -/
theorem not_cofinalPathVacuum_of_goalPos1 (h : GoalPos1) : ¬ CofinalPathVacuum :=
  fun h' => goalNeg2_of_cofinalPathVacuum h' (goalPos2_iff_goalPos1.mpr h)

/-- What the positive reading demands, stated directly: from some scale on, for all large
even radii, EVERY continuous exterior path and EVERY bounded interior profile fail vacuum
nondegeneracy (the first-order correction is invisible on the first vacuum crossing
kernel, or a regularity, gap or scalar clause fails). -/
theorem goalPos1_forces_vacuum_degeneracy (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) →
        ¬ PathVacuumNondegeneracy (2^j) R V f := by
  have h' := not_cofinalPathVacuum_of_goalPos1 h
  by_contra hcon
  apply h'
  intro j₀
  obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hcon j₀)
  obtain ⟨hjj, hj2⟩ := Classical.not_imp.mp hj
  refine ⟨j, hjj, fun R₀ => ?_⟩
  obtain ⟨R, hR⟩ := not_forall.mp (not_exists.mp hj2 R₀)
  obtain ⟨hRR, hR1⟩ := Classical.not_imp.mp hR
  obtain ⟨hR2, hR3⟩ := Classical.not_imp.mp hR1
  obtain ⟨hR18, hR4⟩ := Classical.not_imp.mp hR3
  obtain ⟨V, hV⟩ := not_forall.mp hR4
  obtain ⟨hVc, hV1⟩ := Classical.not_imp.mp hV
  obtain ⟨f, hf⟩ := not_forall.mp hV1
  obtain ⟨hfb, hf1⟩ := Classical.not_imp.mp hf
  exact ⟨R, hRR, hR2, hR18, V, hVc, f, hfb, not_not.mp hf1⟩

/-! ### Special cases: the frozen twist, and the round-4 defect line -/

/-- Vacuum nondegeneracy of the round-4/5 single-defect twist family itself. -/
def VacuumNondegeneracy (q R : ℕ) : Prop :=
  PathVacuumNondegeneracy q R (uthPath q R) (dilMask q R)

def CofinalVacuumNondegeneracy : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    VacuumNondegeneracy (2^j) R

theorem cofinalPathVacuum_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) :
    CofinalPathVacuum := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, uthPath (2^j) R, uthPath_cont (2^j) R, dilMask (2^j) R,
    dilMask_bound (2^j) R, hv⟩

theorem goalNeg2_of_cofinalVacuumNondegeneracy (h : CofinalVacuumNondegeneracy) : GoalNeg2 :=
  goalNeg2_of_cofinalPathVacuum (cofinalPathVacuum_of_cofinalVacuum h)

/-- The round-8 separation premise for the round-4 family follows from its vacuum data. -/
theorem cofinalTwistSeparation_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) :
    CofinalTwistSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have h3 : 3 ≤ R * (2 * 2^j) := by nlinarith
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨ε₀, hε₀, hall⟩ := pathSignChange_of_vacuum hq hR h3 hv
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  refine ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀], ?_⟩
  obtain ⟨t, hu, hnu⟩ := pathSeparation_of_signChange hq hR hroom (uthPath_cont (2^j) R)
    (hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀]))
  refine ⟨t, ?_, ?_⟩
  · rw [twistA_eq_path]; exact hu
  · rw [twistA_eq_path, twistD_eq_path]; exact hnu

/-- The same vacuum data with the scalar clauses supplied by a `U(1)` symmetry: the
crossing kernel is the complex line spanned by `u₀` and `J u₀`, where `J` is orthogonal
with `J (J u₀) = -u₀` and the three first-order operators are symmetric and commute with
`J` (for the diagonal families here, `J` is conjugation by `exp(π/4 · E₁)`, a quarter
turn of the charged components).  NOT proved here. -/
def PathVacuumNondegeneracyU1 (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts g : ℝ) (u₀ : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (J At Ae De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    u₀ ≠ 0 ∧ J (J u₀) = -u₀ ∧ (∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) ∧
    (∀ x y, ⟪At x, y⟫ = ⟪x, At y⟫) ∧ (∀ x y, ⟪Ae x, y⟫ = ⟪x, Ae y⟫) ∧
    (∀ x y, ⟪De x, y⟫ = ⟪x, De y⟫) ∧
    (∀ x, At (J x) = J (At x)) ∧ (∀ x, Ae (J x) = J (Ae x)) ∧ (∀ x, De (J x) = J (De x)) ∧
    pathA q R V f 0 1 ts u₀ = 0 ∧ pathA q R V f 0 1 ts (J u₀) = 0 ∧ 0 < g ∧
    (∀ y ∈ (Submodule.span ℝ {u₀, J u₀})ᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, pathA q R V f 0 1 ts y⟫) ∧
    ⟪u₀, At u₀⟫ < 0 ∧ ⟪u₀, De u₀⟫ ≠ 0 ∧
    HasFDerivAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Ae +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight At) ((0 : ℝ), ts) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0

theorem pathVacuum_of_U1 {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : PathVacuumNondegeneracyU1 q R V f) : PathVacuumNondegeneracy q R V f := by
  obtain ⟨ts, g, u₀, J, At, Ae, De, hu₀, hJJ, hJ, hAts, hAes, hDes, hAtJ, hAeJ, hDeJ,
    hk1, hk2, hg, hgap, hσ, hc, hA, hD⟩ := h
  obtain ⟨σ, hσK⟩ := scalar_on_complex_line At J hAts hJ hAtJ u₀ hu₀ hJJ
  obtain ⟨α, hαK⟩ := scalar_on_complex_line Ae J hAes hJ hAeJ u₀ hu₀ hJJ
  obtain ⟨c, hcK⟩ := scalar_on_complex_line De J hDes hJ hDeJ u₀ hu₀ hJJ
  have hmem : u₀ ∈ Submodule.span ℝ {u₀, J u₀} := Submodule.subset_span (by simp)
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  have hσ' : σ < 0 := by
    have h1 := hσK u₀ hmem
    rw [h1] at hσ
    by_contra hcon
    have := mul_nonneg (not_lt.mp hcon) hn.le
    linarith
  have hc' : c ≠ 0 := by
    intro hc0
    apply hc
    rw [hcK u₀ hmem, hc0, zero_mul]
  refine ⟨ts, Submodule.span ℝ {u₀, J u₀}, g, σ, α, c, At, Ae, De, ?_, hg, hgap,
    ⟨u₀, hmem, hu₀⟩, hσ', hc', hσK, hαK, hcK, hA, hD⟩
  intro u hu
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  rw [map_add, map_smul, map_smul, hk1, hk2, smul_zero, smul_zero, add_zero]

def CofinalPathVacuumU1 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      PathVacuumNondegeneracyU1 (2^j) R V f

theorem goalNeg2_of_cofinalPathVacuumU1 (h : CofinalPathVacuumU1) : GoalNeg2 := by
  apply goalNeg2_of_cofinalPathVacuum
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hV, f, hf, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, V, hV, f, hf, pathVacuum_of_U1 hv⟩

#print axioms pathU
#print axioms pathP
#print axioms pathA
#print axioms pathD
#print axioms path_agrees
#print axioms path_cont
#print axioms pathA_continuous
#print axioms path_data_constant
#print axioms pathD_constant
#print axioms pathD_zero
#print axioms uthPath
#print axioms uthPath_cont
#print axioms dilMask
#print axioms dilMask_bound
#print axioms twistU_eq_path
#print axioms twistA_eq_path
#print axioms twistD_eq_path
#print axioms PathSeparation
#print axioms CofinalPathSeparation
#print axioms goalNeg2_of_cofinalPathSeparation
#print axioms PathSignChange
#print axioms pathSeparation_of_signChange
#print axioms PathVacuumNondegeneracy
#print axioms pathSignChange_of_vacuum
#print axioms CofinalPathVacuum
#print axioms cofinalPathSeparation_of_cofinalPathVacuum
#print axioms goalNeg2_of_cofinalPathVacuum
#print axioms not_cofinalPathVacuum_of_goalPos1
#print axioms goalPos1_forces_vacuum_degeneracy
#print axioms VacuumNondegeneracy
#print axioms CofinalVacuumNondegeneracy
#print axioms cofinalPathVacuum_of_cofinalVacuum
#print axioms goalNeg2_of_cofinalVacuumNondegeneracy
#print axioms cofinalTwistSeparation_of_cofinalVacuum
#print axioms PathVacuumNondegeneracyU1
#print axioms pathVacuum_of_U1
#print axioms CofinalPathVacuumU1
#print axioms goalNeg2_of_cofinalPathVacuumU1

end AdalyFormal.Round9.Guarded.Qualitative
