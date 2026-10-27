import WitnessGate
set_option autoImplicit false
noncomputable section
namespace HConstruction.NfRepair.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.NormalizationAudit
open AdalyFormal.Balaban.RegularityHolonomy
open AdalyFormal.Balaban.NormalizedCounterexampleSearch
variable {L : PeriodicLatticeExtent}

theorem holonomyElem_expand
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyElem U p = U (p.1, p.2.1.1) * U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
      (U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ * (U (p.1, p.2.1.2))⁻¹ := rfl

/-- **Gauge covariance of the plaquette holonomy**: `U(∂p) ↦ γ(x)·U(∂p)·γ(x)⁻¹` where `x` is the
plaquette's base site. The one nontrivial ingredient is `periodicLatticeShift_comm` (LAW-19,
reused), which identifies the two far-corner gauge factors so they cancel. -/
theorem holonomyElem_periodicGaugeTransform
    (γ : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyElem (periodicGaugeTransform γ U) p = γ p.1 * holonomyElem U p * (γ p.1)⁻¹ := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  rw [holonomyElem_expand, holonomyElem_expand]
  simp only [periodicGaugeTransform]
  rw [periodicLatticeShift_comm p.1 hne]
  group

noncomputable def rotA (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)

/-- `b(t) = 2t/(1+t²)`. -/
noncomputable def rotB (t : ℝ) : ℝ := (2 * t) / (1 + t ^ 2)

theorem one_add_sq_ne_zero (t : ℝ) : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity

theorem rotA_sq_add_rotB_sq (t : ℝ) : rotA t ^ 2 + rotB t ^ 2 = 1 := by
  have h : (1 : ℝ) + t ^ 2 ≠ 0 := one_add_sq_ne_zero t
  show ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + ((2 * t) / (1 + t ^ 2)) ^ 2 = 1
  field_simp
  ring

theorem rotA_le_one (t : ℝ) : rotA t ≤ 1 := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [rotA, div_le_one h]
  nlinarith [sq_nonneg t]

theorem rotA_eq_one_iff (t : ℝ) : rotA t = 1 ↔ t = 0 := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [rotA, div_eq_one_iff_eq h.ne']
  constructor
  · intro hh; nlinarith [sq_nonneg t]
  · intro hh; rw [hh]; ring

/-- The rotation matrix `!![a, b; -b, a]`. -/
noncomputable def rotM (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((rotA t : ℝ) : ℂ), ((rotB t : ℝ) : ℂ); -((rotB t : ℝ) : ℂ), ((rotA t : ℝ) : ℂ)]

theorem rotA_sq_add_rotB_sq_complex (t : ℝ) :
    ((rotA t : ℝ) : ℂ) * ((rotA t : ℝ) : ℂ) + ((rotB t : ℝ) : ℂ) * ((rotB t : ℝ) : ℂ) = 1 := by
  have h : ((rotA t ^ 2 + rotB t ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [rotA_sq_add_rotB_sq]
  push_cast at h
  linear_combination h

theorem rotM_conjTranspose (t : ℝ) :
    (rotM t).conjTranspose = !![((rotA t : ℝ) : ℂ), -((rotB t : ℝ) : ℂ);
                   ((rotB t : ℝ) : ℂ), ((rotA t : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, Matrix.conjTranspose_apply]

theorem rotM_mem_unitaryGroup (t : ℝ) : rotM t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, rotM_conjTranspose]
  have hab := rotA_sq_add_rotB_sq_complex t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first
      | linear_combination hab
      | ring1

theorem rotM_det (t : ℝ) : (rotM t).det = 1 := by
  have hab := rotA_sq_add_rotB_sq_complex t
  rw [rotM, Matrix.det_fin_two_of]
  linear_combination hab

theorem rotM_mem (t : ℝ) : rotM t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨rotM_mem_unitaryGroup t, rotM_det t⟩

/-- The rotation, packaged as an `SU(2)` element. -/
noncomputable def rotElem (t : ℝ) : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨rotM t, rotM_mem t⟩

theorem rotElem_coe (t : ℝ) :
    ((rotElem t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = rotM t := rfl

theorem trace_rotM_re (t : ℝ) : (Matrix.trace (rotM t)).re = 2 * rotA t := by
  rw [rotM, Matrix.trace_fin_two]
  simp
  ring

/-- **`rotElem t = 1` exactly at `t = 0`** — the family is genuinely non-trivial. -/
theorem rotElem_eq_one_iff (t : ℝ) :
    rotElem t = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) ↔ t = 0 := by
  constructor
  · intro h
    have hm : rotM t = (1 : Matrix (Fin 2) (Fin 2) ℂ) := congrArg Subtype.val h
    have h01 := congrFun (congrFun hm 0) 1
    simp only [rotM, Matrix.one_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Matrix.head_fin_const] at h01
    norm_num at h01
    have hb : rotB t = 0 := by exact_mod_cast h01
    have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [rotB, div_eq_zero_iff] at hb
    rcases hb with hb | hb
    · linarith
    · exact absurd hb h1.ne'
  · intro h
    subst h
    apply Subtype.ext
    rw [rotElem_coe, rotM]
    have ha : rotA 0 = 1 := by rw [rotA]; norm_num
    have hb : rotB 0 = 0 := by rw [rotB]; norm_num
    rw [ha, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem rotElem_ne_one {t : ℝ} (ht : t ≠ 0) :
    rotElem t ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := fun h => ht ((rotElem_eq_one_iff t).mp h)

/-! ## §3 — `nonflatU t`: the genuinely CURVED background

Built as an instance of the tree's OWN `NormalizedCounterexampleSearch.singleBondU` family
(LAW-19: not a second single-bond construction — `witnessU` and `centralHolonomyU` are the
`witnessMElem`/`negOneElem` instances of the same `def`, proved `rfl` in that file). -/

/-- **The non-flat background**: `rotElem t` on the single bond `(witnessY, 0)`, `1` elsewhere. -/
noncomputable def nonflatU (t : ℝ) :
    PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) AdmissibleSubspace.witnessL :=
  singleBondU (rotElem t)

theorem nonflatU_at_x_mu (t : ℝ) :
    nonflatU t (AdmissibleSubspace.witnessY, (0 : Fin 3)) = rotElem t :=
  singleBondU_at_x_mu _

theorem nonflatU_elsewhere (t : ℝ) {e : Bond AdmissibleSubspace.witnessL}
    (h : e ≠ (AdmissibleSubspace.witnessY, (0 : Fin 3))) : nonflatU t e = 1 :=
  singleBondU_elsewhere _ h

/-- **OPS-3 failure exhibit**: at `t = 0` the background degenerates to the flat one, so the
`t ≠ 0` hypothesis in every curvature statement below is load-bearing. -/
theorem nonflatU_zero_eq_trivial :
    nonflatU 0 = (trivialU (L := AdmissibleSubspace.witnessL)) := by
  funext e
  by_cases h : e = (AdmissibleSubspace.witnessY, (0 : Fin 3))
  · rw [h, nonflatU_at_x_mu, (rotElem_eq_one_iff 0).mpr rfl]; rfl
  · rw [nonflatU_elsewhere 0 h]; rfl

/-- **THE CURVATURE VALUE**: the plaquette holonomy at `witnessPlaquette` is `rotElem t`. -/
theorem holonomyElem_nonflatU_witnessPlaquette (t : ℝ) :
    holonomyElem (nonflatU t) witnessPlaquette = rotElem t :=
  holonomy_singleBondU_witnessPlaquette _

/-- **THE CURVATURE WITNESS — the theorem the dispatch demands.** For every `t ≠ 0` the
background `nonflatU t` has a plaquette whose holonomy is `≠ 1`: its field strength is
genuinely nonzero, not merely "some link value differs from `1`". -/
theorem nonflatU_curvature_ne_one {t : ℝ} (ht : t ≠ 0) :
    holonomyElem (nonflatU t) witnessPlaquette ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [holonomyElem_nonflatU_witnessPlaquette]
  exact rotElem_ne_one ht

theorem nonflatU_has_curved_plaquette {t : ℝ} (ht : t ≠ 0) :
    ∃ p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL,
      holonomyElem (nonflatU t) p ≠ (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨witnessPlaquette, nonflatU_curvature_ne_one ht⟩

noncomputable def defectOfElem (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  4 - 2 * (Matrix.trace (X : Matrix (Fin 2) (Fin 2) ℂ)).re

theorem holonomyDefectSq_eq_defectOfElem
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) :
    holonomyDefectSq U p = defectOfElem (holonomyElem U p) := rfl

theorem defectOfElem_nonneg (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) : 0 ≤ defectOfElem X := by
  have h := holonomyDefectSq_nonneg (singleBondU X) witnessPlaquette
  rwa [holonomyDefectSq_eq_defectOfElem, holonomy_singleBondU_witnessPlaquette] at h

theorem defectOfElem_inv (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    defectOfElem X⁻¹ = defectOfElem X := by
  unfold defectOfElem
  rw [trace_inv_re_eq_trace_re]

theorem defectOfElem_one : defectOfElem (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = 0 := by
  unfold defectOfElem
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.one_apply]

/-- **`singleBondU X`'s holonomy is trivial off the four exceptional plaquettes**, generic in
`X` — the generalisation of `TheLemmaNormalized.holonomy_witnessU_eq_one` (which is its
`X = witnessMElem` case), obtained by replacing `witnessU_elsewhere` with the already-general
`singleBondU_elsewhere` and reusing the SAME case-covering lemmas (LAW-19). -/
theorem holonomy_singleBondU_eq_one (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (hp1 : p ≠ witnessPlaquette) (hp2 : p ≠ myWitnessPlaquette2) (hp3 : p ≠ p3) (hp4 : p ≠ p4) :
    holonomyElem (singleBondU X) p = 1 := by
  rw [holonomyElem_expand]
  have e1 : singleBondU X (p.1, p.2.1.1) = 1 := by
    apply singleBondU_elsewhere
    intro hcon
    rcases eq_witnessPlaquette_or_myWitnessPlaquette2 (congrArg Prod.fst hcon)
        (congrArg Prod.snd hcon) with h | h
    · exact hp1 h
    · exact hp2 h
  have e2 : singleBondU X (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 1 := by
    apply singleBondU_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)
  have e3 : singleBondU X (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 1 := by
    apply singleBondU_elsewhere
    intro hcon
    rcases eq_p3_or_p4 (congrArg Prod.fst hcon) (congrArg Prod.snd hcon) with h | h
    · exact hp3 h
    · exact hp4 h
  have e4 : singleBondU X (p.1, p.2.1.2) = 1 := by
    apply singleBondU_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)
  rw [e1, e2, e3, e4]
  simp

/-- **The trichotomy**: every plaquette holonomy of `singleBondU X` is `X`, `X⁻¹`, or `1`. -/
theorem holonomy_singleBondU_trichotomy (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL) :
    holonomyElem (singleBondU X) p = X ∨ holonomyElem (singleBondU X) p = X⁻¹ ∨
      holonomyElem (singleBondU X) p = 1 := by
  by_cases h1 : p = witnessPlaquette
  · exact Or.inl (by rw [h1]; exact holonomy_singleBondU_witnessPlaquette X)
  by_cases h2 : p = myWitnessPlaquette2
  · exact Or.inl (by rw [h2]; exact holonomy_singleBondU_myWitnessPlaquette2 X)
  by_cases h3 : p = p3
  · exact Or.inr (Or.inl (by rw [h3]; exact holonomy_singleBondU_p3 X))
  by_cases h4 : p = p4
  · exact Or.inr (Or.inl (by rw [h4]; exact holonomy_singleBondU_p4 X))
  · exact Or.inr (Or.inr (holonomy_singleBondU_eq_one X h1 h2 h3 h4))

/-- **GENERIC REGULARITY AT THE SHARP THRESHOLD.** `singleBondU X` is `IsRegularHolonomy` at
exactly `defectOfElem X`. Subsumes `TheLemmaNormalized.witnessU_isRegularHolonomy_four`
(`defectOfElem witnessMElem = 4`) and covers `centralHolonomyU` (`= 8`). -/
theorem singleBondU_isRegularHolonomy (X : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    IsRegularHolonomy (singleBondU X) (defectOfElem X) := by
  intro p
  rw [holonomyDefectSq_eq_defectOfElem]
  rcases holonomy_singleBondU_trichotomy X p with h | h | h
  · rw [h]
  · rw [h, defectOfElem_inv]
  · rw [h, defectOfElem_one]; exact defectOfElem_nonneg X

/-- **SHARPNESS (OPS-3)**: the threshold cannot be lowered — the predicate genuinely fails
below `defectOfElem X`, so the bound above is attained, not slack. -/
theorem singleBondU_not_isRegularHolonomy_of_lt (X : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    {M : ℝ} (h : M < defectOfElem X) : ¬ IsRegularHolonomy (singleBondU X) M := by
  intro hreg
  have hb := hreg witnessPlaquette
  rw [holonomyDefectSq_eq_defectOfElem, holonomy_singleBondU_witnessPlaquette] at hb
  linarith

/-! ### §5.1 — the quantitative small-curvature statement -/

theorem defectOfElem_rotElem (t : ℝ) : defectOfElem (rotElem t) = 8 * t ^ 2 / (1 + t ^ 2) := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  unfold defectOfElem
  rw [rotElem_coe, trace_rotM_re, rotA]
  field_simp
  ring

theorem nonflatU_isRegularHolonomy (t : ℝ) :
    IsRegularHolonomy (nonflatU t) (8 * t ^ 2 / (1 + t ^ 2)) := by
  rw [← defectOfElem_rotElem]
  exact singleBondU_isRegularHolonomy _

theorem nonflatU_not_isRegularHolonomy_of_lt {t M : ℝ} (h : M < 8 * t ^ 2 / (1 + t ^ 2)) :
    ¬ IsRegularHolonomy (nonflatU t) M := by
  apply singleBondU_not_isRegularHolonomy_of_lt
  rwa [defectOfElem_rotElem]

theorem nonflatU_defect_pos {t : ℝ} (ht : t ≠ 0) : 0 < 8 * t ^ 2 / (1 + t ^ 2) := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have ht2 : 0 < t ^ 2 := by positivity
  positivity

theorem nonflatU_defect_le (t : ℝ) : 8 * t ^ 2 / (1 + t ^ 2) ≤ 8 * t ^ 2 := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [div_le_iff₀ h]
  nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]

/-- **The small-`α₁` regime is genuinely populated by CURVED backgrounds**: for every `ε > 0`
there is a background with nonzero curvature that is `IsRegularHolonomy`-regular below `ε`. The
tree previously had no such object — its only witness admitted at a small threshold was the
flat `pureGaugeU`. -/
theorem exists_curved_regular_below {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, t ≠ 0 ∧
      IsRegularHolonomy (nonflatU t) (8 * t ^ 2 / (1 + t ^ 2)) ∧
      8 * t ^ 2 / (1 + t ^ 2) < ε ∧
      holonomyElem (nonflatU t) witnessPlaquette ≠ 1 := by
  refine ⟨Real.sqrt (ε / 16), ?_, nonflatU_isRegularHolonomy _, ?_, ?_⟩
  · have : 0 < Real.sqrt (ε / 16) := Real.sqrt_pos.mpr (by linarith)
    exact this.ne'
  · have hsq : Real.sqrt (ε / 16) ^ 2 = ε / 16 := Real.sq_sqrt (by linarith)
    have hle := nonflatU_defect_le (Real.sqrt (ε / 16))
    rw [hsq] at hle ⊢
    linarith
  · apply nonflatU_curvature_ne_one
    have : 0 < Real.sqrt (ε / 16) := Real.sqrt_pos.mpr (by linarith)
    exact this.ne'

theorem rotM_sub_one (t : ℝ) :
    rotM t - 1 = !![((rotA t - 1 : ℝ) : ℂ), ((rotB t : ℝ) : ℂ);
                    -((rotB t : ℝ) : ℂ), ((rotA t - 1 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotM, Matrix.one_apply] <;> push_cast <;> ring

theorem frobSq_rotM_sub_one (t : ℝ) :
    AdalyFormal.Balaban.RMapLipschitz.frobSq (rotM t - 1) = 8 * t ^ 2 / (1 + t ^ 2) := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [rotM_sub_one]
  simp only [AdalyFormal.Balaban.RMapLipschitz.frobSq, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.of_apply, Matrix.head_fin_const, Complex.normSq_ofReal, map_neg, neg_neg]
  simp only [Complex.normSq_neg, Complex.normSq_ofReal]
  unfold rotA rotB
  field_simp
  ring

end HConstruction.NfRepair.Reproduced
