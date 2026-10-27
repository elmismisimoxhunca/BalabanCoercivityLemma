import GFC6

/-!
# GFC7 -- continuity in the twist `z` and the COMPACTNESS theorem for the cell symbol.

`cell_coercive`: there is `c > 0` (depending only on the cell side `n`) such that for every twist `z`, every bond
field `w` and every `S ≥ 0` with  `|⟨D*w, Δu⟩|² ≤ S ‖Δu‖²` for all `u ⟂ ε`, one has
`c Σ_μ ‖w_μ‖² ≤ ½ Σ_{μν} ‖D_μ w_ν - D_ν w_μ‖² + Σ_μ |Q_μ w_μ|² + S`.   Standard axioms only.
-/
set_option autoImplicit false
open scoped ComplexInnerProductSpace BigOperators

namespace AdalyFormal.FlatCoercivity

variable {n : ℕ}

/-- general lattice shift of cell vectors -/
noncomputable def shiftOp (hn : 0 < n) (z : Fin 3 → ℂ) (a : Z3) (v : CV n) : CV n :=
  WithLp.toLp 2 (fun t => lift hn z v (cc t + a))

theorem shiftOp_apply (hn : 0 < n) (z : Fin 3 → ℂ) (a : Z3) (v : CV n) (t : Cell n) :
    shiftOp hn z a v t = lift hn z v (cc t + a) := rfl

theorem lift_shiftOp (hn : 0 < n) {z : Fin 3 → ℂ} (hz : ∀ μ, z μ ≠ 0) (a : Z3) (v : CV n) (x : Z3) :
    lift hn z (shiftOp hn z a v) x = lift hn z v (x + a) := by
  have hx := eq_cc_modc_add hn x
  have h2 : x + a = (cc (modc n hn x) + a) + (n : ℤ) • (fun ν => x ν / (n : ℤ)) := by
    conv_lhs => rw [hx]
    abel
  calc lift hn z (shiftOp hn z a v) x
      = phase z (fun ν => x ν / (n : ℤ)) * shiftOp hn z a v (modc n hn x) := rfl
    _ = phase z (fun ν => x ν / (n : ℤ)) * lift hn z v (cc (modc n hn x) + a) := by
        rw [shiftOp_apply]
    _ = lift hn z v (x + a) := by rw [h2, lift_qp hn hz]

theorem shiftOp_shiftOp (hn : 0 < n) {z : Fin 3 → ℂ} (hz : ∀ μ, z μ ≠ 0) (a b : Z3) (v : CV n) :
    shiftOp hn z a (shiftOp hn z b v) = shiftOp hn z (a + b) v := by
  ext t
  rw [shiftOp_apply, shiftOp_apply, lift_shiftOp hn hz]
  congr 1
  abel

theorem shiftOp_zero (hn : 0 < n) (z : Fin 3 → ℂ) (v : CV n) : shiftOp hn z 0 v = v := by
  ext t
  rw [shiftOp_apply, add_zero, lift_cc]

theorem Su_eq_shiftOp (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) (v : CV n) :
    Su hn z μ v = shiftOp hn (fun μ => (z μ : ℂ)) (ev μ) v := rfl

theorem Su_symm_eq (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) (v : CV n) :
    (Su hn z μ).symm v = shiftOp hn (fun μ => (z μ : ℂ)) (-ev μ) v := by
  apply (Su hn z μ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, Su_eq_shiftOp, shiftOp_shiftOp hn (z_ne z)]
  simp [shiftOp_zero]

theorem Su_iter_eq (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) (i : ℕ) (v : CV n) :
    (Su hn z μ)^[i] v = shiftOp hn (fun μ => (z μ : ℂ)) ((i : ℤ) • ev μ) v := by
  ext t
  have h1 : ((Su hn z μ)^[i] v) t = ((Sl hn (fun μ => (z μ : ℂ)) μ)^[i] v) t := rfl
  rw [h1, Sl_iter hn (z_ne z)]
  rfl


/-! ### continuity in the twist -/

theorem continuous_phase (k : Z3) : Continuous (fun z : Fin 3 → Circle => phase (fun μ => (z μ : ℂ)) k) := by
  unfold phase
  refine continuous_finsetProd _ (fun μ _ => ?_)
  refine Continuous.zpow₀ ?_ _ (fun z => Or.inl (z_ne z μ))
  exact (continuous_subtype_val).comp (continuous_apply μ)

theorem continuous_coord (t : Cell n) : Continuous (fun v : CV n => v t) :=
  PiLp.continuous_apply 2 _ t

theorem continuous_shiftOp (hn : 0 < n) (a : Z3) :
    Continuous (fun p : (Fin 3 → Circle) × CV n => shiftOp hn (fun μ => (p.1 μ : ℂ)) a p.2) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun t => ?_))
  unfold lift
  exact ((continuous_phase _).comp continuous_fst).mul ((continuous_coord _).comp continuous_snd)

/-- the parameter space: twist and bond field -/
abbrev Pn (n : ℕ) := (Fin 3 → Circle) × (Fin 3 → CV n)

section Cont
variable (hn : 0 < n)

theorem cont_D (μ : Fin 3) :
    Continuous (fun p : (Fin 3 → Circle) × CV n => (cellSym hn p.1).D μ p.2) := by
  have := (continuous_shiftOp hn (ev μ)).sub continuous_snd
  exact this

theorem cont_Ds (μ : Fin 3) :
    Continuous (fun p : (Fin 3 → Circle) × CV n => (cellSym hn p.1).Ds μ p.2) := by
  have := (continuous_shiftOp hn (-ev μ)).sub continuous_snd
  have h : ∀ p : (Fin 3 → Circle) × CV n, (cellSym hn p.1).Ds μ p.2
      = shiftOp hn (fun μ => (p.1 μ : ℂ)) (-ev μ) p.2 - p.2 := by
    intro p
    show ((Su hn p.1 μ).symm p.2) - p.2 = _
    rw [Su_symm_eq]
  simpa only [← h] using this

theorem cont_Qm (μ : Fin 3) :
    Continuous (fun p : (Fin 3 → Circle) × CV n => (cellSym hn p.1).Qm μ p.2) := by
  have h : ∀ p : (Fin 3 → Circle) × CV n, (cellSym hn p.1).Qm μ p.2
      = ⟪epsV n, ∑ i ∈ Finset.range n, shiftOp hn (fun μ => (p.1 μ : ℂ)) ((i : ℤ) • ev μ) p.2⟫ := by
    intro p
    unfold SymData.Qm
    show ⟪epsV n, ∑ i ∈ Finset.range n, (Su hn p.1 μ)^[i] p.2⟫ = _
    simp only [Su_iter_eq]
  simp only [h]
  refine Continuous.inner continuous_const ?_
  exact continuous_finsetSum _ (fun i _ => continuous_shiftOp hn _)

end Cont

section Compact
variable (hn : 0 < n)

theorem cont_pair (ν : Fin 3) : Continuous (fun p : Pn n => ((p.1, p.2 ν) : (Fin 3 → Circle) × CV n)) :=
  continuous_fst.prodMk ((continuous_apply ν).comp continuous_snd)

theorem cont_Dw (μ ν : Fin 3) : Continuous (fun p : Pn n => (cellSym hn p.1).D μ (p.2 ν)) :=
  Continuous.comp (g := fun q : (Fin 3 → Circle) × CV n => (cellSym hn q.1).D μ q.2)
    (f := fun p : Pn n => ((p.1, p.2 ν) : (Fin 3 → Circle) × CV n)) (cont_D hn μ) (cont_pair ν)

theorem cont_Dstar : Continuous (fun p : Pn n => (cellSym hn p.1).Dstar p.2) := by
  unfold SymData.Dstar
  refine continuous_finsetSum _ (fun μ _ => ?_)
  exact Continuous.comp (g := fun q : (Fin 3 → Circle) × CV n => (cellSym hn q.1).Ds μ q.2)
    (f := fun p : Pn n => ((p.1, p.2 μ) : (Fin 3 → Circle) × CV n)) (cont_Ds hn μ) (cont_pair μ)

theorem cont_Lap (u : CV n) : Continuous (fun z : Fin 3 → Circle => (cellSym hn z).Lap u) := by
  unfold SymData.Lap
  refine continuous_finsetSum _ (fun μ _ => ?_)
  have h1 : Continuous (fun z : Fin 3 → Circle => ((z, u) : (Fin 3 → Circle) × CV n)) :=
    continuous_id.prodMk continuous_const
  have h2' : Continuous (fun z : Fin 3 → Circle => (cellSym hn z).D μ u) :=
    Continuous.comp (g := fun q : (Fin 3 → Circle) × CV n => (cellSym hn q.1).D μ q.2)
      (f := fun z : Fin 3 → Circle => ((z, u) : (Fin 3 → Circle) × CV n)) (cont_D hn μ) h1
  have h2 : Continuous (fun z : Fin 3 → Circle => ((z, (cellSym hn z).D μ u) : (Fin 3 → Circle) × CV n)) :=
    continuous_id.prodMk h2'
  exact Continuous.comp (g := fun q : (Fin 3 → Circle) × CV n => (cellSym hn q.1).Ds μ q.2)
    (f := fun z : Fin 3 → Circle => ((z, (cellSym hn z).D μ u) : (Fin 3 → Circle) × CV n)) (cont_Ds hn μ) h2

theorem Lap_ne (z : Fin 3 → Circle) (u : CV n) (hu : ⟪epsV n, u⟫ = 0) (hu0 : u ≠ 0) :
    (cellSym hn z).Lap u ≠ 0 := by
  intro h
  have hfix := (cellSym hn z).Lap_eq_zero u h
  by_cases hall : ∀ μ, ((z μ : Circle) : ℂ) = 1
  · obtain ⟨c, hc⟩ := fixed_span hn z hall u hfix
    apply hu0
    have h1 : c * ⟪epsV n, epsV n⟫ = 0 := by
      rw [hc, inner_smul_right] at hu; exact hu
    have hne : ⟪epsV n, epsV n⟫ ≠ 0 := fun h0 => epsV_ne hn (inner_self_eq_zero.mp h0)
    have : c = 0 := (mul_eq_zero.mp h1).resolve_right hne
    rw [hc, this, zero_smul]
  · push_neg at hall
    obtain ⟨μ0, hμ0⟩ := hall
    exact hu0 ((cellSym hn z).fixed_zero μ0 hμ0 u (hfix μ0))

/-- the energy quantities -/
noncomputable def g1 (p : Pn n) : ℝ :=
  (1 / 2 : ℝ) * ∑ μ, ∑ ν, ‖(cellSym hn p.1).D μ (p.2 ν) - (cellSym hn p.1).D ν (p.2 μ)‖ ^ 2

noncomputable def g2 (p : Pn n) : ℝ := ∑ μ, ‖(cellSym hn p.1).Qm μ (p.2 μ)‖ ^ 2

theorem cont_g1 : Continuous (g1 hn : Pn n → ℝ) := by
  unfold g1
  refine continuous_const.mul (continuous_finsetSum _ (fun μ _ => continuous_finsetSum _ (fun ν _ => ?_)))
  exact ((cont_Dw hn μ ν).sub (cont_Dw hn ν μ)).norm.pow 2

theorem cont_g2 : Continuous (g2 hn : Pn n → ℝ) := by
  unfold g2
  refine continuous_finsetSum _ (fun μ _ => ?_)
  exact (Continuous.comp (g := fun q : (Fin 3 → Circle) × CV n => (cellSym hn q.1).Qm μ q.2)
    (f := fun p : Pn n => ((p.1, p.2 μ) : (Fin 3 → Circle) × CV n)) (cont_Qm hn μ) (cont_pair μ)).norm.pow 2

/-- the index set of test vectors -/
abbrev UIdx (n : ℕ) := {u : CV n // ⟪epsV n, u⟫ = 0 ∧ u ≠ 0}

noncomputable def Rr (p : Pn n) (u : CV n) : ℝ :=
  ‖⟪(cellSym hn p.1).Dstar p.2, (cellSym hn p.1).Lap u⟫‖ ^ 2 / ‖(cellSym hn p.1).Lap u‖ ^ 2

theorem cont_Rr (u : UIdx n) : Continuous (fun p : Pn n => Rr hn p u.1) := by
  unfold Rr
  have hden : ∀ p : Pn n, ‖(cellSym hn p.1).Lap u.1‖ ^ 2 ≠ 0 := fun p => by
    have := Lap_ne hn p.1 u.1 u.2.1 u.2.2
    positivity
  refine Continuous.div ?_ ?_ hden
  · exact (Continuous.inner (cont_Dstar hn) ((cont_Lap hn u.1).comp continuous_fst)).norm.pow 2
  · exact ((cont_Lap hn u.1).comp continuous_fst).norm.pow 2

theorem Rr_le (p : Pn n) (u : CV n) : Rr hn p u ≤ ‖(cellSym hn p.1).Dstar p.2‖ ^ 2 := by
  unfold Rr
  by_cases h : ‖(cellSym hn p.1).Lap u‖ ^ 2 = 0
  · rw [h]; simp
  · rw [div_le_iff₀ (lt_of_le_of_ne (by positivity) (Ne.symm h))]
    have := norm_inner_le_norm (𝕜 := ℂ) ((cellSym hn p.1).Dstar p.2) ((cellSym hn p.1).Lap u)
    have h2 : ‖⟪(cellSym hn p.1).Dstar p.2, (cellSym hn p.1).Lap u⟫‖ ^ 2
        ≤ (‖(cellSym hn p.1).Dstar p.2‖ * ‖(cellSym hn p.1).Lap u‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) this 2
    calc _ ≤ _ := h2
      _ = _ := by ring

theorem Rr_nonneg (p : Pn n) (u : CV n) : 0 ≤ Rr hn p u := by
  unfold Rr; positivity

noncomputable def Phi (p : Pn n) : ℝ := g1 hn p + g2 hn p + ⨆ u : UIdx n, Rr hn p u.1

theorem lsc_Phi : LowerSemicontinuous (Phi hn : Pn n → ℝ) := by
  unfold Phi
  refine LowerSemicontinuous.add ((cont_g1 hn).add (cont_g2 hn)).lowerSemicontinuous ?_
  refine lowerSemicontinuous_ciSup (fun p => ⟨‖(cellSym hn p.1).Dstar p.2‖ ^ 2, ?_⟩) (fun u => ?_)
  · rintro _ ⟨u, rfl⟩; exact Rr_le hn p u.1
  · exact (cont_Rr hn u).lowerSemicontinuous


theorem g1_nonneg (p : Pn n) : 0 ≤ g1 hn p := by unfold g1; positivity
theorem g2_nonneg (p : Pn n) : 0 ≤ g2 hn p := by unfold g2; positivity

theorem bdd_Rr (p : Pn n) : BddAbove (Set.range fun u : UIdx n => Rr hn p u.1) :=
  ⟨‖(cellSym hn p.1).Dstar p.2‖ ^ 2, by rintro _ ⟨u, rfl⟩; exact Rr_le hn p u.1⟩

theorem sup_nonneg (p : Pn n) : 0 ≤ ⨆ u : UIdx n, Rr hn p u.1 :=
  Real.iSup_nonneg (fun u => Rr_nonneg hn p u.1)

/-- pointwise positivity of the energy functional on the unit sphere -/
theorem Phi_pos (p : Pn n) (hp : ∑ μ, ‖p.2 μ‖ ^ 2 = 1) : 0 < Phi hn p := by
  by_contra hle
  push_neg at hle
  have h1 := g1_nonneg hn p
  have h2 := g2_nonneg hn p
  have h3 := sup_nonneg hn p
  unfold Phi at hle
  have hg1 : g1 hn p = 0 := by linarith
  have hg2 : g2 hn p = 0 := by linarith
  have hsup : (⨆ u : UIdx n, Rr hn p u.1) = 0 := by linarith
  -- curl free
  have hcurl : ∀ μ ν, (cellSym hn p.1).D μ (p.2 ν) = (cellSym hn p.1).D ν (p.2 μ) := by
    have := hg1
    unfold g1 at this
    have h0 : ∑ μ, ∑ ν, ‖(cellSym hn p.1).D μ (p.2 ν) - (cellSym hn p.1).D ν (p.2 μ)‖ ^ 2 = 0 := by
      have := this; linarith
    intro μ ν
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ ∑ j, ‖(cellSym hn p.1).D i (p.2 j) - (cellSym hn p.1).D j (p.2 i)‖ ^ 2 :=
      fun i _ => Finset.sum_nonneg (fun j _ => by positivity)
    have h2' := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 μ (Finset.mem_univ μ)
    have h3' := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h2' ν (Finset.mem_univ ν)
    have : ‖(cellSym hn p.1).D μ (p.2 ν) - (cellSym hn p.1).D ν (p.2 μ)‖ = 0 := by simpa using h3'
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hQ : ∀ μ, (cellSym hn p.1).Qm μ (p.2 μ) = 0 := by
    have h0 : ∑ μ, ‖(cellSym hn p.1).Qm μ (p.2 μ)‖ ^ 2 = 0 := hg2
    intro μ
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h0 μ (Finset.mem_univ μ)
    simpa using this
  have hK : ∀ u, ⟪epsV n, u⟫ = 0 → ⟪(cellSym hn p.1).Dstar p.2, (cellSym hn p.1).Lap u⟫ = 0 := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0]; simp [SymData.Lap, SymData.D, SymData.Ds]
    · have hle' : Rr hn p u ≤ 0 := by
        rw [← hsup]
        exact le_ciSup (f := fun u : UIdx n => Rr hn p u.1) (bdd_Rr hn p) ⟨u, hu, hu0⟩
      have hnn := Rr_nonneg hn p u
      have heq : Rr hn p u = 0 := le_antisymm hle' hnn
      unfold Rr at heq
      have hden : ‖(cellSym hn p.1).Lap u‖ ^ 2 ≠ 0 := by
        have := Lap_ne hn p.1 u hu hu0
        positivity
      have hnum : ‖⟪(cellSym hn p.1).Dstar p.2, (cellSym hn p.1).Lap u⟫‖ ^ 2 = 0 := by
        rcases div_eq_zero_iff.mp heq with h | h
        · exact h
        · exact absurd h hden
      exact norm_eq_zero.mp (by simpa using hnum)
  have hw := (cellSym hn p.1).symbol_positive p.2 hcurl hQ hK
  have : ∑ μ, ‖p.2 μ‖ ^ 2 = 0 := Finset.sum_eq_zero (fun μ _ => by rw [hw μ]; simp)
  rw [hp] at this
  exact one_ne_zero this


theorem isCompact_unitSphere (n : ℕ) : IsCompact {w : Fin 3 → CV n | ∑ μ, ‖w μ‖ ^ 2 = 1} := by
  have hclosed : IsClosed {w : Fin 3 → CV n | ∑ μ, ‖w μ‖ ^ 2 = 1} := by
    refine isClosed_eq ?_ continuous_const
    exact continuous_finsetSum _ (fun μ _ => ((continuous_apply μ).norm).pow 2)
  have hbdd : Bornology.IsBounded {w : Fin 3 → CV n | ∑ μ, ‖w μ‖ ^ 2 = 1} := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin 3 → CV n)) (r := 1)).subset ?_
    intro w hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro μ
    have : ‖w μ‖ ^ 2 ≤ 1 := by
      have := Finset.single_le_sum (f := fun μ => ‖w μ‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ μ)
      have hw' : ∑ μ, ‖w μ‖ ^ 2 = 1 := hw
      linarith
    nlinarith [norm_nonneg (w μ)]
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

theorem cell_coercive_unit (hn : 0 < n) : ∃ c : ℝ, 0 < c ∧ ∀ p : Pn n, ∑ μ, ‖p.2 μ‖ ^ 2 = 1 → c ≤ Phi hn p := by
  set K : Set (Pn n) := Set.univ ×ˢ {w : Fin 3 → CV n | ∑ μ, ‖w μ‖ ^ 2 = 1} with hK
  have hKc : IsCompact K := isCompact_univ.prod (isCompact_unitSphere n)
  have hKne : K.Nonempty := by
    refine ⟨((fun _ => 1 : Fin 3 → Circle), Pi.single 0 ((‖epsV n‖⁻¹ : ℝ) • epsV n)), Set.mem_univ _, ?_⟩
    show ∑ μ, ‖(Pi.single 0 ((‖epsV n‖⁻¹ : ℝ) • epsV n) : Fin 3 → CV n) μ‖ ^ 2 = 1
    rw [Fin.sum_univ_three]
    have hne : ‖epsV n‖ ≠ 0 := norm_ne_zero_iff.mpr (epsV_ne hn)
    simp [Pi.single_apply, norm_smul, hne]
  obtain ⟨p0, hp0K, hp0⟩ := (lsc_Phi hn).lowerSemicontinuousOn K |>.exists_isMinOn hKne hKc
  refine ⟨Phi hn p0, Phi_pos hn p0 hp0K.2, ?_⟩
  intro p hp
  exact hp0 (show p ∈ K from ⟨Set.mem_univ _, hp⟩)


theorem Dstar_smul (z : Fin 3 → Circle) (r : ℂ) (w : Fin 3 → CV n) :
    (cellSym hn z).Dstar (fun μ => r • w μ) = r • (cellSym hn z).Dstar w := by
  unfold SymData.Dstar
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun μ _ => (cellSym hn z).Ds_smul μ r (w μ))

theorem Qm_smul (z : Fin 3 → Circle) (μ : Fin 3) (r : ℂ) (x : CV n) :
    (cellSym hn z).Qm μ (r • x) = r * (cellSym hn z).Qm μ x := by
  unfold SymData.Qm
  have h : ∀ i : ℕ, ((cellSym hn z).S μ)^[i] (r • x) = r • ((cellSym hn z).S μ)^[i] x := by
    intro i
    show (Su hn z μ)^[i] (r • x) = r • (Su hn z μ)^[i] x
    simp only [Su_iter_eq]
    ext t
    simp [shiftOp_apply, lift_smul]
  simp only [h, ← Finset.smul_sum, inner_smul_right]

set_option maxHeartbeats 1000000 in
theorem g1_smul (z : Fin 3 → Circle) (r : ℝ) (hr : 0 < r) (w : Fin 3 → CV n) :
    g1 hn (z, fun μ => (r : ℂ) • w μ) = r ^ 2 * g1 hn (z, w) := by
  unfold g1
  have : ∀ μ ν, ‖(cellSym hn z).D μ ((r : ℂ) • w ν) - (cellSym hn z).D ν ((r : ℂ) • w μ)‖ ^ 2
      = r ^ 2 * ‖(cellSym hn z).D μ (w ν) - (cellSym hn z).D ν (w μ)‖ ^ 2 := by
    intro μ ν
    rw [(cellSym hn z).D_smul, (cellSym hn z).D_smul, ← smul_sub, norm_smul, mul_pow]
    simp [abs_of_pos hr]
  show (1 / 2 : ℝ) * ∑ μ, ∑ ν, ‖(cellSym hn z).D μ ((r : ℂ) • w ν) - (cellSym hn z).D ν ((r : ℂ) • w μ)‖ ^ 2
    = r ^ 2 * ((1 / 2 : ℝ) * ∑ μ, ∑ ν, ‖(cellSym hn z).D μ (w ν) - (cellSym hn z).D ν (w μ)‖ ^ 2)
  simp only [this, ← Finset.mul_sum]
  ring

set_option maxHeartbeats 1000000 in
theorem g2_smul (z : Fin 3 → Circle) (r : ℝ) (hr : 0 < r) (w : Fin 3 → CV n) :
    g2 hn (z, fun μ => (r : ℂ) • w μ) = r ^ 2 * g2 hn (z, w) := by
  unfold g2
  have : ∀ μ, ‖(cellSym hn z).Qm μ ((r : ℂ) • w μ)‖ ^ 2 = r ^ 2 * ‖(cellSym hn z).Qm μ (w μ)‖ ^ 2 := by
    intro μ
    rw [Qm_smul hn, norm_mul, mul_pow]
    simp [abs_of_pos hr]
  show ∑ μ, ‖(cellSym hn z).Qm μ ((r : ℂ) • w μ)‖ ^ 2 = r ^ 2 * ∑ μ, ‖(cellSym hn z).Qm μ (w μ)‖ ^ 2
  simp only [this, ← Finset.mul_sum]

theorem Rr_smul (z : Fin 3 → Circle) (r : ℝ) (hr : 0 < r) (w : Fin 3 → CV n) (u : CV n) :
    Rr hn (z, fun μ => (r : ℂ) • w μ) u = r ^ 2 * Rr hn (z, w) u := by
  unfold Rr
  show ‖⟪(cellSym hn z).Dstar (fun μ => (r : ℂ) • w μ), (cellSym hn z).Lap u⟫‖ ^ 2 / ‖(cellSym hn z).Lap u‖ ^ 2
    = r ^ 2 * (‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u⟫‖ ^ 2 / ‖(cellSym hn z).Lap u‖ ^ 2)
  rw [Dstar_smul hn z (r : ℂ) w, inner_smul_left, norm_mul, mul_pow, mul_div_assoc]
  have hnr : ‖(starRingEnd ℂ) (r : ℂ)‖ ^ 2 = r ^ 2 := by
    simp [abs_of_pos hr]
  rw [hnr]

theorem Rr_sup_smul (z : Fin 3 → Circle) (r : ℝ) (hr : 0 < r) (w : Fin 3 → CV n) (S : ℝ) (hS : 0 ≤ S)
    (hhyp : ∀ u : CV n, ⟪epsV n, u⟫ = 0 →
      ‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u⟫‖ ^ 2 ≤ S * ‖(cellSym hn z).Lap u‖ ^ 2) :
    (⨆ u : UIdx n, Rr hn (z, fun μ => (r : ℂ) • w μ) u.1) ≤ r ^ 2 * S := by
  refine Real.iSup_le (fun u => ?_) (by positivity)
  rw [Rr_smul hn z r hr w]
  have hLap : 0 < ‖(cellSym hn z).Lap u.1‖ ^ 2 := by
    have := Lap_ne hn z u.1 u.2.1 u.2.2
    positivity
  have hh := hhyp u.1 u.2.1
  have h1 : Rr hn (z, w) u.1 ≤ S := by
    unfold Rr
    show ‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u.1⟫‖ ^ 2 / ‖(cellSym hn z).Lap u.1‖ ^ 2 ≤ S
    rw [div_le_iff₀ hLap]; exact hh
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **THE CELL COERCIVITY THEOREM**: a constant `c = c(n) > 0` valid for ALL twists. -/
theorem cell_coercive (hn : 0 < n) : ∃ c : ℝ, 0 < c ∧ ∀ (z : Fin 3 → Circle) (w : Fin 3 → CV n) (S : ℝ), 0 ≤ S →
    (∀ u : CV n, ⟪epsV n, u⟫ = 0 →
      ‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u⟫‖ ^ 2 ≤ S * ‖(cellSym hn z).Lap u‖ ^ 2) →
    c * ∑ μ, ‖w μ‖ ^ 2 ≤ g1 hn (z, w) + g2 hn (z, w) + S := by
  obtain ⟨c, hc, hcp⟩ := cell_coercive_unit hn
  refine ⟨c, hc, ?_⟩
  intro z w S hS hhyp
  set N : ℝ := ∑ μ, ‖w μ‖ ^ 2 with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg (fun μ _ => by positivity)
  by_cases hNz : N = 0
  · rw [hNz, mul_zero]
    have := g1_nonneg hn (z, w); have := g2_nonneg hn (z, w); linarith
  · have hNp : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNz)
    set r : ℝ := (Real.sqrt N)⁻¹ with hr
    have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0
    have hrp : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hNp)
    have hr2 : r ^ 2 * N = 1 := by
      rw [hr, inv_pow, hsq]; field_simp
    have hnorm : ∑ μ, ‖((fun μ => (r : ℂ) • w μ) : Fin 3 → CV n) μ‖ ^ 2 = 1 := by
      have : ∀ μ, ‖((fun μ => (r : ℂ) • w μ) : Fin 3 → CV n) μ‖ ^ 2 = r ^ 2 * ‖w μ‖ ^ 2 := fun μ => by
        show ‖(r : ℂ) • w μ‖ ^ 2 = _
        rw [norm_smul, mul_pow]; simp [abs_of_pos hrp]
      simp only [this, ← Finset.mul_sum]
      exact hr2
    have h1 := hcp (z, fun μ => (r : ℂ) • w μ) hnorm
    have hS' : (⨆ u : UIdx n, Rr hn (z, fun μ => (r : ℂ) • w μ) u.1) ≤ r ^ 2 * S :=
      Rr_sup_smul hn z r hrp w S hS hhyp
    have hg1 := g1_smul hn z r hrp w
    have hg2 := g2_smul hn z r hrp w
    have h2 : Phi hn (z, fun μ => (r : ℂ) • w μ) ≤ r ^ 2 * (g1 hn (z, w) + g2 hn (z, w) + S) := by
      unfold Phi
      rw [hg1, hg2]
      nlinarith [hS']
    have h3 : c ≤ r ^ 2 * (g1 hn (z, w) + g2 hn (z, w) + S) := le_trans h1 h2
    have h4 : c * N ≤ (r ^ 2 * N) * (g1 hn (z, w) + g2 hn (z, w) + S) := by
      have := mul_le_mul_of_nonneg_right h3 hN0
      nlinarith [this]
    rw [hr2, one_mul] at h4
    exact h4

#print axioms cell_coercive

end Compact

end AdalyFormal.FlatCoercivity
