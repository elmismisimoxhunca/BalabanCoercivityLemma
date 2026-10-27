
/-!
Round 6, adversarial limits.  The copied round-5 bridge above is unchanged.
The zero-amplitude obstruction below is exact, but zero amplitude is excluded
from that bridge's premise.  The positive-amplitude Taylor obstruction is
conditional; no Fourier/kernel expansion for the actual family is assumed
without being displayed as a hypothesis.
-/
namespace AdalyFormal.Round6.Guarded.LimitsR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.D1Literal (PSD)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- The genuine localized correction vanishes identically at zero interior
amplitude, for every exterior angle and every mass.  No unit is assumed. -/
theorem twistD_zero_amplitude {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (h3 : 3 ≤ R * (2*q)) (a t : ℝ) : twistD q R 0 a t = 0 := by
  classical
  let P := twistP q R 0 a t
  have hflat : ∀ e : Bond P.Lf, e.1 ∈ P.S.Om 0 → P.U e = 1 := by
    intro e he
    have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) :=
      fun h => h.1 he
    change twistU q R 0 t e = 1
    simp only [twistU, dilU, ite_self, AdalyFormal.StatementLane2.Ug_zero,
      ite_eq_right_iff]
    intro h
    exact (hz h).elim
  have hg := AdalyFormal.D1Guarded.G1invS_eq_Ginv_base
    selIn P selIn (dil_admissible hq hR) (by norm_num [P, twistP, gparams]) h3 hflat
  have hid := (dataS selIn selIn P).G1inv_unique
    (AdalyFormal.D1Literal.G1invS_spec selIn selIn P)
    ((dataS selIn selIn P).isG1inv_sub (dataS_laws selIn selIn P))
  have hh : (dataS selIn selIn P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) =
      (dataS selIn selIn P).Ginv := hid.symm.trans hg
  exact sub_eq_self.mp hh

/-- This holds on the entire carrier, hence on every crossing kernel. -/
theorem vacuum_correction_pairing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (h3 : 3 ≤ R * (2*q)) (a t : ℝ)
    (v : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪v, twistD q R 0 a t v⟫ = 0 := by
  rw [twistD_zero_amplitude hq hR h3 a t]
  simp

/-- The unchanged pinned corrected guard equals the carrier guard on the
zero-amplitude path; that path cannot provide a separating witness. -/
theorem vacuum_pencil_iff_carrier_unit {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (h3 : 3 ≤ R * (2*q)) (a t : ℝ) :
    CPen 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (twistU q R 0 t) a (dilLam q R) ↔ IsUnit (twistA q R 0 a t) := by
  change IsUnit (twistA q R 0 a t - twistD q R 0 a t) ↔ _
  rw [twistD_zero_amplitude hq hR h3 a t, sub_zero]

/-- Kernel control forces a genuinely positive correction form somewhere on
an exact crossing kernel.  First-crossing existence is not an extra premise. -/
theorem initial_control_has_positive_correction {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {ε : ℝ} (hc : InitialKernelControl q R ε) :
    ∃ t : ℝ, 0 < t ∧ t < Real.pi ∧ PSD (twistA q R ε 1 t) ∧
      ¬ IsUnit (twistA q R ε 1 t) ∧
      ∃ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
        twistA q R ε 1 t v = 0 ∧ 0 < ⟪v, twistD q R ε 1 0 v⟫ := by
  obtain ⟨t, ht0, htpi, hpsd, hnu, _⟩ :=
    twist_first_crossing_of_initial hq hR hroom ε hc.1 hc.2.1
  exact ⟨t, ht0, htpi, hpsd, hnu, hc.2.2.2 t ht0 htpi hpsd hnu⟩

/-- An actual nonpositive correction on the whole carrier precludes the
round-5 premise, without any separately postulated crossing. -/
theorem not_initial_control_of_correction_nonpositive {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q)) (ε : ℝ)
    (hn : ∀ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      ⟪v, twistD q R ε 1 0 v⟫ ≤ 0) : ¬ InitialKernelControl q R ε := by
  intro hc
  obtain ⟨_, _, _, _, _, v, _, hv⟩ :=
    initial_control_has_positive_correction hq hR hroom hc
  exact (not_lt_of_ge (hn v)) hv

/-- Unconditional exact obstruction at the boundary epsilon=0, at every
admissible scale and room-condition radius.  This does not cover epsilon>0. -/
theorem not_initial_control_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) : ¬ InitialKernelControl q R 0 := by
  apply not_initial_control_of_correction_nonpositive hq hR hroom 0
  intro v
  exact (vacuum_correction_pairing hq hR (by omega) 1 0 v).le

/-- At a PSD singular point the entire real kernel, not just one sampled
vector, must be tested to obstruct the existential sign clause. -/
theorem not_initial_control_of_kernel_nonpositive {q R : ℕ} (ε t : ℝ)
    (ht0 : 0 < t) (htpi : t < Real.pi)
    (hpsd : PSD (twistA q R ε 1 t)) (hnu : ¬ IsUnit (twistA q R ε 1 t))
    (hn : ∀ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      twistA q R ε 1 t v = 0 → ⟪v, twistD q R ε 1 0 v⟫ ≤ 0) :
    ¬ InitialKernelControl q R ε := by
  intro hc
  obtain ⟨v, hker, hv⟩ := hc.2.2.2 t ht0 htpi hpsd hnu
  exact (not_lt_of_ge (hn v hker)) hv

/-- A precise sufficient positive-amplitude obstruction: a negative linear
term and an O(epsilon^2) remainder on EVERY exact kernel vector.  The
expansion and PSD singular point are hypotheses, not numerical certificates. -/
theorem no_small_control_of_kernel_expansion {q R : ℕ}
    (c C η : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hη : 0 < η)
    (hexp : ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ t : ℝ, 0 < t ∧ t < Real.pi ∧ PSD (twistA q R ε 1 t) ∧
        ¬ IsUnit (twistA q R ε 1 t) ∧
        ∀ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
          twistA q R ε 1 t v = 0 →
          ⟪v, twistD q R ε 1 0 v⟫ ≤ (-c*ε + C*ε^2) * ‖v‖^2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ¬ InitialKernelControl q R ε := by
  have hCp : 0 < C + 1 := by linarith
  refine ⟨min η (c/(C+1)), lt_min hη (div_pos hc hCp), ?_⟩
  intro ε hε hεδ
  have hεη : ε < η := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεc : ε < c/(C+1) := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hm : ε*(C+1) < c := (lt_div_iff₀ hCp).mp hεc
  have hlin : C*ε ≤ c := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hlin hε.le
  have hcoef : -c*ε + C*ε^2 ≤ 0 := by nlinarith
  obtain ⟨t, ht0, htpi, hpsd, hnu, hn⟩ := hexp ε hε hεη
  apply not_initial_control_of_kernel_nonpositive ε t ht0 htpi hpsd hnu
  intro v hker
  exact (hn v hker).trans (mul_nonpos_of_nonpos_of_nonneg hcoef (sq_nonneg ‖v‖))

/-- A fixed admissible q,R with a proved small-positive-amplitude obstruction
already refutes the ALL-q sufficient premise of the verbatim round-5 bridge.
It does not refute GoalNeg2 and does not prove GoalPos2. -/
theorem not_round5_premise_of_small_obstruction {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (hbad : ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ¬ InitialKernelControl q R ε) :
    ¬ (∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ InitialKernelControl q R ε) := by
  intro hall
  obtain ⟨δ, hδ, hb⟩ := hbad
  obtain ⟨ε, hε, hεδ, hc⟩ := hall q hq R hR hR18 δ hδ
  exact hb ε hε hεδ hc

#print axioms twistD_zero_amplitude
#print axioms vacuum_correction_pairing
#print axioms vacuum_pencil_iff_carrier_unit
#print axioms initial_control_has_positive_correction
#print axioms not_initial_control_of_correction_nonpositive
#print axioms not_initial_control_zero
#print axioms not_initial_control_of_kernel_nonpositive
#print axioms no_small_control_of_kernel_expansion
#print axioms not_round5_premise_of_small_obstruction

end AdalyFormal.Round6.Guarded.LimitsR1
