import MR5
import MXQ_Base
import AC_MR5

/-! AC copy of MR5: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace MXQ.M2Route
open MXQ.AllC (CF CubeFamOK)
open AdalyFormal.M2Route

open AdalyFormal.AllC MXQ.AllC
variable {Fm : CF} [CubeFamOK Fm]

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.CurvBlock (dv pw CubeChart cube_plaq dv_pw_gauge dv_inv)
open AdalyFormal.M1NonFlat (SU2)

variable {L : PeriodicLatticeExtent}

section hol
variable {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 1 ≤ ell)
  {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) (ha1 : ((12 : ℕ) : ℝ) * M * α₀ ≤ 1)
  {U : LinkCfg L} (hP : PerCubeRegular2HQ ell M Fm 12 k S α₀ η U) (hC : CoversPlaqQ ell M Fm k S)
include hS hell hη hα ha1 hP hC

/-- the bound for an ordered pair `ν < μ`. -/
theorem plaq_class_ltACΦ (j0 : ℕ) (y : PeriodicLatticeSite L) (ν μ : Fin 3) (hνμ : ν < μ)
    (h1 : y ∈ S.Om j0) (h2 : periodicLatticeShift y ν ∈ S.Om j0) (h3 : periodicLatticeShift y μ ∈ S.Om j0)
    (h4 : periodicLatticeShift (periodicLatticeShift y ν) μ ∈ S.Om j0) :
    dv (pw 1 U y ν μ) ≤ (ell : ℝ) ^ 2 *
      (2 * (((12 : ℕ) : ℝ) * M * α₀) + (4 * Real.pi + 2) * (((12 : ℕ) : ℝ) * M * α₀) ^ 2) / (ell : ℝ) ^ (2 * j0) := by
  have h0 : ∀ x, x ∈ S.Om j0 → x ∈ S.Om 0 := fun x hx => AdalyFormal.M1.om_anti hS (Nat.zero_le j0) hx
  have h4' : periodicLatticeShift (periodicLatticeShift y μ) ν ∈ S.Om j0 := by rw [shift_comm]; exact h4
  set p : PeriodicLatticePlaquette L := (y, ⟨(ν, μ), hνμ⟩) with hp
  have hpe : ∀ e ∈ periodicPlaquetteBoundaryEdges p, e = (y, ν) ∨ e = (periodicLatticeShift y ν, μ) ∨
      e = (periodicLatticeShift y μ, ν) ∨ e = (y, μ) := by
    intro e he
    simp only [periodicPlaquetteBoundaryEdges, hp, Finset.mem_insert, Finset.mem_singleton] at he
    exact he
  have hcov : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
    intro e he
    rcases hpe e he with h | h | h | h <;> subst h
    · exact ⟨h0 _ h1, h0 _ h2⟩
    · exact ⟨h0 _ h2, h0 _ h4⟩
    · exact ⟨h0 _ h3, h0 _ h4'⟩
    · exact ⟨h0 _ h1, h0 _ h3⟩
  obtain ⟨sites, i, hqΦ, hb⟩ := hC p hcov
  obtain ⟨fΦ, hfΦ, hq⟩ := hqΦ
  have mem : ∀ e : Bond L, (e = (y, ν) ∨ e = (periodicLatticeShift y ν, μ) ∨
      e = (periodicLatticeShift y μ, ν) ∨ e = (y, μ)) → e ∈ periodicPlaquetteBoundaryEdges p := by
    intro e he
    simp only [periodicPlaquetteBoundaryEdges, hp, Finset.mem_insert, Finset.mem_singleton]
    exact he
  have b1 := hb _ (mem _ (Or.inl rfl))
  have b2 := hb _ (mem _ (Or.inr (Or.inl rfl)))
  have b3 := hb _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))
  have b4 := hb _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))
  obtain ⟨g, A, hA, hD, -⟩ := hP fΦ sites i hfΦ hq
  set a : ℝ := ((12 : ℕ) : ℝ) * M * α₀ with ha
  have ha0 : 0 ≤ a := by positivity
  set ni : ℝ := (ell : ℝ) ^ i with hni
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hni1 : 1 ≤ ni := one_le_pow₀ hl
  have hni0 : 0 < ni := by linarith
  set c1 : ℝ := a * ((ni * η)⁻¹ ^ 1) with hc1
  set c2 : ℝ := a * ((ni * η)⁻¹ ^ 2) with hc2
  let K : CubeChart U (CubeBond sites) η c1 c2 :=
    { g := g, A := A
      hA := fun e he => ⟨(hA e he).1, (hA e he).2.1, by rw [hc1, hni, ha]; push_cast; exact (hA e he).2.2⟩
      hD := fun μ' ν' x hx hy => by rw [hc2, hni, ha]; push_cast; exact hD μ' ν' x hx hy }
  have hηc1 : η * c1 = a / ni := by rw [hc1]; field_simp
  have hηc2 : η ^ 2 * c2 = a / ni ^ 2 := by rw [hc2]; field_simp
  have hsmall : η * c1 ≤ 1 := by
    rw [hηc1, div_le_iff₀ hni0]; nlinarith
  have hpl := cube_plaq hη K hsmall (y, ν, μ) ⟨b1, b2, b3, b4⟩
  rw [dv_pw_gauge] at hpl
  -- the level: `j0 ≤ i + 1`
  have hy2 : y ∉ S.Om (i + 2) := by
    rcases hq.1.2.2.1 b1.1 with hy | hy
    · intro h; exact hy.2 (AdalyFormal.M1.om_anti hS (by omega) h)
    · exact hy.2
  have hj0 : j0 ≤ i + 1 := by
    by_contra hc
    exact hy2 (AdalyFormal.M1.om_anti hS (by omega) h1)
  have hpow : (ell : ℝ) ^ (2 * j0) ≤ (ell : ℝ) ^ 2 * ni ^ 2 := by
    rw [hni, ← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ hl (by omega)
  have hpos : 0 < (ell : ℝ) ^ (2 * j0) := by positivity
  have hN : 0 ≤ 2 * a + (4 * Real.pi + 2) * a ^ 2 := by have := Real.pi_pos; positivity
  calc dv (pw 1 U y ν μ) ≤ 2 * (η ^ 2 * c2) + (4 * Real.pi + 2) * (η * c1) ^ 2 := hpl
    _ = (2 * a + (4 * Real.pi + 2) * a ^ 2) / ni ^ 2 := by rw [hηc2, hηc1]; field_simp
    _ ≤ (ell : ℝ) ^ 2 * (2 * a + (4 * Real.pi + 2) * a ^ 2) / (ell : ℝ) ^ (2 * j0) := by
        rw [div_le_div_iff₀ (by positivity) hpos]
        nlinarith

/-- **`HolRegime` at `U` for the printed class** (plaquette coverage + per-cube regularity). -/
theorem holRegime_classACΦ :
    AdalyFormal.M1IMS.HolRegime S ell k U
      ((ell : ℝ) ^ 2 * (2 * (((12 : ℕ) : ℝ) * M * α₀) + (4 * Real.pi + 2) * (((12 : ℕ) : ℝ) * M * α₀) ^ 2)) := by
  apply AdalyFormal.M1GaugeW4.holRegime_of_plaq (by omega) U
  intro j0 _ y ν μ h1 h2 h3 h4
  rcases lt_trichotomy ν μ with hlt | heq | hgt
  · exact plaq_class_ltACΦ hS hell hη hα ha1 hP hC j0 y ν μ hlt h1 h2 h3 h4
  · subst heq
    rw [pw_diag]
    have : dv (1 : SU2) = 0 := by unfold dv; simp
    rw [this]
    have := Real.pi_pos
    positivity
  · have h4' : periodicLatticeShift (periodicLatticeShift y μ) ν ∈ S.Om j0 := by rw [shift_comm]; exact h4
    rw [show pw 1 U y ν μ = (pw 1 U y μ ν)⁻¹ by rw [pw_swap], dv_inv]
    exact plaq_class_ltACΦ hS hell hη hα ha1 hP hC j0 y μ ν hgt h1 h3 h2 h4'

end hol

end MXQ.M2Route

