import NP8

/-!
# NP9 -- the cut-off comparison configuration (m1_patch_nonflat, 2026-10-14)

Input: a configuration `U` with ONE chart `U^g e = exp((η i) A e)` (`A e` Hermitian traceless) — lane B's `M1Regular` —
and a real cut-off `χ` with `0 ≤ χ ≤ 1`, `|χ(x+e_μ) − χ x| ≤ lip`.  Define
* `Achi e = χ(e.1) • A e`,  `Vchi e = su2Exp((η i) Achi e)`  (an honest SU(2) link: the chart field is in `su(2)`),
* `Upc = (Vchi)^{g⁻¹}`  (the comparison configuration).
Facts:
* `gauge_Upc` : `Upc^g = Vchi`;   `Upc_eq` : `Upc e = U e` wherever `χ(e.1) = 1`;
* `chart_Upc` : if `frobNorm (A e) < c1` for `e.1 ∈ Zr`, `frobNorm (η⁻¹ (A(x+e_μ,ν) − A(x,ν))) < c2` for `x, x+e_μ ∈ Zr`, and
  the support of `χ` lies in `Zr` with its unit neighbours, then `Upc` has a `CubeChart` on ALL bonds with constants
  `(η, c1, c2 + lip c1/η)`;
* `Vchi_link` : `dv (Vchi e) ≤ η c1`;  `Vchi_plaq` : `dv (pw 1 Vchi) ≤ 2 η² c2' + (4π+2)(η c1)²` (`η c1 ≤ 1`);
* `Vchi_diff` : `frobNorm (Vchi(x,μ) − Vchi(x−e_μ,μ)) ≤ η² c2' + 2π (η c1)²` (`η c1 ≤ 1`)  — first differences only.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobNorm_nonneg frobSq_mul_right_isometry)
open AdalyFormal.Balaban.SuTwoLogExp (su2Exp M2)
open AdalyFormal.Balaban.Bch2 (IsSu2)
open AdalyFormal.CurvBlock (dv pw HTm CubeChart chart chart_exp cube_link cube_plaq diff_chart dv_exp_div_le)

variable {L : PeriodicLatticeExtent}

/-- the cut-off chart field. -/
noncomputable def Achi (A : Bond L → M2) (χ : PeriodicLatticeSite L → ℝ) (e : Bond L) : M2 := (χ e.1) • A e

/-- the cut-off configuration in the chart gauge. -/
noncomputable def Vchi (η : ℝ) (A : Bond L → M2) (χ : PeriodicLatticeSite L → ℝ) : Cfg L :=
  fun e => su2Exp (((η : ℂ) * Complex.I) • Achi A χ e)

/-- the comparison configuration. -/
noncomputable def Upc (η : ℝ) (g : PeriodicLatticeSite L → SU2) (A : Bond L → M2) (χ : PeriodicLatticeSite L → ℝ) :
    Cfg L :=
  periodicGaugeTransform (fun x => (g x)⁻¹) (Vchi η A χ)

theorem gauge_Upc (η : ℝ) (g : PeriodicLatticeSite L → SU2) (A : Bond L → M2) (χ : PeriodicLatticeSite L → ℝ) :
    periodicGaugeTransform g (Upc η g A χ) = Vchi η A χ := by
  funext e
  unfold Upc periodicGaugeTransform
  group

theorem HTm_smul (r : ℝ) {X : M2} (h : HTm X) : HTm (r • X) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, h.1, star_trivial]
  · rw [Matrix.trace_smul, h.2, smul_zero]

theorem frobNorm_rsmul (r : ℝ) (X : M2) : frobNorm (r • X) = |r| * frobNorm X :=
  AdalyFormal.Balaban.Bch2.frobNorm_smul r X

section chartsec
variable (η : ℝ) (hη : 0 < η) (U : Cfg L) (g : PeriodicLatticeSite L → SU2) (A : Bond L → M2)
  (hHT : ∀ e, HTm (A e))
  (hUA : ∀ e, ((periodicGaugeTransform g U e : SU2) : M2) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
  (χ : PeriodicLatticeSite L → ℝ) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)

include hη hHT in
theorem Vchi_coe (e : Bond L) :
    ((Vchi η A χ e : SU2) : M2) = NormedSpace.exp (((η : ℂ) * Complex.I) • Achi A χ e) := by
  obtain ⟨hX, -⟩ := chart η hη.le (Achi A χ e) (HTm_smul _ (hHT e))
  exact AdalyFormal.Balaban.SuTwoLogExp.su2Exp_of_mem
    (AdalyFormal.Balaban.ClassPropagationUbar.exp_mem_special hX.1 hX.2)

include hη hHT hUA in
/-- the comparison configuration agrees with `U` where the cut-off is `1`. -/
theorem Upc_eq (e : Bond L) (h1 : χ e.1 = 1) : Upc η g A χ e = U e := by
  have hV : Vchi η A χ e = periodicGaugeTransform g U e := by
    obtain ⟨hX, -⟩ := chart η hη.le (A e) (hHT e)
    have h2 := chart_exp _ hX _ (hUA e)
    rw [h2]
    show su2Exp (((η : ℂ) * Complex.I) • ((χ e.1) • A e)) = _
    rw [h1, one_smul]
  unfold Upc
  show (g e.1)⁻¹ * Vchi η A χ e * ((g (periodicLatticeShift e.1 e.2))⁻¹)⁻¹ = U e
  rw [hV]
  unfold periodicGaugeTransform
  group

variable (Zr : Set (PeriodicLatticeSite L)) (c1 c2 lip : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) (hlip0 : 0 ≤ lip)
  (hZ1 : ∀ e : Bond L, e.1 ∈ Zr → frobNorm (A e) < c1)
  (hZ2 : ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L), x ∈ Zr → periodicLatticeShift x μ ∈ Zr →
    frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) < c2)
  (hsupp : ∀ x, χ x ≠ 0 → x ∈ Zr ∧ ∀ μ : Fin 3, periodicLatticeShift x μ ∈ Zr ∧ periodicLatticeShiftBack x μ ∈ Zr)
  (hlip : ∀ x (μ : Fin 3), |χ (periodicLatticeShift x μ) - χ x| ≤ lip)

include hη hHT hχ0 hχ1 hc1 hc2 hlip0 hZ1 hZ2 hsupp hlip in
/-- **the chart of the comparison configuration** (all bonds). -/
noncomputable def chart_Upc : CubeChart (Upc η g A χ) (fun _ => True) η c1 (c2 + lip * c1 / η) where
  g := g
  A := Achi A χ
  hA := fun e _ => by
    refine ⟨HTm_smul _ (hHT e), ?_, ?_⟩
    · rw [gauge_Upc]; exact Vchi_coe η hη A hHT χ e
    · show frobNorm ((χ e.1) • A e) < c1
      rw [frobNorm_rsmul, abs_of_nonneg (hχ0 _)]
      by_cases h0 : χ e.1 = 0
      · rw [h0, zero_mul]; exact hc1
      · have := hZ1 e (hsupp e.1 h0).1
        calc χ e.1 * frobNorm (A e) ≤ 1 * frobNorm (A e) :=
              mul_le_mul_of_nonneg_right (hχ1 _) (frobNorm_nonneg _)
          _ < c1 := by rw [one_mul]; exact this
  hD := fun μ ν x _ _ => by
    show frobNorm ((η⁻¹ : ℝ) • ((χ (periodicLatticeShift x μ)) • A (periodicLatticeShift x μ, ν) - (χ x) • A (x, ν)))
      < c2 + lip * c1 / η
    by_cases h0 : χ x = 0 ∧ χ (periodicLatticeShift x μ) = 0
    · rw [h0.1, h0.2, zero_smul, zero_smul, sub_zero, smul_zero]
      have h00 : frobNorm (0 : M2) = 0 := by
        unfold AdalyFormal.Balaban.RMapLipschitz.frobNorm AdalyFormal.Balaban.RMapLipschitz.frobSq; simp
      rw [h00]
      have : (0 : ℝ) < c2 + lip * c1 / η := by positivity
      exact this
    · have hxZ : x ∈ Zr ∧ periodicLatticeShift x μ ∈ Zr := by
        by_cases hx : χ x = 0
        · have hx' : χ (periodicLatticeShift x μ) ≠ 0 := fun h => h0 ⟨hx, h⟩
          obtain ⟨h1, h2⟩ := hsupp _ hx'
          have := (h2 μ).2
          rw [AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack_shift] at this
          exact ⟨this, h1⟩
        · obtain ⟨h1, h2⟩ := hsupp _ hx
          exact ⟨h1, (h2 μ).1⟩
      have e1 : (η⁻¹ : ℝ) • ((χ (periodicLatticeShift x μ)) • A (periodicLatticeShift x μ, ν) - (χ x) • A (x, ν))
          = (χ (periodicLatticeShift x μ)) • ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
            + ((χ (periodicLatticeShift x μ) - χ x) * η⁻¹) • A (x, ν) := by
        module
      rw [e1]
      have hA1 := hZ1 (x, ν) hxZ.1
      have hA2 := hZ2 μ ν x hxZ.1 hxZ.2
      have t1 : frobNorm ((χ (periodicLatticeShift x μ)) • ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))))
          < c2 := by
        rw [frobNorm_rsmul, abs_of_nonneg (hχ0 _)]
        calc χ (periodicLatticeShift x μ) * frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
            ≤ 1 * frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) :=
              mul_le_mul_of_nonneg_right (hχ1 _) (frobNorm_nonneg _)
          _ < c2 := by rw [one_mul]; exact hA2
      have t2 : frobNorm (((χ (periodicLatticeShift x μ) - χ x) * η⁻¹) • A (x, ν)) ≤ lip * c1 / η := by
        rw [frobNorm_rsmul, abs_mul, abs_of_pos (inv_pos.mpr hη)]
        have := hlip x μ
        calc |χ (periodicLatticeShift x μ) - χ x| * η⁻¹ * frobNorm (A (x, ν)) ≤ lip * η⁻¹ * c1 := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right this (by positivity)) hA1.le (frobNorm_nonneg _)
                (by positivity)
          _ = lip * c1 / η := by ring
      have tri := AdalyFormal.Balaban.Bch2.frobNorm_add_le
        ((χ (periodicLatticeShift x μ)) • ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))))
        (((χ (periodicLatticeShift x μ) - χ x) * η⁻¹) • A (x, ν))
      linarith

theorem frob_sub_eq_dv (V1 V2 : SU2) :
    frobNorm ((V1 : M2) - (V2 : M2)) = dv (V1 * V2⁻¹) := by
  unfold dv frobNorm
  congr 1
  have e : ((V1 * V2⁻¹ : SU2) : M2) - 1 = ((V1 : M2) - (V2 : M2)) * (V2 : M2)ᴴ := by
    rw [Submonoid.coe_mul, coe_inv_su2, Matrix.sub_mul, su2_mul_conj]
  rw [e, frobSq_mul_right_isometry _ _ (by rw [Matrix.conjTranspose_conjTranspose]; exact su2_conj_mul V2)]

include g hη hHT hχ0 hχ1 hc1 hc2 hlip0 hZ1 hZ2 hsupp hlip in
theorem Vchi_link (e : Bond L) : dv (Vchi η A χ e) ≤ η * c1 := by
  have h := cube_link hη (chart_Upc η hη g A hHT χ hχ0 hχ1 Zr c1 c2 lip hc1 hc2 hlip0 hZ1 hZ2 hsupp hlip) e trivial
  have hg : (chart_Upc η hη g A hHT χ hχ0 hχ1 Zr c1 c2 lip hc1 hc2 hlip0 hZ1 hZ2 hsupp hlip).g = g := rfl
  rw [hg, gauge_Upc] at h
  exact h

include g hη hHT hχ0 hχ1 hc1 hc2 hlip0 hZ1 hZ2 hsupp hlip in
theorem Vchi_plaq (hsmall : η * c1 ≤ 1) (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    dv (pw 1 (Vchi η A χ) y ν μ) ≤ 2 * (η ^ 2 * (c2 + lip * c1 / η)) + (4 * Real.pi + 2) * (η * c1) ^ 2 := by
  have h := cube_plaq hη (chart_Upc η hη g A hHT χ hχ0 hχ1 Zr c1 c2 lip hc1 hc2 hlip0 hZ1 hZ2 hsupp hlip) hsmall
    (y, ν, μ) ⟨trivial, trivial, trivial, trivial⟩
  have hg : (chart_Upc η hη g A hHT χ hχ0 hχ1 Zr c1 c2 lip hc1 hc2 hlip0 hZ1 hZ2 hsupp hlip).g = g := rfl
  rw [hg, gauge_Upc] at h
  exact h

include g hη hHT hχ0 hχ1 hc1 hc2 hlip0 hZ1 hZ2 hsupp hlip in
/-- **first differences of the comparison links**. -/
theorem Vchi_diff (hsmall : η * c1 ≤ 1) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    frobNorm (((Vchi η A χ (x, μ) : SU2) : M2) - ((Vchi η A χ (periodicLatticeShiftBack x μ, μ) : SU2) : M2))
      ≤ η ^ 2 * (c2 + lip * c1 / η) + 2 * Real.pi * (η * c1) ^ 2 := by
  set K := chart_Upc η hη g A hHT χ hχ0 hχ1 Zr c1 c2 lip hc1 hc2 hlip0 hZ1 hZ2 hsupp hlip with hK
  have hKA : K.A = Achi A χ := rfl
  have hX : ∀ e : Bond L, IsSu2 (((η : ℂ) * Complex.I) • Achi A χ e) ∧
      frobNorm (((η : ℂ) * Complex.I) • Achi A χ e) ≤ η * c1 := by
    intro e
    obtain ⟨hHTe, -, hn⟩ := K.hA e trivial
    rw [hKA] at hHTe hn
    obtain ⟨hXs, hXn⟩ := chart η hη.le (Achi A χ e) hHTe
    exact ⟨hXs, by rw [hXn]; exact mul_le_mul_of_nonneg_left hn.le hη.le⟩
  obtain ⟨h1s, h1n⟩ := hX (x, μ)
  obtain ⟨h2s, h2n⟩ := hX (periodicLatticeShiftBack x μ, μ)
  have hd : frobNorm (((η : ℂ) * Complex.I) • Achi A χ (x, μ)) +
      frobNorm (((η : ℂ) * Complex.I) • Achi A χ (periodicLatticeShiftBack x μ, μ)) ≤ 2 := by linarith
  have hdiff := diff_chart η hη _ _ _ (K.hD μ μ (periodicLatticeShiftBack x μ) trivial trivial)
  rw [hKA, periodicLatticeShift_shiftBack] at hdiff
  rw [frob_sub_eq_dv]
  refine (dv_exp_div_le h1s h2s hd).trans ?_
  have hp := Real.pi_pos
  have hm : frobNorm (((η : ℂ) * Complex.I) • Achi A χ (x, μ)) *
      frobNorm (((η : ℂ) * Complex.I) • Achi A χ (periodicLatticeShiftBack x μ, μ)) ≤ (η * c1) ^ 2 := by
    rw [sq]; exact mul_le_mul h1n h2n (frobNorm_nonneg _) (by positivity)
  nlinarith

end chartsec

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.gauge_Upc
#print axioms AdalyFormal.M1NonFlat.Vchi_coe
#print axioms AdalyFormal.M1NonFlat.Upc_eq
#print axioms AdalyFormal.M1NonFlat.chart_Upc
#print axioms AdalyFormal.M1NonFlat.frob_sub_eq_dv
#print axioms AdalyFormal.M1NonFlat.Vchi_link
#print axioms AdalyFormal.M1NonFlat.Vchi_plaq
#print axioms AdalyFormal.M1NonFlat.Vchi_diff
