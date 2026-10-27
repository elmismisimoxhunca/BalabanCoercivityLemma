import MF2
import MA3

/-!
# MA4 -- the FLAT floor on the good unit plaquettes (lane m1_assembly_20261014)

`flat_floor_good`: for `B~ in Lambda~` (touching support, `Lambda = B(Lambda')`, `Lambda` deep in `Omega_k` (`LambdaOK`), `3 <= R M`),
`B1 = C_1 B~` (flat `C`) and ANY unit field `Bf`:
  `(1/54) ell^-5 ||B~||^2 <= 2 sum_{q good} ||curl Bf q||^2 + 64 sum_{b : tail embedded in Omega_k} ||Bf b - B1 b||^2`.
(Adaptation of MF2 `flat_floor_pert`: the curl of `B1` vanishes off the good plaquettes, FE5a `curl_zero_of_not_good`.)
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.M1Assembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.GenuineU1
open AdalyFormal.FlatEllGeneral
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy)
open AdalyFormal.M0Finish (sq_sub_le2)

/-- the four bonds of a good plaquette have tails embedded in `Omega_k`. -/
theorem good_bonds_tail {ell k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
    (q : PeriodicLatticePlaquette Lu) (hg : ∀ c, InBox q.1 c → embY ell k Lu hell c ∈ S.Om k) :
    ∀ e : Bond Lu, (e = (q.1, q.2.1.1) ∨ e = (periodicLatticeShift q.1 q.2.1.1, q.2.1.2) ∨
        e = (periodicLatticeShift q.1 q.2.1.2, q.2.1.1) ∨ e = (q.1, q.2.1.2)) →
        embY ell k Lu hell e.1 ∈ S.Om k := by
  intro e he
  have hμν : q.2.1.1 ≠ q.2.1.2 := ne_of_lt q.2.2
  rcases he with rfl | rfl | rfl | rfl
  · exact hg _ (self_inBox _)
  · exact hg _ (shift_inBox _ _)
  · exact hg _ (shift_inBox _ _)
  · exact hg _ (self_inBox _)

open Classical in
theorem flat_floor_good {Lu : PeriodicLatticeExtent} {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    {Lam : Set (PeriodicLatticeSite Lu)} (hLB : LamBlockSum ell Lam)
    (hb : Function.Bijective (H0 Lam (q1SU2 ell))) (Bt : Bond Lu → SuTwo)
    (hBt : OnLambdaTildeIn Lam ell Bt) (hBT : OnLambdaT Lam Bt)
    {M R k : ℕ} {S : Tower (scaleUp ell k Lu)} (hRM : 3 ≤ R * M) (hL : LambdaOK ell M R k S Lam)
    (Bf : Bond Lu → SuTwo) :
    (1 / 54 * (1 / (ell : ℝ) ^ 5)) * bondEnergy Bt
      ≤ 2 * ∑ q ∈ (Finset.univ : Finset (PeriodicLatticePlaquette Lu)).filter
              (fun q => ∀ c, InBox q.1 c → embY ell k Lu (by omega) c ∈ S.Om k), ‖flatCurlValue Bf q‖ ^ 2
        + 64 * ∑ b ∈ (Finset.univ : Finset (Bond Lu)).filter (fun b => embY ell k Lu (by omega) b.1 ∈ S.Om k),
              ‖Bf b - Cop Lam (q1SU2 ell) Bt b‖ ^ 2 := by
  have hell : 0 < ell := by omega
  have hu : ∀ μ, 1 ≤ Lu μ := fun μ => by have := hstrict μ; omega
  obtain ⟨hax, hker, hen, hsup⟩ := AdalyFormal.FlatEllGeneral.Cop_props_gen hell hd hu hLB hb Bt hBt hBT
  have h24 := AdalyFormal.FlatEllGeneral.lemma24Su_sharp hell2 hstrict hd
    (Cop Lam (q1SU2 ell) Bt) hax hker
  set B1 := Cop Lam (q1SU2 ell) Bt with hB1
  set Qg : Finset (PeriodicLatticePlaquette Lu) := Finset.univ.filter
    (fun q => ∀ c, InBox q.1 c → embY ell k Lu hell c ∈ S.Om k) with hQg
  set E : Finset (Bond Lu) := Finset.univ.filter (fun b => embY ell k Lu hell b.1 ∈ S.Om k) with hE
  set d : Bond Lu → SuTwo := fun b => Bf b - B1 b with hd'
  set d' : Bond Lu → SuTwo := fun b => if b ∈ E then d b else 0 with hdd'
  -- the curl of B1 vanishes off the good plaquettes
  have hsumB1 : ∑ p : PeriodicLatticePlaquette Lu, ‖flatCurlValue B1 p‖ ^ 2
      = ∑ q ∈ Qg, ‖flatCurlValue B1 q‖ ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun q _ hq => ?_)
    have hnq : ¬ ∀ c, InBox q.1 c → embY ell k Lu hell c ∈ S.Om k := fun h =>
      hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [AdalyFormal.FlatEllGeneral.curl_zero_of_not_good hell hu hRM hL B1 hsup q hnq]; simp
  -- on good plaquettes the curl of d is the curl of d'
  have hcurld : ∀ q ∈ Qg, flatCurlValue d q = flatCurlValue d' q := by
    intro q hq
    have hg := (Finset.mem_filter.mp hq).2
    have hmem := good_bonds_tail hell q hg
    have hE' : ∀ e : Bond Lu, (e = (q.1, q.2.1.1) ∨ e = (periodicLatticeShift q.1 q.2.1.1, q.2.1.2) ∨
        e = (periodicLatticeShift q.1 q.2.1.2, q.2.1.1) ∨ e = (q.1, q.2.1.2)) → d' e = d e := by
      intro e he
      have hmE : e ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem e he⟩
      simp only [hdd']
      exact if_pos hmE
    unfold flatCurlValue
    rw [hE' (q.1, q.2.1.1) (Or.inl rfl), hE' (periodicLatticeShift q.1 q.2.1.1, q.2.1.2) (Or.inr (Or.inl rfl)),
      hE' (periodicLatticeShift q.1 q.2.1.2, q.2.1.1) (Or.inr (Or.inr (Or.inl rfl))),
      hE' (q.1, q.2.1.2) (Or.inr (Or.inr (Or.inr rfl)))]
  have hpt : ∀ q ∈ Qg, ‖flatCurlValue B1 q‖ ^ 2 ≤ 2 * ‖flatCurlValue Bf q‖ ^ 2 + 2 * ‖flatCurlValue d' q‖ ^ 2 := by
    intro q hq
    have e1 : flatCurlValue B1 q = flatCurlValue Bf q - flatCurlValue d q := by
      simp only [flatCurlValue, hd']; abel
    rw [e1, hcurld q hq]
    exact sq_sub_le2 _ _
  have h1 : ∑ q ∈ Qg, ‖flatCurlValue B1 q‖ ^ 2
      ≤ 2 * ∑ q ∈ Qg, ‖flatCurlValue Bf q‖ ^ 2 + 2 * ∑ q ∈ Qg, ‖flatCurlValue d' q‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpt
  have h2 : ∑ q ∈ Qg, ‖flatCurlValue d' q‖ ^ 2 ≤ ∑ p : PeriodicLatticePlaquette Lu, ‖flatCurlValue d' p‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => sq_nonneg _)
  have h3 : plaqEnergy (flatCurlValue d') ≤ 32 * bondEnergy d' :=
    AdalyFormal.Balaban.WitnessInequality.plaqEnergy_flatCurl_le d'
  unfold plaqEnergy bondEnergy at h3
  have h4 : ∑ b : Bond Lu, ‖d' b‖ ^ 2 = ∑ b ∈ E, ‖d b‖ ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ E) (fun b _ hb => by simp [hdd', hb])]
    exact Finset.sum_congr rfl (fun b hb => by simp [hdd', hb])
  have hγ : (0 : ℝ) ≤ 1 / 54 * (1 / (ell : ℝ) ^ 5) := by positivity
  have h5 := mul_le_mul_of_nonneg_left hen hγ
  have hdE : ∑ b ∈ E, ‖d b‖ ^ 2 = ∑ b ∈ E, ‖Bf b - B1 b‖ ^ 2 := rfl
  rw [hsumB1] at h24
  rw [h4] at h3
  nlinarith [h24, h1, h2, h3, h5, hdE]

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.good_bonds_tail
#print axioms AdalyFormal.M1Assembly.flat_floor_good
