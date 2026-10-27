import GenKComparison
import AdalyFormal.Balaban.CovariantDoor
/-! Physical, depth-independent perturbation bounds for the *linear covariant*
curl and line average. No identification with nonflat QjInChart, G1, or (3.156).
The final estimate deliberately retains the fine-field mass remainder. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace HConstruction.RegU
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo curlCovariantLM)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.RegularUQChain (coarseDriftEnergy_le)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open HConstruction.GenK (fineExtent fineTiling unitField bonds Fine Unit)
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- Physical fine L2 norm squared at mesh 1/n. -/
def mass {L : PeriodicLatticeExtent} (n : ℕ) (A : Bond L → SuTwo) : ℝ :=
  (1/(n:ℝ)^3) * bondEnergy A

def energy {L : PeriodicLatticeExtent} (n : ℕ)
    (U : PeriodicLinkConfiguration SU2 L) (A : Bond L → SuTwo) : ℝ :=
  (1/(n:ℝ)) * plaqEnergy (curlCovariantLM U A)

/-- A GLOBAL, physical smallness condition, not the local cube class. -/
def Small {L : PeriodicLatticeExtent} (n : ℕ) (α : ℝ)
    (U : PeriodicLinkConfiguration SU2 L) : Prop := frobSupBond U ≤ α/(n:ℝ)

variable {L : PeriodicLatticeExtent} {n : ℕ} {α : ℝ}

/-- The apparent n-growth cancels against eta in the link displacement. -/
theorem curl_drift_physical (hn : 0 < n) (hα : 0 ≤ α)
    (U : PeriodicLinkConfiguration SU2 L) (hU : Small n α U) (A : Bond L → SuTwo) :
    (1/(n:ℝ)) * plaqEnergy (curlDrift U A) ≤ 32*α^2*mass n A := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hb := plaqEnergy_curlDrift_le U A (α/(n:ℝ)) (div_nonneg hα hnR.le)
    (fun b => (frobNorm_le_frobSupBond U b).trans hU)
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ 1/(n:ℝ))
  calc (1/(n:ℝ)) * plaqEnergy (curlDrift U A)
      ≤ (1/(n:ℝ)) * (32*(α/(n:ℝ))^2*bondEnergy A) := hh
    _ = 32*α^2*mass n A := by unfold mass; field_simp

/-- Incoming length-n covariant average, with constant fixed before n and volume. -/
theorem q_drift_physical (hn : 0 < n) (hdvd : ∀ μ : Fin 3, n ∣ L μ+1)
    (U : PeriodicLinkConfiguration SU2 L) (hU : Small n α U)
    (A : Bond L → SuTwo) :
    (∑ c : CoarseBond L n,
      ‖lineCoarseRestrictCov (trivialU L) n A c - lineCoarseRestrictCov U n A c‖^2)
        ≤ 64*α^2*mass n A := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hsq : frobSupBond U ^ 2 ≤ (α/(n:ℝ))^2 :=
    pow_le_pow_left₀ (frobSupBond_nonneg U) hU 2
  calc _ ≤ (64/(n:ℝ))*frobSupBond U^2*bondEnergy A := coarseDriftEnergy_le U hn hdvd A
    _ ≤ (64/(n:ℝ))*(α/(n:ℝ))^2*bondEnergy A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity))
        (bondEnergy_nonneg A)
    _ = 64*α^2*mass n A := by unfold mass; field_simp

/-- Young's inequality before minimization; a mass error is essential. -/
theorem flat_energy_le (hn : 0 < n) (hα : 0 ≤ α)
    (U : PeriodicLinkConfiguration SU2 L) (hU : Small n α U) (A : Bond L → SuTwo) :
    energy n (trivialU L) A ≤ 2*energy n U A + 64*α^2*mass n A := by
  have hp : plaqEnergy (curlCovariantLM (trivialU L) A) ≤
      2*plaqEnergy (curlCovariantLM U A) + 2*plaqEnergy (curlDrift U A) := by
    unfold plaqEnergy
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p _
    have h := AdalyFormal.Balaban.CovariantDoor.norm_sq_young
      (curlCovariantLM (trivialU L) A p) (curlCovariantLM U A p) (by norm_num : (0:ℝ)<1)
    norm_num at h
    have he : ‖curlDrift U A p‖ = ‖curlCovariantLM (trivialU L) A p - curlCovariantLM U A p‖ :=
      norm_sub_rev _ _
    rw [he]
    exact h
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 1/(n:ℝ))
  have hd := curl_drift_physical hn hα U hU A
  unfold energy
  nlinarith

variable (M : PeriodicLatticeExtent) (hn : 0 < n)

/-- The natural covariant extension of GenK's incoming map, BEFORE any source
identification. At U=1 it is the actual certified incoming map. -/
def incomingField (U : PeriodicLinkConfiguration SU2 (fineExtent M n))
    (A : Bond (fineExtent M n) → SuTwo) : Bond M → SuTwo :=
  unitField M hn (lineCoarseRestrictCov U n A)

theorem incomingField_flat (A : Fine M (n := n)) :
    incomingField M hn (trivialU _) (bfl2Equiv A) = bfl2Equiv (GenK.incoming M hn A) := rfl

theorem bond_reindex (B : CoarseBond (fineExtent M n) n → SuTwo) :
    bondEnergy (unitField M hn B) = ∑ c, ‖B c‖^2 :=
  Equiv.sum_comp (bonds M hn) (fun c => ‖B c‖^2)

theorem incoming_drift
    (U : PeriodicLinkConfiguration SU2 (fineExtent M n)) (hU : Small n α U)
    (A : Bond (fineExtent M n) → SuTwo) :
    bondEnergy (incomingField M hn U A - incomingField M hn (trivialU _) A)
      ≤ 64*α^2*mass n A := by
  change bondEnergy (unitField M hn (fun c => lineCoarseRestrictCov U n A c -
    lineCoarseRestrictCov (trivialU _) n A c)) ≤ _
  rw [bond_reindex]
  simp only [norm_sub_rev (lineCoarseRestrictCov U n A _) (lineCoarseRestrictCov (trivialU _) n A _)]
  exact q_drift_physical hn (fineTiling M hn) U hU A

/-- A genuine generic-depth perturbative Stokes estimate, with an UNABSORBED
fine mass term. 4224=4*32+2*32*64; it does not grow with incoming depth. -/
theorem stokes_with_mass (hα : 0 ≤ α)
    (U : PeriodicLinkConfiguration SU2 (fineExtent M n)) (hU : Small n α U)
    (A : Bond (fineExtent M n) → SuTwo) :
    GenK.curlEnergy (incomingField M hn U A) ≤
      4*energy n U A + 4224*α^2*mass n A := by
  have hflat : GenK.curlEnergy (incomingField M hn (trivialU _) A) ≤
      energy n (trivialU _) A := by
    have h := GenK.comparison M hn (bfl2Equiv.symm A)
    rw [← incomingField_flat, bfl2Equiv.apply_symm_apply] at h
    have he : GenK.fineEnergy M (bfl2Equiv.symm A) = energy n (trivialU _) A := by
      rw [GenK.fineEnergy, GenK.curl_norm, bfl2Equiv.apply_symm_apply]
      unfold energy
      rw [curlCovariantLM_trivialU_eq_flatCurlLM]
      rfl
    rwa [he] at h
  have hy := AdalyFormal.Balaban.CovariantDoor.curlEnergy_young
    (incomingField M hn U A) (incomingField M hn (trivialU _) A) (by norm_num : (0:ℝ)<1)
  norm_num at hy
  have hc := AdalyFormal.Balaban.WitnessInequality.plaqEnergy_flatCurl_le
    (incomingField M hn U A - incomingField M hn (trivialU _) A)
  have hq := incoming_drift M hn U hU A
  have he := flat_energy_le hn hα U hU A
  change GenK.curlEnergy (incomingField M hn U A) ≤
    2*GenK.curlEnergy (incomingField M hn (trivialU _) A) +
      2*GenK.curlEnergy (incomingField M hn U A - incomingField M hn (trivialU _) A) at hy
  change GenK.curlEnergy (incomingField M hn U A - incomingField M hn (trivialU _) A)
    ≤ 32*bondEnergy (incomingField M hn U A - incomingField M hn (trivialU _) A) at hc
  nlinarith

/-- Outgoing fixed-ratio Poincare DOES have perturbation room: use its nonzero
Q term instead of pretending the flat kernel is the covariant kernel. -/
theorem outgoing_poincare (hM : ∀ μ : Fin 3, 4 ≤ M μ)
    (heven : ∀ μ : Fin 3, 2 ∣ M μ+1) {β : ℝ}
    (V : PeriodicLinkConfiguration SU2 M) (hV : frobSupBond V ≤ β)
    (B : Bond M → SuTwo) (hAx : GenK.Axial B)
    (hQ : ∀ c, lineCoarseRestrictCov V 2 B c = 0) :
    (1/1728-64*β^2)*bondEnergy B ≤ GenK.curlEnergy B := by
  have hp := GenK.lemma24 hM heven B hAx
  have hq := coarseDriftEnergy_le V (by decide : 0<2) heven B
  simp only [hQ,sub_zero,lineCoarseRestrictCov_trivialU] at hq
  change GenK.qEnergy B ≤ (64/(2:ℝ))*frobSupBond V^2*bondEnergy B at hq
  have hs := pow_le_pow_left₀ (frobSupBond_nonneg V) hV 2
  have hm := mul_le_mul_of_nonneg_right hs (bondEnergy_nonneg B)
  change (1/1728:ℝ)*bondEnergy B ≤ _ at hp
  norm_num only at hq
  nlinarith

/-- Best completed direct route: genuine incoming depth and a moving outgoing
kernel, but the fine mass remainder is still present. NOT a coercivity theorem
for Delta_k or for its reduced precision. -/
theorem every_extension_defect (hM : ∀ μ : Fin 3, 4 ≤ M μ)
    (heven : ∀ μ : Fin 3, 2 ∣ M μ+1) (hα : 0 ≤ α)
    (U : PeriodicLinkConfiguration SU2 (fineExtent M n)) (hU : Small n α U)
    {β : ℝ} (V : PeriodicLinkConfiguration SU2 M) (hV : frobSupBond V ≤ β)
    (A : Bond (fineExtent M n) → SuTwo)
    (hAx : GenK.Axial (incomingField M hn U A))
    (hQ : ∀ c, lineCoarseRestrictCov V 2 (incomingField M hn U A) c = 0) :
    (1/1728-64*β^2)*bondEnergy (incomingField M hn U A) ≤
      4*energy n U A + 4224*α^2*mass n A :=
  (outgoing_poincare M hM heven V hV _ hAx hQ).trans (stokes_with_mass M hn hα U hU A)

/-- A free Young parameter prevents the fixed factor-four loss at alpha=0. -/
theorem flat_energy_young {L : PeriodicLatticeExtent} {n : ℕ} {α ε : ℝ}
    (hn : 0 < n) (hα : 0 ≤ α) (hε : 0 < ε)
    (U : PeriodicLinkConfiguration SU2 L) (hU : Small n α U) (A : Bond L → SuTwo) :
    energy n (trivialU L) A ≤ (1+ε)*energy n U A +
      (1+1/ε)*32*α^2*mass n A := by
  have hp : plaqEnergy (curlCovariantLM (trivialU L) A) ≤
      (1+ε)*plaqEnergy (curlCovariantLM U A) + (1+1/ε)*plaqEnergy (curlDrift U A) := by
    unfold plaqEnergy
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p _
    have h := AdalyFormal.Balaban.CovariantDoor.norm_sq_young
      (curlCovariantLM (trivialU L) A p) (curlCovariantLM U A p) hε
    have he : ‖curlDrift U A p‖ = ‖curlCovariantLM (trivialU L) A p - curlCovariantLM U A p‖ :=
      norm_sub_rev _ _
    rw [he]
    exact h
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 1/(n:ℝ))
  have hd := mul_le_mul_of_nonneg_left (curl_drift_physical hn hα U hU A)
    (by positivity : (0:ℝ) ≤ 1+1/ε)
  unfold energy
  nlinarith

/-- The actual continuity-shaped output of Strategy A: multiplicative loss
(1+alpha)^2 tends to one; the fine mass tax is O(alpha), uniformly in n. -/
theorem stokes_continuous (hα : 0 < α)
    (U : PeriodicLinkConfiguration SU2 (fineExtent M n)) (hU : Small n α U)
    (A : Bond (fineExtent M n) → SuTwo) :
    GenK.curlEnergy (incomingField M hn U A) ≤
      (1+α)^2*energy n U A + 32*α*(1+α)*(65+α)*mass n A := by
  have hflat : GenK.curlEnergy (incomingField M hn (trivialU _) A) ≤
      energy n (trivialU _) A := by
    have h := GenK.comparison M hn (bfl2Equiv.symm A)
    rw [← incomingField_flat, bfl2Equiv.apply_symm_apply] at h
    have he : GenK.fineEnergy M (bfl2Equiv.symm A) = energy n (trivialU _) A := by
      rw [GenK.fineEnergy, GenK.curl_norm, bfl2Equiv.apply_symm_apply]
      unfold energy
      rw [curlCovariantLM_trivialU_eq_flatCurlLM]
      rfl
    rwa [he] at h
  have hy := AdalyFormal.Balaban.CovariantDoor.curlEnergy_young
    (incomingField M hn U A) (incomingField M hn (trivialU _) A) hα
  change GenK.curlEnergy (incomingField M hn U A) ≤
    (1+α)*GenK.curlEnergy (incomingField M hn (trivialU _) A) +
      (1+1/α)*GenK.curlEnergy (incomingField M hn U A - incomingField M hn (trivialU _) A) at hy
  have hc := AdalyFormal.Balaban.WitnessInequality.plaqEnergy_flatCurl_le
    (incomingField M hn U A - incomingField M hn (trivialU _) A)
  change GenK.curlEnergy (incomingField M hn U A - incomingField M hn (trivialU _) A)
    ≤ 32*bondEnergy (incomingField M hn U A - incomingField M hn (trivialU _) A) at hc
  have hq := incoming_drift M hn U hU A
  have he := flat_energy_young hn hα.le hα U hU A
  have hcq : GenK.curlEnergy (incomingField M hn U A - incomingField M hn (trivialU _) A)
      ≤ 2048*α^2*mass n A := by linarith
  have h1 := mul_le_mul_of_nonneg_left (hflat.trans he) (by positivity : (0:ℝ)≤1+α)
  have h2 := mul_le_mul_of_nonneg_left hcq (by positivity : (0:ℝ)≤1+1/α)
  have hid : (1+α)*((1+α)*energy n U A + (1+1/α)*32*α^2*mass n A) +
      (1+1/α)*(2048*α^2*mass n A) =
      (1+α)^2*energy n U A + 32*α*(1+α)*(65+α)*mass n A := by
    field_simp
    ring
  linarith

/-- No mass-to-coarse estimate is hidden here. Both nonflat parameters are
field smallness budgets, not hypotheses that assert the desired form bound. -/
theorem every_extension_continuous (hM : ∀ μ : Fin 3, 4 ≤ M μ)
    (heven : ∀ μ : Fin 3, 2 ∣ M μ+1) (hα : 0 < α)
    (U : PeriodicLinkConfiguration SU2 (fineExtent M n)) (hU : Small n α U)
    {β : ℝ} (V : PeriodicLinkConfiguration SU2 M) (hV : frobSupBond V ≤ β)
    (A : Bond (fineExtent M n) → SuTwo)
    (hAx : GenK.Axial (incomingField M hn U A))
    (hQ : ∀ c, lineCoarseRestrictCov V 2 (incomingField M hn U A) c = 0) :
    (1/1728-64*β^2)*bondEnergy (incomingField M hn U A) ≤
      (1+α)^2*energy n U A + 32*α*(1+α)*(65+α)*mass n A :=
  (outgoing_poincare M hM heven V hV _ hAx hQ).trans
    (stokes_continuous M hn hα U hU A)

end HConstruction.RegU
