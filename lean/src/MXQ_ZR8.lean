import MXQ_Base
import ZR8Class

/-!
# MXQ_ZR8 -- class-bond locality for the MIXED class (lane mixed_20261017)

`ClassBondQ` (MXQ_Base) is `∃ f ∈ Fm, ClassBond ell M f`.  Mixed versions of `ZR8Class.bothIn_classBond`, `classBond_bothIn`, `InstIneq_congr_class`, `InstAtWD_congr_class`.
-/
set_option autoImplicit false

namespace MXQ.StatementLaneR8
open MXQ.AllC (CF CubeFamOK)

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2 (BothIn Cfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open MXQ.AllC

variable {L : PeriodicLatticeExtent}

theorem classBond_bothInΦ {ell M R k : ℕ} {Fm : CF} {S : Tower L} (hS : Admissible ell M R k S) {e : Bond L}
    (he : ClassBondQ ell M Fm k S e) : BothIn (S.Om 0) e := by
  obtain ⟨sites, j, ⟨f, -, hq⟩, hcb⟩ := he
  exact classBond_bothIn hS ⟨sites, j, hq, hcb⟩

/-- with the mixed plaquette coverage, every `BothIn Ω₀` bond is class-constrained. -/
theorem bothIn_classBondΦ {ell M R k : ℕ} {Fm : CF} {S : Tower L} (hS : Admissible ell M R k S) (hM : 2 ≤ M)
    (hcov : CoversOmQ ell M Fm k S) {e : Bond L} (he : BothIn (S.Om 0) e) : ClassBondQ ell M Fm k S e := by
  have hdvd : ∀ κ : Fin 3, M ∣ L κ + 1 := fun κ => by
    have := hS.2.2.1 0 (Nat.zero_le _) κ; simpa [bigSide] using this
  have hbc : BlockClosed M (S.Om 0) := by
    have := hS.2.2.2.1 0 (Nat.zero_le _); simpa [bigSide] using this
  obtain ⟨p, hep, hall⟩ := plaq_of_bothIn hM hdvd hbc he
  obtain ⟨sites, j, hqΦ, hcb⟩ := hcov.2 p hall
  obtain ⟨f, hf, hq⟩ := hqΦ
  exact ⟨sites, j, ⟨f, hf, hq⟩, hcb e hep⟩

theorem InstIneq_congr_classΦ {ell k : ℕ} (hell0 : 0 < ell) (a : ℝ) {Lu : PeriodicLatticeExtent} (γ₀ : ℝ)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {M R : ℕ} {Fm : CF} (h : LocHyp ell M R k S Lam)
    (hM : 2 ≤ M) (hcov : CoversOmQ ell M Fm k S) {U U' : Cfg (scaleUp ell k Lu)}
    (hUU : ∀ e : Bond (scaleUp ell k Lu), ClassBondQ ell M Fm k S e → U e = U' e) :
    InstIneq ell k hell0 a Lu γ₀ S Lam U ↔ InstIneq ell k hell0 a Lu γ₀ S Lam U' :=
  InstIneq_congr hell0 a γ₀ h (fun e he => hUU e (bothIn_classBondΦ h.adm hM hcov he))

theorem InstAtWD_congr_classΦ {ell k : ℕ} (hell0 : 0 < ell) (a : ℝ) {Lu : PeriodicLatticeExtent} (γ₀ : ℝ)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {M R : ℕ} {Fm : CF} (h : LocHyp ell M R k S Lam)
    (hM : 2 ≤ M) (hcov : CoversOmQ ell M Fm k S) {U U' : Cfg (scaleUp ell k Lu)}
    (hUU : ∀ e : Bond (scaleUp ell k Lu), ClassBondQ ell M Fm k S e → U e = U' e) :
    InstAtWD ell k hell0 a Lu γ₀ S Lam U ↔ InstAtWD ell k hell0 a Lu γ₀ S Lam U' :=
  InstAtWD_congr hell0 a γ₀ h (fun e he => hUU e (bothIn_classBondΦ h.adm hM hcov he))

end MXQ.StatementLaneR8

#print axioms MXQ.StatementLaneR8.InstIneq_congr_classΦ
#print axioms MXQ.StatementLaneR8.InstAtWD_congr_classΦ
