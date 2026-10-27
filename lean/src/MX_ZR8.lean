import MX_Base
import ZR8Class

/-!
# MX_ZR8 -- class-bond locality for the MIXED class (lane mixed_20261017)

`ClassBondΦ` (MX_Base) is `∃ f ∈ Φ, ClassBond ell M f`.  Mixed versions of `ZR8Class.bothIn_classBond`, `classBond_bothIn`, `InstIneq_congr_class`, `InstAtWD_congr_class`.
-/
set_option autoImplicit false

namespace MXP.StatementLaneR8

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2 (BothIn Cfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open MXP.AllC

variable {L : PeriodicLatticeExtent}

theorem classBond_bothInΦ {ell M R k : ℕ} {Φ : Set ℕ} {S : Tower L} (hS : Admissible ell M R k S) {e : Bond L}
    (he : ClassBondΦ ell M Φ k S e) : BothIn (S.Om 0) e := by
  obtain ⟨f, -, hf⟩ := he
  exact classBond_bothIn hS hf

/-- with the mixed plaquette coverage, every `BothIn Ω₀` bond is class-constrained. -/
theorem bothIn_classBondΦ {ell M R k : ℕ} {Φ : Set ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 2 ≤ M)
    (hcov : CoversOmΦ ell M Φ k S) {e : Bond L} (he : BothIn (S.Om 0) e) : ClassBondΦ ell M Φ k S e := by
  have hdvd : ∀ κ : Fin 3, M ∣ L κ + 1 := fun κ => by
    have := hS.2.2.1 0 (Nat.zero_le _) κ; simpa [bigSide] using this
  have hbc : BlockClosed M (S.Om 0) := by
    have := hS.2.2.2.1 0 (Nat.zero_le _); simpa [bigSide] using this
  obtain ⟨p, hep, hall⟩ := plaq_of_bothIn hM hdvd hbc he
  obtain ⟨sites, j, hqΦ, hcb⟩ := hcov.2 p hall
  obtain ⟨f, hf, hq⟩ := hqΦ
  exact ⟨f, hf, sites, j, hq, hcb e hep⟩

theorem InstIneq_congr_classΦ {ell k : ℕ} (hell0 : 0 < ell) (a : ℝ) {Lu : PeriodicLatticeExtent} (γ₀ : ℝ)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {M R : ℕ} {Φ : Set ℕ} (h : LocHyp ell M R k S Lam)
    (hM : 2 ≤ M) (hcov : CoversOmΦ ell M Φ k S) {U U' : Cfg (scaleUp ell k Lu)}
    (hUU : ∀ e : Bond (scaleUp ell k Lu), ClassBondΦ ell M Φ k S e → U e = U' e) :
    InstIneq ell k hell0 a Lu γ₀ S Lam U ↔ InstIneq ell k hell0 a Lu γ₀ S Lam U' :=
  InstIneq_congr hell0 a γ₀ h (fun e he => hUU e (bothIn_classBondΦ h.adm hM hcov he))

theorem InstAtWD_congr_classΦ {ell k : ℕ} (hell0 : 0 < ell) (a : ℝ) {Lu : PeriodicLatticeExtent} (γ₀ : ℝ)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {M R : ℕ} {Φ : Set ℕ} (h : LocHyp ell M R k S Lam)
    (hM : 2 ≤ M) (hcov : CoversOmΦ ell M Φ k S) {U U' : Cfg (scaleUp ell k Lu)}
    (hUU : ∀ e : Bond (scaleUp ell k Lu), ClassBondΦ ell M Φ k S e → U e = U' e) :
    InstAtWD ell k hell0 a Lu γ₀ S Lam U ↔ InstAtWD ell k hell0 a Lu γ₀ S Lam U' :=
  InstAtWD_congr hell0 a γ₀ h (fun e he => hUU e (bothIn_classBondΦ h.adm hM hcov he))

end MXP.StatementLaneR8

#print axioms MXP.StatementLaneR8.InstIneq_congr_classΦ
#print axioms MXP.StatementLaneR8.InstAtWD_congr_classΦ
