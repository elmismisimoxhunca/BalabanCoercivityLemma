import TL7d

/-!
# TL8a -- the tower geometry (`geomOf`, `OmGe`, `bondsLam`, ...) pulled back along `phiS`
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.IngredientFamilyR2

/-- tower pulled back along `phiS h o` -/
def towerPull {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (S : Tower L) : Tower Lt :=
  ⟨fun j => phiS h o ⁻¹' S.Om j⟩

theorem liftTower_eq {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (S : Tower L) :
    liftTower h S = towerPull h (fun _ => 0) S := by
  cases S; simp only [liftTower, towerPull, projS_eq_phiS]

theorem mod_mod_dvd_val {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {b : ℕ} (hp : PhiOK h o b)
    (x : PeriodicLatticeSite Lt) (μ : Fin 3) : (phiS h o x μ).val % b = (x μ).val % b := by
  rw [phiS_val, Nat.mod_mod_of_dvd _ (hp.side μ), Nat.add_mod, (Nat.mod_eq_zero_of_dvd (hp.off μ)), Nat.add_zero, Nat.mod_mod]

theorem mod_eq_sub_of_aligned_block (b y z : ℕ) (hb : 0 < b) (hy : b ∣ y) (h1 : y ≤ z) (h2 : z < y + b) :
    z % b = z - y := by
  obtain ⟨c, rfl⟩ := hy
  have hdiv : z / b = c := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact h1) (by rw [Nat.succ_mul, Nat.mul_comm]; omega)
  have := Nat.mod_add_div z b
  rw [hdiv] at this
  omega

theorem exists_lift_block {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {b : ℕ} (hp : PhiOK h o b)
    (hb : 0 < b) (x : PeriodicLatticeSite Lt) (y : PeriodicLatticeSite L) (hy : Aligned b y)
    (hyx : ∀ μ, (y μ).val ≤ (phiS h o x μ).val ∧ (phiS h o x μ).val < (y μ).val + b) :
    ∃ y' : PeriodicLatticeSite Lt, Aligned b y' ∧ phiS h o y' = y ∧ ∀ μ, (y' μ).val ≤ (x μ).val ∧ (x μ).val < (y' μ).val + b := by
  have hlt : ∀ μ : Fin 3, (x μ).val - (x μ).val % b < Lt μ + 1 := fun μ => lt_of_le_of_lt (Nat.sub_le _ _) (x μ).isLt
  let y' : PeriodicLatticeSite Lt := fun μ => ⟨(x μ).val - (x μ).val % b, hlt μ⟩
  have hy'al : Aligned b y' := by
    intro μ
    show b ∣ (x μ).val - (x μ).val % b
    exact Nat.dvd_sub_mod (x μ).val
  have hblock : ∀ μ, (y' μ).val ≤ (x μ).val ∧ (x μ).val < (y' μ).val + b := by
    intro μ
    have := Nat.mod_lt (x μ).val hb
    have h2 := Nat.sub_add_cancel (Nat.mod_le (x μ).val b)
    show (x μ).val - (x μ).val % b ≤ (x μ).val ∧ (x μ).val < (x μ).val - (x μ).val % b + b
    omega
  refine ⟨y', hy'al, ?_, hblock⟩
  funext μ
  apply Fin.ext
  have hv := phiS_val_in_block hp hb hy'al μ (hblock μ).1 (hblock μ).2
  have hm := mod_mod_dvd_val hp x μ
  have hyal := hy μ
  obtain ⟨hy1, hy2⟩ := hyx μ
  have e1 : (phiS h o x μ).val % b = (phiS h o x μ).val - (y μ).val :=
    mod_eq_sub_of_aligned_block b _ _ hb hyal hy1 hy2
  have e2 : (x μ).val - (y' μ).val = (x μ).val % b := by
    show (x μ).val - ((x μ).val - (x μ).val % b) = _
    have := Nat.mod_le (x μ).val b
    omega
  omega

end AdalyFormal.Thin
