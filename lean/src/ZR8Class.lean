import ZR8Data

/-!
# ZR8Class -- the class-constrained bonds ARE the `BothIn Ω₀` bonds; locality stated with the class's own bond set

`ClassBond ell M c k S e` : `e` is a `CubeBond` of some class cube (`IsClassCube`), i.e. a bond on which `PerCubeRegular2` puts a
constraint (CMP99b p.396: "these regularity conditions do not impose any constraints on U outside the domain Ω₀").
 * `classBond_bothIn` : every class-constrained bond has both endpoints in `Ω₀` (class cubes lie in `B^i ∪ B^{i+1} ⊆ Ω₀`);
 * `bothIn_classBond` : conversely, with the r6 coverage `CoversOm0p` and `2 ≤ M`, every `BothIn Ω₀` bond is a boundary bond of a
   plaquette of `Ω₀` (`Ω₀` is a union of `M`-blocks, `plaq_of_bothIn`), hence lies in a class cube (`CoversPlaqOm0c`);
 * `InstIneq_congr_class`, `InstAtWD_congr_class` : the locality theorem with hypothesis "`U = U'` on every class-constrained bond".
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.StatementLaneR8

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)

variable {L : PeriodicLatticeExtent}

/-- bonds constrained by the class: `CubeBond`s of class cubes. -/
def ClassBond (ell M c k : ℕ) (S : Tower L) (e : Bond L) : Prop :=
  ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M c k S sites j ∧ CubeBond sites e

theorem classBond_bothIn {ell M R c k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) {e : Bond L}
    (he : ClassBond ell M c k S e) : BothIn (S.Om 0) e := by
  obtain ⟨sites, j, hq, h1, h2⟩ := he
  have hsub := hq.1.2.2.1
  have hin : ∀ x ∈ sites, x ∈ S.Om 0 := by
    intro x hx
    rcases hsub hx with h | h
    · exact admissible_mono hS j h.1
    · exact admissible_mono hS (j + 1) h.1
  exact ⟨hin _ h1, hin _ h2⟩

/-! ## block arithmetic -/

theorem succ_div_same {a M : ℕ} (h : ¬ M ∣ a + 1) : (a + 1) / M = a / M := Nat.succ_div_of_not_dvd h

theorem shift_self_val {z : PeriodicLatticeSite L} {ν : Fin 3} (hl : z ν ≠ Fin.last (L ν)) :
    (periodicLatticeShift z ν ν).val = (z ν).val + 1 := by
  unfold periodicLatticeShift
  rw [Function.update_self, Fin.val_add_one, if_neg hl]

theorem shift_ne (z : PeriodicLatticeSite L) {ν κ : Fin 3} (h : κ ≠ ν) : periodicLatticeShift z ν κ = z κ := by
  unfold periodicLatticeShift; rw [Function.update_of_ne h]

theorem shiftBack_ne (z : PeriodicLatticeSite L) {ν κ : Fin 3} (h : κ ≠ ν) : periodicLatticeShiftBack z ν κ = z κ := by
  unfold periodicLatticeShiftBack; rw [Function.update_of_ne h]

/-- one step in direction `ν` stays in the `M`-block if `M ∤ z_ν + 1` and `M ∣ N_ν`. -/
theorem shift_sameBlock {M : ℕ} (hdvd : ∀ κ : Fin 3, M ∣ L κ + 1) {z : PeriodicLatticeSite L} {ν : Fin 3}
    (h : ¬ M ∣ (z ν).val + 1) : ∀ κ, (periodicLatticeShift z ν κ).val / M = (z κ).val / M := by
  intro κ
  by_cases hk : κ = ν
  · subst hk
    have hl : z κ ≠ Fin.last (L κ) := by
      intro e; apply h; rw [e, Fin.val_last]; exact hdvd κ
    rw [shift_self_val hl, succ_div_same h]
  · rw [shift_ne z hk]

theorem shiftBack_sameBlock {M : ℕ} {z : PeriodicLatticeSite L} {ν : Fin 3} (h : ¬ M ∣ (z ν).val) :
    ∀ κ, (periodicLatticeShiftBack z ν κ).val / M = (z κ).val / M := by
  intro κ
  by_cases hk : κ = ν
  · subst hk
    have h0 : z κ ≠ 0 := by intro e; apply h; rw [e, Fin.val_zero]; exact dvd_zero M
    have hv : (periodicLatticeShiftBack z κ κ).val = (z κ).val - 1 := by
      unfold periodicLatticeShiftBack
      rw [Function.update_self]
      exact Fin.val_sub_one_of_ne_zero h0
    have hpos : 1 ≤ (z κ).val := Nat.one_le_iff_ne_zero.mpr (fun e => h0 (Fin.ext e))
    rw [hv]
    have h' : ¬ M ∣ ((z κ).val - 1) + 1 := by rwa [Nat.sub_add_cancel hpos]
    have := succ_div_same h'
    rw [Nat.sub_add_cancel hpos] at this
    exact this.symm
  · rw [shiftBack_ne z hk]

theorem shift_comm (z : PeriodicLatticeSite L) {μ ν : Fin 3} (h : μ ≠ ν) :
    periodicLatticeShift (periodicLatticeShift z μ) ν = periodicLatticeShift (periodicLatticeShift z ν) μ := by
  have e1 : periodicLatticeShift z μ ν = z ν := shift_ne z h.symm
  have e2 : periodicLatticeShift z ν μ = z μ := shift_ne z h
  unfold periodicLatticeShift at e1 e2 ⊢
  rw [e1, e2, Function.update_comm h]

theorem shift_shiftBack_comm' (z : PeriodicLatticeSite L) {μ ν : Fin 3} (h : μ ≠ ν) :
    periodicLatticeShift (periodicLatticeShiftBack z ν) μ = periodicLatticeShiftBack (periodicLatticeShift z μ) ν := by
  have e1 : periodicLatticeShiftBack z ν μ = z μ := shiftBack_ne z h
  have e2 : periodicLatticeShift z μ ν = z ν := shift_ne z h.symm
  unfold periodicLatticeShiftBack at e1
  unfold periodicLatticeShift at e2
  unfold periodicLatticeShift periodicLatticeShiftBack
  rw [e1, e2, Function.update_comm h.symm]

/-! ## every `BothIn Ω₀` bond is a boundary bond of a plaquette of `Ω₀` -/

/-- a plaquette with base `w` in the `(α, β)` plane, all four corners in `Ω`: it contains `(w, α)` and `(w + β, α)` and all its
bonds are `BothIn Ω`. -/
theorem plaq_of_corners {Om : Set (PeriodicLatticeSite L)} (w : PeriodicLatticeSite L) {α β : Fin 3} (hab : α ≠ β)
    (h0 : w ∈ Om) (ha : periodicLatticeShift w α ∈ Om) (hb : periodicLatticeShift w β ∈ Om)
    (hab' : periodicLatticeShift (periodicLatticeShift w α) β ∈ Om) :
    ∃ p : PeriodicLatticePlaquette L, (w, α) ∈ periodicPlaquetteBoundaryEdges p ∧
      (periodicLatticeShift w β, α) ∈ periodicPlaquetteBoundaryEdges p ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond Om e := by
  have hba' : periodicLatticeShift (periodicLatticeShift w β) α ∈ Om := by rw [← shift_comm w hab]; exact hab'
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · refine ⟨(w, ⟨(α, β), hlt⟩), ?_, ?_, ?_⟩
    · simp [periodicPlaquetteBoundaryEdges]
    · simp [periodicPlaquetteBoundaryEdges]
    · intro e he
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact ⟨h0, ha⟩
      · exact ⟨ha, hab'⟩
      · exact ⟨hb, hba'⟩
      · exact ⟨h0, hb⟩
  · refine ⟨(w, ⟨(β, α), hlt⟩), ?_, ?_, ?_⟩
    · simp [periodicPlaquetteBoundaryEdges]
    · simp [periodicPlaquetteBoundaryEdges]
    · intro e he
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact ⟨h0, hb⟩
      · exact ⟨hb, hba'⟩
      · exact ⟨ha, hab'⟩
      · exact ⟨h0, ha⟩

theorem plaq_of_bothIn {M : ℕ} (hM : 2 ≤ M) (hdvd : ∀ κ : Fin 3, M ∣ L κ + 1) {Om : Set (PeriodicLatticeSite L)}
    (hbc : BlockClosed M Om) {e : Bond L} (he : BothIn Om e) :
    ∃ p : PeriodicLatticePlaquette L, e ∈ periodicPlaquetteBoundaryEdges p ∧
      ∀ e' ∈ periodicPlaquetteBoundaryEdges p, CubeBond Om e' := by
  obtain ⟨x, μ⟩ := e
  obtain ⟨hx, hxμ⟩ := he
  set ν : Fin 3 := if μ = 0 then 1 else 0 with hν
  have hμν : μ ≠ ν := by rw [hν]; split_ifs with h <;> [rw [h]; exact h] <;> decide
  have hxμν : (periodicLatticeShift x μ ν).val = (x ν).val := by rw [shift_ne x hμν.symm]
  by_cases hA : M ∣ (x ν).val + 1
  · -- base `x - ν`
    have hB : ¬ M ∣ (x ν).val := by
      intro h; have := (Nat.dvd_add_right h).mp hA; have := Nat.le_of_dvd one_pos this; omega
    set w := periodicLatticeShiftBack x ν with hw
    have hwν : periodicLatticeShift w ν = x := periodicLatticeShift_shiftBack x ν
    have h0 : w ∈ Om := hbc x hx w (shiftBack_sameBlock hB)
    have ha : periodicLatticeShift w μ ∈ Om := by
      rw [hw, shift_shiftBack_comm' x hμν]
      exact hbc _ hxμ _ (shiftBack_sameBlock (by rw [hxμν]; exact hB))
    have hb : periodicLatticeShift w ν ∈ Om := by rw [hwν]; exact hx
    have hab : periodicLatticeShift (periodicLatticeShift w μ) ν ∈ Om := by
      rw [shift_comm w hμν, hwν]; exact hxμ
    obtain ⟨p, -, h2, h3⟩ := plaq_of_corners w hμν h0 ha hb hab
    rw [hwν] at h2
    exact ⟨p, h2, h3⟩
  · -- base `x`
    have hb : periodicLatticeShift x ν ∈ Om := hbc x hx _ (shift_sameBlock hdvd hA)
    have hab : periodicLatticeShift (periodicLatticeShift x μ) ν ∈ Om :=
      hbc _ hxμ _ (shift_sameBlock hdvd (by rw [hxμν]; exact hA))
    obtain ⟨p, h1, -, h3⟩ := plaq_of_corners x hμν hx hxμ hb hab
    exact ⟨p, h1, h3⟩

/-- with the r6 coverage, every `BothIn Ω₀` bond is class-constrained. -/
theorem bothIn_classBond {ell M R c k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 2 ≤ M)
    (hcov : CoversOm0p ell M c k S) {e : Bond L} (he : BothIn (S.Om 0) e) : ClassBond ell M c k S e := by
  have hdvd : ∀ κ : Fin 3, M ∣ L κ + 1 := fun κ => by
    have := hS.2.2.1 0 (Nat.zero_le _) κ; simpa [bigSide] using this
  have hbc : BlockClosed M (S.Om 0) := by
    have := hS.2.2.2.1 0 (Nat.zero_le _); simpa [bigSide] using this
  obtain ⟨p, hep, hall⟩ := plaq_of_bothIn hM hdvd hbc he
  obtain ⟨sites, j, hq, hcb⟩ := hcov.2 p hall
  exact ⟨sites, j, hq, hcb e hep⟩

/-- **the constrained set is exactly `BothIn Ω₀`** (under `Admissible`, `CoversOm0p`, `2 ≤ M`). -/
theorem classBond_iff_bothIn {ell M R c k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hM : 2 ≤ M)
    (hcov : CoversOm0p ell M c k S) (e : Bond L) : ClassBond ell M c k S e ↔ BothIn (S.Om 0) e :=
  ⟨classBond_bothIn hS, bothIn_classBond hS hM hcov⟩

/-- **LOCALITY, with the class's own constrained bonds**: the printed inequality at `U` and at `U'` are the same proposition when
`U = U'` on every bond the class constrains. -/
theorem InstIneq_congr_class {ell k : ℕ} (hell0 : 0 < ell) (a : ℝ) {Lu : PeriodicLatticeExtent} (γ₀ : ℝ)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {M R c : ℕ} (h : LocHyp ell M R k S Lam)
    (hM : 2 ≤ M) (hcov : CoversOm0p ell M c k S) {U U' : Cfg (scaleUp ell k Lu)}
    (hUU : ∀ e : Bond (scaleUp ell k Lu), ClassBond ell M c k S e → U e = U' e) :
    InstIneq ell k hell0 a Lu γ₀ S Lam U ↔ InstIneq ell k hell0 a Lu γ₀ S Lam U' :=
  InstIneq_congr hell0 a γ₀ h (fun e he => hUU e (bothIn_classBond h.adm hM hcov he))

theorem InstAtWD_congr_class {ell k : ℕ} (hell0 : 0 < ell) (a : ℝ) {Lu : PeriodicLatticeExtent} (γ₀ : ℝ)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {M R c : ℕ} (h : LocHyp ell M R k S Lam)
    (hM : 2 ≤ M) (hcov : CoversOm0p ell M c k S) {U U' : Cfg (scaleUp ell k Lu)}
    (hUU : ∀ e : Bond (scaleUp ell k Lu), ClassBond ell M c k S e → U e = U' e) :
    InstAtWD ell k hell0 a Lu γ₀ S Lam U ↔ InstAtWD ell k hell0 a Lu γ₀ S Lam U' :=
  InstAtWD_congr hell0 a γ₀ h (fun e he => hUU e (bothIn_classBond h.adm hM hcov he))

/-- the genForm form of the class locality. -/
theorem genForm_congr_class (P : IngrBParams) {M R c : ℕ} (h : LocHyp P.ell M R P.k P.S P.Lam) (hM : 2 ≤ M)
    (hcov : CoversOm0p P.ell M c P.k P.S) (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), ClassBond P.ell M c P.k P.S e → P.U e = U' e) (Bt : Bond P.Lu → SuTwo) :
    GenP.genForm ({ P with U := U' } : IngrBParams) (WithLp.toLp 2 (GenP.genC ({ P with U := U' } : IngrBParams) Bt))
      = GenP.genForm P (WithLp.toLp 2 (GenP.genC P Bt)) :=
  genForm_congr_outside P h U' (fun e he => hUU e (bothIn_classBond h.adm hM hcov he)) Bt

#print axioms classBond_bothIn
#print axioms plaq_of_bothIn
#print axioms bothIn_classBond
#print axioms classBond_iff_bothIn
#print axioms InstIneq_congr_class
#print axioms InstAtWD_congr_class
#print axioms genForm_congr_class

end AdalyFormal.StatementLaneR8
