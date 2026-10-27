import GenKPoincare
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.GenK
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)
open AdalyFormal.Balaban.RegularUGamma0 (coarseCurlEnergySuTwo)
open AdalyFormal.Balaban.SuTwoInner (inner_eq_hsInner)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)

/-- The fine torus of mesh 1/n underlying the given unit torus. -/
abbrev fineExtent (M : PeriodicLatticeExtent) (n : ℕ) : PeriodicLatticeExtent :=
  fun μ => n * (M μ + 1) - 1

lemma fineSide (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n) (μ : Fin 3) :
    fineExtent M n μ + 1 = n * (M μ + 1) := by
  unfold fineExtent
  have : 0 < n * (M μ + 1) := Nat.mul_pos hn (Nat.zero_lt_succ _)
  omega

lemma fineTiling (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n) :
    ∀ μ : Fin 3, n ∣ (fineExtent M n μ + 1) := by
  intro μ; rw [fineSide M hn]; exact dvd_mul_right _ _

variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)

def embed (x : PeriodicLatticeSite M) : PeriodicLatticeSite (fineExtent M n) :=
  fun μ => ⟨n * (x μ).val, by rw [fineSide M hn]; exact Nat.mul_lt_mul_of_pos_left (x μ).isLt hn⟩

lemma embed_coarse (x : PeriodicLatticeSite M) : embed M hn x ∈ CoarseLattice (fineExtent M n) n := by
  rw [mem_CoarseLattice]
  intro μ
  exact Nat.mul_mod_right _ _

/-- A genuine bijection, not repetition of a field onto unused sites. -/
def sites : PeriodicLatticeSite M ≃ {x : PeriodicLatticeSite (fineExtent M n) //
    x ∈ CoarseLattice (fineExtent M n) n} where
  toFun x := ⟨embed M hn x, embed_coarse M hn x⟩
  invFun x := fun μ => ⟨(x.1 μ).val / n, by
    have hx := (x.1 μ).isLt
    have hx' : (x.1 μ).val < n * (M μ + 1) := by simpa only [fineSide M hn] using hx
    exact (Nat.div_lt_iff_lt_mul hn).mpr (by simpa [Nat.mul_comm] using hx')⟩
  left_inv x := by
    funext μ; apply Fin.ext
    exact Nat.mul_div_cancel_left (x μ).val hn
  right_inv x := by
    apply Subtype.ext; funext μ; apply Fin.ext
    have hd := mem_CoarseLattice.mp x.2 μ
    change n * ((x.1 μ).val / n) = (x.1 μ).val
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd)

lemma sites_shift (x : PeriodicLatticeSite M) (μ : Fin 3) :
    (sites M hn (periodicLatticeShift x μ)).1 =
      coarseShift (sites M hn x).1 n μ := by
  funext ν
  apply Fin.ext
  by_cases h : ν = μ
  · subst ν
    rw [coarseShift_val_eq]
    change n * ((periodicLatticeShift x μ) μ).val = (n * (x μ).val + n) % (fineExtent M n μ + 1)
    rw [fineSide M hn]
    have hs : ((periodicLatticeShift x μ) μ).val = ((x μ).val + 1) % (M μ + 1) := by
      simp only [periodicLatticeShift,Function.update_self,Fin.val_add,Fin.val_one',Nat.add_mod_mod]
    rw [hs, ← Nat.mul_succ, Nat.mul_mod_mul_left]
  · rw [coarseShift_apply_ne _ _ _ _ h]
    change n * ((periodicLatticeShift x μ) ν).val = n * (x ν).val
    rw [periodicLatticeShift, Function.update_of_ne h]

def bonds : Bond M ≃ CoarseBond (fineExtent M n) n :=
  Equiv.prodCongr (sites M hn) (Equiv.refl _)

def plaquettes : PeriodicLatticePlaquette M ≃ CoarsePlaquette (fineExtent M n) n :=
  Equiv.prodCongr (sites M hn) (Equiv.refl _)

/-- Reindexing a coarse field onto the unit torus. -/
def unitField (A : CoarseBond (fineExtent M n) n → SuTwo) : Bond M → SuTwo :=
  fun b => A (bonds M hn b)

lemma curl_reindex (A : CoarseBond (fineExtent M n) n → SuTwo) (p : PeriodicLatticePlaquette M) :
    flatCurlValue (unitField M hn A) p =
      coarseCurlSuTwo (fineTiling M hn) A (plaquettes M hn p) := by
  unfold flatCurlValue coarseCurlSuTwo unitField
  have h0 : (sites M hn (periodicLatticeShift p.1 p.2.1.1)) =
      ⟨coarseShift (sites M hn p.1).1 n p.2.1.1, coarseShift_mem_coarseLattice (fineTiling M hn) (sites M hn p.1).2 p.2.1.1⟩ :=
    Subtype.ext (sites_shift M hn p.1 p.2.1.1)
  have h1 : (sites M hn (periodicLatticeShift p.1 p.2.1.2)) =
      ⟨coarseShift (sites M hn p.1).1 n p.2.1.2, coarseShift_mem_coarseLattice (fineTiling M hn) (sites M hn p.1).2 p.2.1.2⟩ :=
    Subtype.ext (sites_shift M hn p.1 p.2.1.2)
  change A (sites M hn p.1,p.2.1.1) + A (sites M hn (periodicLatticeShift p.1 p.2.1.1),p.2.1.2) -
    A (sites M hn (periodicLatticeShift p.1 p.2.1.2),p.2.1.1) - A (sites M hn p.1,p.2.1.2) = _
  rw [h0,h1]
  rfl

lemma curlEnergy_reindex (A : CoarseBond (fineExtent M n) n → SuTwo) :
    curlEnergy (unitField M hn A) = coarseCurlEnergySuTwo (fineTiling M hn) A := by
  unfold curlEnergy coarseCurlEnergySuTwo
  simp only [← inner_eq_hsInner, real_inner_self_eq_norm_sq, curl_reindex]
  exact Equiv.sum_comp (plaquettes M hn) (fun p => ‖coarseCurlSuTwo (fineTiling M hn) A p‖^2)

#print axioms sites
#print axioms sites_shift
#print axioms curlEnergy_reindex
end HConstruction.GenK
