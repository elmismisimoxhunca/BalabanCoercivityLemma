import UD3
import AC_UD2
import AC_Base

/-! AC copy of UD3: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (Ball pcd_comm pcd_self pcd_triangle pcd_le_diff pdist_triangle pdist_comm mem_Ball_self)
open AdalyFormal.IngredientFamilyR2 (embY embY_val)
open AdalyFormal.M2Bridge (offc offc_lt mem_siteBox_offc)

theorem class_cube_atAC {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (hM : 0 < M)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) {Lam : Set (PeriodicLatticeSite Lu)}
    (hL : AdalyFormal.StatementLane.LambdaOK ell M R k S Lam)
    (hthick : ∀ σ : Fin 3, 12 * (M * ell ^ k) ≤ scaleUp ell k Lu σ + 1)
    {y0 : PeriodicLatticeSite Lu} (hy0 : y0 ∈ Lam) (q : PeriodicLatticeSite Lu)
    (hD : pdist y0 q + 3 * (fc * M) ≤ R * M) (r : ℕ) (hr : r + 128 * ell ^ k + 5 ≤ 4 * (M * ell ^ k)) :
    ∃ z : PeriodicLatticeSite (scaleUp ell k Lu),
      IsClassCube ell M fc k S (siteBox z (fc * bigSide M ell k)) k ∧
      ∀ x' ∈ Ball (embY ell k Lu hell q) r, ∀ σ : Fin 3, fc * bigSide M ell k ≤ scaleUp ell k Lu σ + 1 →
        2 * (64 * ell ^ k) + 4 ≤ offc z x' σ ∧ offc z x' σ + 2 * (64 * ell ^ k) + 5 ≤ fc * bigSide M ell k := by
  have hfc10 : 10 ≤ fc := CubeFactor.ge
  set n := ell ^ k with hn0
  have hnpos : 0 < n := pow_pos hell k
  have hB : 0 < M * n := Nat.mul_pos hM hnpos
  have hbs : bigSide M ell k = M * n := rfl
  have h10 : 10 * (M * n) ≤ fc * (M * n) := Nat.mul_le_mul_right _ hfc10
  set x : PeriodicLatticeSite (scaleUp ell k Lu) := embY ell k Lu hell q with hx
  set z := cornerOf (M * n) x with hz
  have hgrid := cornerOf_grid hB (fun σ => hS.2.2.1 k le_rfl σ) x
  have hr5 : r ≤ 5 * (M * n) := by omega
  have hxin : x ∈ siteBox z (fc * bigSide M ell k) := by
    rw [hbs, mem_siteBox_offc]
    intro σ
    have : 5 * (M * n) ≤ offc z x σ + 0 ∧ offc z x σ + 1 ≤ 6 * (M * n) + 0 :=
      corner_off_ball (x := x) (x' := x) hB (Nat.zero_le (5 * (M * n))) σ (hthick σ) (by rw [AdalyFormal.StatementLane.pdist_self])
    omega
  have hOm : ∀ x'' ∈ siteBox z (fc * bigSide M ell k), x'' ∈ S.Om k := by
    intro x'' hx''
    rw [hbs] at hx'' hxin
    refine near_mem_OmAC (T0 := fc) hell hS hL hy0 q hD x'' (fun σ => ?_)
    have e1 := (mem_siteBox_offc _ _ _).mp hx'' σ
    have e2 := (mem_siteBox_offc _ _ _).mp hxin σ
    have h6 : 6 * (M * n) ≤ fc * (M * n) := by omega
    have := pcd_of_offAC hB (hthick σ) (x σ).isLt (x'' σ).isLt h6 e1
    have e3 : fc * (M * n) = fc * (M * n) := rfl
    exact this
  have hxOm : x ∈ S.Om k := hOm x hxin
  have hOm1 : S.Om (k + 1) = ∅ := hS.2.1 (k + 1) (by omega)
  have hOm2 : S.Om (k + 1 + 1) = ∅ := hS.2.1 (k + 1 + 1) (by omega)
  have hdesc : DescribedAt ell M fc k S (siteBox z (fc * bigSide M ell k)) k := by
    refine ⟨le_rfl, ⟨z, hgrid, rfl⟩, ?_, ⟨x, hxin, ?_⟩⟩
    · intro y hy
      left
      refine ⟨hOm y hy, ?_⟩
      rw [hOm1]; exact fun h => h
    · refine ⟨hxOm, ?_⟩
      rw [hOm1]; exact fun h => h
  refine ⟨z, ⟨hdesc, ?_⟩, ?_⟩
  · intro i hi
    obtain ⟨hik, -, hsub, w, hwin, hwB⟩ := hi
    by_contra hne
    have hlt : i < k := lt_of_le_of_ne hik hne
    have h1 : w ∈ S.Om k := hOm w hwin
    have h2 : S.Om k ⊆ S.Om (i + 1) := om_anti hS.1 (by omega)
    exact hwB.2 (h2 h1)
  · intro x' hx' σ _
    have hp : pdist x x' ≤ r := hx'
    have : 5 * (M * n) ≤ offc z x' σ + r ∧ offc z x' σ + 1 ≤ 6 * (M * n) + r :=
      corner_off_ball (x := x) (x' := x') hB hr5 σ (hthick σ) hp
    rw [hbs]
    omega

end AdalyFormal.M2UnitCharts


#print axioms AdalyFormal.M2UnitCharts.class_cube_atAC
