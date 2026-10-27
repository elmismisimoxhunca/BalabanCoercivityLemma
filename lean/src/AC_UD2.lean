import UD2
import AC_Base

/-!
# AC_UD2 -- box offsets / membership in `Omega_k` for a cube of ARBITRARY side `T B` (lane allc_20261016)

UD1/UD2 give, for the 12-box centred at the block of `a` (corner `zc N B a`), the offset window and `box_pcd`/`near_mem_Om` with the constant `7`
(`7 B <-> 12 B`).  The class cube of factor `fc` at index `k` is the box of side `T = fc B`.  Here the corresponding statements with a free side `T >= 6 B`:
* `pcd_of_offAC` : `12 B <= N`, offset of `b` from `zc N B a` is `< T`  =>  `pcd N a b <= T`;
* `near_mem_OmAC` : `pcd (embY q) x'' <= T0 * (M n)` for all coordinates, `pdist y0 q + 3 T0 M <= R M`  =>  `x'' in Omega_k`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.M2UnitCharts

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8 (Ball pcd_comm pcd_self pcd_triangle pcd_le_diff pdist_triangle pdist_comm pdist_self mem_Ball_self)
open AdalyFormal.IngredientFamilyR2 (embY embY_val)
open AdalyFormal.M2Bridge (offc offc_lt mem_siteBox_offc)

theorem pcd_of_offAC {N B T a b : ℕ} (hB : 0 < B) (h12 : 12 * B ≤ N) (ha : a < N) (hb : b < N) (hT : 6 * B ≤ T)
    (hoff : offN N (zc N B a) b < T) : pcd N a b ≤ T := by
  have hN : 0 < N := by omega
  have hoa := off_bounds (r := 0) hB h12 ha ha (Nat.zero_le _) (by rw [pcd_self])
  have hzl := zc_lt (B := B) (a := a) hN
  have hmodb := Nat.mod_add_div (b + (N - zc N B a)) N
  have hmoda := Nat.mod_add_div (a + (N - zc N B a)) N
  have hltb : (b + (N - zc N B a)) / N < 3 := by apply Nat.div_lt_of_lt_mul; omega
  have hlta : (a + (N - zc N B a)) / N < 3 := by apply Nat.div_lt_of_lt_mul; omega
  have hnb : offN N (zc N B a) b < N := Nat.mod_lt _ hN
  unfold offN at hoff hoa hnb
  generalize (b + (N - zc N B a)) % N = ob at *
  generalize (b + (N - zc N B a)) / N = jb at *
  generalize (a + (N - zc N B a)) % N = oa at *
  generalize (a + (N - zc N B a)) / N = ja at *
  unfold pcd
  split_ifs <;>
  interval_cases jb <;> interval_cases ja <;> omega

theorem near_mem_OmAC {ell M R k T0 : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) {Lam : Set (PeriodicLatticeSite Lu)}
    (hL : AdalyFormal.StatementLane.LambdaOK ell M R k S Lam)
    {y0 : PeriodicLatticeSite Lu} (hy0 : y0 ∈ Lam) (q : PeriodicLatticeSite Lu)
    (hD : pdist y0 q + 3 * (T0 * M) ≤ R * M) (x'' : PeriodicLatticeSite (scaleUp ell k Lu))
    (hn : ∀ σ : Fin 3, pcd (scaleUp ell k Lu σ + 1) (embY ell k Lu hell q σ).val (x'' σ).val ≤ T0 * (M * ell ^ k)) :
    x'' ∈ S.Om k := by
  set n := ell ^ k with hn0
  have hnpos : 0 < n := pow_pos hell k
  let y' : PeriodicLatticeSite Lu := fun σ => ⟨(x'' σ).val / n, by
    have h1 := (x'' σ).isLt
    have h2 : scaleUp ell k Lu σ + 1 = (Lu σ + 1) * n := scaleUp_succ ell k Lu hell σ
    exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq h1 (by rw [h2, mul_comm]))⟩
  have hy'cd : ∀ σ : Fin 3, pcd (Lu σ + 1) (q σ).val (y' σ).val ≤ T0 * M := by
    intro σ
    have hN : scaleUp ell k Lu σ + 1 = (Lu σ + 1) * n := scaleUp_succ ell k Lu hell σ
    have hmul := pcd_mul (Lu σ + 1) n (q σ).val (y' σ).val hnpos
    rw [← hN] at hmul
    have e1 : (embY ell k Lu hell q σ).val = n * (q σ).val := embY_val ell k Lu hell q σ
    have e2 : n * (y' σ).val ≤ (x'' σ).val := by
      show n * ((x'' σ).val / n) ≤ _
      exact Nat.mul_div_le _ _
    have e3 : (x'' σ).val < n * (y' σ).val + n := by
      show _ < n * ((x'' σ).val / n) + n
      have := Nat.mod_add_div (x'' σ).val n
      have h3 := Nat.mod_lt (x'' σ).val hnpos
      omega
    have hyN : n * (y' σ).val < scaleUp ell k Lu σ + 1 := lt_of_le_of_lt e2 (x'' σ).isLt
    have hqN : n * (q σ).val < scaleUp ell k Lu σ + 1 := by rw [← e1]; exact (embY ell k Lu hell q σ).isLt
    have t1 := pcd_triangle (scaleUp ell k Lu σ + 1) (n * (q σ).val) (x'' σ).val (n * (y' σ).val) hqN (x'' σ).isLt hyN
    have t2 : pcd (scaleUp ell k Lu σ + 1) (x'' σ).val (n * (y' σ).val) < n := by
      rw [pcd_comm]
      have := pcd_le_diff (scaleUp ell k Lu σ + 1) (n * (y' σ).val) (x'' σ).val e2
      omega
    have t0 := hn σ
    rw [e1] at t0
    have eT : T0 * (M * n) = n * (T0 * M) := by ring
    have hlt : n * pcd (Lu σ + 1) (q σ).val (y' σ).val < n * (T0 * M + 1) := by
      rw [← hmul]; nlinarith
    have := Nat.lt_of_mul_lt_mul_left hlt
    omega
  have hpd : pdist q y' ≤ 3 * (T0 * M) := by
    unfold pdist
    calc ∑ μ : Fin 3, pcd (Lu μ + 1) (q μ).val (y' μ).val ≤ ∑ _μ : Fin 3, T0 * M :=
          Finset.sum_le_sum (fun σ _ => hy'cd σ)
      _ = 3 * (T0 * M) := by simp <;> ring
  have hy'Om : embY ell k Lu hell y' ∈ S.Om k :=
    embY_mem_Om hell hL hy0 (le_trans (pdist_triangle y0 q y') (by omega))
  have hbc := hS.2.2.2.1 k le_rfl
  refine hbc _ hy'Om x'' (fun μ => ?_)
  rw [embY_val]
  show (x'' μ).val / (M * n) = (n * ((x'' μ).val / n)) / (M * n)
  rw [mul_comm M n, Nat.mul_div_mul_left _ _ hnpos, Nat.div_div_eq_div_mul]

end AdalyFormal.M2UnitCharts

#print axioms AdalyFormal.M2UnitCharts.pcd_of_offAC
#print axioms AdalyFormal.M2UnitCharts.near_mem_OmAC
