import NsPtQ4
import NsPtI1

/-!
# PtQ5 -- `Q*` is injective at the flat nested point (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {ell M R : ℕ}

/-- the coefficient of a row on a single-bond field. -/
theorem Q_single (hP : PGeo ell M R) (hell : 0 < ell) (a : ℝ) (β : Bond (scaleUp ell 2 (neLu M R))) (v : SuTwo)
    (q : BIdx (geomOf ell 2 (neS ell M R))) :
    (QfullOf (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) (dB β v)) q
      = ((1 / ((ell ^ (q.1 : ℕ) : ℕ) : ℝ) ^ 4) * (hits q.2.1.1 q.2.1.2 (ell ^ (q.1 : ℕ)) β : ℝ)) • v := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  have hdvdJ : ∀ ν, (geomOf ell 2 (neS ell M R)).ell ^ 2 ∣ scaleUp ell 2 (neLu M R) ν + 1 :=
    fun ν => dvd_scaleUp (R := R) hell hP.hM ν le_rfl
  have hq2 : (q.1 : ℕ) ≤ 2 := by
    have := q.1.isLt
    have e : (geomOf ell 2 (neS ell M R)).k = 2 := rfl
    omega
  have hcrs : Crs (ell ^ (q.1 : ℕ)) q.2.1.1 := crs_of_bondsLam hg hP.hM hq2 q.2.1 q.2.2
  have hcl : q.2.1.1 ∈ CoarseLattice (scaleUp ell 2 (neLu M R)) ((geomOf ell 2 (neS ell M R)).ell ^ (q.1 : ℕ)) := by
    rw [mem_CoarseLattice]; intro μ; exact Nat.mod_eq_zero_of_dvd (hcrs μ)
  rw [Qfull_flat_row (geomOf ell 2 (neS ell M R)) hell 2 hdvdJ q hq2 hcl (dB β v)]
  exact lcr_single q.2.1.1 q.2.1.2 (ell ^ (q.1 : ℕ)) hcl β v


theorem lev_le (p : BIdx (geomOf ell 2 (neS ell M R))) : (p.1 : ℕ) ≤ 2 := by
  have := p.1.isLt
  have e : (geomOf ell 2 (neS ell M R)).k = 2 := rfl
  omega

theorem peak_zero (hP : PGeo ell M R) (hell : 0 < ell) (a : ℝ)
    (lam : FSp (PF ell M R hell a).G)
    (hperp : ∀ x : ↥(bondSupp (PF ell M R hell a).G), ⟪(PF ell M R hell a).data.Q x, lam⟫ = 0)
    (p : BIdx (geomOf ell 2 (neS ell M R)))
    (hhigh : ∀ p' : BIdx (geomOf ell 2 (neS ell M R)), (p.1 : ℕ) < (p'.1 : ℕ) → lam p' = 0) : lam p = 0 := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  obtain ⟨⟨j, hjlt⟩, ⟨⟨Y, μ⟩, hb⟩⟩ := p
  have hj : j ≤ 2 := by
    have e : (geomOf ell 2 (neS ell M R)).k = 2 := rfl
    omega
  have hpos : 0 < ell ^ j := pow_pos hell j
  set β : Bond (scaleUp ell 2 (neLu M R)) := (pathSite Y μ (ell ^ j - 1), μ) with hβ
  have hβm : β ∈ bondsOm0 (geomOf ell 2 (neS ell M R)) := peak_mem_Om0 hP hj Y μ hb
  set v : SuTwo := lam ⟨⟨j, hjlt⟩, ⟨(Y, μ), hb⟩⟩ with hv
  let xs : ↥(bondSupp (PF ell M R hell a).G) := ⟨dB β v, fun b' hb' => by
    unfold dB
    show (if b' = β then v else 0) = 0
    rw [if_neg]
    intro h; exact hb' (h ▸ hβm)⟩
  have h0 := hperp xs
  have hQ : (PF ell M R hell a).data.Q xs = WithLp.toLp 2 (fun q => (QfullOf (geomOf ell 2 (neS ell M R))
      (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) (dB β v)) q) := rfl
  rw [PiLp.inner_apply] at h0
  have key : ∀ q : BIdx (geomOf ell 2 (neS ell M R)), q ≠ ⟨⟨j, hjlt⟩, ⟨(Y, μ), hb⟩⟩ →
      ⟪((PF ell M R hell a).data.Q xs) q, lam q⟫ = 0 := by
    intro q hq
    by_cases hlev : j < (q.1 : ℕ)
    · rw [hhigh q hlev, inner_zero_right]
    · have hle : (q.1 : ℕ) ≤ j := by omega
      have hq2 := lev_le q
      have hhits : hits q.2.1.1 q.2.1.2 (ell ^ (q.1 : ℕ)) β = 0 := by
        by_contra hne
        have hpos' : 0 < hits q.2.1.1 q.2.1.2 (ell ^ (q.1 : ℕ)) β := Nat.pos_of_ne_zero hne
        obtain ⟨⟨jq, hjq⟩, ⟨⟨Yq, μq⟩, hbq⟩⟩ := q
        simp only at hpos' hle hq2
        obtain ⟨hμq, -⟩ := hit_extract Yq μq μ (ell ^ j) (ell ^ jq) Y hpos'
        subst hμq
        have hfin : jq = j ∧ Yq = Y := by
          by_cases h0' : μq = 0
          · subst h0'
            exact nc_dir0 hP hj hq2 hle Y Yq hb hbq hpos'
          · exact nc_trans hP hj hq2 hle Y Yq μq h0' hb hbq hpos'
        apply hq
        obtain ⟨h1, h2⟩ := hfin
        subst h2
        subst h1
        rfl
      have := Q_single hP hell a β v q
      show ⟪(QfullOf (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) (dB β v)) q, lam q⟫ = 0
      rw [this, hhits]
      simp
  rw [Finset.sum_eq_single (⟨⟨j, hjlt⟩, ⟨(Y, μ), hb⟩⟩ : BIdx (geomOf ell 2 (neS ell M R)))
    (fun q _ hq => key q hq) (fun h => absurd (Finset.mem_univ _) h)] at h0
  have hself := Q_single hP hell a β v ⟨⟨j, hjlt⟩, ⟨(Y, μ), hb⟩⟩
  have h0' : ⟪(QfullOf (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) (dB β v))
      ⟨⟨j, hjlt⟩, ⟨(Y, μ), hb⟩⟩, v⟫ = 0 := h0
  rw [hself] at h0'
  simp only at h0'
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at h0'
  have hK : 0 < (1 / ((ell ^ j : ℕ) : ℝ) ^ 4) * (hits Y μ (ell ^ j) β : ℝ) := by
    have := hits_pos Y μ (ell ^ j) hpos
    positivity
  have hn : ‖v‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp h0' with h | h
    · exact absurd h hK.ne'
    · exact h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hn)


theorem qs_injective (hP : PGeo ell M R) (hell : 0 < ell) (a : ℝ) :
    Function.Injective (PF ell M R hell a).data.Qs := by
  rw [injective_iff_map_eq_zero]
  intro lam hlam
  have hperp : ∀ x : ↥(bondSupp (PF ell M R hell a).G), ⟪(PF ell M R hell a).data.Q x, lam⟫ = 0 := by
    intro x
    rw [(PF ell M R hell a).data.Q_adj x lam, hlam, inner_zero_right]
  have all : ∀ m : ℕ, ∀ p : BIdx (geomOf ell 2 (neS ell M R)), 2 - (p.1 : ℕ) ≤ m → lam p = 0 := by
    intro m
    induction m with
    | zero =>
      intro p hp
      exact peak_zero hP hell a lam hperp p (fun p' hlt => by
        have := lev_le p'; omega)
    | succ m ih =>
      intro p hp
      exact peak_zero hP hell a lam hperp p (fun p' hlt => ih p' (by
        have := lev_le p'; omega))
  exact PiLp.ext (fun p => all 2 p (by omega))

#print axioms qs_injective

end AdalyFormal.CoverOmega
