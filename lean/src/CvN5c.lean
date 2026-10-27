import CvN5b

/-!
# CvN5c -- the two endpoints of the path (lane cover_necessary_20261016)

* `Ginv_form`: `⟪x, Ginv x⟫ = ⟪W x, Δ W x⟫ + ‖T x‖² + ⟪x, Q*aQ x⟫` on `E₀` (3.122).
* `Ginv_psd_one` (θ = 0): at the constant configuration `U ≡ 1` the operator `Ginv` is positive semidefinite
  (`Δ(1) = D*χD`: the `Δ'` terms vanish because `Re U(∂p) - 1 = 0` and `Im U(∂p) = 0`).
* `Ginv_neg_flip` (θ = π): at `U = 1[b ↦ -1]`, with `b` based farther than `9 ell` from `Ω₁`, `b` a bond of `E₀`, and a plaquette
  `p₀ ∈ plaqIn Ω₀` having `b` as a boundary bond, the single-bond field `y = X δ_b` has
  `⟪y, Ginv y⟫ ≤ (a - 1) ‖X‖²`: `R D* y = 0` (so `T y = 0`, `W y = y`), the mass term is at most `a ‖X‖²`, and every plaquette
  contributes `cos π ‖X‖² = -‖X‖²` if it contains `b`, `0` otherwise.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AdalyFormal.CoverNec

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply gradValueCovariant curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (inner_eq_trace)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-! ### the whole form at `1[b ↦ -1]` -/

open Classical in
theorem Delta_form_sum (G : TowerGeom L) (U : Cfg L) (y : BondFnL2 L) :
    ⟪y, Delta G U y⟫ = ∑ p : PeriodicLatticePlaquette L, (if p ∈ plaqIn G.Om0 then
      (‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2 + (1 / 2 : ℝ) * bilPlaq U p (WithLp.ofLp y) (WithLp.ofLp y)) else 0) := by
  classical
  unfold Delta
  rw [inner_deltaKLocCLM]
  have e1 : ⟪plaqMask (plaqIn G.Om0) (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U y),
      plaqMask (plaqIn G.Om0) (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U y)⟫ =
      ∑ p : PeriodicLatticePlaquette L, (if p ∈ plaqIn G.Om0 then ‖curlValueCovariant U (WithLp.ofLp y) p‖ ^ 2 else 0) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [plaqMask_apply]
    split_ifs
    · exact real_inner_self_eq_norm_sq _
    · simp
  have e2 : deltaPrimeBilL2NormLoc U (plaqIn G.Om0) y y =
      ∑ p : PeriodicLatticePlaquette L, (if p ∈ plaqIn G.Om0 then
        (1 / 2 : ℝ) * bilPlaq U p (WithLp.ofLp y) (WithLp.ofLp y) else 0) := by
    show deltaPrimeBilNormLoc U (plaqIn G.Om0) (WithLp.ofLp y) (WithLp.ofLp y) = _
    simp only [deltaPrimeBilNormLoc, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply,
      deltaPrimeBilRawLoc_apply, smul_eq_mul]
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> ring
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> simp

theorem Delta_flip_le (hL : ∀ μ, 1 ≤ L μ) (G : TowerGeom L) (b : Bond L) (X : SuTwo)
    (p0 : PeriodicLatticePlaquette L) (hp0 : p0 ∈ plaqIn G.Om0) (hbp : b ∈ periodicPlaquetteBoundaryEdges p0) :
    ⟪(WithLp.toLp 2 (Pi.single b X) : BondFnL2 L), Delta G (Upi b) (WithLp.toLp 2 (Pi.single b X))⟫ ≤ -‖X‖ ^ 2 := by
  classical
  rw [Delta_form_sum]
  simp only [WithLp.ofLp_toLp, contrib_flip hL]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p0), if_pos hp0, if_pos hbp]
  have : ∑ p ∈ Finset.univ.erase p0, (if p ∈ plaqIn G.Om0 then
      (if b ∈ periodicPlaquetteBoundaryEdges p then -‖X‖ ^ 2 else 0) else (0 : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos (fun p _ => ?_)
    split_ifs <;> nlinarith [sq_nonneg ‖X‖]
  linarith

/-! ### `R D* y = 0`, `W y = y`, mass -/

theorem Rproj_single {ell : ℕ} (S : Tower L) (U : Cfg L) (b : Bond L) (X : SuTwo)
    (hfar : ∀ y ∈ S.Om 1, 2 < pdist y b.1) :
    Rproj (geomOf ell 1 S) U (gradAdj U (WithLp.toLp 2 (Pi.single b X))) = 0 := by
  classical
  unfold Rproj
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro v hv
  rw [gradAdj, ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  have h1 : (WithLp.ofLp v) b.1 = 0 := by
    refine RImage_support S U hv _ (fun y hy hyO => ?_)
    have := hfar y hyO
    have h2 : pdist b.1 y ≤ 1 := hy
    rw [pdist_comm] at h2; omega
  have h2 : (WithLp.ofLp v) (periodicLatticeShift b.1 b.2) = 0 := by
    refine RImage_support S U hv _ (fun y hy hyO => ?_)
    have := hfar y hyO
    have h3 : pdist (periodicLatticeShift b.1 b.2) y ≤ 1 := hy
    have h4 := pdist_triangle y (periodicLatticeShift b.1 b.2) b.1
    have h5 : pdist (periodicLatticeShift b.1 b.2) b.1 ≤ 1 := by rw [pdist_comm]; exact pdist_shift_le _ _
    have h6 : pdist y (periodicLatticeShift b.1 b.2) = pdist (periodicLatticeShift b.1 b.2) y := pdist_comm _ _
    omega
  refine Finset.sum_eq_zero (fun e _ => ?_)
  by_cases he : e = b
  · subst he
    show inner ℝ ((WithLp.ofLp (gradL2 U v)) e) ((Pi.single e X : Bond L → SuTwo) e) = 0
    rw [gradL2_apply]
    unfold gradValueCovariant
    rw [h1, h2, map_zero, sub_zero, inner_zero_left]
  · show inner ℝ ((WithLp.ofLp (gradL2 U v)) e) ((Pi.single b X : Bond L → SuTwo) e) = 0
    rw [Pi.single_apply, if_neg he, inner_zero_right]

theorem mass_single_le {ell : ℕ} (hell : 0 < ell) (S : Tower L) (U : Cfg L) {a : ℝ} (ha : 0 ≤ a) (b : Bond L)
    (X : SuTwo) (hfar : ∀ y ∈ S.Om 1, 5 * ell < pdist y b.1) :
    ⟪(WithLp.toLp 2 (Pi.single b X) : BondFnL2 L),
      MassFull (geomOf ell 1 S) a (bondSectorOf (geomOf ell 1 S) U) (WithLp.toLp 2 (Pi.single b X))⟫ ≤ a * ‖X‖ ^ 2 := by
  classical
  set G := geomOf ell 1 S with hG
  set y : BondFnL2 L := WithLp.toLp 2 (Pi.single b X) with hy
  rw [inner_MassFull]
  -- level-1 rows vanish
  have hlev1 : ∀ c : Bond L, c ∈ bondsLam G 1 → (WithLp.ofLp (QlinB G U 1 y)) c = 0 := by
    intro c hc
    rw [QlinB_apply]
    have h0 : QlinCompL G.ell (bgTower G U) 1 (suCoord y) c = QlinCompL G.ell (bgTower G U) 1 (0 : XS L) c := by
      refine QlinCompL_congr_in G.ell hell (bgTower G U) 1 c (fun e he => ?_)
      have hne : e ≠ b := by
        rintro rfl
        have he' : pdist c.1 e.1 ≤ 4 * ell := by
          have := he; simp only [Ball, Set.mem_setOf_eq] at this
          rw [show rhoT G.ell 1 = 4 * ell from rhoT_one ell] at this; exact this
        rcases hc.1 with hy1 | hy1
        · have := hfar c.1 hy1.2.1; omega
        · have h3 := hfar _ hy1.2.1
          have h4 := pdist_triangle (coarseShift c.1 (G.ell ^ 1) c.2) c.1 e.1
          have h5 : pdist (coarseShift c.1 (G.ell ^ 1) c.2) c.1 ≤ ell := by
            rw [pdist_comm]; have := pdist_coarseShift_le c.1 (G.ell ^ 1) c.2; simpa [hG, geomOf] using this
          omega
      show fromM2 (((WithLp.ofLp y) e : SuTwo) : M2m) = (0 : XS L) e
      rw [hy, WithLp.ofLp_toLp, Pi.single_apply, if_neg hne]
      simp
    rw [suCoordInv_apply_congr h0, map_zero, map_zero]
    rfl
  set g : BIdx G → ℝ := fun p => a * (G.ell : ℝ) ^ (p.1 : ℕ) * ‖(bondSectorOf G U).Qfull y p‖ ^ 2 with hgdef
  have hval : ∀ p : BIdx G, g p = if ((p.1 : ℕ) = 0 ∧ p.2.1 = b) then a * ‖X‖ ^ 2 else 0 := by
    rintro ⟨⟨j, hj⟩, c, hc⟩
    have hj2 : j < 2 := hj
    interval_cases j
    · show a * (G.ell : ℝ) ^ (0 : ℕ) * ‖(((G.ell : ℝ) ^ (0 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U 0 y)) c‖ ^ 2 = _
      rw [QlinB_zero, hy, WithLp.ofLp_toLp, Pi.single_apply]
      by_cases hcb : c = b
      · rw [if_pos hcb, if_pos ⟨rfl, hcb⟩]; simp
      · rw [if_neg hcb, if_neg (fun h => hcb h.2)]; simp
    · show a * (G.ell : ℝ) ^ (1 : ℕ) * ‖(((G.ell : ℝ) ^ (1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U 1 y)) c‖ ^ 2 = _
      rw [hlev1 c hc, if_neg (fun h => by simp at h)]
      simp
  show ∑ p : BIdx G, g p ≤ a * ‖X‖ ^ 2
  set T : Finset (BIdx G) := Finset.univ.filter (fun p : BIdx G => (p.1 : ℕ) = 0 ∧ p.2.1 = b) with hT
  have hsub : ∑ p : BIdx G, g p = ∑ p ∈ T, g p := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) (fun p _ hp => ?_)).symm
    rw [hval p, if_neg]
    intro h; exact hp (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hcard : T.card ≤ 1 := by
    refine Finset.card_le_one.2 (fun p hp q hq => ?_)
    rw [Finset.mem_filter] at hp hq
    rcases p with ⟨⟨j, hj⟩, c, hc⟩
    rcases q with ⟨⟨j', hj'⟩, c', hc'⟩
    obtain ⟨h1, h2⟩ := hp.2
    obtain ⟨h1', h2'⟩ := hq.2
    simp only at h1 h2 h1' h2'
    subst h1 h2 h1' h2'
    rfl
  have hle : ∑ p ∈ T, g p ≤ T.card • (a * ‖X‖ ^ 2) :=
    Finset.sum_le_card_nsmul T g _ (fun p _ => by rw [hval p]; split_ifs <;> first | exact le_rfl | positivity)
  rw [hsub]
  refine le_trans hle ?_
  rw [nsmul_eq_mul]
  have hc1 : ((T.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hcard
  have hnn : 0 ≤ a * ‖X‖ ^ 2 := by positivity
  nlinarith

/-- **the negative direction at `θ = π`.** -/
theorem Ginv_neg_flip {ell : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} (S : Tower (scaleUp ell 1 Lu))
    (hL : ∀ μ, 1 ≤ scaleUp ell 1 Lu μ) {a : ℝ} (ha : 0 ≤ a) (Lam : Set (PeriodicLatticeSite Lu))
    (b : Bond (scaleUp ell 1 Lu)) (hfar : ∀ y ∈ S.Om 1, 9 * ell < pdist y b.1) (hb0 : b.1 ∈ S.Om 0)
    (p0 : PeriodicLatticePlaquette (scaleUp ell 1 Lu)) (hp0 : p0 ∈ plaqIn (S.Om 0))
    (hbp : b ∈ periodicPlaquetteBoundaryEdges p0) (X : SuTwo) :
    ∃ Y : ↥(bondSupp (geomOf ell 1 S)),
      ⟪Y, (gparams ell 1 Lu hell S (Upi b) a Lam).data.Ginv Y⟫ ≤ (a - 1) * ‖X‖ ^ 2 := by
  classical
  set G := geomOf ell 1 S with hG
  have hmem : (WithLp.toLp 2 (Pi.single b X) : BondFnL2 (scaleUp ell 1 Lu)) ∈ bondSupp G := by
    intro e he
    have hne : e ≠ b := by rintro rfl; exact he (Or.inl hb0)
    show (Pi.single b X : Bond _ → SuTwo) e = 0
    rw [Pi.single_apply, if_neg hne]
  refine ⟨⟨_, hmem⟩, ?_⟩
  set P := gparams ell 1 Lu hell S (Upi b) a Lam with hP
  rw [Ginv_form P]
  have hiE : iE P.G ⟨_, hmem⟩ = (WithLp.toLp 2 (Pi.single b X) : BondFnL2 (scaleUp ell 1 Lu)) := rfl
  rw [hiE]
  have hR : Rproj G (Upi b) (gradAdj (Upi b) (WithLp.toLp 2 (Pi.single b X))) = 0 :=
    Rproj_single S (Upi b) b X (fun y hy => by have := hfar y hy; omega)
  have hW : Wop P.G P.U P.a (WithLp.toLp 2 (Pi.single b X)) = WithLp.toLp 2 (Pi.single b X) := by
    show Wop G (Upi b) a _ = _
    unfold Wop
    simp only [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, hR,
      map_zero, sub_zero]
  have hT : Tfull P.G P.U (WithLp.toLp 2 (Pi.single b X)) = 0 := by
    show Tfull G (Upi b) _ = 0
    unfold Tfull
    rw [ContinuousLinearMap.comp_apply, hR]
  rw [hW, hT, norm_zero]
  have hD := Delta_flip_le hL G b X p0 hp0 hbp
  have hM := mass_single_le hell S (Upi b) ha b X (fun y hy => by have := hfar y hy; omega)
  have hD' : ⟪(WithLp.toLp 2 (Pi.single b X) : BondFnL2 (scaleUp ell 1 Lu)),
      Delta P.G P.U (WithLp.toLp 2 (Pi.single b X))⟫ ≤ -‖X‖ ^ 2 := hD
  have hM' : ⟪(WithLp.toLp 2 (Pi.single b X) : BondFnL2 (scaleUp ell 1 Lu)),
      MassFull P.G P.a P.sector (WithLp.toLp 2 (Pi.single b X))⟫ ≤ a * ‖X‖ ^ 2 := hM
  have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [h0]
  linarith

#print axioms Delta_form_sum
#print axioms Delta_flip_le
#print axioms Rproj_single
#print axioms mass_single_le
#print axioms Ginv_neg_flip

end AdalyFormal.CoverNec
