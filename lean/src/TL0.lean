import RC2

/-!
# TL0 -- ALIGNED-agreement congruence of the raw step (copy of ZR8Read `coarsePathHolonomy_congr` ... `qStepComp_congr_bg`)

At an `s`-aligned bond `c` (`s ∣ L`), the raw step `rawStep s ell V0 V1 c` (hence `qStepComp s ell V0 c`) reads `V0` only at the
`s`-ALIGNED sites of the ball `(c₋, 4 s ell)`: every transport path starts at an aligned site and moves by multiples of `s`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.TowerLoc

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage Qcomposite)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS cPlusS_eq coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)

variable {L : PeriodicLatticeExtent}

theorem coarseShift_mul_mem_al (s t : ℕ) (hdvd : ∀ ν, s ∣ L ν + 1) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L s) (μ : Fin 3) : coarseShift y (s * t) μ ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice] at hy ⊢
  intro ν
  by_cases hν : ν = μ
  · subst hν
    rw [coarseShift_val_eq, Nat.mod_mod_of_dvd _ (hdvd ν), Nat.add_mul_mod_self_left]
    exact hy ν
  · rw [coarseShift_apply_ne y _ μ ν hν]; exact hy ν

theorem coarseShift_mem_al1 (s : ℕ) (hdvd : ∀ ν, s ∣ L ν + 1) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L s) (μ : Fin 3) : coarseShift y s μ ∈ CoarseLattice L s := by
  have := coarseShift_mul_mem_al s 1 hdvd y hy μ
  rwa [mul_one] at this

/-- the block sites of an aligned base are aligned -/
theorem stepBlock_al {y x : PeriodicLatticeSite L} {s ell : ℕ} (hy : y ∈ CoarseLattice L s)
    (hx : x ∈ stepBlockOf y s ell) : x ∈ CoarseLattice L s := by
  rw [mem_stepBlockOf] at hx
  rw [mem_CoarseLattice] at hy ⊢
  intro μ
  obtain ⟨h1, _, h3⟩ := hx μ
  have h4 : (x μ).val = (y μ).val + ((x μ).val - (y μ).val) := by omega
  have h5 : s ∣ (y μ).val := Nat.dvd_of_mod_eq_zero (hy μ)
  exact Nat.mod_eq_zero_of_dvd (by rw [h4]; exact Nat.dvd_add h5 h3)

theorem agree_mono_al {A : Set (PeriodicLatticeSite L)} {y y' : PeriodicLatticeSite L} {R r : ℕ}
    {G : Type*} {V V' : PeriodicLinkConfiguration G L}
    (h : AgreeAt (Ball y R ∩ A) V V') (hs : Ball y' r ⊆ Ball y R) : AgreeAt (Ball y' r ∩ A) V V' :=
  h.mono (fun z hz => ⟨hs hz.1, hz.2⟩)

theorem coarsePathHolonomy_congr_al {G : Type*} [Group G] (s : ℕ) (hd : ∀ ν, s ∣ L ν + 1)
    {V V' : PeriodicLinkConfiguration G L} (p : List (Fin 3)) :
    ∀ (y : PeriodicLatticeSite L), y ∈ CoarseLattice L s →
      AgreeAt (Ball y (s * p.length) ∩ CoarseLattice L s) V V' →
      coarsePathHolonomy s V y p = coarsePathHolonomy s V' y p := by
  induction p with
  | nil => intro y _ _; rfl
  | cons μ rest ih =>
      intro y hy h
      show V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) rest
        = V' (y, μ) * coarsePathHolonomy s V' (coarseShift y s μ) rest
      rw [h y ⟨mem_Ball_self _ _, hy⟩ μ]
      congr 1
      refine ih _ (coarseShift_mem_al1 s hd y hy μ)
        (agree_mono_al h (Ball_sub (pdist_coarseShift_le y s μ) ?_))
      simp only [List.length_cons]; rw [Nat.mul_succ]; omega

theorem stridedBlockedGauge_congr_al {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]
    (P : AdalyFormal.Balaban.BlockedGauge.LogExpAd G 𝔤) (s ell : ℕ) (hs : 0 < s) (hd : ∀ ν, s ∣ L ν + 1)
    {V V' : PeriodicLinkConfiguration G L} (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L s)
    (h : AgreeAt (Ball c.1 (4 * (s * ell)) ∩ CoarseLattice L s) V V') :
    stridedBlockedGauge P s ell V c = stridedBlockedGauge P s ell V' c := by
  have hbond : coarseBondVar s ell V c = coarseBondVar s ell V' c := by
    unfold coarseBondVar
    refine coarsePathHolonomy_congr_al s hd _ _ hc (agree_mono_al h (Ball_mono ?_))
    simp only [List.length_replicate]; nlinarith
  have hcp : cPlusS s ell c ∈ CoarseLattice L s := by
    rw [cPlusS_eq]; exact coarseShift_mul_mem_al s ell hd _ hc _
  have hloop : ∀ x ∈ stepBlockOf c.1 s ell, loopVar s ell V c x = loopVar s ell V' c x := by
    intro x hx
    have hlen := length_coarseGammaPath_le hs hx
    have hdx := pdist_stepBlock_le hx
    have hxal := stepBlock_al hc hx
    unfold loopVar gammaVarStrided
    rw [hbond]
    congr 2
    · congr 1
      · refine coarsePathHolonomy_congr_al s hd _ _ hc (agree_mono_al h (Ball_mono ?_))
        have : s * (coarseGammaPath s c.1 x).length ≤ s * (3 * ell) := Nat.mul_le_mul_left _ hlen
        nlinarith
      · refine coarsePathHolonomy_congr_al s hd _ _ hxal (agree_mono_al h (Ball_sub hdx ?_))
        simp only [List.length_replicate]; nlinarith
    · congr 1
      have hc' := pdist_coarseShift_le c.1 (s * ell) c.2
      rw [← cPlusS_eq] at hc'
      refine coarsePathHolonomy_congr_al s hd _ _ hcp (agree_mono_al h (Ball_sub hc' ?_))
      have : s * (coarseGammaPath s c.1 x).length ≤ s * (3 * ell) := Nat.mul_le_mul_left _ hlen
      nlinarith
  have hsum : (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell V c x))
      = ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell V' c x) :=
    Finset.sum_congr rfl (fun x hx => by rw [hloop x hx])
  unfold stridedBlockedGauge
  rw [hbond, hsum]

theorem rProd_congr_al (s : ℕ) (hd : ∀ ν, s ∣ L ν + 1) {V0 V0' V1 V1' : PeriodicLinkConfiguration SU2 L}
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s) (p : List (Fin 3))
    (h0 : AgreeAt (Ball y (s * p.length) ∩ CoarseLattice L s) V0 V0')
    (h1 : AgreeAt (Ball y (s * p.length) ∩ CoarseLattice L s) V1 V1') :
    rProd s V0 V1 y p = rProd s V0' V1' y p := by
  rw [rProd_eq, rProd_eq]
  have h01 : AgreeAt (Ball y (s * p.length) ∩ CoarseLattice L s) (fun b => V1 b * V0 b) (fun b => V1' b * V0' b) :=
    fun z hz μ => by simp only [h0 z hz μ, h1 z hz μ]
  rw [coarsePathHolonomy_congr_al s hd p y hy h01, coarsePathHolonomy_congr_al s hd p y hy h0]

theorem sBlock_congr_al (s ell : ℕ) (hs : 0 < s) (hd : ∀ ν, s ∣ L ν + 1)
    {V0 V0' V1 V1' : PeriodicLinkConfiguration SU2 L} (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s)
    (h0 : AgreeAt (Ball y (3 * (s * ell)) ∩ CoarseLattice L s) V0 V0')
    (h1 : AgreeAt (Ball y (3 * (s * ell)) ∩ CoarseLattice L s) V1 V1') :
    sBlock s ell V0 V1 y = sBlock s ell V0' V1' y := by
  unfold sBlock
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hlen := length_coarseGammaPath_le hs hx
  have hb : s * (coarseGammaPath s y x).length ≤ 3 * (s * ell) := by
    have := Nat.mul_le_mul_left s hlen; nlinarith
  rw [rProd_congr_al s hd y hy _ (agree_mono_al h0 (Ball_mono hb)) (agree_mono_al h1 (Ball_mono hb))]

theorem rawStep_congr_al (s ell : ℕ) (hs : 0 < s) (hd : ∀ ν, s ∣ L ν + 1)
    {V0 V0' V1 V1' : PeriodicLinkConfiguration SU2 L} (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L s)
    (h0 : AgreeAt (Ball c.1 (4 * (s * ell)) ∩ CoarseLattice L s) V0 V0')
    (h1 : AgreeAt (Ball c.1 (4 * (s * ell)) ∩ CoarseLattice L s) V1 V1') :
    rawStep s ell V0 V1 c = rawStep s ell V0' V1' c := by
  have hc' := pdist_coarseShift_le c.1 (s * ell) c.2
  rw [← cPlusS_eq] at hc'
  have hcp : cPlusS s ell c ∈ CoarseLattice L s := by
    rw [cPlusS_eq]; exact coarseShift_mul_mem_al s ell hd _ hc _
  have hsub : Ball (cPlusS s ell c) (3 * (s * ell)) ⊆ Ball c.1 (4 * (s * ell)) := Ball_sub hc' (by omega)
  have hsub0 : Ball c.1 (3 * (s * ell)) ⊆ Ball c.1 (4 * (s * ell)) := Ball_mono (by omega)
  have h01 : AgreeAt (Ball c.1 (4 * (s * ell)) ∩ CoarseLattice L s) (fun b => V1 b * V0 b) (fun b => V1' b * V0' b) :=
    fun z hz μ => by simp only [h0 z hz μ, h1 z hz μ]
  unfold rawStep
  rw [sBlock_congr_al s ell hs hd c.1 hc (agree_mono_al h0 hsub0) (agree_mono_al h1 hsub0),
    sBlock_congr_al s ell hs hd (cPlusS s ell c) hcp (agree_mono_al h0 hsub) (agree_mono_al h1 hsub),
    stridedBlockedGauge_congr_al su2LogExp s ell hs hd c hc h01,
    stridedBlockedGauge_congr_al su2LogExp s ell hs hd c hc h0]

theorem qStepComp_congr_bg_al (s ell : ℕ) (hs : 0 < s) (hd : ∀ ν, s ∣ L ν + 1)
    {V0 V0' : PeriodicLinkConfiguration SU2 L} (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L s)
    (h : AgreeAt (Ball c.1 (4 * (s * ell)) ∩ CoarseLattice L s) V0 V0') :
    qStepComp s ell V0 c = qStepComp s ell V0' c := by
  funext a
  show fromM2 (su2Log (rawStep s ell V0 (expCfgX a) c)) = fromM2 (su2Log (rawStep s ell V0' (expCfgX a) c))
  rw [rawStep_congr_al s ell hs hd c hc h (fun _ _ _ => rfl)]

end AdalyFormal.TowerLoc

#print axioms AdalyFormal.TowerLoc.stepBlock_al
#print axioms AdalyFormal.TowerLoc.coarsePathHolonomy_congr_al
#print axioms AdalyFormal.TowerLoc.stridedBlockedGauge_congr_al
#print axioms AdalyFormal.TowerLoc.rawStep_congr_al
#print axioms AdalyFormal.TowerLoc.qStepComp_congr_bg_al
