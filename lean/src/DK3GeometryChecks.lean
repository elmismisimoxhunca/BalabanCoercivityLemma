import DK3C
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.DK3
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf mem_blockOf mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (pathSite)
attribute [local irreducible] blockOf CoarseLattice

/-- Unit shifts on side32 are stride-eight shifts on the original fine torus. -/
theorem embed_shift (x : US) (μ : Fin 3) :
    embed (periodicLatticeShift x μ) =
      AdalyFormal.Balaban.CoarseCurl.coarseShift (embed x) 8 μ := by
  funext ν
  apply Fin.ext
  by_cases h : ν = μ
  · subst ν
    rw [AdalyFormal.Balaban.CoarseCurl.coarseShift_val_eq]
    change 8 * ((periodicLatticeShift x μ) μ).val = (8*(x μ).val+8)%256
    rw [shift_self_val]
    have hx : (x μ).val < 32 := (x μ).isLt
    omega
  · rw [AdalyFormal.Balaban.CoarseCurl.coarseShift_apply_ne _ _ _ _ h]
    change 8 * ((periodicLatticeShift x μ) ν).val = 8*(x ν).val
    rw [periodicLatticeShift,Function.update_of_ne h]

theorem unit_plaquette_reindex (t : ℝ) (x : US) (μ ν : Fin 3) :
    DepthUniformity.Strided.orientedPlaqHolS 1 (V t) x μ ν =
    DepthUniformity.Strided.orientedPlaqHolS 8 (Vfine t) (embed x) μ ν := by
  simp only [DepthUniformity.Strided.orientedPlaqHolS,
    SmallnessBridge.Assemble.coarseShift_one_eq,V,embed_shift]

/-- Prop1's certified bound on the ACTUAL side32 background after reindexing. -/
theorem unit_background_regular (t : ℝ) (ht : |t| ≤ interval) (x : US) (μ ν : Fin 3) :
    AdalyFormal.Balaban.RMapLipschitz.frobNorm
      (((DepthUniformity.Strided.orientedPlaqHolS 1 (V t) x μ ν :
        AdalyFormal.Balaban.SuTwoLogExp.SU2) : AdalyFormal.Balaban.SuTwoLogExp.M2)-1) ≤ 2*alpha0 := by
  rw [unit_plaquette_reindex]
  exact current_background_regular t (ht.trans interval_le_regularity)
    (embed x) (embed_coarse x) μ ν

/-- The raw time-one convention differs by exactly two, so its kernel is
precisely the normalized one-step Q1 kernel in (3.155). -/
theorem nativeRawQ_kernel_iff (t : ℝ) (B : K) :
    nativeRawQ t B = 0 ↔ unitQ1 t (unitInput B) = 0 := by
  have he : HConstruction.Carrier.cfl2Equiv 2 (nativeRawQ t B) =
      (2:ℝ) • unitQ1 t (unitInput B) := by
    change unitQ1 t ((2:ℝ) • unitInput B) = _
    rw [map_smul]
  constructor
  · intro h
    rw [h,map_zero] at he
    exact (smul_eq_zero.mp he.symm).resolve_left (by norm_num)
  · intro h
    apply (HConstruction.Carrier.cfl2Equiv 2).injective
    rw [he,h,smul_zero,map_zero]

theorem C_unitQ1_kernel (t : ℝ) (ht : |t| ≤ interval) (B : Reduced) :
    unitQ1 t (unitInput (C t B)) = 0 :=
  (nativeRawQ_kernel_iff t (C t B)).mp (C_kernel t ht B)

/-- The actual two unit edges in the next coarse bond c. -/
def coarseSegment (c : CoarseBond unitL 2) : Finset (Bond unitL) :=
  (Finset.range 2).image (fun i => (pathSite c.1.1 c.2 i,c.2))

/-- B(c): interface bonds leaving the block at c's initial endpoint. -/
def interface (c : CoarseBond unitL 2) (b : Bond unitL) : Prop :=
  b.1 ∈ blockOf c.1.1 2 ∧ periodicLatticeShift b.1 b.2 ∉ blockOf c.1.1 2

theorem crossing_end_outside (c : CoarseBond unitL 2) :
    periodicLatticeShift (crossingBond c).1 c.2 ∉ blockOf c.1.1 2 := by
  intro h
  have hi := mem_blockOf.mp h c.2
  have he := mem_CoarseLattice.mp c.1.2 c.2
  have hl : (c.1.1 c.2).val < 32 := (c.1.1 c.2).isLt
  change (c.1.1 c.2).val ≤
    ((periodicLatticeShift (periodicLatticeShift c.1.1 c.2) c.2) c.2).val ∧
    ((periodicLatticeShift (periodicLatticeShift c.1.1 c.2) c.2) c.2).val <
      (c.1.1 c.2).val+2 at hi
  rw [shift_self_val,shift_self_val] at hi
  omega

theorem crossing_interface (c : CoarseBond unitL 2) : interface c (crossingBond c) :=
  ⟨crossing_mem c,crossing_end_outside c⟩

/-- Explicit source identification: B(c) intersect c contains exactly b0. -/
theorem unique_interface_crossing (c : CoarseBond unitL 2) (b : Bond unitL) :
    b ∈ coarseSegment c ∧ interface c b ↔ b = crossingBond c := by
  have hs : coarseSegment c = {(c.1.1,c.2), crossingBond c} := by
    have hr : Finset.range 2 = {0,1} := by decide
    simp [coarseSegment, hr, AdalyFormal.Balaban.QOne.pathSite_zero,
      AdalyFormal.Balaban.QOne.pathSite_succ,crossingBond]
  rw [hs]
  constructor
  · rintro ⟨hb,hi⟩
    rcases Finset.mem_insert.mp hb with he | he
    · subst b
      exact (hi.2 (crossing_mem c)).elim
    · exact Finset.mem_singleton.mp he
  · rintro rfl
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _),crossing_interface c⟩

/-- Literal B(c) of p.428: endpoints lie in the specified two blocks. -/
def sourceInterface (c : CoarseBond unitL 2) (b : Bond unitL) : Prop :=
  b.1 ∈ blockOf c.1.1 2 ∧ periodicLatticeShift b.1 b.2 ∈
    blockOf (AdalyFormal.Balaban.CoarseCurl.coarseShift c.1.1 2 c.2) 2

theorem crossing_sourceInterface (c : CoarseBond unitL 2) : sourceInterface c (crossingBond c) := by
  refine ⟨crossing_mem c,?_⟩
  change AdalyFormal.Balaban.CoarseCurl.coarseShift c.1.1 2 c.2 ∈
    blockOf (AdalyFormal.Balaban.CoarseCurl.coarseShift c.1.1 2 c.2) 2
  exact center_mem _

theorem center_not_sourceInterface (c : CoarseBond unitL 2) :
    ¬ sourceInterface c (c.1.1,c.2) := by
  intro h
  have hi := mem_blockOf.mp h.2 c.2
  have he := mem_CoarseLattice.mp c.1.2 c.2
  have hl : (c.1.1 c.2).val < 32 := (c.1.1 c.2).isLt
  change ((periodicLatticeShift (periodicLatticeShift c.1.1 c.2) c.2) c.2).val ≤
      ((periodicLatticeShift c.1.1 c.2) c.2).val ∧
    ((periodicLatticeShift c.1.1 c.2) c.2).val <
      ((periodicLatticeShift (periodicLatticeShift c.1.1 c.2) c.2) c.2).val+2 at hi
  simp only [shift_self_val] at hi
  omega

/-- Exactly one bond of the actual B(c) lies in c, including wrapping blocks. -/
theorem literal_unique_b0 (c : CoarseBond unitL 2) (b : Bond unitL) :
    b ∈ coarseSegment c ∧ sourceInterface c b ↔ b = crossingBond c := by
  have hr : Finset.range 2 = {0,1} := by decide
  have hs : coarseSegment c = {(c.1.1,c.2), crossingBond c} := by
    simp [coarseSegment,hr,AdalyFormal.Balaban.QOne.pathSite_zero,
      AdalyFormal.Balaban.QOne.pathSite_succ,crossingBond]
  rw [hs]
  constructor
  · rintro ⟨hb,hi⟩
    rcases Finset.mem_insert.mp hb with he | he
    · subst b; exact (center_not_sourceInterface c hi).elim
    · exact Finset.mem_singleton.mp he
  · rintro rfl
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _),crossing_sourceInterface c⟩

/-- Fine curvature witness stays on the original side256 torus. -/
def plaquette : PeriodicLatticePlaquette fineL := (origin, ⟨(0,1),by decide⟩)

theorem origin_shift_ne (μ : Fin 3) : periodicLatticeShift origin μ ≠ origin := by
  intro h
  have hh := congrFun h μ
  change (Function.update origin μ (origin μ+1)) μ = origin μ at hh
  simp only [Function.update_self,origin] at hh
  norm_num at hh

theorem curvature (t : ℝ) : AdalyFormal.Balaban.DeltaPrime.holonomyElem (U t) plaquette =
    HConstruction.NfRepair.Reproduced.rotElem t := by
  have hmain : U t (origin,0) = HConstruction.NfRepair.Reproduced.rotElem t := by simp [U]
  have hoff (b : Bond fineL) (hb : b ≠ (origin,0)) : U t b = 1 := by simp [U,hb]
  change U t (origin,0) * U t (periodicLatticeShift origin 0,1) *
    (U t (periodicLatticeShift origin 1,0))⁻¹ * (U t (origin,1))⁻¹ = _
  rw [hmain,hoff _ (by intro h; have := congrArg Prod.snd h; norm_num at this),
    hoff _ (by intro h; exact origin_shift_ne 1 (congrArg Prod.fst h)),
    hoff _ (by intro h; have := congrArg Prod.snd h; norm_num at this)]
  simp

theorem interval_has_curved_endpoint :
    AdalyFormal.Balaban.DeltaPrime.holonomyElem (U interval) plaquette ≠ 1 := by
  rw [curvature]
  exact HConstruction.NfRepair.Reproduced.rotElem_ne_one interval_pos.ne'
end HConstruction.DK3
