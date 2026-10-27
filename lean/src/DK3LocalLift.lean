import DK3UnitRaw
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.DK3.Unit
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
attribute [local irreducible] AdalyFormal.Balaban.AdmissibleSubspace.blockOf
  AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice
  AdalyFormal.Balaban.AdmissibleSubspace.staircasePath
  AdalyFormal.Balaban.AdmissibleSubspace.axisSegment unitCoordinates

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
theorem smoothAt_inverse (f : ℝ → E →L[ℝ] E) (h : ContDiffAt ℝ ⊤ f 0)
    (hu : IsUnit (f 0)) : ContDiffAt ℝ ⊤ (fun t => Ring.inverse (f t)) 0 := by
  obtain ⟨u,he⟩ := hu
  have hi : ContDiffAt ℝ ⊤ Ring.inverse (f 0) := by
    rw [← he]
    exact contDiffAt_ringInverse ℝ (R := E →L[ℝ] E) u
  exact hi.comp 0 h

end General

/-- Linear maps commute with the genuine second jet of a C2 germ. -/
theorem jet_clm {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (f : E → F) (hf : ContDiffAt ℝ 2 f 0) (B : E) :
    HConstruction.Reproduced.Dtilde2Shape (fun X => L (f X)) B = L (HConstruction.Reproduced.Dtilde2Shape f B) := by
  let g : ℝ → F := fun t => f (t • B)
  have hl : ContDiffAt ℝ 2 (fun t : ℝ => t • B) 0 := contDiffAt_id.smul contDiffAt_const
  have hs : ContDiffAt ℝ 2 f ((0 : ℝ) • B) := by simpa using hf
  have hg : ContDiffAt ℝ 2 g 0 := hs.comp (0 : ℝ) hl
  have hgd : ContDiffAt ℝ 1 (deriv g) 0 := hg.derivWithin (by norm_num)
  have hev : ∀ᶠ t in nhds (0 : ℝ), DifferentiableAt ℝ g t :=
    ((hg.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).eventually (by simp)).mono
      (fun t ht => ht.differentiableAt one_ne_zero)
  have heq : deriv (fun t => L (g t)) =ᶠ[nhds 0] (fun t => L (deriv g t)) := by
    filter_upwards [hev] with t ht
    exact (L.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).deriv
  have hd := (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hgd.differentiableAt one_ne_zero).hasDerivAt).deriv
  change (1/2 : ℝ) • deriv (deriv (fun t => L (g t))) 0 =
    L ((1/2 : ℝ) • deriv (deriv g) 0)
  simp only [Function.comp_def] at hd
  rw [heq.deriv_eq,hd,map_smul]


theorem second_ray_eq_hessian {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiffAt ℝ 2 f 0) (B : E) :
    deriv (deriv (fun t : ℝ => f (t • B))) 0 =
      (fderiv ℝ (fderiv ℝ f) 0) B B := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => s • B) B t := by
    simpa using (hasDerivAt_id t).smul_const B
  have h1 : ContDiffAt ℝ 1 f 0 := hf.of_le (by norm_num)
  have hev : ∀ᶠ x in nhds (0 : E), DifferentiableAt ℝ f x :=
    (h1.eventually (by simp)).mono (fun x hx => hx.differentiableAt one_ne_zero)
  have ht : Filter.Tendsto (fun t : ℝ => t • B) (nhds 0) (nhds (0 : E)) := by
    simpa only [ContinuousAt,zero_smul] using (hline 0).continuousAt
  have heq : deriv (fun t : ℝ => f (t • B)) =ᶠ[nhds 0]
      (fun t : ℝ => (fderiv ℝ f (t • B)) B) := by
    filter_upwards [ht.eventually hev] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  rw [heq.deriv_eq]
  have hc := (hdf.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt_of_eq
    0 (hline 0) (by simp)
  have hd := hc.clm_apply (hasDerivAt_const (0 : ℝ) B)
  simpa only [ContinuousLinearMap.map_zero,add_zero,Function.comp_def] using hd.deriv


def crossingMatrix (t : ℝ) : W →L[ℝ] W := (rawQ t).comp corridorLift

theorem crossingMatrix_zero : crossingMatrix 0 = 1 := by
  unfold crossingMatrix
  rw [rawQ_zero]
  apply ContinuousLinearMap.ext
  exact rawLinear_corridorLift

theorem smoothAt_crossingMatrix : ContDiffAt ℝ ⊤ crossingMatrix 0 :=
  smoothAt_rawQ.clm_comp contDiffAt_const

theorem crossingMatrix_zero_unit : IsUnit (crossingMatrix 0) := by rw [crossingMatrix_zero]; exact isUnit_one

theorem eventually_crossingMatrix_unit : ∀ᶠ t in nhds (0 : ℝ), IsUnit (crossingMatrix t) :=
  smoothAt_crossingMatrix.continuousAt.eventually
    ((Units.isOpen (R := W →L[ℝ] W)).mem_nhds crossingMatrix_zero_unit)

def localLift (t : ℝ) : W →L[ℝ] K := corridorLift.comp (Ring.inverse (crossingMatrix t))

theorem smoothAt_localLift : ContDiffAt ℝ ⊤ localLift 0 :=
  contDiffAt_const.clm_comp (smoothAt_inverse crossingMatrix smoothAt_crossingMatrix crossingMatrix_zero_unit)

theorem localLift_right (t : ℝ) (ht : IsUnit (crossingMatrix t)) :
    (rawQ t).comp (localLift t) = ContinuousLinearMap.id ℝ W := Ring.mul_inverse_cancel _ ht

theorem localLift_support (t : ℝ) (v : W) (b : Bond unitL) (hb : ¬ Crossing b) :
    unitCoordinates (localLift t v) b = 0 := by
  change unitCoordinates (corridorLift _) b = 0
  rw [corridorLift_apply, if_neg hb]

theorem localLift_unique (t : ℝ) (ht : IsUnit (crossingMatrix t)) (D : K) (v : W)
    (hs : ∀ b : Bond unitL, ¬ Crossing b → unitCoordinates D b = 0)
    (hq : rawQ t D = v) : D = localLift t v := by
  have hD := corridor_unique D (rawLinear D) hs rfl
  have hC : crossingMatrix t (rawLinear D) = v := by
    change rawQ t (corridorLift (rawLinear D)) = v
    rw [← hD, hq]
  have hi := congrArg (fun T : W →L[ℝ] W => T (rawLinear D)) (Ring.inverse_mul_cancel _ ht)
  change Ring.inverse (crossingMatrix t) (crossingMatrix t (rawLinear D)) = rawLinear D at hi
  rw [hC] at hi
  change D = corridorLift (Ring.inverse (crossingMatrix t) v)
  rw [hi, ← hD]

def rawHessianAt (t : ℝ) : K →L[ℝ] K →L[ℝ] W := fderiv ℝ (fderiv ℝ (raw t)) 0

theorem smoothAt_rawHessianAt : ContDiffAt ℝ ⊤ rawHessianAt 0 := by
  have hg : ContDiffAt ℝ ⊤ (fun z : (ℝ × K) × K => (z.1.1,z.2)) ((0,0),0) :=
    (contDiffAt_fst.fst).prodMk contDiffAt_snd
  have h := smoothAt_raw_joint.comp ((0,0),0) hg
  have hf : ContDiffAt ℝ ⊤ (fun z : ℝ × K => fderiv ℝ (raw z.1) z.2) (0,0) :=
    h.fderiv contDiffAt_snd (by simp)
  exact hf.fderiv contDiffAt_const (by simp)

def unitD2 (t : ℝ) (B : K) : K := localLift t ((1/2 : ℝ) • rawHessianAt t B B)

def liftedRaw (t : ℝ) (B : K) : K := localLift t (raw t B)

theorem liftedRaw_jet (t : ℝ) (ht : ContDiffAt ℝ 2 (raw t) 0) (B : K) :
    HConstruction.Reproduced.Dtilde2Shape (liftedRaw t) B = unitD2 t B := by
  change HConstruction.Reproduced.Dtilde2Shape (fun X => localLift t (raw t X)) B = _
  rw [jet_clm (localLift t) (raw t) ht]
  change localLift t ((1/2 : ℝ) • deriv (deriv (fun s : ℝ => raw t (s • B))) 0) = _
  rw [second_ray_eq_hessian ht]
  rfl

theorem unitD2_characterization (t : ℝ) (ht : IsUnit (crossingMatrix t)) (B : K) :
    (∀ b : Bond unitL, ¬ Crossing b → unitCoordinates (unitD2 t B) b = 0) ∧
    rawQ t (unitD2 t B) = (1/2 : ℝ) • rawHessianAt t B B ∧
    ∀ D : K, (∀ b : Bond unitL, ¬ Crossing b → unitCoordinates D b = 0) →
      rawQ t D = (1/2 : ℝ) • rawHessianAt t B B → D = unitD2 t B := by
  refine ⟨fun b hb => localLift_support t _ b hb, ?_, fun D hs hq => localLift_unique t ht D _ hs hq⟩
  exact congrArg (fun T : W →L[ℝ] W => T ((1/2 : ℝ) • rawHessianAt t B B)) (localLift_right t ht)

end HConstruction.DK3.Unit
