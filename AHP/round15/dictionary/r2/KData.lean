import DrEquiv

/-! Exact full-collar matrices and Schur-complement identities. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000


/-!
Round 15: an exact dominant two-sublattice collar transfer certificate.

The displayed 16-by-16 matrix is the reduced eight-transverse-mode companion
matrix identified by `inspect_full.py` and `factor_audit.py`.  This file proves
its two dominant reciprocal eigenpairs directly.  It does NOT assert that this
matrix has already been identified with the frozen right-star operator in Lean;
that physical dictionary is recorded separately in NOTES.md.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.Round15.Dictionary

noncomputable section

/-- The dominant root satisfies rho+rho⁻¹=5-sqrt(2). -/
def rho : ℝ := (5-Real.sqrt 2+Real.sqrt (23-10*Real.sqrt 2))/2

/-- A sparse charged internal-sublattice phase. -/
def phase : ℂ := (1+Complex.I)/(Real.sqrt 2:ℂ)

def mode0 : Fin 8 → ℂ
  | 0 => 1 | 1 => phase | 2 => 1 | 3 => phase | _ => 0

def mode1 : Fin 8 → ℂ
  | 4 => 1 | 5 => phase | 6 => 1 | 7 => phase | _ => 0

/-- Geometric state at adjacent layers: the second half is rho⁻¹ times the first. -/
def forward (w : Fin 8 → ℂ) : Fin 16 → ℂ :=
  fun i => if h : i.val < 8 then w ⟨i.val,h⟩ else (1/rho : ℂ)*w ⟨i.val-8,by omega⟩

/-- The same charged internal mode transported by the reciprocal root. -/
def backward (w : Fin 8 → ℂ) : Fin 16 → ℂ :=
  fun i => if h : i.val < 8 then w ⟨i.val,h⟩ else (rho : ℂ)*w ⟨i.val-8,by omega⟩

def collarA : Matrix (Fin 8) (Fin 8) ℂ :=
    !![(-193/329 : ℂ),(-41/329 : ℂ)+(41/329 : ℂ)*Complex.I,(52/329 : ℂ),(-6/329 : ℂ)+(6/329 : ℂ)*Complex.I,(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(1/47 : ℂ)*Complex.I;(-41/329 : ℂ)+(-41/329 : ℂ)*Complex.I,(-193/329 : ℂ),(-6/329 : ℂ)+(-6/329 : ℂ)*Complex.I,(52/329 : ℂ),(1/47 : ℂ)+(-6/47 : ℂ)*Complex.I,(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-1/47 : ℂ)+(6/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I;(52/329 : ℂ),(-6/329 : ℂ)+(6/329 : ℂ)*Complex.I,(-193/329 : ℂ),(-41/329 : ℂ)+(41/329 : ℂ)*Complex.I,(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I;(-6/329 : ℂ)+(-6/329 : ℂ)*Complex.I,(52/329 : ℂ),(-41/329 : ℂ)+(-41/329 : ℂ)*Complex.I,(-193/329 : ℂ),(-1/47 : ℂ)+(6/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(1/47 : ℂ)+(-6/47 : ℂ)*Complex.I,(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I;(6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(1/47 : ℂ)+(6/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-1/47 : ℂ)+(-6/47 : ℂ)*Complex.I,(-33/47 : ℂ),(2/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-14/47 : ℂ),(-2/47 : ℂ)+(2/47 : ℂ)*Complex.I;(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(2/47 : ℂ)+(2/47 : ℂ)*Complex.I,(-33/47 : ℂ),(-2/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-14/47 : ℂ);(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-1/47 : ℂ)+(-6/47 : ℂ)*Complex.I,(6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(1/47 : ℂ)+(6/47 : ℂ)*Complex.I,(-14/47 : ℂ),(-2/47 : ℂ)+(2/47 : ℂ)*Complex.I,(-33/47 : ℂ),(2/47 : ℂ)+(-2/47 : ℂ)*Complex.I;(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(-2/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-14/47 : ℂ),(2/47 : ℂ)+(2/47 : ℂ)*Complex.I,(-33/47 : ℂ)]
def collarB : Matrix (Fin 8) (Fin 8) ℂ :=
    !![(1373/329 : ℂ),(82/329 : ℂ)+(-82/329 : ℂ)*Complex.I,(-762/329 : ℂ),(12/329 : ℂ)+(-12/329 : ℂ)*Complex.I,(-59/47 : ℂ)+(2/47 : ℂ)*Complex.I,(59/47 : ℂ)+(2/47 : ℂ)*Complex.I,(59/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-59/47 : ℂ)+(-2/47 : ℂ)*Complex.I;(82/329 : ℂ)+(82/329 : ℂ)*Complex.I,(1373/329 : ℂ),(12/329 : ℂ)+(12/329 : ℂ)*Complex.I,(-762/329 : ℂ),(-2/47 : ℂ)+(59/47 : ℂ)*Complex.I,(-59/47 : ℂ)+(2/47 : ℂ)*Complex.I,(2/47 : ℂ)+(-59/47 : ℂ)*Complex.I,(59/47 : ℂ)+(-2/47 : ℂ)*Complex.I;(-762/329 : ℂ),(12/329 : ℂ)+(-12/329 : ℂ)*Complex.I,(1373/329 : ℂ),(82/329 : ℂ)+(-82/329 : ℂ)*Complex.I,(59/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-59/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-59/47 : ℂ)+(2/47 : ℂ)*Complex.I,(59/47 : ℂ)+(2/47 : ℂ)*Complex.I;(12/329 : ℂ)+(12/329 : ℂ)*Complex.I,(-762/329 : ℂ),(82/329 : ℂ)+(82/329 : ℂ)*Complex.I,(1373/329 : ℂ),(2/47 : ℂ)+(-59/47 : ℂ)*Complex.I,(59/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-2/47 : ℂ)+(59/47 : ℂ)*Complex.I,(-59/47 : ℂ)+(2/47 : ℂ)*Complex.I;(-59/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-2/47 : ℂ)+(-59/47 : ℂ)*Complex.I,(59/47 : ℂ)+(2/47 : ℂ)*Complex.I,(2/47 : ℂ)+(59/47 : ℂ)*Complex.I,(207/47 : ℂ),(-51/47 : ℂ)+(51/47 : ℂ)*Complex.I,(28/47 : ℂ),(4/47 : ℂ)+(-4/47 : ℂ)*Complex.I;(59/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-59/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-59/47 : ℂ)+(2/47 : ℂ)*Complex.I,(59/47 : ℂ)+(2/47 : ℂ)*Complex.I,(-51/47 : ℂ)+(-51/47 : ℂ)*Complex.I,(207/47 : ℂ),(4/47 : ℂ)+(4/47 : ℂ)*Complex.I,(28/47 : ℂ);(59/47 : ℂ)+(2/47 : ℂ)*Complex.I,(2/47 : ℂ)+(59/47 : ℂ)*Complex.I,(-59/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-2/47 : ℂ)+(-59/47 : ℂ)*Complex.I,(28/47 : ℂ),(4/47 : ℂ)+(-4/47 : ℂ)*Complex.I,(207/47 : ℂ),(-51/47 : ℂ)+(51/47 : ℂ)*Complex.I;(-59/47 : ℂ)+(2/47 : ℂ)*Complex.I,(59/47 : ℂ)+(2/47 : ℂ)*Complex.I,(59/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-59/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(4/47 : ℂ)+(4/47 : ℂ)*Complex.I,(28/47 : ℂ),(-51/47 : ℂ)+(-51/47 : ℂ)*Complex.I,(207/47 : ℂ)]
def collarC : Matrix (Fin 8) (Fin 8) ℂ :=
    !![(-193/329 : ℂ),(-41/329 : ℂ)+(41/329 : ℂ)*Complex.I,(52/329 : ℂ),(-6/329 : ℂ)+(6/329 : ℂ)*Complex.I,(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(1/47 : ℂ)*Complex.I;(-41/329 : ℂ)+(-41/329 : ℂ)*Complex.I,(-193/329 : ℂ),(-6/329 : ℂ)+(-6/329 : ℂ)*Complex.I,(52/329 : ℂ),(1/47 : ℂ)+(-6/47 : ℂ)*Complex.I,(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-1/47 : ℂ)+(6/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I;(52/329 : ℂ),(-6/329 : ℂ)+(6/329 : ℂ)*Complex.I,(-193/329 : ℂ),(-41/329 : ℂ)+(41/329 : ℂ)*Complex.I,(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I;(-6/329 : ℂ)+(-6/329 : ℂ)*Complex.I,(52/329 : ℂ),(-41/329 : ℂ)+(-41/329 : ℂ)*Complex.I,(-193/329 : ℂ),(-1/47 : ℂ)+(6/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(1/47 : ℂ)+(-6/47 : ℂ)*Complex.I,(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I;(6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(1/47 : ℂ)+(6/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-1/47 : ℂ)+(-6/47 : ℂ)*Complex.I,(-33/47 : ℂ),(2/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-14/47 : ℂ),(-2/47 : ℂ)+(2/47 : ℂ)*Complex.I;(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(2/47 : ℂ)+(2/47 : ℂ)*Complex.I,(-33/47 : ℂ),(-2/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-14/47 : ℂ);(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-1/47 : ℂ)+(-6/47 : ℂ)*Complex.I,(6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(1/47 : ℂ)+(6/47 : ℂ)*Complex.I,(-14/47 : ℂ),(-2/47 : ℂ)+(2/47 : ℂ)*Complex.I,(-33/47 : ℂ),(2/47 : ℂ)+(-2/47 : ℂ)*Complex.I;(6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(-1/47 : ℂ)*Complex.I,(-6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(6/47 : ℂ)+(1/47 : ℂ)*Complex.I,(-2/47 : ℂ)+(-2/47 : ℂ)*Complex.I,(-14/47 : ℂ),(2/47 : ℂ)+(2/47 : ℂ)*Complex.I,(-33/47 : ℂ)]
def dominantTransfer : Matrix (Fin 16) (Fin 16) ℂ :=
    !![(7 : ℂ),(-1 : ℂ)+(1 : ℂ)*Complex.I,(-2 : ℂ),0,0,0,0,0,(-1 : ℂ),0,0,0,0,0,0,0;(-1 : ℂ)+(-1 : ℂ)*Complex.I,(7 : ℂ),0,(-2 : ℂ),0,0,0,0,0,(-1 : ℂ),0,0,0,0,0,0;(-2 : ℂ),0,(7 : ℂ),(-1 : ℂ)+(1 : ℂ)*Complex.I,0,0,0,0,0,0,(-1 : ℂ),0,0,0,0,0;0,(-2 : ℂ),(-1 : ℂ)+(-1 : ℂ)*Complex.I,(7 : ℂ),0,0,0,0,0,0,0,(-1 : ℂ),0,0,0,0;0,0,0,0,(7 : ℂ),(-1 : ℂ)+(1 : ℂ)*Complex.I,(-2 : ℂ),0,0,0,0,0,(-1 : ℂ),0,0,0;0,0,0,0,(-1 : ℂ)+(-1 : ℂ)*Complex.I,(7 : ℂ),0,(-2 : ℂ),0,0,0,0,0,(-1 : ℂ),0,0;0,0,0,0,(-2 : ℂ),0,(7 : ℂ),(-1 : ℂ)+(1 : ℂ)*Complex.I,0,0,0,0,0,0,(-1 : ℂ),0;0,0,0,0,0,(-2 : ℂ),(-1 : ℂ)+(-1 : ℂ)*Complex.I,(7 : ℂ),0,0,0,0,0,0,0,(-1 : ℂ);(1 : ℂ),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,(1 : ℂ),0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,(1 : ℂ),0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,(1 : ℂ),0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,(1 : ℂ),0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,(1 : ℂ),0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,(1 : ℂ),0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,(1 : ℂ),0,0,0,0,0,0,0,0]
def dominantTransferInverse : Matrix (Fin 16) (Fin 16) ℂ :=
    !![0,0,0,0,0,0,0,0,(1 : ℂ),0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,(1 : ℂ),0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,(1 : ℂ),0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,(1 : ℂ),0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,(1 : ℂ),0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0,(1 : ℂ),0,0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,(1 : ℂ),0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(1 : ℂ);(-1 : ℂ),0,0,0,0,0,0,0,(7 : ℂ),(-1 : ℂ)+(1 : ℂ)*Complex.I,(-2 : ℂ),0,0,0,0,0;0,(-1 : ℂ),0,0,0,0,0,0,(-1 : ℂ)+(-1 : ℂ)*Complex.I,(7 : ℂ),0,(-2 : ℂ),0,0,0,0;0,0,(-1 : ℂ),0,0,0,0,0,(-2 : ℂ),0,(7 : ℂ),(-1 : ℂ)+(1 : ℂ)*Complex.I,0,0,0,0;0,0,0,(-1 : ℂ),0,0,0,0,0,(-2 : ℂ),(-1 : ℂ)+(-1 : ℂ)*Complex.I,(7 : ℂ),0,0,0,0;0,0,0,0,(-1 : ℂ),0,0,0,0,0,0,0,(7 : ℂ),(-1 : ℂ)+(1 : ℂ)*Complex.I,(-2 : ℂ),0;0,0,0,0,0,(-1 : ℂ),0,0,0,0,0,0,(-1 : ℂ)+(-1 : ℂ)*Complex.I,(7 : ℂ),0,(-2 : ℂ);0,0,0,0,0,0,(-1 : ℂ),0,0,0,0,0,(-2 : ℂ),0,(7 : ℂ),(-1 : ℂ)+(1 : ℂ)*Complex.I;0,0,0,0,0,0,0,(-1 : ℂ),0,0,0,0,0,(-2 : ℂ),(-1 : ℂ)+(-1 : ℂ)*Complex.I,(7 : ℂ)]

theorem rho_pos : 0 < rho := by
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hs2 := Real.sq_sqrt h2
  have hdisc : 0 ≤ 23-10*Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hsd := Real.sq_sqrt hdisc
  have hs12 : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hr : 0 < 5-Real.sqrt 2+Real.sqrt (23-10*Real.sqrt 2) := by
    nlinarith [Real.sqrt_nonneg (23-10*Real.sqrt 2)]
  exact div_pos hr (by norm_num)

theorem rho_quad : rho^2 = (5-Real.sqrt 2)*rho-1 := by
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hs2 := Real.sq_sqrt h2
  have hdisc : 0 ≤ 23-10*Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hsd := Real.sq_sqrt hdisc
  unfold rho
  field_simp
  ring_nf at *
  linear_combination hsd - hs2

theorem rho_ne_zero : rho ≠ 0 := ne_of_gt rho_pos

theorem phase_sq : phase^2 = Complex.I := by
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hs2 := Real.sq_sqrt h2
  unfold phase
  rw [div_pow, ← Complex.ofReal_pow, hs2]
  ring_nf
  simp

/-- Direct verification of the first sparse dominant eigenvector. -/
theorem dominant_mode0_forward : Matrix.mulVec dominantTransfer (forward mode0) = (rho : ℂ) • forward mode0 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [dominantTransfer, forward, mode0, phase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    norm_num <;> ring

/-- Direct verification of the shifted independent dominant eigenvector. -/
theorem dominant_mode1_forward : Matrix.mulVec dominantTransfer (forward mode1) = (rho : ℂ) • forward mode1 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [dominantTransfer, forward, mode1, phase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    norm_num <;> ring

/-- The reciprocal root acts on the first sparse mode. -/
theorem dominant_mode0_backward : Matrix.mulVec dominantTransfer (backward mode0) = (1/rho : ℂ) • backward mode0 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [dominantTransfer, backward, mode0, phase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    norm_num

/-- The reciprocal root acts on the shifted sparse mode. -/
theorem dominant_mode1_backward : Matrix.mulVec dominantTransfer (backward mode1) = (1/rho : ℂ) • backward mode1 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [dominantTransfer, backward, mode1, phase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, smul_eq_mul] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    norm_num

/-- Exact reciprocal dominant eigenpairs of the displayed collar transfer. -/
theorem dominant_eigenpairs :
    Matrix.mulVec dominantTransfer (forward mode0) = (rho : ℂ) • forward mode0 ∧
    Matrix.mulVec dominantTransfer (forward mode1) = (rho : ℂ) • forward mode1 ∧
    Matrix.mulVec dominantTransfer (backward mode0) = (1/rho : ℂ) • backward mode0 ∧
    Matrix.mulVec dominantTransfer (backward mode1) = (1/rho : ℂ) • backward mode1 :=
  ⟨dominant_mode0_forward, dominant_mode1_forward,
    dominant_mode0_backward, dominant_mode1_backward⟩


/-- The companion matrix is explicitly invertible. -/
theorem transfer_inverse :
    dominantTransfer * dominantTransferInverse = 1 ∧
    dominantTransferInverse * dominantTransfer = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dominantTransfer, dominantTransferInverse, Matrix.mul_apply,
        Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dominantTransfer, dominantTransferInverse, Matrix.mul_apply,
        Fin.sum_univ_succ]

/-- A transported scalar seed. -/
def observation (w : Fin 8 → ℂ) (n : ℕ) : Fin 8 → ℂ :=
  fun k => (rho^n : ℂ) * w k

/-- The exact second-order recurrence for the first sparse mode. -/
theorem dominant_mode0_recurrence (n : ℕ) :
    Matrix.mulVec collarA (observation mode0 (n+2)) +
      Matrix.mulVec collarB (observation mode0 (n+1)) +
      Matrix.mulVec collarC (observation mode0 n) = 0 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [collarA, collarB, collarC, observation, mode0, phase,
      dotProduct, Fin.sum_univ_succ] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    ring

/-- The exact second-order recurrence for the shifted sparse mode. -/
theorem dominant_mode1_recurrence (n : ℕ) :
    Matrix.mulVec collarA (observation mode1 (n+2)) +
      Matrix.mulVec collarB (observation mode1 (n+1)) +
      Matrix.mulVec collarC (observation mode1 n) = 0 := by
  have hr := rho_quad
  have hrC : (rho : ℂ)^2 = (5-Real.sqrt 2 : ℂ)*(rho : ℂ)-1 := by exact_mod_cast hr
  have hs2C : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hz := rho_ne_zero
  have hp := phase_sq
  funext i
  fin_cases i <;>
    simp [collarA, collarB, collarC, observation, mode1, phase,
      dotProduct, Fin.sum_univ_succ] <;>
    field_simp [hz] <;>
    ring_nf <;>
    norm_num [hrC, hs2C, hp, Complex.I_mul_I] <;>
    ring_nf <;>
    rw [hs2C] <;>
    ring

/-- Both dominant sparse modes satisfy the displayed constant-coefficient recurrence. -/
theorem dominant_recurrence :
    (∀ n : ℕ, Matrix.mulVec collarA (observation mode0 (n+2)) +
      Matrix.mulVec collarB (observation mode0 (n+1)) +
      Matrix.mulVec collarC (observation mode0 n) = 0) ∧
    (∀ n : ℕ, Matrix.mulVec collarA (observation mode1 (n+2)) +
      Matrix.mulVec collarB (observation mode1 (n+1)) +
      Matrix.mulVec collarC (observation mode1 n) = 0) :=
  ⟨dominant_mode0_recurrence, dominant_mode1_recurrence⟩

/-- Recurrence, invertible transfer and exact dominant eigenpairs. -/
theorem collar_dictionary :
    (dominantTransfer * dominantTransferInverse = 1 ∧
      dominantTransferInverse * dominantTransfer = 1) ∧
    (Matrix.mulVec dominantTransfer (forward mode0) = (rho : ℂ) • forward mode0 ∧
      Matrix.mulVec dominantTransfer (forward mode1) = (rho : ℂ) • forward mode1 ∧
      Matrix.mulVec dominantTransfer (backward mode0) = (1/rho : ℂ) • backward mode0 ∧
      Matrix.mulVec dominantTransfer (backward mode1) = (1/rho : ℂ) • backward mode1) ∧
    (∀ n : ℕ, Matrix.mulVec collarA (observation mode0 (n+2)) +
      Matrix.mulVec collarB (observation mode0 (n+1)) +
      Matrix.mulVec collarC (observation mode0 n) = 0) ∧
    (∀ n : ℕ, Matrix.mulVec collarA (observation mode1 (n+2)) +
      Matrix.mulVec collarB (observation mode1 (n+1)) +
      Matrix.mulVec collarC (observation mode1 n) = 0) :=
  ⟨transfer_inverse, dominant_eigenpairs, dominant_recurrence⟩

#print axioms collarA
#print axioms collarB
#print axioms collarC
#print axioms dominantTransferInverse
#print axioms transfer_inverse
#print axioms observation
#print axioms dominant_mode0_recurrence
#print axioms dominant_mode1_recurrence
#print axioms dominant_recurrence
#print axioms collar_dictionary

#print axioms rho
#print axioms phase
#print axioms mode0
#print axioms mode1
#print axioms forward
#print axioms backward
#print axioms dominantTransfer
#print axioms rho_pos
#print axioms rho_quad
#print axioms rho_ne_zero
#print axioms phase_sq
#print axioms dominant_mode0_forward
#print axioms dominant_mode1_forward
#print axioms dominant_mode0_backward
#print axioms dominant_mode1_backward
#print axioms dominant_eigenpairs

end
end AdalyFormal.Round15.Dictionary

open AdalyFormal.Round15.Dictionary

noncomputable def q1Kplus : Matrix (Fin 12) (Fin 12) ℂ :=
    !![(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(1 : ℂ),(1 : ℂ) * Complex.I,(0 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(1 : ℂ),(1 : ℂ) * Complex.I,(-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ)]

noncomputable def q1Kzero : Matrix (Fin 12) (Fin 12) ℂ :=
    !![(5 : ℂ),(-1 : ℂ) + (1 : ℂ) * Complex.I,(-2 : ℂ),(0 : ℂ),(-1 : ℂ),(-1 : ℂ) * Complex.I,(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ);
    (-1 : ℂ) + (-1 : ℂ) * Complex.I,(5 : ℂ),(0 : ℂ),(-2 : ℂ),(1 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ);
    (-2 : ℂ),(0 : ℂ),(5 : ℂ),(-1 : ℂ) + (1 : ℂ) * Complex.I,(0 : ℂ),(0 : ℂ),(-1 : ℂ),(-1 : ℂ) * Complex.I,(1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ);
    (0 : ℂ),(-2 : ℂ),(-1 : ℂ) + (-1 : ℂ) * Complex.I,(5 : ℂ),(0 : ℂ),(0 : ℂ),(1 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ);
    (-1 : ℂ),(1 : ℂ),(0 : ℂ),(0 : ℂ),(5 : ℂ),(0 : ℂ),(-2 : ℂ),(0 : ℂ),(-1 : ℂ),(1 : ℂ),(1 : ℂ),(-1 : ℂ);
    (1 : ℂ) * Complex.I,(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(5 : ℂ),(0 : ℂ),(-2 : ℂ),(1 : ℂ) * Complex.I,(-1 : ℂ),(-1 : ℂ) * Complex.I,(1 : ℂ);
    (0 : ℂ),(0 : ℂ),(-1 : ℂ),(1 : ℂ),(-2 : ℂ),(0 : ℂ),(5 : ℂ),(0 : ℂ),(1 : ℂ),(-1 : ℂ),(-1 : ℂ),(1 : ℂ);
    (0 : ℂ),(0 : ℂ),(1 : ℂ) * Complex.I,(-1 : ℂ),(0 : ℂ),(-2 : ℂ),(0 : ℂ),(5 : ℂ),(-1 : ℂ) * Complex.I,(1 : ℂ),(1 : ℂ) * Complex.I,(-1 : ℂ);
    (-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ),(-1 : ℂ) * Complex.I,(1 : ℂ),(1 : ℂ) * Complex.I,(5 : ℂ),(-1 : ℂ) + (1 : ℂ) * Complex.I,(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ),(1 : ℂ),(-1 : ℂ),(-1 : ℂ),(1 : ℂ),(-1 : ℂ) + (-1 : ℂ) * Complex.I,(5 : ℂ),(0 : ℂ),(0 : ℂ);
    (1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ),(1 : ℂ) * Complex.I,(-1 : ℂ),(-1 : ℂ) * Complex.I,(0 : ℂ),(0 : ℂ),(5 : ℂ),(-1 : ℂ) + (1 : ℂ) * Complex.I;
    (0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ),(-1 : ℂ),(1 : ℂ),(1 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ) + (-1 : ℂ) * Complex.I,(5 : ℂ)]

noncomputable def q1Kminus : Matrix (Fin 12) (Fin 12) ℂ :=
    !![(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (1 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (-1 : ℂ) * Complex.I,(1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(1 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(-1 : ℂ) * Complex.I,(1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ);
    (-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ);
    (0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ)]

noncomputable def q1B00 : Matrix (Fin 4) (Fin 4) ℂ :=
    !![(5 : ℂ),(-1 : ℂ) + (1 : ℂ) * Complex.I,(-2 : ℂ),(0 : ℂ);
    (-1 : ℂ) + (-1 : ℂ) * Complex.I,(5 : ℂ),(0 : ℂ),(-2 : ℂ);
    (-2 : ℂ),(0 : ℂ),(5 : ℂ),(-1 : ℂ) + (1 : ℂ) * Complex.I;
    (0 : ℂ),(-2 : ℂ),(-1 : ℂ) + (-1 : ℂ) * Complex.I,(5 : ℂ)]

noncomputable def q1B00Inv : Matrix (Fin 4) (Fin 4) ℂ :=
    !![(95/329 : ℂ),(27/329 : ℂ) + (-27/329 : ℂ) * Complex.I,(46/329 : ℂ),(20/329 : ℂ) + (-20/329 : ℂ) * Complex.I;
    (27/329 : ℂ) + (27/329 : ℂ) * Complex.I,(95/329 : ℂ),(20/329 : ℂ) + (20/329 : ℂ) * Complex.I,(46/329 : ℂ);
    (46/329 : ℂ),(20/329 : ℂ) + (-20/329 : ℂ) * Complex.I,(95/329 : ℂ),(27/329 : ℂ) + (-27/329 : ℂ) * Complex.I;
    (20/329 : ℂ) + (20/329 : ℂ) * Complex.I,(46/329 : ℂ),(27/329 : ℂ) + (27/329 : ℂ) * Complex.I,(95/329 : ℂ)]

noncomputable def q1A01 : Matrix (Fin 4) (Fin 8) ℂ :=
    !![(1 : ℂ),(1 : ℂ) * Complex.I,(0 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ);
    (-1 : ℂ),(1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ);
    (0 : ℂ),(0 : ℂ),(1 : ℂ),(1 : ℂ) * Complex.I,(-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(-1 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ)]

noncomputable def q1B01 : Matrix (Fin 4) (Fin 8) ℂ :=
    !![(-1 : ℂ),(-1 : ℂ) * Complex.I,(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ);
    (1 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ);
    (0 : ℂ),(0 : ℂ),(-1 : ℂ),(-1 : ℂ) * Complex.I,(1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(1 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ)]

noncomputable def q1C01 : Matrix (Fin 4) (Fin 8) ℂ :=
    !![(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ)]

noncomputable def q1A11 : Matrix (Fin 8) (Fin 8) ℂ :=
    !![(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ)]

noncomputable def q1B11 : Matrix (Fin 8) (Fin 8) ℂ :=
    !![(5 : ℂ),(0 : ℂ),(-2 : ℂ),(0 : ℂ),(-1 : ℂ),(1 : ℂ),(1 : ℂ),(-1 : ℂ);
    (0 : ℂ),(5 : ℂ),(0 : ℂ),(-2 : ℂ),(1 : ℂ) * Complex.I,(-1 : ℂ),(-1 : ℂ) * Complex.I,(1 : ℂ);
    (-2 : ℂ),(0 : ℂ),(5 : ℂ),(0 : ℂ),(1 : ℂ),(-1 : ℂ),(-1 : ℂ),(1 : ℂ);
    (0 : ℂ),(-2 : ℂ),(0 : ℂ),(5 : ℂ),(-1 : ℂ) * Complex.I,(1 : ℂ),(1 : ℂ) * Complex.I,(-1 : ℂ);
    (-1 : ℂ),(-1 : ℂ) * Complex.I,(1 : ℂ),(1 : ℂ) * Complex.I,(5 : ℂ),(-1 : ℂ) + (1 : ℂ) * Complex.I,(0 : ℂ),(0 : ℂ);
    (1 : ℂ),(-1 : ℂ),(-1 : ℂ),(1 : ℂ),(-1 : ℂ) + (-1 : ℂ) * Complex.I,(5 : ℂ),(0 : ℂ),(0 : ℂ);
    (1 : ℂ),(1 : ℂ) * Complex.I,(-1 : ℂ),(-1 : ℂ) * Complex.I,(0 : ℂ),(0 : ℂ),(5 : ℂ),(-1 : ℂ) + (1 : ℂ) * Complex.I;
    (-1 : ℂ),(1 : ℂ),(1 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ) + (-1 : ℂ) * Complex.I,(5 : ℂ)]

noncomputable def q1C11 : Matrix (Fin 8) (Fin 8) ℂ :=
    !![(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(0 : ℂ),(-1 : ℂ)]

noncomputable def q1B10 : Matrix (Fin 8) (Fin 4) ℂ :=
    !![(-1 : ℂ),(1 : ℂ),(0 : ℂ),(0 : ℂ);
    (1 : ℂ) * Complex.I,(-1 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(-1 : ℂ),(1 : ℂ);
    (0 : ℂ),(0 : ℂ),(1 : ℂ) * Complex.I,(-1 : ℂ);
    (-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ);
    (0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ);
    (1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ);
    (0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ)]

noncomputable def q1C10 : Matrix (Fin 8) (Fin 4) ℂ :=
    !![(1 : ℂ),(-1 : ℂ),(0 : ℂ),(0 : ℂ);
    (-1 : ℂ) * Complex.I,(1 : ℂ),(0 : ℂ),(0 : ℂ);
    (0 : ℂ),(0 : ℂ),(1 : ℂ),(-1 : ℂ);
    (0 : ℂ),(0 : ℂ),(-1 : ℂ) * Complex.I,(1 : ℂ);
    (1 : ℂ),(0 : ℂ),(-1 : ℂ),(0 : ℂ);
    (0 : ℂ),(1 : ℂ),(0 : ℂ),(-1 : ℂ);
    (-1 : ℂ),(0 : ℂ),(1 : ℂ),(0 : ℂ);
    (0 : ℂ),(-1 : ℂ),(0 : ℂ),(1 : ℂ)]

noncomputable def q1WeightB : Matrix (Fin 8) (Fin 4) ℂ :=
    !![(-68/329 : ℂ) + (27/329 : ℂ) * Complex.I,(68/329 : ℂ) + (27/329 : ℂ) * Complex.I,(-26/329 : ℂ) + (20/329 : ℂ) * Complex.I,(26/329 : ℂ) + (20/329 : ℂ) * Complex.I;
    (-27/329 : ℂ) + (68/329 : ℂ) * Complex.I,(-68/329 : ℂ) + (27/329 : ℂ) * Complex.I,(-20/329 : ℂ) + (26/329 : ℂ) * Complex.I,(-26/329 : ℂ) + (20/329 : ℂ) * Complex.I;
    (-26/329 : ℂ) + (20/329 : ℂ) * Complex.I,(26/329 : ℂ) + (20/329 : ℂ) * Complex.I,(-68/329 : ℂ) + (27/329 : ℂ) * Complex.I,(68/329 : ℂ) + (27/329 : ℂ) * Complex.I;
    (-20/329 : ℂ) + (26/329 : ℂ) * Complex.I,(-26/329 : ℂ) + (20/329 : ℂ) * Complex.I,(-27/329 : ℂ) + (68/329 : ℂ) * Complex.I,(-68/329 : ℂ) + (27/329 : ℂ) * Complex.I;
    (-7/47 : ℂ),(-1/47 : ℂ) + (1/47 : ℂ) * Complex.I,(7/47 : ℂ),(1/47 : ℂ) + (-1/47 : ℂ) * Complex.I;
    (-1/47 : ℂ) + (-1/47 : ℂ) * Complex.I,(-7/47 : ℂ),(1/47 : ℂ) + (1/47 : ℂ) * Complex.I,(7/47 : ℂ);
    (7/47 : ℂ),(1/47 : ℂ) + (-1/47 : ℂ) * Complex.I,(-7/47 : ℂ),(-1/47 : ℂ) + (1/47 : ℂ) * Complex.I;
    (1/47 : ℂ) + (1/47 : ℂ) * Complex.I,(7/47 : ℂ),(-1/47 : ℂ) + (-1/47 : ℂ) * Complex.I,(-7/47 : ℂ)]

noncomputable def q1WeightC : Matrix (Fin 8) (Fin 4) ℂ :=
    !![(68/329 : ℂ) + (-27/329 : ℂ) * Complex.I,(-68/329 : ℂ) + (-27/329 : ℂ) * Complex.I,(26/329 : ℂ) + (-20/329 : ℂ) * Complex.I,(-26/329 : ℂ) + (-20/329 : ℂ) * Complex.I;
    (27/329 : ℂ) + (-68/329 : ℂ) * Complex.I,(68/329 : ℂ) + (-27/329 : ℂ) * Complex.I,(20/329 : ℂ) + (-26/329 : ℂ) * Complex.I,(26/329 : ℂ) + (-20/329 : ℂ) * Complex.I;
    (26/329 : ℂ) + (-20/329 : ℂ) * Complex.I,(-26/329 : ℂ) + (-20/329 : ℂ) * Complex.I,(68/329 : ℂ) + (-27/329 : ℂ) * Complex.I,(-68/329 : ℂ) + (-27/329 : ℂ) * Complex.I;
    (20/329 : ℂ) + (-26/329 : ℂ) * Complex.I,(26/329 : ℂ) + (-20/329 : ℂ) * Complex.I,(27/329 : ℂ) + (-68/329 : ℂ) * Complex.I,(68/329 : ℂ) + (-27/329 : ℂ) * Complex.I;
    (7/47 : ℂ),(1/47 : ℂ) + (-1/47 : ℂ) * Complex.I,(-7/47 : ℂ),(-1/47 : ℂ) + (1/47 : ℂ) * Complex.I;
    (1/47 : ℂ) + (1/47 : ℂ) * Complex.I,(7/47 : ℂ),(-1/47 : ℂ) + (-1/47 : ℂ) * Complex.I,(-7/47 : ℂ);
    (-7/47 : ℂ),(-1/47 : ℂ) + (1/47 : ℂ) * Complex.I,(7/47 : ℂ),(1/47 : ℂ) + (-1/47 : ℂ) * Complex.I;
    (-1/47 : ℂ) + (-1/47 : ℂ) * Complex.I,(-7/47 : ℂ),(1/47 : ℂ) + (1/47 : ℂ) * Complex.I,(7/47 : ℂ)]


/-- The four-by-four central inverse is exact. -/
theorem q1B00_inv :
    q1B00 * q1B00Inv = 1 ∧ q1B00Inv * q1B00 = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [q1B00, q1B00Inv, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      field_simp <;> ring_nf <;> try simp only [pow_two, Complex.I_mul_I] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [q1B00, q1B00Inv, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
      field_simp <;> ring_nf <;> try simp only [pow_two, Complex.I_mul_I] <;> ring

/-- The Schur complement of the full direction-zero elimination is R1's `collarA`. -/
theorem q1_schurA :
    q1A11 - q1B10 * q1B00Inv * q1A01 = collarA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q1A11, q1B10, q1B00Inv, q1A01, collarA,
      Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> try simp only [pow_two, Complex.I_mul_I] <;> ring

/-- The central-plus-forward Schur complement is R1's `collarB`. -/
theorem q1_schurB :
    q1B11 - q1B10 * q1B00Inv * q1B01 - q1C10 * q1B00Inv * q1A01 = collarB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q1B11, q1B10, q1B00Inv, q1B01, q1C10, q1A01, collarB,
      Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> try simp only [pow_two, Complex.I_mul_I] <;> ring

/-- The backward Schur complement is R1's `collarC`. -/
theorem q1_schurC :
    q1C11 - q1C10 * q1B00Inv * q1B01 = collarC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q1C11, q1C10, q1B00Inv, q1B01, collarC,
      Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> try simp only [pow_two, Complex.I_mul_I] <;> ring

#print axioms q1B00_inv
#print axioms q1_schurA
#print axioms q1_schurB
#print axioms q1_schurC
