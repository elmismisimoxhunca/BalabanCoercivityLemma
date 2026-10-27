import DrEquiv
set_option autoImplicit false
example : (136/329 : ℂ) + Complex.I * (82/329) + -(54/329) =
    82/329 + Complex.I * (82/329) := by
  ring
example : (136 : ℂ) + Complex.I * 82 + -54 = 82 + Complex.I * 82 := by
  ring
example : -68 + Complex.I * 41 - Complex.I ^ 2 * 27 = -41 + Complex.I * 41 := by
  field_simp
  norm_num [pow_two, Complex.I_mul_I]
  ring
example : (136/329 : ℂ) + Complex.I * (82/329) + -(54/329) =
    82/329 + Complex.I * (82/329) := by
  field_simp
  ring_nf
  norm_num [Complex.I_mul_I]
  ring
