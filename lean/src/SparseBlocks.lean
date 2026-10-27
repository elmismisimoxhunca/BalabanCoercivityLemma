import StrideInput

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedTest.Stride

open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

/-- Eight possible offsets, filtered to remove periodic wraps. This is proved
identical to the imported nonwrapping block, solely to keep kernel evaluation
small; it is not a replacement averaging operator. -/
def offsetSite (y : Site) (o : Fin 3 → Fin 2) : Site :=
  fun μ => ⟨((y μ).val + 2 * (o μ).val) % 8, Nat.mod_lt _ (by norm_num)⟩

def sparseBlock (y : Site) : Finset Site :=
  ((Finset.univ : Finset (Fin 3 → Fin 2)).image (offsetSite y)).filter
    (fun x => ∀ μ : Fin 3, (y μ).val ≤ (x μ).val)

theorem stepBlock_sparse (y : Site) : stepBlockOf y 2 2 = sparseBlock y := by
  ext x
  simp only [mem_stepBlockOf, sparseBlock, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    let o : Fin 3 → Fin 2 := fun μ =>
      ⟨((x μ).val - (y μ).val) / 2, by have h := hx μ; omega⟩
    refine ⟨⟨o, ?_⟩, fun μ => (hx μ).1⟩
    funext μ
    apply Fin.ext
    change ((y μ).val + 2 * (((x μ).val - (y μ).val) / 2)) % 8 = (x μ).val
    have h := hx μ
    have hlt : (x μ).val < 8 := (x μ).isLt
    omega
  · rintro ⟨⟨o, rfl⟩, hle⟩ μ
    have ho := (o μ).isLt
    have hy : (y μ).val < 8 := (y μ).isLt
    have hh := hle μ
    change (y μ).val ≤ ((y μ).val + 2 * (o μ).val) % 8 at hh
    change (y μ).val ≤ ((y μ).val + 2 * (o μ).val) % 8 ∧
      ((y μ).val + 2 * (o μ).val) % 8 < (y μ).val + 2 * 2 ∧
      2 ∣ (((y μ).val + 2 * (o μ).val) % 8 - (y μ).val)
    omega

end Prop1.ScaleFittedTest.Stride

#print axioms Prop1.ScaleFittedTest.Stride.stepBlock_sparse
