# Kernel R1 hand-off (in progress)

The finite exterior star is a much better dimension route than the left-twist Fourier problem. `kernel/r1/KernelStructure.lean` now proves:

```lean
kernel_finrank_le_two_of_boundary (A : E →L[ℝ] E) (r : E →ₗ[ℝ] ℂ)
  (hpos : ∀ u, u ≠ 0 → r u = 0 → 0 < ⟪u, A u⟫) :
  Module.finrank ℝ A.ker ≤ 2
```

The map is injective on the COMPLETE real kernel, not one Fourier block. With quarter-rotation commutation and a charged nonzero kernel witness, `kernel_eq_charged_span_of_boundary` identifies the full kernel as span{u,Ju}. This is exactly the star's proposed central-coordinate strategy. No spatial-translation proof is needed.

`ActualKernel.lean` now **COMPILES, exit 0, all standard axioms** (1820 lines; final published copy `shared/kernel/R1_ActualKernel.lean` also separately compiled). It copies the round10 R1 dictionary and original `KernelLine`/`vacEdge` definitions verbatim, defines `Actual.chargedCoordinate q R b` as the physical upper-right complex entry of u(b), and applies that result to the original `KernelLine`. Actual gauge commutation is generalized to arbitrary paths fixed by the rotation at the crossing.

**Chargedness is now derived, not assumed.** `chargedCoordinate_quarter_twice` proves the actual local r(J²u)=-r(u) identity. `charged_of_boundary` propagates it to the full kernel by injectivity. The main actual theorem `AdalyFormal.Round12.Kernel.Actual.kernelLine_of_boundary_positive` only needs: (i) quarter-gauge fixes V at vacEdge, (ii) actual strict carrier positivity on chargedCoordinate b=0, (iii) any nonzero crossing vector. It returns original `R2.KernelLine`. No separate character decomposition, neutral exclusion, finrank, or chargedness assumption. `kernelLine_finrank` explicitly gives real nullity two. `oneColor_not_crossing` excludes the specific historical `ColorObstruction.oneColor` witness conditionally on hpos and b differing from its support bond; **this does not exclude all invisible fields**. Physical hpos, negative-endpoint/first-crossing range, and crossing CurlDetected remain open.

Numerics: independent all 128 charge/character sectors at q=2,R=32 left twist completed. Only charged (7,7) is zero to double precision; other sectors >=0.05196094657; within selected block next eigenvalue 0.99807575986. High-precision selected/competitor checks running. These do not certify actual infinite-family spectral statements. Star q,R tests will be separate from noncancel's q=1,R=18.
