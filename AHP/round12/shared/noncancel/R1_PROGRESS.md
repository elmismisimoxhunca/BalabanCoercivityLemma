# Noncancel R1 hand-off: finite exterior star

**Status: partial; neither the cofinal premise nor GoalNeg2 is proved or disproved.**

## Published, compiled package

`AHP/round12/shared/noncancel/R1_Star.lean` is a 692-line standalone file importing only frozen `DrEquiv`. It is byte-identical to `AHP/round12/noncancel/r1/Attempt.lean`. Both compile separately through `AHP/round3/lean1.sh`, exit 0, in 8-GiB memory-capped scopes. All 53 printed axiom lists are standard. Logs, exits, and resource records accompany both files. Full evidence and exact open statements: `AHP/round12/noncancel/r1/NOTES.md`; machine audit: `AHP/round12/noncancel/r1/AUDIT.json`.

Prefix: `AdalyFormal.Round12.Noncancel.`

- `Plaquette.frozen_three_form` (line 236), `frozen_three_form_right` (258): the actual frozen local curl energy plus half `bilPlaq` is the charged three-atom form; the exterior second/fourth atom is zero respectively.
- `Star.pair_completion` (33), `star_mass_lower` (52): exact leaf-mass completion of the square. This is the intended route to whole-carrier positivity on one complex trace's zero fiber.
- `Trace.physical_kernel_line` (351): physical bond trace and actual gauge quarter rotation yield full charged-line containment under trace-zero positivity and commutation. It derives chargedness; it does not assume it globally.
- `Path.starPath` (434), `starPath_zero`, `starPath_cont`, `starPath_an` (452): genuine local equal-angle four-link family, identity start, continuous and analytic in the original copied `AnFam` sense.
- `Path.starLinks_exterior`, `starPath_off_exterior` (472): exterior support for a transversely invariant slab.
- `Path.star_negative_endpoint` (527): an actual negative endpoint at pi for the star immediately outside a **right** `BdPt`, using frozen single-bond energy/mass/W/T theorems.
- `Gauge.star_all_comm` (660): actual all-plaquette star carrier commutes with diagonal rotations.
- `Gauge.star_kernel_line` (673): specializes the trace criterion to the actual frozen star operator, discharging commutation but **not** positivity or a nonzero crossing witness.

The kernel track's original-`KernelLine` bridge can use this same trace-zero positivity strategy. No selected-character exclusion is needed once that actual positivity is proved.

## Side distinction: do not silently identify two paths

Numerics use the **left** exterior site \((4q-1,0,0)\). The negative-endpoint theorem uses the **right** boundary to reuse frozen `BdPt` lemmas. No reflection equivalence has been formalized. A final theorem must choose one side consistently, not combine their properties without a bridge. Both left and right local charged plaquette formulas are now compiled.

## New numerical evidence, not closure

All transverse characters are assembled into the physical nine-bond resolvent, not a selected Fourier block.

- Uniform left star, q=1,R=18: charged root `1.20798785641901928304390613798561910599321772929534432491798...`; next Schur eigenvalue `0.93201280627581617...`; neutral root `1.7601668108...`.
- Uniform left star, q=2,R=18 (64 characters): charged root `1.208030537534755`; next `0.9318300997626887`; neutral root `1.7601821139136906`.
- At q=2,R=18, physical trial energies at pi/2 are approximately `0` and `-1/4`, with numerical gauge right-hand side exactly zero. The general physical trial identification is still unproved.
- Independent 60/80-digit q=1,R=18 physical reconstructions yield stable first top-jet sums approximately `1.00872731019e-41`, `4.87537241180e-40`, `4.87537242991e-40`. At 80 digits: solve residual `1.15e-76`, boundary null residual `4.19e-80`. These are not interval enclosures or a Lean normalization dictionary.

Files under `noncancel/r1`: `star_q1_R18.json`, `star_q2_R18.json`, `starjet_q1_R18_p60.json`, `starjet_q1_R18_p80.json`, with scripts/logs/exits. Maximum numerical RSS 519636 KiB, all jobs capped below 2 GiB.

## Exact next work

1. Prove the physical pi/2 negative trial, including collar support (`W=id`, `T=0`), actual mass terms, and the full plaquette sum. The current polynomial `starTrialEnergy` is only a model identity.
2. Show the actual first crossing is in `(0, pi/2)`.
3. Prove positivity on the complete real carrier with the central charged coordinate zero: pairwise leaf masses plus the remaining flat localized carrier form, neutral positivity, and charged/neutral orthogonality. This also needs `W u = u` on the boundary patch for arbitrary carrier fields, not only on the trial. This is **not yet a proved physical decomposition**.
4. Prove crossing-specific `TopJetDetected`/`CurlDetected` for the same star path. Chargedness alone does not imply detection.
5. Supply the dyadic cofinal-scale and even-radius quantifiers and the existing assembly joins.

The sufficient cofinal target remains `AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine`; the exact ultimate target remains `AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation`.
