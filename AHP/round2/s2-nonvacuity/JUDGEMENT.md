# Judgement — S-2 non-vacuity

**Status: `closed-holds`, for the pinned four-bond non-vacuity item.**

**Plain answer:** Yes. The specified four-bond touching class contains proper nonempty admissible domains, with compatible Lambda and genuinely nonzero admissible test fields, at arbitrarily large headline scales and below every positive smallness cap. The stronger corner class has the opposite outcome: its additional coverage requirement forces the base domain to be empty or the whole torus. Neither result identifies the formal class with Balaban's printed class.

## Why this settles the item

[PIN.md](pin/PIN.md) explicitly makes the four-bond branch decisive; corner-only progress would be partial. The independently verified positive attempt proves exactly `GoalPos1`, without extra hypotheses. Therefore the item is `closed-holds`, not `partly-closed`, `closed-fails`, or merely `closed-reduced`.

The four pinned goals are competing alternatives within two branches, not four assertions that must all be proved together. The accepted corner saturation result does not contradict the four-bond witness and does not change the item's positive verdict. Statements in individual attempt reports that the other branch remains open describe those attempts in isolation; they are superseded by this combined disposition.

All declaration names below have prefix `AdalyFormal.AHP.Round2.S2Nonvacuity.`.

| Pinned goal | Combined disposition | Evidence |
|---|---|---|
| `GoalPos1` | Proved: cofinal proper-domain four-bond non-vacuity. | `goalPos1_proved`, [r1-prove/Attempt.lean:293](r1-prove/Attempt.lean#L293). |
| `GoalNeg1` | Ruled out by the positive witness and the compiled incompatibility implication. | `goalNeg1_implies_not_goalPos1`, [r1-prove/Attempt.lean:334](r1-prove/Attempt.lean#L334), together with `goalPos1_proved`. This is a logical consequence of the checked declarations, not a newly compiled standalone negation theorem. |
| `GoalNeg2` | Proved: universal corner-class empty/whole-torus saturation. | `goalNeg2_proved`, [r1-refute/Attempt.lean:519](r1-refute/Attempt.lean#L519). |
| `GoalPos2` | Refuted by an explicit compiled negation. | `not_goalPos2`, [r1-refute/Attempt.lean:524](r1-refute/Attempt.lean#L524). |

The negative goals are stronger than the exact negations of the positive goals. No converse of the pin's incompatibility implications is used.

## What is now proved

### Four-bond class: complete witnesses, not assumed coverage

[properFourAt_two, r1-prove/Attempt.lean:268](r1-prove/Attempt.lean#L268) supplies the complete `ProperFourAt 2 m R a₀` conjunction for every \(m\ge1\), \(R\ge18\), and \(a_0>0\). The construction uses:

- \(\ell=k=2\), \(M=2^m\), the frozen slab tower, torus, and Lambda;
- a nonempty base domain strictly smaller than the fine torus;
- actual factor-12 site and four-bond plaquette coverage;
- flat background and \(\alpha_0=a_0/(12M)>0\), meeting the cap with equality;
- a nonzero frozen input field satisfying both `OnLambdaTildeIn` and `OnLambdaT`, with positive `bondEnergy`.

The new transverse-invariance argument at [lines 185–237](r1-prove/Attempt.lean#L185) proves the slab's four-bond coverage from frozen coverage; shell-class inhabitation is not substituted for this obligation. The main theorem chooses \(m=\max(1,m_{\rm lower})\), then \(R=\max(R_{\rm lower},18)\), before receiving the cap. It meets the pin's exact cofinal quantifier order.

### Corner class: genuine universal obstruction

[corner_saturation, r1-refute/Attempt.lean:506](r1-refute/Attempt.lean#L506) proves the stronger geometric statement from admissibility and `CoversPlaqCorner` alone. A product box touching every edge of a square contains all its corners; every frozen class box lies inside the base domain. Any proper nonempty domain has an exit bond and hence an explicitly uncovered corner plaquette ([lines 454–504](r1-refute/Attempt.lean#L454)). This gives the exact `GoalNeg2` and the compiled negation of `GoalPos2`.

The obstruction depends on the additional demand that one contained class box touch all four edges of every one-corner plaquette. It is not a theorem that Balaban's printed regularity class has no proper domains, and it cannot be transferred to the four-bond class.

## Acceptance evidence checked in this judgement

Read the handoff, requested OPEN_ITEMS sections B, K–N, R and S, Stage-B results, the prior S-2 specification/attack/decision and implementation, the pin, and both attempts' complete `NOTES.md` and `Attempt.VERIFY.md`. Read both complete attempt sources, independent compiler logs, exit records, and verification audits.

A fresh read-only source/log audit in this judgement confirmed:

- current attempt and pin SHA-256 hashes match the independent verifiers' records;
- all 14 pinned definitions match each attempt character-for-character; the eight touching definitions also match Stage B;
- both exact main declarations have no additional hypotheses;
- both independent recompilation exits are **0**, without warnings or errors;
- all **40** positive-attempt and **48** negative-attempt dependency records use only permitted axioms;
- no forbidden source tokens; direct imports resolve only to frozen `lean/src` modules.

Both main declarations print exactly:

```text
'AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.AHP.Round2.S2Nonvacuity.goalNeg2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Independent evidence: [positive verification](r1-prove/Attempt.VERIFY.md), [positive log](r1-prove/Attempt.verify.log), [positive exit](r1-prove/Attempt.verify.exit); [corner verification](r1-refute/Attempt.VERIFY.md), [corner log](r1-refute/Attempt.verify.log), [corner exit](r1-refute/Attempt.verify.exit).

Checked source hashes:

| File | SHA-256 |
|---|---|
| `pin/Statement.lean` | `826f93c754d1c78a13e8ee7a832fc3041b36cd9cbe4628cde3a7475d752909f9` |
| `r1-prove/Attempt.lean` | `2e2d384afeab5a5fa1a0249c7e3960eef91078888b071463bf0228538cc07f8a` |
| `r1-refute/Attempt.lean` | `c4a1d4d0614dd1fcf700219fbd12fd03349a4b7f600dea0da15d678dfb553ccd` |

This is a judgement of the independently compiled, unchanged attempts. No further Lean compilation or numerical experiment was run here; numerical scans are not acceptance evidence. No source-page image was independently re-read in this judgement; the verifiers' source-reading disclosures are retained, including the unavailable local CMP102 p.277 image.

## What remains open

**Nothing remains open in the pinned four-bond existence question; the pinned corner alternative is also decided.** The former Stage-B non-vacuity hold is discharged for the four-bond formal class, while proper-domain corner inhabitation is ruled out rather than left pending.

Broader S-2 printed-class fidelity remains open. In particular:

- Four-bond coverage is not the printed one-corner selector. Site and single-box plaquette coverage are additional formal conditions, not derived from the printed regularity paragraph.
- The fixed-factor-12 aligned product boxes, reading-A tower/base law, finite periodic 3D SU(2) setting, derivative guards, Frobenius class bounds, and frozen Lambda/test-space conventions remain disclosed choices.
- The positive witness uses blocking factor two, depth two, and a flat background. Odd blocking factors greater than eleven, non-flat richness, and all-depth witness families are not supplied. The pin allows natural radii; the stronger helper works for every natural radius at least 18, but 18 is not claimed sharp or necessary.
- No new coercivity inequality, inverse-existence theorem, changed-operator comparison, reconstructed-field correspondence, eta/tau-star normalization, or guarded all-plaquette result is proved. S-1, S-3 and the guarded headline are not closed by this judgement.

Only this `JUDGEMENT.md` was written. Protected files, attempts, pin, prior reports and logs were left unchanged. No build, update, reproduction run, removal, commit or push was performed.
