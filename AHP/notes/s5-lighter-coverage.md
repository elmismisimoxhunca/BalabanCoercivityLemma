# S-5 — lighter coverage

Uncompiled draft: [LighterCoverage.lean](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/s5-lighter-coverage/LighterCoverage.lean). Not a Lake root. Not compiled. Not a theorem of the project tree. Frozen files were not edited. The external repository was not copied. The clause is taken only from `notes/external_ymx/HARVEST.md` and `notes/external_ymx/SCOUT_FINDINGS.md`.

## Answer

Yes. The frozen proof needs a fine plaquette that this hypothesis does not cover. The lemma is `plaq_small_class` (`lean/src/CJ3.lean`).

`classRows_read` (`lean/src/CJ4.lean`) is the caller. For a bond `b ∈ bondsLam j` and a read row `ReadRow ell j b l e`, it invokes `plaq_small_class` at every site of

\[
\mathrm{Ball}\ e_1\ \bigl(4\,(\ell^l\cdot\ell) + 2\,\mathrm{rhoT}\,\ell\,l\bigr),
\]

the ball named in `read_region` in the same file. `plaq_small_class` then uses `CoversPlaqOm0c`: that fine plaquette, `pw 1 U z ν μ`, must have all four bonds in one `IsClassCube` of factor `c`.

The lighter clause does not give that plaquette. It puts a gauge only on a cube of side \(M\) that contains a bond of the active set. In the frozen proof the active row is `bondsLam` (`lean/src/ZXR2Ops3.lean`), not an arbitrary bond of the read ball.

## The distance

`rhoT` in `lean/src/ZR8Read.lean` is `rhoT ell 0 = 0` and `rhoT ell (l+1) = rhoT ell l + 4*(ell^l*ell)`. The draft copies that recursion and nothing else. It is not definitional equality with the frozen function.

For \(\ell\ge 2\) and a block \(M = \ell^m\), at read level \(l = m\),

\[
M = \ell^m < 4\,\ell^{m+1} \le \mathrm{readRadius}\,\ell\,m.
\]

So the site at offset \(M\) from the bond base lies in the closed ball (`Ball` is `pdist ≤ r`, `lean/src/ZR8Geo.lean`). For \(M\ge 2\), no side-\(M\) interval contains both endpoints of the unit bond at \(0\) and that site (`no_side_containing_bond_and_far`). The four corners of the unit plaquette based there are at least that far.

`classRows_read` permits this level. It assumes \(1\le j\le k\) and \(l < j\), and the headline chooses \(k\) after \(m\). Take \(l = m\) and \(j = m+1\le k\). Then \(l+1 = j\), so the `ReadRow` bound is \(\mathrm{rhoT}\,\ell\,j - \mathrm{rhoT}\,\ell\,(l+1) = 0\): the row base is at distance \(0\) from the bond base, and the ball is centered there. This draft does not re-prove that frozen `pdist` zero means equal sites. `read_region` puts the ball in \(\Omega_{j-1}\) under the collar \(17\ell\le RM\). It does not put the outer site into a side-\(M\) cube about `b`.

The numeric check at \(\ell = 2\), \(l = 1\) is `readRadius = 32`, against a block of side \(2\).

## What the lighter clause is not

`DescribedAt` (`lean/src/ZStatementP428.lean`) is a box of side \(c\cdot\mathrm{bigSide}\), and `bigSide M ell i = M * ell^i`. For \(c\ge 2\) and \(M\ge 1\) that side is strictly longer than \(M\) (`class_side_gt_block`). The headline factor is \(12\). A side-\(M\) cube is not an `IsClassCube` of factor \(12\), at any index.

`HARVEST.md` says the lighter clause could replace the frozen coverage only if the active set is the \(\Omega_0\) bonds under the touching mask (`bondsOm0`). That enlargement is not the hypothesis as stated, and it was not checked downstream there. Under it, the far plaquette would meet an active bond of its own, since `read_region` lands in \(\Omega_{j-1}\subseteq\Omega_0\), and for \(M\ge 2\) a unit plaquette fits in some side-\(M\) cube. `plaq_small_class` would still not apply: its hypothesis is `ClassCoupled`, hence `CoversPlaqOm0c` at factor \(c\), not a side-\(M\) gauge. The bound it returns also uses the class index, \((\ell^2)^{m-1}\) in the denominator. A side-\(M\) chart does not supply that index.

## Uses that do not give this gap

`bothIn_classBond` (`lean/src/ZR8Class.lean`) builds, for \(M\ge 2\), one unit plaquette of a `BothIn` bond inside the same \(M\)-block (`plaq_of_bothIn`). That plaquette does sit in a side-\(M\) cube containing the bond. It is not the gap.

`plaq_common_gauge` (`lean/src/ZR6A.lean`) is the same one-cube demand as `CoversPlaqOm0c`, without the read-ball radius. The place the radius exceeds \(M\) is `classRows_read`.

## What this does not say

- Not that the coercivity inequality fails if regularity is assumed only on those side-\(M\) cubes.
- Not that `P428Target8` is false, and not that the lighter clause is false.
- Not a theorem of the project tree. No `lean` run, no axiom print. `compiled` is false.
