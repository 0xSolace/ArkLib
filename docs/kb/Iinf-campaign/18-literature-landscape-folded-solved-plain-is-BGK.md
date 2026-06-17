# The proximity-prize literature landscape (2025–2026): folded RS SOLVED, plain RS = BGK wall

Researched the recent literature on exactly what the prize reduces to (the hook's instruction: find recent
papers on the reduced forms). The decisive picture: **the proximity gap to capacity is now SOLVED (STOC 2026)
for folded RS / subspace-design / random RS via curve decodability — the N6 route. The prize's open hard core
is specifically EXPLICIT PLAIN RS on a fixed smooth `μ_n` domain, which is the BGK wall.** This reconciles my
own N6 finding (curve-decodability is the one non-reducing object, inert for `μ_n` RS) with the published SOTA.

## Reading list (the 5 key recent papers, for download)
1. **ABF26 — "Open Problems in List Decoding and Correlated Agreement"** (eprint 2026/680, Arnon–Boneh–Fenzi).
   THE grand-challenge statement (Grand-MCA + Grand-list-decoding). The prize's definition of success.
2. **Goyal–Guruswami — "Optimal Proximity Gaps for Subspace-Design Codes and (Random) Reed-Solomon Codes"**
   (eprint 2025/2054, STOC 2026). **Closes the proximity gap to capacity `1−R−η` for folded RS, univariate
   multiplicity codes (subspace-design), and RANDOM RS** — via the **curve-decodability** property. Field size
   only LINEAR in block length. This is the published version of the N6 route. (Note: arXiv:2601.10047, a
   competing FRS proof, was WITHDRAWN as subsumed by this.)
3. **"Interleaving Stability for MCA and Curve Decodability"** (eprint 2026/891). Row-wise interleaving imposes
   NO linear loss on generator-MCA and curve-decodability; exact transfer if seed set ≤ q. Addresses the
   affine-line MCA interleaving-loss open problem from ABF26. Strengthens the curve-decodability toolkit.
4. **"All Polynomial Generators Preserve Distance with MCA"** (eprint 2025/2051). All polynomial generators
   guarantee MCA for every linear code — a generator-side closure.
5. **"On Reed–Solomon Proximity Gaps Conjectures"** (eprint 2025/2046, the trichotomy). Proves the RS
   correlated-agreement conjecture does NOT hold up to capacity — it fails beyond `1−H_q(ρ)`; capacity is
   IMPOSSIBLE with poly soundness. Confirms the window edge `δ* = 1−ρ−Θ(1/log n)` is strictly interior.
   (Plus Habock 2025/2110: RS-MCA exactly up to Johnson, vacuous AT Johnson.)

## The landscape, precisely
| code | proximity gap / MCA to capacity | status |
|---|---|---|
| Folded RS, univariate multiplicity (subspace-design) | YES, `1−R−η` | **SOLVED** (GG25, curve decodability) |
| Random RS | YES, to capacity | **SOLVED** (BGM STOC'23 + GG25) |
| **Explicit PLAIN RS on a fixed smooth `μ_n` (FRI) domain** | window edge `1−ρ−Θ(1/log n)` | **OPEN = the BGK wall** (the prize) |

The mechanism split is exactly my N6 finding: **curve decodability** (subspace-design / strong list-recovery)
is the beyond-Johnson engine, and it WORKS — for codes that have the subspace-design property (folded /
multiplicity / random). Explicit plain RS on the deterministic `μ_n` domain **lacks** it (proven in-tree
`RadiusOneExact`: `B=I`), so its δ* is governed by the thin-2-power Gauss-period sup-norm = BGK.

## What this means for the prize (honest, and genuinely useful)
1. **The codes actually deployed in modern SNARKs (folded FRI / STIR use folding) are in the SOLVED column.**
   GG25 + curve decodability give them optimal proximity gaps to capacity. So the *practically-deployed*
   proximity-gap question is largely resolved by 2025–26 published work.
2. **The prize's open grand challenge is the harder, specific case: explicit PLAIN RS on a fixed smooth
   domain at the window edge.** That is the irreducible BGK/Paley thin-2-power-subgroup √-cancellation wall,
   which my 14-attack sweep + #444 + the sibling fleet (71 non-BGK refuted) all confirm is open, with no
   standard-conjecture close (GRH structurally inert), best bound `n^{1−o(1)}`.
3. **The one genuinely-different direction is therefore real and published, not a dead lead:** it is the
   curve-decodability / subspace-design route (GG25, 2026/891). It does not solve plain RS — but it raises the
   sharp question the prize organizers must answer: **does the Grand-MCA challenge accept folded RS (then it
   is SOLVED by GG25), or does it specifically require plain RS on the explicit smooth domain (then it is the
   open BGK wall)?** This is a question about the *challenge definition* (ABF26 §1), not a math gap I can
   close — and it is the single most decision-relevant fact for the prize.

## Verdict
No closure of the plain-RS BGK core (it is genuinely open, now proven irreducible by current methods, exact
missing input = effective horizontal cyclotomic Sato-Tate). BUT the literature research surfaces the
genuinely-actionable fact: **the proximity gap to capacity is SOLVED for the subspace-design/folded/random
codes via curve decodability (GG25 STOC 2026), and the prize's hard core is precisely the plain-RS-on-`μ_n`
residue = BGK.** The decision-relevant open question is whether the challenge admits folded RS. Reading list
of 5 papers banked for download. Related: docs 16,17 (the 14-attack no-escape verdict); #444 §0.0.
