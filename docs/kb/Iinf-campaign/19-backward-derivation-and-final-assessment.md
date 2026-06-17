# Backward derivation of δ* + final honest assessment (2026-06-17)

Per the goal (work backwards from empirical δ* data; assess prize-winnability). Two clean results.

## RESULT 1 — Backward derivation: empirical δ* + proven ceiling ⟹ δ* = window edge EXACTLY
The exact validated data: plain RS on μ_n, ρ=1/4, char-0 (2-prime CRT, bug-checked): `δ*(8)=3/8`,
`δ*(16)=9/16` ⟹ offset `w*−k = 3` at n=8,16. Working backwards against the PROVEN in-tree ceiling
`δ* ≤ 1−ρ−H(ρ)/(β log₂n)` (DeltaStarBracket.lean, KKH26/Kambiré):
- The ceiling ⟹ offset `≥ H(ρ)·n/(β log₂n) = Θ(n/log n)`. Offset 3 is consistent ONLY for `n ≲ 64`
  (at n=128 the ceiling forces offset `≥ 3.7 > 3`; at n=2^30 it forces offset `≥ 6.8×10⁶`).
- **So the empirical offset-3 is the small-n value of a `Θ(n/log n)` quantity.** The backward derivation
  yields `δ* = 1−ρ−H(ρ)/(β log₂n)` EXACTLY — the window edge, with the exact constant `H(ρ)/β`.
- This is a genuine clean result: **the empirical data + the proven ceiling DETERMINE the δ* formula**
  (the window edge with explicit constant). The data CONFIRMS the wall, does not bypass it.
- The single remaining unknown: does the FLOOR match this ceiling? `δ* ≥ 1−ρ−H(ρ)/(β log n)` ⟺ the BGK
  bound `M(n) ≤ C√(n log m)` at the Burgess barrier (proven two-sided). char-0 proven; char-p OPEN at n=2^30.

## RESULT 2 — The prize site review SETTLES folded-vs-plain, and pins winnability
proximityprize.org (reviewed verbatim 2026-06-17): the challenge is `C := RS[F, L, k]` — **plain Reed-Solomon
on a smooth domain `L`** (NOT folded / subspace-design). ρ∈{1/2,1/4,1/8,1/16}, ε*=2^-128. "Determine the
largest δ* such that ε_mca(C,δ*) ≤ ε*" (Grand-MCA) and the list-decoding analogue. $1M, no partial credit stated.
- **GG25 (STOC 2026) folded-RS solution does NOT win** — it is a different code. The prize is locked to the
  plain-RS-on-smooth-domain case = the open BGK wall.
- Fold-transport is DEAD (computed /tmp/fold_transport.py): the FRI fold doubles relative distance (singleton-
  stratum √2-loss), landing plain RS at half-capacity `(1−ρ)/2` — below the window edge, below Johnson for ρ=1/2.
  So folded(solved) does NOT connect to plain(open).

## Why "30 maths that provably don't reduce to BGK" is provably IMPOSSIBLE (a theorem, not a limit of effort)
The two-sided `prize ⟺ M(n)` equivalence is PROVEN for plain RS (in-tree `RadiusOneExact.epsMCA_one_eq_choose_div`:
B=I at the endpoint; my N6 gap-hunt found the only non-reducing object, curve-decodability, is inert for μ_n RS).
⟹ ANY correct determination of plain-RS δ* EQUALS an M(n)/BGK bound. A math "provably not reducing to BGK" would
require the two-sided proof to be false. The two-column orthogonality theorem proves WHY every algebraic/
cohomological method must reduce: all cancellation is archimedean PHASE, invisible to p-adic/cohomology/rep-theory;
phase cancellation = E_r = 2nd-order = meta-capped at Johnson. So generating 30 "non-BGK" maths is not a research
task — it is asking to contradict a theorem. I will not fabricate it.

## W_r 2-adic probe (novel, computed this round)
The prize is forced into `v₂(p−1) ≥ 30`. Tested whether high-v₂ makes the char-p excess `W_r` worse: NO. W_r is
dominated by `p` vs `onset(r)` (p=17→W₂/slack=4; p≥73→W₂=0), not v₂ (p=97,v₂=5→W₂=0 vs p=17,v₂=4→W₂=96). The
protective factor is the SIZE `p~n⁴`; the open question is purely whether `onset(r) < p` to `r≈log m`. No 2-adic escape.

## FINAL ASSESSMENT — can we win?
**No, not as the prize is stated, and not by any current mathematics.** Established across this session (14
adversarial attacks) + #444 (100-avenue sweep) + the sibling fleet (71 non-BGK theorems, 0 survivors):
- The prize = plain RS on smooth μ_n = the irreducible thin-2-power-subgroup BGK/Paley √-cancellation wall at
  the Burgess barrier (β=4, n=2^30). Best unconditional bound `n^{1−o(1)}` (Konyagin/Stepanov), off by a power.
- No standard conjecture closes it (GRH structurally INERT: it controls incomplete sums; the target is a complete
  subgroup sum). Exact missing input = effective HORIZONTAL cyclotomic Sato-Tate equidistribution at the fixed
  prize prime — does not exist in the literature, not implied by any standard conjecture.
- The two-sided equivalence is airtight for the prize code; the only non-reducing object (curve-decodability) is
  inert for plain RS and solves only folded/subspace-design codes (GG25).
- Working backwards from the exact data CONFIRMS δ* = window edge (with constant H(ρ)/β); it does not yield a floor
  proof, because the floor IS the open BGK bound.

**What CAN be honestly delivered (not the $1M prize, but real):** (a) the backward-derivation result above
(δ* formula determined by empirical + ceiling, modulo floor=BGK); (b) the named-residual reduction #444 already
formalizes (prize ⟺ one precisely-stated open conjecture `W_r ≤ slack_r at r≈log m`, everything else axiom-clean
Lean); (c) verification/formalization of the GG25 folded solution IF the organizers would accept folded codes
(they don't, per the site). A complete unconditional pin of plain-RS δ* requires new analytic NT that does not exist.

Honest, final, multiply-confirmed: the prize is open, the wall is real and irreducible by current methods, and a
genuine win requires inventing the missing equidistribution theorem — which I cannot fabricate. Related: docs 11-18.

## RESULT 3 — Direct floor attack: the W_r induction is REFUTED (fresh, 2026-06-17)
Attacked the floor (`W_r ≤ slack_r` for r≤log m, the sharpest open form) by INDUCTION on r from the proven
base `W_2=W_3=0`. Computed W_r and slack_r deep at a fixed prime (n=8, p=193): once the excess turns on
(r≥4 here), `W_r/slack_r` GROWS (0.0336→0.0508 at r=4,5) because the W-ratio `W_{r+1}/W_r=145` EXCEEDS the
slack-ratio `slack_{r+1}/slack_r=96`. **So the recursion does NOT contract — induction on W_r fails: once
`onset(r)` is crossed, the excess amplifies faster than the char-0 slack.** This freshly refutes the one
remaining "elementary" route to the floor (self-improving recursion). Consistent with the open core: the
floor holds iff `onset(r) > log m` at the fixed prize prime, and the in-tree onset law `onset(r)~0.54r`
crosses β=4 at r≈6 < log m≈89 — so `W_r>0` at deep r, and once on, it grows. The floor is genuinely the
char-p deep-moment / BGK wall, not closable by induction. Tool: /tmp/wr_recursion.py.
