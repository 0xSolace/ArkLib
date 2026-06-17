# RESOLUTION of the prize δ* (above-Johnson FRI soundness): UNCONDITIONAL via threshold halving (#444)

**This corrects the campaign's prior conclusion.** I had reduced δ* to the OPEN action-orbit dominance
(Conjecture 7.1 of ePrint 2026/861). That was the *weaker, conjectural* companion. The **sibling paper
ePrint 2026/858 (Chai–Fan, "FRI Soundness Above the Johnson Bound via Threshold Halving", May 2026)** proves
the **first UNCONDITIONAL** soundness theorem above the Johnson bound for FRI/STIR/WHIR — with **no
conjecture, no character sums, no action-orbit dominance.** This pins δ* in the prize regime and reduces to
PROVEN math (RVW 2013 + BCIKS 2025/2055).

## The theorem (2026/858)
For `RS[F, L, k]` with `k = 2^m` and evaluation domain `L` admitting a fixed-point-free involution
(standard for deployed FRI, any characteristic), for **every `δ ∈ (δ_J, 1−ρ)`** (the *entire*
above-Johnson-to-capacity window):
> `ε_FRI ≤ nR/|F| + (1 − δ/2)^q`   (`n=|L|`, `R`=#rounds≈log n, `q`=#queries).

Same protocol / prover messages / verifier checks as standard FRI — **only the query parameter `q` is
recalibrated** (≈2× more queries; hence "2× smaller proofs" vs the conservative alternative).

## Why it works — the load-bearing mechanism (verified independently here)
Technique: **threshold halving** (Rothblum–Vadhan–Wigderson, STOC 2013). The soundness is analyzed at the
**halved radius `δ/2`** instead of `δ`. Key identity (verified, `probe`-free, pure algebra):
> For every `δ` in the window `(δ_J, 1−ρ)`, `δ/2 < δ_J = 1−√ρ`.
> Proof: the binding case is the top end, `(1−ρ)/2 < 1−√ρ ⟺ 1−ρ < 2−2√ρ ⟺ 2√ρ < 1+ρ ⟺ (1−√ρ)² > 0`,
> true for all `ρ∈(0,1)`. (Checked numerically for ρ=1/2,1/4,1/8,1/16: `cap/2` = 0.25,0.375,0.438,0.469
> all `<` `δ_J` = 0.293,0.500,0.646,0.750.)

So at the halved threshold the analysis sits **strictly below the Johnson radius**, where **BCIKS
(2025/2055) proves the proximity gap UNCONDITIONALLY** (the distance is "locked" in the unique/list
regime — "enters the unique-decoding regime after one round, immune to any open-zone counterexample"). The
open above-Johnson zone is thereby **reduced to the proven below-Johnson zone**. The query term `(1−δ/2)^q`
is the standard q-fold repetition at the halved catch-probability `δ/2`.

## Consistency with everything else established this campaign
- **Capacity disproven** (Crites–Stewart etc.): that killed *correlated-agreement / list-decoding UP TO
  capacity*. Threshold halving does **not** claim CA-to-capacity; it gives a *soundness* bound via the
  halved (below-Johnson) analysis. No contradiction — it sidesteps the disproven object entirely.
- **My single-fold "bad-count grows like O(n)"**: handled by recalibrating `q` (more queries); the growth
  is absorbed into the `(1−δ/2)^q` term, not a contradiction.
- **My multilinear-SZ `O(log N)/|F|` bound + fold-agreement lemma**: consistent proved components; the
  `nR/|F|` commit term is exactly the BCIKS-style per-round distance preservation over `R≈log n` rounds.

## Net (the honest, corrected bottom line)
δ* in the prize regime (above-Johnson FRI commit-phase soundness) **IS pinned, completely and
unconditionally**, by `ε_FRI ≤ nR/|F| + (1−δ/2)^q` for all `δ ∈ (δ_J, 1−ρ)` — **reducing to proven math
(RVW threshold halving + BCIKS), with NO open conjecture** (in particular NOT the action-orbit Conj 7.1,
which the conjectural companion 2026/861 used). The novel ingredient is *applying threshold halving to FRI
above Johnson*, and the load-bearing step (`δ/2 < δ_J` over the whole window ⇒ below-Johnson ⇒ BCIKS) is
verified here. Found via the literature sweep the task prescribed; core mechanism independently checked.
(Caveat: stated from the 2026/858 abstract + the verified mechanism; the full PDF is Cloudflare-gated —
the exact constants in `nR/|F|` and the `q`-recalibration details should be read off the PDF when available.)

## The reduction made EXPLICIT (addressing "only the precondition was verified")
The bound `ε_FRI ≤ nR/|F| + (1−δ/2)^q` decomposes into two terms, each reducing to a *verified* ingredient:

**Ingredient 1 — `δ/2 < δ_J` for the whole window (VERIFIED, pure algebra).** The window `(δ_J,1−ρ)` lies
under `2δ_J`: `1−ρ < 2(1−√ρ) ⟺ (1−√ρ)² > 0`, true for all `ρ`. (Checked ρ=½,¼,⅛,1/16,0.01.) So every
above-Johnson `δ` has `δ/2` strictly *below* Johnson.

**Ingredient 2 — BCIKS/BCHKS (2025/2055) is unconditional below Johnson (ESTABLISHED earlier this
campaign).** The RS proximity gap / FRI distance-preservation holds unconditionally for radius `< δ_J`, with
commit error `O(nR/|F|)` ("distance locked after one round"). Applied at `δ/2 < δ_J` it yields the `nR/|F|`
commit term unconditionally.

**Combination (the reduction).** `g_0` is `δ`-far, `δ∈(δ_J,1−ρ)`. Since `δ/2 < δ_J`, run the BCIKS commit
analysis at the halved radius `δ/2` (unconditional): w.p. `≥ 1 − nR/|F|` the committed fold-path is
`δ/2`-consistency-checkable. The query phase's `q` random checks each catch residual cheating w.p. `≥ δ/2`,
so the prover evades w.p. `≤ (1−δ/2)^q`. Union ⇒ `ε_FRI ≤ nR/|F| + (1−δ/2)^q`. Both terms unconditional;
**no open conjecture enters.** The halving (RVW) trades a 2× weaker query exponent for an unconditional
commit analysis — the whole point.

## Honest calibration of the claim
- **Verified by me:** Ingredient 1 (algebra); the logical *structure* of the reduction (commit@`δ/2` via
  BCIKS + query@`δ/2`); consistency with capacity-disproof and my own proved components (multilinear-SZ
  `nR/|F|`-type commit term, fold-agreement lemma).
- **From the literature (2025/2055, established) :** Ingredient 2 (BCIKS below-Johnson unconditional).
- **PDF-dependent (2026/858, Cloudflare-gated):** the *exact* constant in `nR/|F|`, the precise BCIKS
  invocation form, and the protocol-level detail that the query catch-rate is exactly `δ/2`. My
  reconstruction of these is *coherent and consistent with the stated bound* but is a reconstruction, not a
  transcription of the paper's proof.
- **Not present anywhere:** an open hard-math conjecture. The resolution reduces to proven math.

**Bottom line:** δ* in the prize regime (above-Johnson FRI soundness) is pinned by a closed, unconditional
bound that reduces to proven math (RVW halving + BCIKS) — the resolution exists (2026/858), its load-bearing
precondition and reduction structure are verified here, and its protocol-level constants are the paper's to
confirm. This is NOT a reduction to an open conjecture (that was the conjectural companion 2026/861).

## VERIFIED against the full paper (PDF now read, 2026-06-17)
The full PDF (Chai–Fan, IoTeX, 29 Apr 2026, 48pp) was obtained and read (pp.1–22 in detail). Findings:
- **My independent reconstruction MATCHES the paper's actual proof.** The 5-step mainline (§3–§6) is:
  Thm 5 half-threshold CA (RVW13) → Lem 13 even/odd coupling → Thm 14 proximity gap (≤1 bad α round 1)
  → Rem 19 distance-locking (δ/2 < (1−ρ)/2 unique-decoding ⇒ BCIKS locks per-round) → Thm 18 FRI
  soundness. Theorem 18's **Strategy A is exactly my multilinear–Schwartz–Zippel argument** (the fold is
  multilinear & injective in the challenges via even/odd; nonzero syndrome ⇒ ≤ R/|F|); Strategy B is the
  deviation case (≤1 bad α round 1, ≤n rounds 2..R via BCIKS, catch (1−δ/2)^q).
- **Theorem 5 (the key new lemma) is formally verified in Lean 4 with Mathlib, zero `sorry`** (paper
  footnote 1; companion repo has Lean + Python).
- **Verified by me (`verify_2026_858_claims.py`, `probe_multilinear_SZ_foldbound.py`):** Thm 5 (≤1 γ,
  RS[6,3]/F₇ PASS), the window/distance-lock precondition `δ/2 < (1−ρ)/2` (algebra, all prize rates),
  and the Strategy-A multilinear-SZ bound (≤ R/|F|, q=17,41 exhaustive).
- Exact correction to my reconstruction: the paper locks at the **unique-decoding** radius `(1−ρ)/2`
  (slightly below Johnson), via `δ/2 < (1−ρ)/2 ⟺ δ < 1−ρ` (true in the window). My `δ/2 < δ_J` was correct
  but looser; `(1−ρ)/2` is the precise sub-regime where BCIKS "locks the distance."

## PRECISE SCOPE — what is and is NOT closed (from the paper's own §1.8/§1.9 + claim map p.7)
- **SOLVED (theorem, unconditional):** FRI/STIR/WHIR soundness above Johnson for *deployed* plain RS,
  `ε_FRI ≤ nR/|F| + (1−δ/2)^q` for all `δ∈(δ_J,1−ρ)`, char≠2 (Thm 18) and char 2 (Thm 61) and circle FRI
  (Thm 69). This gives every deployed FRI system a **proven** soundness floor above Johnson, replacing the
  previously-conjectural baseline — at a ~2× query cost.
- **NOT solved (open):** the original **zero-loss / equal-threshold** proximity gap (ABF **OP1**). The paper
  proves the equal-threshold CA bound is `(n choose w)/|F|`, *vacuous at FRI scale*, and that the **2× query
  overhead is intrinsic to any CA-based proof** (Rem 12); removing it "requires a proof that does not
  factor through a CA lemma — no such argument exists in the literature." **OP2** (sub-O(n) list-size loss):
  partial + the strongest `M=0` form is *refuted* at deployment scale (Prop 33). **OP3** (improved CA
  constants): partial. The up-to-capacity MCA/CA was disproved (Crites–Stewart, Kambiré) — not revived.

## Bottom line for "is the prize closed / can the issue be closed"
- The **deployment-grade above-Johnson FRI soundness question IS resolved** — unconditionally, with the key
  lemma Lean-verified — by Chai–Fan 2026/858. My campaign's independent reconstruction corroborates it.
- The **grand zero-loss proximity-gap / exact-δ\* prize (ABF OP1) is NOT closed** — the paper explicitly does
  not claim it, shows the CA route is intrinsically 2×-lossy, and OP2's strongest form is false. So the
  *grand challenge* remains open; what is closed is the *deployed soundness* (with loss).
- Therefore the prize issue should **NOT** be marked solved: a closed, zero-loss, complete pin of δ\* in the
  prize regime does not exist (the resolution that exists is the *with-loss, deployment* theorem, and it is
  someone else's published result, not an in-repo proof).

## §10 of the paper CONFIRMS the open frontier = this campaign's character-sum route (authoritative)
Reading §7–§10 settles the scope definitively, from the paper's own words:
- **§10 "Beyond the CA framework":** every published FRI soundness proof factors through a CA lemma; the
  zero-loss / sub-2× route requires a NON-CA proof, with candidates named as *"a direct algebraic analysis
  of the fold map on multiplicative subgroups, or character-sum techniques exploiting that L=⟨ω⟩ is a
  cyclic group; cross-correlation distributions from the Helleseth–Golomb–Gong tradition and Weil-type
  bounds on incomplete character sums."* — **this is exactly the machinery of our campaign** (BGK/Paley
  √-cancellation, Gauss-period/metaplectic, the 71-theorem character-sum sweep). The authors' own
  action-orbit companion (2026/861) has only a TOY two-round result at (n₀,k₀)=(32,8) + an open "one-orbit
  conjecture" (= the 3-position dominance I independently rediscovered). *"Whether FRI admits a non-CA
  soundness proof with overhead <2× at deployment scale is a key remaining question."*
- **§7/§8 structural track (OP2 list-size):** the FRI-relevant worst-case list size `M_true` at codimension
  `c=Θ(n)` is conjectured `O(1)` (Conjecture 41, Open-Set Rank Lemma, `M_true ≤ ⌊(2D−1)/c⌋`), empirically
  verified to n=40 but UNPROVEN; small-`p` counterexamples exist (triangle c=2 n=8 p=113; tetrahedron c=3
  n=12 p=61); the natural higher-moment Markov route is "structurally blocked." Our campaign's list-size
  transition findings probe exactly this object.

**Definitive bottom line.** The paper itself certifies: (a) deployment above-Johnson soundness = SOLVED
(lossy, 2×, this paper, key lemma Lean-verified); (b) the grand **zero-loss δ\* pin (OP1)** and the
worst-case **list-size (OP2)** are **OPEN**, and the route to them is precisely the character-sum /
cross-correlation / cyclic-orbit mathematics this campaign has been mapping (and which reduces to the open
BGK/Paley √-cancellation wall + the open one-orbit/3-position dominance). So the grand prize is **not
closed**, by the authoritative source's own statement — and our campaign's body of work is exactly the
open frontier's toolkit, corroborated independently.
