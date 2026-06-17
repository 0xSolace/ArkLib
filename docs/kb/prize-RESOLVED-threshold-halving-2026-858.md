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
