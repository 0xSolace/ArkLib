# MAJOR ground-truth pivot (June 2026): capacity DISPROVEN, prize floor moved to the Johnson frontier, and 2026/861 reduces it to ONE combinatorial conjecture — NOT BGK (#444)

A literature scan for the **sharpened** target (signed word-line incidence / above-Johnson soundness, not the
sup-norm) surfaced a cluster of late-2025 / 2026 papers that **postdate and reframe** most of this campaign.
The prize is no longer "prove √-cancellation to reach capacity" — that target is **dead**.

## The new ground truth (June 2026)
- **Up to the Johnson radius `δ = 1−√ρ`: PROVEN.** BCIKS (Ben-Sasson, Carmon, Haböck, Kopparty, Saraf),
  ePrint **2025/2055**, "On Proximity Gaps for Reed–Solomon Codes": proximity gap holds up to `1−√ρ`,
  matching best-known list-decodability; positive soundness `a = O(n/η⁵)` at `γ < 1−√ρ−η`.
- **At/above capacity `1−ρ`: DISPROVEN** (three independent groups, Nov 2025):
  - Crites–Stewart **2025/2046**: CA/MCA/list-decodability up-to-capacity ⟹ impossibly good list-decoding ⟹ false.
  - Diamond–Gruen **2025/2010**: explicit counterexamples, `err(C,z) > n^{c}/q` for all constants `c`.
  - BCHKS **2025/2055** (algebraic impossibility): proximity loss below `2^{−(τ+1)}` needs `a ≥ n^{τ−o(1)}`.
  This kills the up-to-capacity protocols (aggressive WHIR).
- **Above Johnson, plain RS, `O(1)/|F|` error: ePrint 2026/861 (Chai–Fan, May 2026)**,
  "Action–Orbit FRI Soundness Above the Johnson Radius." First rigorous `O(1)/|F|` FRI commit-phase
  soundness for **plain** RS **above** Johnson, via **action–orbit symmetry on the cyclic FRI evaluation
  domain** — a *five-line* proof with **no correlated agreement, no character sums, no list-decoding**.
  **Unconditional for sparse adversary inputs.** General case reduces to **a single conjecture**:

  > **Conjecture 7.1 (sparse-worst-case dominance).** FRI soundness is dominated by its **3-position
  > sparse witnesses** (an "action-non-stabilised admissibility class"), consistent with every adversarial
  > construction in the proximity-gap literature.

## Why this is the correct pivot
My campaign correctly proved that pushing **into the window toward capacity** reduces to BGK/Paley
√-cancellation (the 71-theorem no-escape result). The new ground truth **explains** that wall: going to
capacity is not merely hard, it is **impossible** (disproven). The honest prize target is the
**above-Johnson `O(1)/|F|` regime**, and 2026/861 reduces it to **Conjecture 7.1** — a **closed combinatorial
dominance statement that does NOT reduce to character sums / BGK**. This is exactly the shape the prize asks
for: "a complete, closed conjecture that does not reduce to the open hard math."

Crucially, "action–orbit symmetry on the cyclic domain" is the **same structure** as this repo's ACL
(antipodal / coset-closure law, #389 commits) and the equivariance/coset-closure cone (A5). The campaign's
own machinery is aimed at the right object after all — just for the above-Johnson dominance question, not
the capacity √-cancellation.

## New attack surface (replaces the BGK wall)
**Target: Conjecture 7.1 (sparse-worst-case dominance).** Actionable because it is finite/combinatorial:
1. **Computationally test** whether worst-case FRI soundness on plain RS over a thin cyclic (dyadic) domain
   is dominated by 3-position sparse witnesses (probe machinery: rust-pg/cuda-pg + python probes).
2. **Connect** the in-tree ACL / coset-closure / equivariance bricks to the action-orbit symmetry of 2026/861.
3. If robust, **prove** 3-position dominance (a finite orbit-counting / admissibility-class argument);
   if it fails, that **refutes** 2026/861's general claim (also publishable).

## Reading list (user asked for 5 — these are the load-bearing ones; eprint.iacr.org is Cloudflare-gated,
## so PDFs must be downloaded interactively)
1. **2026/861** Chai–Fan, *Action–Orbit FRI Soundness Above the Johnson Radius* — THE paper; Conj 7.1 is the
   sole gap to the prize. https://eprint.iacr.org/2026/861.pdf
2. **2026/680** Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement* — the prize
   companion; defines the grand challenges post-disproof. https://eprint.iacr.org/2026/680
3. **2025/2055** BCHKS, *On Proximity Gaps for Reed–Solomon Codes* — Johnson-radius proximity gap PROVEN +
   algebraic impossibility. https://eprint.iacr.org/2025/2055
4. **2025/2046** Crites–Stewart — up-to-capacity DISPROOF. https://eprint.iacr.org/2025/2046
5. **2025/2010** Diamond–Gruen — explicit super-polynomial counterexamples.
6. **2025/1712** *Syndrome-Space Lens* — CA via syndrome-space change of basis (same `V=F` geometry as our
   in-tree IncidencePeriodBridge). https://eprint.iacr.org/2025/1712
7. **2025/2054** Goyal–Guruswami — optimal gaps `1−R−η` for random RS via curve-decodability.
8. **2601.10047** (arXiv, Jan 2026) — optimal proximity gap for FOLDED RS via subspace designs.

## Honest status
This does NOT close δ*. It **relocates** the open problem from the (impossible) capacity √-cancellation to
the (plausibly closeable) above-Johnson **3-position sparse-worst-case dominance** conjecture — a genuinely
different, non-BGK target. Next: attack Conjecture 7.1 directly.
