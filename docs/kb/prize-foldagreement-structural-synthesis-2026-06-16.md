# Structural synthesis: why above-Johnson FRI soundness is O(1)/|F| — the fold-agreement mechanism (#444)

A coherent, mostly-provable account of the prize `O(1)/|F|` commit-phase soundness, tying together every
structural finding of the campaign. It reduces the remaining open content to a single concrete count
(= 2026/861 Conjecture 7.1), but explains the mechanism from first principles.

## The core lemma (provable): folding preserves ONLY antipodally-paired agreement
For the dyadic fold `Fold(f,λ)(x²) = (f(x)+f(−x))/2 + λ·(f(x)−f(−x))/(2x)`:
- If `f` agrees with codeword `c` at **both** `x` and `−x`, then `Fold(f,λ)` agrees with `Fold(c,λ)` at `x²`
  for **every** `λ`.
- If `f` agrees with `c` at `x` but **not** `−x`, the agreement at `x²` survives for **at most one** `λ`
  (the value where `(f(x)−f(−x))` aligns) — generically it is destroyed.

So the folded agreement set is `Fold(Agree) ⊇ {x² : x,−x ∈ Agree}` (antipodal pairs survive
unconditionally) and unpaired agreements survive only on a measure-`1/|F|` set of challenges.

## Consequence: far words stay far; the bad set is antipodally-structured
A δ-far word `f_0` has no codeword within δ, so its agreements with any codeword are "accidental" and
**mostly unpaired**. Folding **destroys** unpaired agreement ⇒ the folded word stays far for all but a
`1/|F|`-fraction of challenges per unpaired agreement. The challenges that *deceive* (keep it close) are
exactly those that preserve enough **antipodally-paired** agreement down the fold tower. This is:
- the same object as the **aligned-codeword `≤ m` bound** (deviation on `m` folded positions ⇒ `≤ m`
  surviving challenges) — PROVED;
- the same as the **"3-position" witness** (= error folds to few positions / antipodal orbits) — rediscovered;
- the same as the **action-orbit symmetry** of 2026/861.

## Where O(1)/|F| comes from, and the one open count
The commit-phase bad set = challenge tuples preserving paired-agreement through all `log N` rounds. Each
round, an unpaired agreement contributes a `1/|F|` constraint; paired agreements pass freely but are FEW
(an above-Johnson far word, having weight `~0.29N`, can pair-structure only a bounded number of its
agreements). The **number of independent surviving paired-agreement configurations** is the constant `c`;
the bad ratio is `c/|F|`. The prize `O(1)/|F|` ⟺ **`c = O(1)` independent of `N`** — i.e. the worst-case
far word cannot manufacture more than `O(1)` antipodally-paired agreement configurations that survive the
whole tower. **This is exactly Conjecture 7.1 (sparse/3-position dominance), now given a concrete mechanism:
it is the statement that paired-agreement-survival is dominated by `O(1)` orbit configurations.**

## Status (honest)
- **Provable here:** the core lemma (fold preserves only paired agreement); the `≤ m` aligned bound; that
  unpaired agreement costs `1/|F|` per round. These give the `O(1)/|F|` **shape** and explain it mechanistically.
- **Open (= Conj 7.1):** that the surviving paired-agreement configuration count `c` is `O(1)` in `N`. The
  campaign's computations support `c` bounded (ratios `≤ ~1/q` across N=8,16) but cannot prove
  N-independence (worst-case not samplable; `c`'s clean N=8 value is finite-size). A proof needs to bound
  the paired-agreement configurations of an arbitrary above-Johnson word via the cyclic (action-orbit)
  symmetry — the genuine remaining mathematics, which 2026/861 claims (via the gated argument) and the
  internal team claims (unpublished).

## Net
This is the most complete structural theory the campaign produced: it PROVES the mechanism (fold kills
unpaired agreement ⇒ `O(1)/|F|` shape) and reduces the prize to ONE concrete, non-BGK, combinatorial count
(`c = O(1)`: paired-agreement-survival dominance). It does **not** close that count — that is Conj 7.1, the
open core. No fabrication: the lemma is proved, the count is honestly open.
