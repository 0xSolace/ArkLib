# CANDIDATE COUNTEREXAMPLE to Conjecture 41's worst-case form (ePrint 2026/858 §7.6) — the (w+1)-clique (#444)

A constructive, mechanistically-grounded candidate counterexample to **Conjecture 41** (Open-Set Rank Lemma):
`max_{s1,s2} M_true(s1,s2) ≤ ⌊(2D−1)/c⌋` for `c≥3`, `D=n−k`, `w=D−c`. **Presented with explicit humility:
a candidate pending independent confirmation against the authors' exact `M_true` definition / scripts —
NOT a certain refutation; and it does NOT affect the FRI soundness theorem (see scope).**

## The finding (constructive, fully verified)
At the paper's **exact Remark-42 parameters**, large primes, random domains, the `(w+1)`-clique line gives
`M_true(s1,s2) = w+1 > ⌊(2D−1)/c⌋`:

| n | k | c | w | bound ⌊(2D−1)/c⌋ | clique M_true | primes (all EXCEED) | paper's random-search obs |
|---|---|---|---|---|---|---|---|
| 20 | 10 | 5 | 5 | 3 | **6** | 1009, 10⁵, 10⁶ | ≤2 |
| 24 | 12 | 5 | 7 | 4 | **8** | 1009, 10⁵, 10⁶ | ≤2 |
| 28 | 14 | 6 | 8 | 4 | **9** | 1009, 10⁵, 10⁶ | ≤4 |

Each clique decoding is explicitly verified (`allok=True`): isolated unique γ per support, all-nonzero
weight-`w` error, `V_E·v = s(γ)` exactly; the `w+1` γ are distinct; the FULL `M_true` over all `C(n,w)`
supports equals `w+1` (no spurious overcount). Probe: `scripts/probes/probe_conj41_clique_counterexample.py`.

## Why it is NOT a small-p artifact (the mechanism — verified over ℚ)
The `(w+1)`-clique on set `S` (`|S|=w+1`), supports `E_i=S\{a_i}`, `Λ_{E_i}=Λ_S/(x−a_i)`, satisfies the
**partial-fraction identity** `Σ_i Λ_{E_i}/Λ_S'(a_i) = 1` — a **characteristic-0 polynomial identity**
(verified exactly over ℚ, `/tmp/conj41_mechanism.py`). This linear dependency among the clique's error-
locator polynomials reduces mod **every** prime not dividing the `Λ_S'(a_i)` (i.e. all large p), making the
clique's rank-deficiency (and hence the `M_true=w+1` line) **characteristic-independent**. This directly
contradicts the paper's claim that the `(w+1)`-clique is "realizable only at primes below an explicit
threshold `p_0`."

## Why the paper's verification missed it
2026/858 verifies Conj 41 (a **universal/worst-case** statement) by **random-syndrome search** (Remark 42).
The clique line is a **measure-zero** configuration in `(s1,s2)`-space — random search cannot reach it. The
paper *names* the `(w+1)`-clique as "the general obstruction" but only *claims* (does not verify) it's small-
p-only. The constructive (kernel-of-A) search here targets exactly that obstruction and finds it realized at
all large p.

## Scope and honest caveats
- **Does NOT affect the FRI soundness theorem.** 2026/858 §1.10 / the proof map: "the mainline uses no
  result from §7"; Conj 41 is on the **structural track** (OP2 list-size), off the critical path to
  Theorems 5/14/18. The unconditional above-Johnson soundness (and our Lean Theorem 5) stands untouched.
- **Worst-case vs average-case.** This contradicts only the **worst-case (universal)** bound. The
  **average/random-case** behavior the authors verified (and the `O(n/c)` envelope) is unaffected — the
  clique is exceptional, not typical.
- **Confidence + humility.** My single-syndrome `M_true` matches the paper's anchor table exactly (10/10),
  so my `M_true` is their `M_true`; the mechanism is a verified ℚ-identity; the computation is exhaustively
  checked across params/primes/domains. This is **high-confidence**. BUT this session has produced earlier
  apparent "refutations" that were my own bugs, so I flag this as a **candidate requiring independent
  reproduction** against the authors' reference scripts [36] before being treated as settled. I do not
  claim certainty.

## Net
If confirmed: Conjecture 41's worst-case form is false (the `(w+1)`-clique violates it at all large p via a
char-0 partial-fraction dependency); the correct statement is an **average/typical-case** bound, with the
worst case governed by clique structure. The prize (pinning δ*) is unaffected and remains open; this refines
the OP2 list-size picture.
