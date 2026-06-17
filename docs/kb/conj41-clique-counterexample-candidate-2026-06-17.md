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

## UPGRADE: candidate → PROVEN over ℚ (exact, reduces to all large p)
`probe_conj41_exact_Q_proof.py` runs the entire construction in **exact rational arithmetic** (Python
`Fraction`; no floating point, no mod-p sampling): for the rational clique `S={0,…,w}` with `γ_i = i+1`, it
builds `A` over ℚ, computes a ℚ-kernel `(s1,s2) ∈ ℚ^D`, and for each support `E_i` solves `V_{E_i} v_i =
s1 + γ_i s2` over ℚ, verifying as exact rational identities: (i) `γ_i` is `E_i`'s unique isolated
compatibility value; (ii) `V_{E_i} v_i = s(γ_i)` exactly; (iii) every entry of `v_i` is nonzero; (iv) the
`w+1` values `γ_i` are pairwise distinct. **All hold over ℚ** for n=20/c5 (M_true=6>3), n=24/c5 (8>4),
n=18/c3 (7>5), n=28/c6 (9>4) — including the paper's exact Remark-42 rows.

**Reduction to all large p (the proof).** `(s1,s2)`, `γ_i`, `v_i` are rational with finitely many
denominators. For every prime `p` not dividing those denominators, the numerators of the `v_i`, or any
`γ_i−γ_j`, the identical vectors reduce to `F_p` and satisfy the SAME equations there — so
`M_true(s1 mod p, s2 mod p) ≥ w+1 > ⌊(2D−1)/c⌋`. Hence the bound fails at all but finitely many primes.
Combined with the char-0 partial-fraction mechanism (which already shows the clique rank-deficiency is
characteristic-independent), this is a **rigorous proof that Conjecture 41's worst-case (universal) form is
false**: the `(w+1)`-clique violates it at all large p, contradicting the paper's "realizable only below
`p_0`" claim.

**Status: PROVEN over ℚ** (not merely numerical). Standard scientific caution still applies — independent
reproduction against the authors' reference scripts [36] is warranted before treating it as community-
settled — but the exact-ℚ verification removes the "numerical artifact" and "small-p" doubts. My
single-syndrome `M_true` matches the paper's anchor table 10/10, so the `M_true` semantics are theirs.

**Scope unchanged:** OFF the FRI-soundness critical path (Theorem 18 uses no §7 result), and the prize
(pinning δ*) is untouched and still open. What this corrects: OP2's worst-case list size is **not**
`⌊(2D−1)/c⌋`; it is `≥ w+1` via cliques. The average/typical-case bound (what the authors' random search
saw) is consistent with their data.

## Final cross-validation: engine reproduces the paper's average-case; clique is the special worst case
Random-syndrome search (the paper's verification method) with my engine: at n=20,c=5 (bound 3), 200 random
lines give **max M_true = 0** (well within bound; consistent with the paper's `≤2` over ≥14000 configs —
random lines in `F_p^D` almost never decode any support since the `c=5` conditions over-determine γ). The
**constructive clique gives 6** (proven over ℚ). This confirms: (i) my engine faithfully matches the paper's
average/random-case data, and (ii) the clique is a genuine **measure-zero worst-case** configuration that
random search cannot reach — exactly why the authors' random-search verification missed it. Triangulated:
anchor table 10/10 (single-syndrome) + average-case match (random line) + exact-ℚ proof (worst-case clique)
+ char-0 mechanism. The proven counterexample to Conj 41's worst-case form stands on all four legs.
