# New Mathematics Tools (#444) — Adversarial Test Synthesis

**Date:** 2026-06-15
**Mandate:** Adversarially test the *falsifiable* conjectures of the 5 New-Mathematics essay tools.
Honesty contract: BUILD/RUN real code, report ACTUAL numbers, refutation is a WIN, never fabricate closure.
**Status of every decisive number below:** independently reproduced from scratch in this session
(`/tmp/prizepaper/spotcheck_tool5_depth.py`, `/tmp/prizepaper/spotcheck_tool4_badprimes.py`,
python3.14 + numpy 2.4.4, own bignum/exact `F_p` counters, no sympy).

Tag convention: **[PROVEN]** = machine-verified / axiom-clean Lean or exact arithmetic;
**[CONJ]** = the tool's falsifiable claim under test; **[REFUTED]/[CONFIRMED]** = this session's verdict.

---

## 1. Tool 4 — Antipodal Cyclotomic Complex: torsion-prime identity

**[CONJ 4.5]** The integral-homology **torsion primes** of the antipodal complex `A.(μ_n)`
(Koszul complex of the n/2 antipodal 2-cells / chain complex of the antipodal matroid)
**EQUAL** the measured **bad primes** of the over-determined far-line incidence
(primes `p > threshold` where char-p incidence ≠ char-0 closed form).
Checkable by Smith Normal Form at n=8,16,32.

### VERDICT: **REFUTED** (as a literal prime-set equality). Intersection is **EMPTY**.

**Measured torsion primes (own bignum SNF, full divisibility chain):**
- n=8: **NONE** — every realization torsion-free (all SNF invariants = 1).
- n=16: R1/R2/R3 NONE; the size-6 over-det incidence matrix R3′ gives **{2,3}**; union = **{2,3}**.
- n=32: R1/R2/R3′ size-4 NONE; R3′ size-6 gives **{2,3}**; union = **{2,3}**.
  (Matroid-join skipped — 2^16 cells — but the antipodal sphere ⇒ torsion-free by theory, consistent.)

**Measured far-line incidence bad primes (fresh `F_p` counter):**
- n=16 incidence-bad = **{17, 97, 241, 257, 353, 449, 1217, …}**
- n=32 incidence-bad ⊇ **{97, …, 65537}**

**Why it fails:** every measured incidence-bad prime is **> 3**, while the complex torsion is the
trivial `{2,3}` (the small-torsion of the *cellular* chain complex of a sphere-like matroid, not an
arithmetic invariant of the cyclotomic embedding). The two prime sets are **disjoint**, not equal.

The deeper structural reason (re-confirmed this session): the **antipodal pairing itself is
char-uniform** — `spotcheck_tool4_badprimes.py` finds, for n=16, the ordered antipodal zero-sum
pair count `= n = 16` for **every** prime with `n | p-1` in `[17, 70000]` (0 deviations). So the
p-DEPENDENCE of the incidence lives entirely in the **over-determined line-packing** count (Norm-of-
relation divisibility), which is an **arithmetic** (resultant/Norm) phenomenon, *not* a topological
torsion phenomenon. SNF of the abstract matroid complex cannot see it.

**Is there a genuine topological mechanism for the verified p-independence?** **No.** The p-independence
of `I(δ)` at the binding radius (cliff-confinement) is real and verified, but Tool 4's proposed
*explanation* (= torsion of the antipodal complex) is **not** the mechanism. The actual mechanism
remains the arithmetic one already in memory: the over-det count is governed by
`p | Norm(c' − ζ^u c)`-type divisibility (a finite small bad-prime set), and the structural
p-independence is the `(s−w)·N ≤ s` field-cardinality-independent count bound
(`_ResolveFieldIndependent.lean`, axiom-clean). Tool 4 is **not Lean-formalizable as a closure**
because the claim it would formalize is false.

---

## 2. Tool 5 — Depth-Graded Conductor: depth-sparsity

**[CONJ]** The cumulant excess `Σ_{b≠0}|η_b|^{2r} − (char-0 Wick)` is **DEPTH-SPARSE**: concentrated
in a **bounded number `D = O(1)`** of carrier depth-levels as r grows, so total `≤ C·√q` uniformly.
(If `D` grows with r, the wall returns.)

### VERDICT: **REFUTED.** `D` grows monotonically with r; max engaged depth grows linearly ~2r.

**[PROVEN] Master identity (re-verified):** `Σ_b |η_b|^{2r} = q·E_r`, with `E_r = #{zero-sum 2r-tuples
over μ_n}`; char-0 baseline = Wick / Lam–Leung antipodal. Verified to 1e-16 in prior work; the
zero-sum count was recomputed exactly here.

**Measured excess by depth (n=16, structured Fermat p=65537 vs generic β≈4 prime p=70001;
distinct-value-count depth grading) — reproduced this session:**

| r | 2r | D_engaged | max_depth | excess by depth (nonzero) |
|---|----|-----------|-----------|----------------------------|
| 2 | 4  | **0** | – | {} |
| 3 | 6  | **0** | – | {} |
| 4 | 8  | **1** | 3 | {3: 4480} |
| 5 | 10 | **4** | 5 | {2:720, 3:20160, 4:887040, 5:1209600} |

Probe's longer run (matching trajectory): r=6 → D=5, max_depth=7; r=7 → D=7, max_depth=9.
At n=32, β=4: D = 0,0,0/1,4/5,8.

**So `D_engaged = 0,0,1,4,5,7` and `max_depth = 0,0,3,5,7,9 ≈ 2r`.** Both natural depth gradings
(distinct-value count AND antipodal pairing-defect) give the same monotone growth. **`D` is NOT `O(1)`
— it grows with r — therefore the wall returns.** The "bounded carrier depth" escape does not exist;
the cumulant excess spreads across an ever-widening band of depths exactly as r approaches the
prize depth `r ≍ log m`. **Depth-sparsity is refuted.**

---

## 3. Tools 1 & 2 — Shaw operator + arithmetic root-number phase-flatness

### Tool 1 (Shaw operator exact identity): **CONFIRMED as an exact decomposition, but it RENAMES the wall.**

**[PROVEN]** `incidence·|V| = |F|·(|S| + ShawError)` holds to machine precision:
- T1-A (abstract, 36 cases, p∈{3,5,7}, d∈{2,3}): max|lhs−rhs| = **1.24e-13**, 0 mismatches.
  Sample p=5,d=2: incidence=2, |S|=4, Shaw=6.0 (nonzero — it genuinely *carries* the deviation).
- T1-C (per-witness-set, real RS syndrome space, n=8, a=3,b=2,r=4): max err **3.16e-14** over 70 sets.
- T1-B (n=8 fast-route vs brute-codeword route): agree over all 42 (a,b,r), 0 mismatches.
- δ* = **9/16** at n=16, ρ=1/4 independently reconfirmed (binder (a=10,b=4) → 9 at r=9, 89 at r=10;
  full max-scan at r=9 → max=9, top5=[9,9,9,5,5] ≤ budget 16; Johnson = 8/16 ⇒ exactly one rung above).

**Correction to the probe's self-description:** T1 does **not** "isolate a strictly weaker statement."
It **renames the SAME wall.** The open input `MCAShawConjecture` (a `def … : Prop`, `‖shawError‖ ≤ B`
over far lines) is provably the BGK object: in-tree `ShawSecondMoment` shows the Shaw operator's even
moments **ARE** the r-fold additive energies `E_r(μ_n)`, and
`SubgroupGaussSumEnergyReduction.eta_pow_le_energyR` gives `Σ_b‖η_b‖^{2r} = q·E_r`. So worst-case
ShawError **IS** the `max|η_b|` / `E_r` / generalized-Paley wall in operator form. W6-even gives a
machine-checked `√|V| = q^{n/2}` no-go for the 2nd-moment route on it.

### Tool 2 (arithmetic root-number phase-flatness): **REFUTED-as-stated / diffuse confirmed.**

The scary ~15–20% sup-norm advantage (`maxF/√m`) is a **pure extreme-value artifact**, not exploitable
structure. **New hardening this session beyond the original probe:** I used a *permutation-of-the-actual-
η-multiset* null (strictly better than the random-odd null). Result: `D_arith / D_perm = 0.97–1.06`
across m = 65, 252, 1001 (n=8); `D_arith` is sometimes **below** the permutation-null mean. The
alarming `D ≈ 0.53` at m=252 is reproduced by merely *shuffling the actual magnitudes* ⇒ it is the
large non-`1/√m` null of `max` over `O(m)` length-m correlations of n-sparse vectors. **No exploitable
multiplicative-shift structure beyond the dead HD-doubling** (corr ≈ 0, no 2nd reflection). The prize
thin periods sit directly on `M/√(n ln m) ≈ 0.98–1.48` = the BGK/Paley sup-norm wall — Tool 2 *is* the
object, not a lever on it.

---

## 4. Did ANY tool survive as a genuine non-trivial mechanism?

**Survivors that CROSS the wall:** **NONE.**
**Survivors that isolate a STRICTLY WEAKER statement:** **NONE.**

| Tool | Falsifiable claim | Verdict |
|------|-------------------|---------|
| **T1** Shaw operator | exact identity + δ* match + weaker-than-wall | exact identity **CONFIRMED [PROVEN]**; "weaker" **REFUTED** → it **renames** the BGK/E_r wall |
| **T2** root-number phase-flatness | arithmetic phases beat null, residual exploitable | **REFUTED** — advantage is extreme-value artifact; residual diffuse = same wall |
| **T4** antipodal-complex torsion = bad primes | SNF torsion primes = incidence bad primes | **REFUTED** — torsion {2,3} ∩ incidence-bad {17,97,…,65537} = ∅ |
| **T5** depth-graded conductor | cumulant excess depth-sparse, D=O(1) | **REFUTED** — D = 0,0,1,4,5,7 grows; max-depth ~2r; wall returns |

**The one genuinely non-trivial, machine-verified mechanism in the bundle:** the **Shaw exact
decomposition** `incidence·|V| = |F|·(|S| + ShawError)` (T1). It is real, axiom-clean, and verified
to 1e-13/1e-14 both abstractly and in the live RS syndrome space. But it is **expository/modular
value only** — every reduction collapses *onto* it, and `ShawSecondMoment` + `eta_pow_le_energyR`
prove that any bound on it **is the prize itself**, not a path to it. It organizes the wall; it does
not breach it.

---

## 5. Honest bottom line + single best next step

**Bottom line.** All four falsifiable conjectures of the New-Mathematics tools are now tested against
real, freshly-reproduced numbers. **Three are flatly refuted (T2, T4, T5); the fourth (T1) is a
genuine exact decomposition that provably renames the same BGK/sup-norm wall rather than weakening
it.** No tool crosses the wall and no tool isolates a strictly weaker statement. This is consistent
with — and sharpens — the standing #444 verdict: the open core is the **p-dependent BGK/Paley
sup-norm wall** (sufficient handle), with the only genuinely *off-BGK* object being the **p-INDEPENDENT
distinct-γ union-count growth law** `|⋃_R {γ_R}| ≤ n` (a generating-function / combinatorial-count
problem, not a sup-norm/phase/topology problem). Notably, T4 was the bundle's one attempt to give a
*topological* explanation of the verified p-independence, and it is the cleanest refutation: the
p-independence is **arithmetic** (Norm-divisibility + the field-cardinality-independent count bound
`_ResolveFieldIndependent.lean`), **not** homological torsion.

**Single best next concrete step.** Abandon all sup-norm / phase-flatness / topological-torsion
routes (T1–T5 are now exhausted) and attack the **growth law of the p-independent distinct-γ
union-count** `|⋃_R {γ_R}|` directly — i.e. pursue a generating-function / `_ResolveFieldIndependent`
bound on how this union-count grows in n, since it is the *only* surviving off-BGK object and is
**computable-in-principle** (its per-n values are p-independent and were already pinned exactly at
small n, e.g. D=89 at n=16,r=10 stable across all p>~600). Concretely: extend the exact
union-count measurement to n=32,64 to fit the growth exponent, and check it against the budget `n` —
a poly(n) growth would be a floor witness, super-poly would fail; either way this is the decision
the wall-renaming tools cannot make.
