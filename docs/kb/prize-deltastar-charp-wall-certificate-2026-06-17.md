# δ* prize-regime certificate: the char-p / thin-subgroup sup-norm wall (2026-06-17)

**One-line verdict.** δ* is **NOT pinned** in the prize regime. A disciplined 11-agent
recon→invent→adversarial-verify attack plus four exact-arithmetic probes produced **0 closures /
0 survivors**; they sharpened the reduction, *resolved* the empirically-ambiguous sup-norm exponent
against the literature, found new on-regime (failure-side) papers, and quantified the wall — but did
not move the irreducible open core (the ~25-yr BGK / Paley-graph short-character-sum wall for thin
2-power subgroups). No fabricated closure.

Scope: RS proximity-gap / MCA threshold δ* for RS[N,k] over F_q, ρ∈{1/2,1/4,1/8,1/16}, dyadic n=2^μ,
thin field q≈n·2^128 (n≈q^{1/4..1/5}), target ε*=2^-128. Issue #444; companion ABF ePrint 2026/680.

---

## 1. Exact reduction δ* → single closed quantity Q (independently re-derived vs Lean source)

| Link | Statement | Status |
|---|---|---|
| L0 | δ* := mcaDeltaStar = sSup{δ : epsMCA C δ ≤ ε*}; well-defined, bracketed by `le_mcaDeltaStar_of_good`/`mcaDeltaStar_le_of_bad`. | PROVEN (def) |
| L1 | epsMCA C δ = ⨆_{stack u} Pr_{γ←$F}[mcaEvent]; sup over adversary stack, prob over uniform γ in the **single fixed field**. | PROVEN (def) |
| L2 | Pr_γ = #{γ:mcaEvent}/q ⟹ δ* ⟺ worst-case bad-γ count B(δ)=max_u #{γ:mcaEvent}. | **PROVEN — exact biconditional** (the only true two-sided link beyond defs) |
| L3 | On a non-degenerate monomial pencil over μ_n, mcaEvent ⟺ x^a+γx^b δ-close to RS[k]; B(δ)=far-line incidence I(δ). | PROVEN as ≥ (`epsMCA_ge_far_incidence`); `=` is monomial-pencil-specific |
| L4 | WorstCaseIncidenceBounded, B/q≤ε* ⟹ δ≤δ* (**floor**). Ceiling δ*≤(1−ρ)−Θ(1/log n) proven **unconditionally** by a constructed bad family (a different object). | PROVEN (sufficiency only) — **SANDWICH** |
| L5 | I(δ)≤B reduces to a character-sum input. **The bare sup-norm B_sup is necessary but INSUFFICIENT** — its only in-tree route pays a triangle factor q·B_sup ⟹ I≤n+q·B_sup, VACUOUS at budget q·ε*≈n. Operative input is the stronger √q-cancellation I≤n+√q·B (= **BCHKS Conj 1.12**, generalized-Paley eigenvalue). | PROVEN reduction (forward) to the correct stronger input |
| L6 | Moment ladder Σ_{b≠0}‖η_b‖^{2r}=q·E_r(μ_n) (orthogonality). Char-0 main term E_r(ℂ)≤(2r−1)!!·n^r **PROVEN** (Lam–Leung; E_2..E_8 closed in-tree). **OPEN CORE:** sup_p W_r ≤ slack_r, W_r=E_r(F_p)−E_r(ℂ)≥0, at r≈ln q. | PROVEN identity + PROVEN char-0 + **OPEN char-p** |

**The single closed quantity:** `Q := sup_{p admissible} W_r(p)` at saddle depth `r*≈ln q`
(verified r*≈110 at n=2^30; 83–89 at the lower-n end — both on-regime). Equivalently the √q-cancellation
incidence bound (BCHKS 1.12) ⟺ the non-principal eigenvalue of Cay(F_q, μ_n).

**Two corrections to the "biconditional on one Q" framing (load-bearing):**
1. **Sufficiency ≠ necessity.** Only L2 is a genuine biconditional; L4–L6 are one-directional
   (Q-bound ⟹ δ* floor). "δ* pinned" is a **sandwich**: open Q-floor + unconditional constructed
   ceiling. No proven inverse "small δ* ⟹ large W_r."
2. **The bare sup-norm is the WRONG Q.** The operative input is the strictly-stronger
   √q-cancellation / BCHKS-1.12 form.

**Quantifier-on-p (decisive).** epsMCA/mcaDeltaStar take the field as a **fixed free parameter**
(`evalCode {p}(g)`; no ⨆/inf over Field/Prime in the prize defs). So **target T2** (one deployed code,
`GrandMCAResolution`) is **per-fixed-p** — a bad-prime escape is *formally available* to the deployer;
**target T1** (the paper-side uniform `mcaConjecture`, `GrandChallenges.lean:650`, constants quantified
before ∀-over-fields) is **worst-case-over-p** and needs sup_p W_r. **Whether the bad-prime escape
actually exists at thin q≈n^4 is the load-bearing open sub-question** — the "union of weight-2r bad
families is dense" claim is an over-union heuristic, NOT a per-prime exclusion theorem.

---

## 2. Thin-regime literature verdict: WALL CONFIRMED (exact exponent gaps)

| Quantity (at t=n≈p^{1/4}) | Best known unconditional | Source | Prize/Gaussian target | **Exponent gap** |
|---|---|---|---|---|
| E_2(R) additive energy | n^{49/20}=n^{2.45} | MRSS 2017 (1712.00410) | 3n² (exp 2) | **0.45** |
| ↳ method floor | n^{7/3}=n^{2.333} (Balog–Wooley, unbeatable by sum-product/Stepanov/energy) | — | exp 2 | **0.333 — unreachable by current tech** |
| sup-norm max_a\|Σe_p(ax)\| | n^{1−31/2880}=**n^{0.98924}** | di Benedetto et al. 2020 (2003.06165) | n^{1/2} | **0.489** |
| ↳ BGK qualitative | p^{−β}\|H\|, β≫exp(−exp(C/ε)) doubly-exp small | BGK 2006 | — | quantitatively useless for ε*=2^-128 |
| E_3(R) | n^4·log n | MRSS | 15n³ (exp 3) | **1.0** |
| E_r, r>3 (prize needs r≈110) | **NOTHING** of form (2r−1)!!·n^r known | — | (2r−1)!!·n^r | entire char-p excess open |

At prize size n≈2^30 the E_2 overcount n^{0.45}≈6×10^5 dwarfs the budget ε*q≈n. Thin-regime "trivial
completion" does NOT rescue E_2 (at p=n^4 the a=0 term t^4/p = O(1); reducing the off-diagonal 4th
moment to O(t²) *is* the unknown sup-norm bound). **No citation closes the prize.**

**New on-regime literature (failure side, the ceiling):** Krachun–Kazanin–Haböck (eprint 2026/782) +
Kambiré (arXiv 2604.09724) prove proximity gaps / correlated agreement **FAIL** at δ=1−ρ−Θ(1/log n)
over order-n subgroups: explicit line L={X^{rm}+λX^{(r−1)m} : λ∈H^{(+r)}}, |H^{(+r)}|≥(n/2r)^r distinct
subset-sums lifted by a quantitative Linnik theorem ⟹ ≥n^C close points ⟹ polynomial **lower** bound
B(δ)≫ε*q ⟹ **δ* < 1−ρ.** Same open-core object (W_r / divisible signed sums of roots of unity); supplies
**no matching upper bound.** Reinforces the wall; does not breach it. (IACR 403'd the 2026/782 PDF this
session — read the roots-of-unity-lemma constants from the PDF before any load-bearing use.)

---

## 3. This session's exact-arithmetic probes (independent corroboration)

Files: `scripts/probes/probe_charp_energy_{supwall,thin,largeR}.py`, `probe_charp_nonDC_supnorm.py`,
`probe_supnorm_exponent.py`.

- **DC-escape is mandatory (corrects a naive reading).** With the a=0 DC term included, the bound
  `E_r ≤ (2r−1)!!·n^r` looks slack only because probes sat in the r>n regime. At true prize scale
  (r≈ln q ≪ n=2^μ) the DC term alone beats the Gaussian bound by `e^{500–1000}` (analytic, verified
  μ=20,r=55→503; μ=24,r=89→1041). The genuine prize quantity is the **DC-excluded sup-norm**
  M(R)=max_{a≠0}|S(a)|.
- **Non-DC Gaussian energy bound is FALSE in worst case.** Exact: at n=64 the non-DC moment ratio
  E_r^{(≠0)}/((2r−1)!!·n^r) = 1.15 (r=6), 1.82 (r=8) > 1; independently re-verified by a workflow agent
  at exact prime p=13640513. The 2-power (smoothest) case maximizes the excess.
- **Worst-case thin-regime sup-norm exponent (the crux).** Over p~n^4, worst M(R) for n=16..96:
  M/√n ∈ [3.5, 5.4] (M at 55–87% of trivial n); naive LS fit κ≈0.67, local logM/logn decreasing
  0.95→0.87. **Computation alone cannot decide κ=½ (polylog/BGK, bound TRUE) vs κ>½ (power, bound
  FALSE)** at accessible n — this ambiguity is itself why it is the wall. Literature resolves the
  *provable* side: SOTA n^{0.989}, target n^{0.5}, gap 0.489 uncrossed.

---

## 4. Invented mechanisms (0/6 survivors; cumulative campaign 0/108+)

Ranks [proximity, feasibility, novelty, insight], 1–10.

| Mechanism | Ranks | Verdict | Why it fails |
|---|---|---|---|
| 2-power cyclotomic Gauss–Jacobi eval of E_r | [5,6,8,3] | **refuted** | Gaussian bound false in worst case (exact p=13640513,n=64); provable part = ordinary energy = BGK; 2-power = extreme smooth case *maximizes* excess |
| Stepanov w/ exact prize constants | [2,3,9,9] | reduces-to-open | μ_n separable ⟹ no Frobenius multiplicity window at β>2; HBK/Konyagin/Weil members all worse than trivial n (+36 bits over √n at real p) |
| Fixed-deployed-field genericity | [3,5,7,2] | reduces-to-open | quantifier premise correct (vindicates audit), but mcaPrize is a growing family p≈n^{1+o(1)}·2^128; char-p rigidity false at prize depth (threshold (2r)^{n/2}=n^4 at r=4–6 ≪ r≈110) |
| Multi-round FRI loss-telescoping | [3,5,8,7] | reduces-to-open | commit-phase loss telescopes (Σ‖D_i‖=2N−2) but factor-2 is per-query; #eroding λ = B(δ) = BGK incidence; query penalty 2.41–4.38× |
| Frobenius/Galois (Burnside) descent on E_r | [2,3,1,1] | reduces-to-open | char-p vacuous (p≡1 mod n ⟹ Frob=id); char-0 AGL order n²/2 divides count by only n^{O(1)}, inert vs r-exponential W_r |
| Haemers inertia / Lovász θ on Cay(F_p,μ_n) | [6,5,1,1] | reduces-to-open | θ = Hoffman ratio exactly (vertex-transitive); all bounds give a Θ(q) density blind to the o(1) exponent; Hoffman value strictly increasing in M ⟹ no inversion to an M upper bound (Haemers genuinely sharper on α but cannot transfer to M) |

---

## 5. Honest bottom line

δ* is **NOT pinned**. Genuinely proven (axiom-clean): the sufficiency reduction δ*(floor)⟹Q (L0–L6),
char-0 closure E_r(ℂ)≤(2r−1)!!·n^r, and the unconditional ceiling δ*≤(1−ρ)−Θ(1/log n) (now corroborated
by 2026 failure-side literature). **Irreducible open core:** `sup_p W_r ≤ slack_r at r≈ln q`, equivalently
the √q-cancellation Paley eigenvalue bound (BCHKS 1.12), equivalently M(n)≤C√(n·log(p/n)) — the BGK /
Paley short-character-sum wall for thin 2-power subgroups at the Burgess barrier (β≈4). SOTA n^{0.989},
in-regime n^{0.9583}; target n^{0.5}; **the full half-power gap is uncrossed.**

The attack moved nothing in the core but sharpened that it is **hard-open, not impossible**: negative-arm
N1–N8 all NO-GAIN/REFUTED (no impossibility obstruction; Parseval forces only M≥√n; value well-defined &
computable); the moment/energy method is dead **as a route** (faithfulness window r*≈ln q/ln n ≈ 5.3 at
n=2^30, but the bound needs r≈110) though not dead as a *value* (DC-escape separation); the structural
barrier is sharp (at r=89,n=2^30 the W_r slack is ~960 decimal digits / 3189 bits vs symmetry cap 907
bits — a 2282-bit gap ⟹ a congruence/parity pin can never bound the *size*). Two non-BCHKS levers remain
genuinely unsettled but lean wall: A6 determinantal/Plücker-minor (Lang–Weil expected vacuous, V_r is
0-dimensional) and A3 dedup-strictness at log depth (slack (log n)²/2n→0).

**No fabricated closure.** The prize δ* is not pinned; the irreducible core is the BGK/Paley sup-norm
wall, and this attack did not move it.

## Reading list (downloadable)
NT core: 1712.00410 (MRSS, E_2 record 49/20), 2003.06165 (di Benedetto, sup-norm n^{0.989}),
HBK 2000 (ora.ox.ac.uk uuid:bd933322), 0705.4573 (Kurlberg expo of BGK), 2401.04756 (no β improvement
through 2024), 2504.10202 (Hanson–Petridis 2025, unbeaten).
FRI/PG: eprint 2026/782 + arXiv 2604.09724 (failure near capacity — NEW on-regime), 2026/858
(threshold halving), 2026/861 (action-orbit), 2025/2054 (Goyal–Guruswami, random/folded RS only),
2025/2110 (Haböck MCA note), 2025/2197 (Fenzi–Sanso small-field caution), 2026/680 (ABF prize statement).
