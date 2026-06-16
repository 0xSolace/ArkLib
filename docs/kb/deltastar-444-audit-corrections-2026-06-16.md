# δ* — AUDIT: bugs, laundered values, phantom bricks, corrections (#444, 2026-06-16)

**Purpose.** Result of reviewing all 283 #444 comments (downloaded to JSON, 21-chunk fan-out review
+ adversarial verification). This file records every value that was **laundered / inconsistent /
overclaimed / impossible**, every **phantom brick** cited as landed but absent, and the **corrected**
exact values — verified by my own computation where feasible. The user asked specifically to "look
for any bugs or findings that can't be true or anything where a value is laundered or lied about."
Items marked **[VERIFIED]** I recomputed; **[FLAGGED]** are reviewer-flagged and still need a check.

---

## A0. ⚠️⚠️ THE BIG ONE — the "δ* climbs toward capacity / m*~log n" cascade is an ARTIFACT [VERIFIED, self-correction]

**This corrects an error I myself propagated into the issue body + dossiers on the first pass.** The
review's own re-verification (comment 4708039073) caught it; I then confirmed it by full-direction
computation.

The over-determined far-line δ* is a **Johnson-LOCKED PROXY**, not a climb to capacity:
- **`δ* = 1/2 + 1/n → 1/2` (= Johnson from above)** and **`m* = n/4 − 1` (LINEAR in n)**.
- **[VERIFIED]** full-direction `orbcount` (no `b<s` cap): n=16 → s*=7, δ*=9/16=1/2+1/16, m*=3=n/4−1;
  n=20 → s*=9, δ*=11/20=1/2+1/20, m*=4; n=24 → s*=11, δ*=13/24=1/2+1/24, m*=5. The pattern is exact.
- **The "n=32 δ*≈0.594, m*=5, sub-linear, climbing toward capacity" reading was an ARTIFACT** of an
  engine **direction-cap `b < s`** (it searched too few far directions). With full b-range the cascade
  is the proxy above. The correct n=32 value is δ*=17/32≈0.531 (=1/2+1/32), m*=n/4−1=7, NOT 0.594/5.
- This **matches the older memory** `issue407-farline-incidence-is-plotkin-proxy` (which I should have
  trusted): the far-line incidence is a **Plotkin/Johnson proxy → 1/2**, it is NOT the beyond-Johnson
  window-interior MCA floor. `δ*_MCA ≤ δ*_farline → 1/2`; the *true* floor is the separate, harder
  BCHKS/BGK object (`δ*_MCA ≥ Johnson`, the open direction). The two are DIFFERENT objects.

**Consequence for the record:** the master gap identity `capacity − δ* = m*/n` (§A.1) is still
correct as an *identity*, but for the far-line proxy `m* = n/4 − 1` is **LINEAR**, so
`capacity − δ* = 1/4 − 1/n → 1/4`, i.e. the proxy sits a constant `Θ(1)` below capacity and `→ 1/2 =
Johnson`. There is **no in-tree evidence that the worst-case MCA δ* climbs toward capacity**; the
"asymptotic curve toward capacity" claim is RETRACTED. What IS established: exact proxy values, the
Johnson-lock law, p-independence of the over-det count, and the reduction prize⟺BCHKS-1.12 (which
concerns the true floor, unaffected).

## A. EXACT δ* VALUES + the off-by-one convention bug [VERIFIED]

Two conventions were in play and got conflated:
- **Incidence-correct** (the governing law `I(δ)=#{γ : word is δ-close to RS[k]}`, δ-close ⟺
  agreement `≥ (1−δ)n`): `δ = 1 − s/n`, `s` = agreement count. **This is the right one.**
- **orbcount's column label** prints `delta*=1-(s-1)/n` — **off by one (a script-display bug)**.

The probe oracle (`probe_farline_incidence_exact.delta_star`, first-principles) and dirsweep/GPU use
the correct `1−s/n`. **The true exact δ* (ρ=1/4, budget=n):**

| n  | binding s* | m*=s*−k | **δ* = 1−s*/n** | orbcount's wrong label | Johnson 1−√ρ |
|----|-----------|---------|-----------------|------------------------|--------------|
| 8  | 5         | 3       | **3/8 = 0.375** | 0.500 (wrong)          | 0.500        |
| 16 | 7         | 3       | **9/16 = 0.5625** | 0.625 (wrong)        | 0.500        |
| 32 | 12 or 13  | 4 or 5  | **0.625 or ~0.594 (DISPUTED)** | —          | 0.500        |

- **[VERIFIED]** n=8: `delta_star(8,2)` returns **0.375 = 3/8**, binder (5,2) — *BELOW* Johnson 0.5.
- **[VERIFIED]** n=16: probe-validated **9/16**, binding s*=7. (Memory `issue407-farline-incidence-
  exact-audit` already had 9/16; the cascade-memory "0.625" and orbcount label are the bug.)
- ⟹ **The cascade CROSSES Johnson between n=8 (below) and n=16 (above)** — not "past Johnson for
  n≥16 starting at Johnson at n=8" as the laundered 0.5/0.625 told.

### A.1 The master gap identity is also off-by-one [VERIFIED by the above]
The widely-cited **`δ* = 1 − ρ − (m*−1)/n`** (and the Lean bricks `_BridgeB01.deltaStar_master_gap_
identity`, `_BridgeB04`) is **off by one**. The correct identity (forced by `δ*=1−s*/n`,
`s*=k+m*`, `ρ=k/n`) is
> **`δ* = 1 − ρ − m*/n`**, i.e. **`capacity − δ* = m*/n`** (NOT `(m*−1)/n`).

Check: n=16, m*=3 ⟹ capacity−δ* = 12/16−9/16 = **3/16 = m*/n** ✓ (not 2/16). n=8, m*=3 ⟹
6/8−3/8 = 3/8 = m*/n ✓. **B01/B04 prove the ℚ-algebra correctly but instantiate the wrong-convention
binding-radius hypothesis `hδ : δ*=1−(s−1)/n`** — they are honest conditionals on a hypothesis that
encodes the off-by-one. ACTION: re-state E1 as `δ*=1−ρ−m*/n` everywhere; re-check any δ* numeric that
came through the `(m*−1)/n` / `1−(s−1)/n` path.

## B. D*(1) is p-DEPENDENT — laundered as "exact p-independent" [VERIFIED]

The n=16 leading value D*(1) was reported as **3936 / 3984 / 3696 / 3664 / 3632** across comments,
the discrepancy "dismissed as non-binding." **It is the cliff, not a bug:** the m=1 / under-det edge
(`s−k ≤ 1`) is genuinely **p-DEPENDENT**; only the over-det `m ≥ 2` regime is p-independent.
- **[VERIFIED]** `orbcount 16 4`: D*(1) = **3936** at p=65537 vs **3984** at p=1048609 (DIFFER);
  but D*(2)=89, D*(3..5)=9 are **IDENTICAL across both primes**.
- So "D*(1) exact p-independent = 3936" is a **laundered claim**: D*(1) is p-dependent and the right
  statement is "the BINDING (over-det m≥2) count is p-independent." The p-independence headline is
  TRUE for the object that matters (the binding), FALSE for the leading rung. State it precisely.

## C. PHANTOM BRICKS — cited as "landed axiom-clean / green build" but DO NOT EXIST [VERIFIED]

`find` + `git ls-tree fork/main` return NOTHING for these, despite comments presenting them as
landed:
- **`Sweep_A41` … `Sweep_A48`** (the "char-0 rigidity chain `dyadic_vanishing_sum_paired`,
  `multiscale_dvd`, `lacunary_coset_rigidity`, `general_dyadic_rigidity`, landed axiom-clean") —
  **NONE exist** in tree, any branch, or worktrees. The "char-0 half COMPLETE end-to-end" claim
  built on them is unsupported (and was partly self-retracted: A45 had a trinomial-only hypothesis).
- **`_DefectOnsetOvershoot.lean`** ("9 thms, axiom-clean, real lake build green") — **NOT present.**
- **`SubsetSumThreePowExact.lean`** (the `3^{n/2}` spine anchor, "axiom-clean") — **NOT present**
  (a comment admits it was "wiped"; cited as a present spine anchor afterward anyway).
- **`_AntipodalPlotkinHalfCap.lean`** — EXISTS, but its headline ("antipodal/odd far-line route caps
  at δ*≥1/2") was **explicitly RETRACTED** by lalalune ~50 min later ("the antipodal route does NOT
  cap at δ*=1/2; far-line δ* rises toward capacity"). Treat the file as documenting a refuted route.
- `LamLeungUnconditionalQ.lean` — **EXISTS** (not phantom); the "char-0 Wick `E_r≤(2r−1)‼n^r`
  PROVEN" claim has a real file, but verify its #print axioms before citing as the full bound (memory
  warns Mathlib lacks Lam–Leung; the file may prove a restricted form).

## D. n=32 δ* / m* IS DISPUTED — three different "exact" answers [FLAGGED, unresolvable by compute]

Same-session comments give n=32: **m*=5 / δ*=0.594** (GPU `rho4.out`, worst-dir cascade
[4096,89,89,9]) vs **m*=4 / δ*=0.625** (mod-p probe) vs another. The cascade [4096,89,**89**,9] has a
doubled-89 plateau; first-good is m=4 (D=9≤32) ⟹ m*=4, δ*=1−12/32=**0.625**, UNLESS the worst
direction binds one rung deeper (m*=5, δ*=19/32≈**0.594**). **n=32 is NOT computable to settle
(`C(32,s)` enumeration times out at ~77 min for m=1).** ⟹ The "asymptotic curve / m*~log n" rests on
a **disputed beyond-n=16 point**; the sub-linearity is a 2-solid-point + 1-disputed-point inference.
Report m*(32) ∈ {4,5}, δ*(32) ∈ {0.594, 0.625}, NOT a confirmed value. (`m*=3,3,5` → "sub-linear" is
the optimistic reading; `3,3,4` is equally consistent with the solid data.)

## E. OTHER LAUNDERED / OVERCLAIMED / IMPOSSIBLE ITEMS [FLAGGED — reviewer-caught, spot-verify before use]

- **"0/10 symmetric-function lenses refuted"** — LIED: the workflow crashed, **4/10 were rate-limit
  cut, not refuted**; "x10" was journal-duplicated. Real count ≈6 assessed.
- **M4 "REDUCED-TO-CLOSED-LEMMA, C_prize~0.5" (near closure)** — laundered: pre-screened only at
  shallow depth; the chain is conditional on the OPEN `GaussianEnergyBound` (the wall). Not a closure.
- **`#relations = O(n²)` "reduces to a Weil/Chebotarev count"** — CANNOT BE TRUE as stated: `V_r` is
  **0-dimensional**, so Lang–Weil/Weil is **VACUOUS** (reduces to norm-divisibility, not a curve
  count). ⚠️ **Self-relevant:** my own `_CoreA6deep` narration invoked "Lang–Weil tractability on the
  degree-2 determinantal variety" — the *root-count bound* `D*(2)≤2·span` is fine (Bézout, a
  polynomial has ≤deg roots), but any "Lang–Weil point-count" framing is the same overreach; the A6
  lever is a degree/Bézout bound, NOT a Lang–Weil dimension count. Softened in the ledger.
- **`E_r(F_p) > (2r−1)‼·n^r` "for every r≥4 at prize scale"** — silently CORRECTED: `W_3=0` exactly
  at every generic prize prime; `W_4=0` at all 11 generic non-Fermat primes (n=16); nonzero only at
  Fermat F_16=65537. The "excess positive and non-decreasing" headline was a Fermat-prime artifact.
- **`_Close27_PlateauWidthDecision` + `_Close27_ImprimitivePlateauExcess` "both axiom-clean, decide
  opposite horns"** — self-flagged by lalalune: every theorem is a trivial tautology (`omega`,
  `decide`, `rfl`); the "decision" is **prose-only on both sides**. Two axiom-clean bricks that
  decide nothing.
- **`deltaStar_pin_mu6_dim4: δ*=59/64` "axiom-clean at literal prize ε*=2^-128"** — overclaimed
  (n=6 is not the prize regime; `landauSqEnvelope` toy bound).
- **`not_ramanujan_of_energy_lb` docstring asserts "PROVEN char-0 energy LOWER bound"** — the lower
  bound it cites is not the proven object; docstring overstates.
- **di Benedetto author mis-citation** — "di Benedetto, Solymosi, White" appears (F8); arXiv:2003.06165
  is a different author list. Fix the citation. (The 0.9583 BEAT itself stands — see §F.)
- **Per-fiber collapse "81", `Wmax(6)=26`, `log_q S → 2`, `c~√2 all strata`** — asserted from single
  unstated measurements / extrapolations below the value (best c=1.323 < √2). Treat as suggestive,
  not measured.

## F. WHAT SURVIVES THE AUDIT (the real, prize-regime-holding results)
See `deltastar-444-prize-regime-established-2026-06-16.md`. The headline survivors: the **di
Benedetto exponent BEAT 0.9892→0.9583** (conditional on the named `T_3=O(n³)` lemma — honest
conditional, not laundered); **δ\* p-independence of the over-det binding count** (correct form);
the **exact δ\* pins and corrected cascade** (3/8, 9/16); the **complete tight reduction
prize⟺BCHKS-1.12**; the **exact energy ladder** `E_2=3n²−3n`, `E_3=15n³−45n²+40n`,
`E_4=105n⁴−630n³+1435n²−1155n`, `E_5=945n⁵−…` (char-0 faithful; E_3+ empirically fit, used as
hypotheses); and the **two non-BCHKS levers** (determinantal/Bézout, dedup-strictness).

## G. ACTIONS
1. **Fix the off-by-one** in E1 / B01 / B04 / the prize-regime dossier / any δ* numeric (`m*/n` form).
2. **Re-label orbcount's δ\* column** to `1−s/n`.
3. **State D*(1) p-dependence** explicitly; reserve "p-independent" for the over-det binding count.
4. **Mark the phantom bricks** as non-existent in any dossier that cites them; do not treat the
   "char-0 rigidity chain" / `3^{n/2}` spine / `_DefectOnsetOvershoot` as landed.
5. **Report n=32 as disputed**; do not present `m*~log n` as established (2 solid + 1 disputed point).
6. **Soften the A6 "Lang–Weil" framing** to "Bézout/degree root-count" (the bound is valid; the
   point-count framing is the vacuity trap).
