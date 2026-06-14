# Q1 char-p crux: the inequality deg H + m ≥ k−1 SHARPENED + localized to NOVEL-A (2026-06-14, wakesync)

Engaged the swarm's "single best forward bet" (unlock-workflow-synthesis): the char-uniform Q1 crux
= the inequality **deg H + m ≥ k−1** (for H≠0), exhaustively verified k=2,4,8. Independent re-derivation
sharpens it and pins exactly what the char-p version needs.

## Setup
S a 2k-subset of μ_{4k}; σ_S(z)=∏_{s∈S}(z−s)=G(z²)+zH(z²) (deg_w G=k); m=#antipodal pairs {s,−s}⊆S
= deg gcd(G,H). The odd coeffs of σ_S are ±e_1,±e_3,… (elementary symmetric); top odd coeff (w^{k−1})
= ±e_1(S). So **deg H = k−1 ⟺ e_1(S) = Σ_{s∈S} s ≠ 0.**

## SHARPENING (char 0, dyadic 4k=2^μ) — verified probe_degH_exact_mechanism.py, N=8,16
- **Claim A:** e_1(S)=0 ⟺ S=−S (antipodal-symmetric). [= dyadic Lam–Leung: a vanishing sum of distinct
  2^μ-th roots is a disjoint union of negation pairs ⟹ S=−S.] 0 violations N=8,16.
- **Claim B:** H≠0 (S≠−S) ⟹ **deg H = k−1 EXACTLY.** 0 violations N=8,16.
⟹ deg H + m = (k−1)+m ≥ k−1, with deg H = k−1 the exact value. STRICTLY SHARPER than the swarm's
"deg H + m ≥ k−1 ⟹ (via m≤deg H) deg H ≥ k/2": the +m / m≤deg H machinery is UNNECESSARY — the bound
is purely about e_1, and the higher odd sums e_3,e_5,… are irrelevant to it.
- **DYADIC NECESSITY (verified):** non-dyadic N=12 (k=3), 24 (k=6) FAIL both claims, with
  #(ClaimA viol) = #(ClaimB viol) EXACTLY (4=4, 496=496) — proving the two are the SAME phenomenon, and
  that the failures are exactly the e_1≡0-without-S=−S spurious sums (cube/other roots break Lam–Leung).

## What the CHAR-P crux actually is (the localization)
char-0: deg H = k−1 for all H≠0 dyadic ⟹ NO antipodal-free bad config exists in char 0 (the inequality
holds, with room m). A char-p bad config (the thing that would lower δ*) needs deg_p H ≤ k/2−1 with m=0,
i.e. the odd power sums **e_1 ≡ e_3 ≡ … ≡ e_{~k/2} ≡ 0 mod p SIMULTANEOUSLY for an antipodal-free S.**
This is EXACTLY the swarm's **NOVEL-A simultaneous-rigidity** object. My char-0 result shows it has zero
char-0 solutions; the whole crux = whether this simultaneous system stays field-independent at prize scale.
[NOVEL-C showed a SINGLE size-4 vanishing gets dirty at n≳2.4 log₂p; the SIMULTANEOUS system is the open
question — if rigid at scale ⟹ inequality holds char-p ⟹ Q1 closed char-uniformly ⟹ removes field-dep.]

## Net
SHARPENED the inequality to the exact deg H = k−1 (via e_1 + dyadic Lam–Leung), proved the +m machinery
unnecessary, established dyadic-necessity computationally (matched violation counts), and pinned the char-p
crux to NOVEL-A's simultaneous odd-system rigidity. NOT a closure (the simultaneous-rigidity-at-scale is
open, same family as the BGK/Paley wall) — but a clean unification of Q1 ↔ NOVEL-A and a sharper char-0
statement for whoever proves the simultaneous version. Probes: probe_degH_m_inequality.py, probe_degH_exact_mechanism.py.
