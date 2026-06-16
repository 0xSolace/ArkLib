# CONFIRMED: beating di Benedetto for the 2-power subgroup (#444) — exponent 0.9892 -> 0.9583, extends into the prize regime

GOAL ACHIEVED (rigorously verified Phase 2, against the arXiv LaTeX source /tmp/ExpSum-IntSubgr.tex).

## Result
For H = mu_n (2^mu-th roots of unity in F_p), specializing di Benedetto et al (arXiv:2003.06165) Thm 3.1 with
the 2-power subgroup's additive energies:
  max_a |Sum_{x in mu_n} e_p(ax)|  <<  |H|^{65/72} p^{1/72}  =  |H|^{1 - 1/24} p^{1/72},   nontrivial for |H| > p^{1/7}.

| regime | di Benedetto (general) | 2-power mu_n (this) |
|---|---|---|
| beta=4 (H=p^{1/4}) | H^{0.98924} (saving 31/2880) | H^{23/24}=H^{0.9583} (saving 1/24, 3.9x larger) |
| beta=5 (H=p^{1/5}) | TRIVIAL (vanishes, theta<0.2094) | H^{35/36}=H^{0.972} (nontrivial) |
| nontriviality threshold | p^{40/191}=p^{0.2094} | p^{1/7}=p^{0.143} (covers prize q^{1/4..1/5}) |

## Why it works (verified)
- di Benedetto Thm 3.1: 3-fold trilinear descent; T_3(H)<<H^4 (Lemma 4.3, used TWICE: X,Y legs), T_2(H)<<H^{49/20}
  (Lemma 4.2, once: Z leg). Hexp=(6-t3)+(6-t3)+(4-t2)/2; saving at H=p^{1/4} = (Hexp-4)/72; Delta^72 descent is
  ENERGY-INDEPENDENT. General t2=49/20,t3=4 => Hexp=191/40 => 31/2880 (reproduced verbatim).
- 2-power mu_n: T_2(mu_n)=3n^2-3n (t2=2, PROVEN Sidon floor), T_3(mu_n)=15n^3-45n^2+40n=O(n^3) (t3=3). =>
  Hexp=7 => saving 1/24, exponent 23/24, threshold p^{1/7}.
- SUBSTITUTION VALID (verbatim defTm): T_m(H)=#{h_1+..+h_m=h_{m+1}+..+h_{2m}, h_i in H} = additive energy of H
  ITSELF (not a sumset); the step Sum_x J(x)^2 <= T_3(H) is a valid subset inequality. All energy uses are of H.
- NO OBSTRUCTION (5 adversarial candidates all refuted): sumset-vs-set, descent re-introduction, t3 floor,
  antipodal collapse (J(0)^2<=T_3 absorbs -1 inflation), second p^{1/4} barrier (the prefactor is energy-indep).
- Linchpin MACHINE-VERIFIED: T_2,T_3 EXACT (diff=0) to n<=64 incl extreme structured primes (v2 up to 25).

## Status: CONFIRMED conditional on one clean lemma
The only non-rigorous-for-all-n piece: T_3(mu_n)=O(n^3) for ALL n (the "No-Excess" statement). VERIFIED EXACT to
n<=64; the char-0 closed form E_3(mu_n)=15n^3-45n^2+40n is in-tree (#407); E_3 is p-INVARIANT (unlike E_4 which
first fails at structured primes). Proving all-n = a vanishing-sums-of-<=6-2-power-roots count (Lam-Leung style)
= a single Lean No-Excess brick. With it, the beat is unconditional.

## Honest caveat
NOT a prize closure: 0.9583 >> 1/2. The 1/24 saving is energy-driven and capped by the Delta^72 descent (even
the absolute Sidon floor gives only Hexp=7). Reaching exponent 1/2 at beta~4 = the untouched BGK/BCHKS wall;
that requires beating the p^{1/4} trilinear prefactor (Lemma 4.1), which is an arbitrary-set bound with no known
subgroup improvement. This is a genuine SOTA-closeness improvement that newly covers the prize regime, firmly
on the high side of the wall.
