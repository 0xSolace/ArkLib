# Comprehensive research: the Burgess crossing + Bourgain's full arsenal vs the prize wall (2026-06-15)

Deep arxiv research (13 facets across two workflows) on CROSSING THE BURGESS BARRIER at n=p^{1/4} for the
thin 2-power subgroup sum, and whether ANY Bourgain technique (incl. the just-resolved slicing conjecture,
arXiv:2501.06854) transfers. **Unanimous, structural verdict: NO crossing, NO transfer. Our wall IS the one
unfinished corner of Bourgain's own BGK program.**

## A. The Burgess crossing — every facet VANISHES at p^{1/4} (structural, not fixable)
- **Burgess method itself:** the 2r-th-moment shift-Hölder amplification has exponent infimum EXACTLY 1 at
  β=4 (best α=1.000006 at r=399; never <1). Provably vanishes — this is the DEFINING barrier, not an
  inefficiency. (β=2→0.875.)
- **Subgroup SOTA:** di Benedetto-Garaev et al. (arXiv:2003.06165) H^{1−31/2880}=H^{0.989} is an ENDPOINT
  bound requiring β<4 STRICTLY; at exactly β=4 it degrades to trivial. Nothing 2024-2026 approaches it.
- **Sum-product / energy:** DECISIVE — E_+(μ_n)=3n²−3n is at its absolute Sidon FLOOR (provably optimal,
  cannot be improved), yet it STILL does not cross. So the barrier is NOT energy-size; it is the
  energy→char-sum transfer exponent itself.
- **Stepanov / Weil low-genus curve:** reaches EXACTLY p^{1/4+ε} (Konyagin 2002) as a strict OPEN endpoint;
  AT p^{1/4} yields nothing. Weil √p=n²=p^{1/4} is exactly n-too-big because μ_n is 0-DIMENSIONAL — the
  structural origin of the barrier. (Ostafe-Shparlinski-Voloch arXiv:2211.07739.)
- **Kelley-Meka / PFR / additive-comb breakthroughs:** vanish at β=4 (μ_n additive density 2^{−90..−128} far
  below the 3AP ceiling; maximal-doubling subgroup is the wrong setting). In-tree Lean no-go already.
- **Paley Graph Conjecture directly:** Hanson-Petridis √(p/2), Yip — all live at β=2, give NOTHING at β=4;
  Kunisky-Yu (arXiv:2211.02713) prove a degree-4 SOS LOWER bound for the Paley clique (SOS can't even do it).
  PGC OPEN for density ≤1/2.
- **Effective monodromy (Katz/Deligne):** VACUOUS by hundreds-to-thousands of orders of magnitude
  (structural: r-fold convolution rank d_r~f^r/r! with f~p^{3/4} explodes). Sawin-Forey-Fresán-Kowalski
  arXiv:2101.00635 (quantitative sheaf theory) — the conductor blows up.

## B. Bourgain's arsenal — NO technique transfers (the profound answer)
- **Slicing / KLS / stochastic localization (arXiv:2501.06854, your paper):** "90% name/vibe coincidence,
  10% one reusable idea." The MACHINERY (Eldan stochastic localization, Guan's bound, M-ellipsoids,
  small-ball, Chen bootstrap) operates on CONTINUOUS log-concave measures on R^d — structurally
  inapplicable to a deterministic finite-field exponential-sum sup. NO transfer.
- **Decoupling / Vinogradov (Bourgain-Demeter-Guth):** NO — two fatal mismatches: (1) bounds an L^p NORM
  (average), not a pointwise MAX (the prize is the sup); (2) needs polynomial-curve CURVATURE, but ζ^j is a
  GEOMETRIC progression (no 2nd-derivative structure). Name-coincidence.
- **Restriction / Kakeya (Bourgain-Guth):** NO — curvature-extraction machines; our object is provably
  curvature-FREE (arithmetic, not geometric). Structural mismatch.
- **BGK / sum-product (Bourgain's OWN direct work):** ALREADY-THE-WALL — this is not a technique to import,
  it IS our problem. The prize M(n)≤C√(n log m) is precisely the UNATTAINED SHARP ENDPOINT of Bourgain's
  BGK program: the half-power saving (1/2) at density exponent α=1/4. The wall is literally named after this
  work. BGK gives savings β(γ)→0 as γ→1/4; closing the endpoint is the 25-year-open prize.

## C. The punchline (answer to "research Bourgain and all solutions")
Our wall is the ONE piece of Bourgain's own exponential-sum program he did NOT finish. Every Bourgain
triumph either IS this exact wall (BGK/sum-product — name-identity) or is domain-mismatched (slicing =
continuous geometry; decoupling/restriction = needs curvature the arithmetic object lacks; average not max).
The slicing-conjecture resolution does NOT transfer. Crossing Burgess at exactly p^{1/4} requires a
genuinely new sum-product / effective-equidistribution input that does not exist in any of Bourgain's (or
anyone's) solved problems. NO unconditional crack; the half-power gap at the Burgess barrier is the
irreducible open core.

## Reading list (download)
1. Ostafe-Shparlinski-Voloch, "Weil Sums over Small Subgroups," arXiv:2211.07739 (the curve/Stepanov endpoint).
2. di Benedetto-Garaev-García-González-Sánchez-Shparlinski-Trujillo, arXiv:2003.06165 (the SOTA H^{1−31/2880}).
3. Kunisky-Yu, "Degree-4 SOS lower bound for the Paley clique number," arXiv:2211.02713 (PGC obstruction).
4. Sawin-Forey-Fresán-Kowalski, "Quantitative sheaf theory," arXiv:2101.00635 (effective-equidist conductor).
5. Bourgain-Glibichuk-Konyagin (2006) + the "Exponential sums over small subgroups, revisited" arXiv:2401.04756 (the program + its endpoint).
(Also: GGMT PFR arXiv:2311.05762, Kelley-Meka arXiv:2302.05537 — confirmed non-applicable, in-tree Lean no-go.)
