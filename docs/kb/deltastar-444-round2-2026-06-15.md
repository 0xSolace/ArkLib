# #444 ROUND 2 (2026-06-15) — over-det Johnson-lock (lead-closure) + nonlinear-lever wall + C21-C28

Comment lalalune/ArkLib#444 issuecomment-4707170752. Push 9629193c6. CORE OPEN, no closure.

## ★ LEAD-CLOSURE (verified): over-determined far-line is JOHNSON-LOCKED
Exact p-independent enumeration (proper μ_n, p~n⁴ incl non-Fermat, never n=q−1): c*=k−1 ⇒ s*=2k−1=n/2−1
⇒ δ*=½+1/n→½ (Johnson+o(1)), (δ*−½)·n=1.0000 flat n=16,20,24,28. So the off-BGK floor candidate CANNOT
come through a far-line construction — settles wf-D2/D5 regime-B §6 sub-question in the NO-CLIMB direction.
Mechanism: I(c)=z+(n/gcd)·O(c) (wf-D5), budget (n/gcd)·O≤n ⟺ O≤gcd; O(c)=RS list size collapses ≤2 at
Johnson radius (Johnson bound + Gur02/GS03 tightness). LANDED `_wf3D6_overdet_johnson_lock.lean` axiom-clean
[propext,Quot.sound] (budget-orbit arithmetic only; the O(c)-collapse is CITED list-decoding theory, NOT
Lean). HONEST SCOPE: exact n≤28 (+ crossdeep n=28); **n=32 PREDICTED not exact-verified** (C(32,9)~28M/dir
+ C(32,s) both time out); GPU "n=32 δ*=0.5938 deviation"=plausible search-ceiling artifact, HYPOTHESIS not
confirmed. Framing correction: binding dir frequently gcd=1 (single size-n orbit), not always gcd=2; Lean
lemma is the gcd=2 instance; asymptotic unchanged. REDUCE-TO-WALL (refutes the route, doesn't close prize).

## Nonlinear phase-aware levers (rule-5e) — ALL reduce to q·E_r moment wall
(A0) full triple-corr Σ_{a,b}η_aη_bη_{−a−b}=p²n PROVABLE TELESCOPE (=#{x=z,y=z}=n, zero subgroup structure,
ratio 1.00000000). (A1) signed cube Σ_{b≠0}η_b³=−n³ exact ⟸ zero-sum triples Z3(μ_n)=0 ∀n=8..256 β≥3 incl
non-Fermat; SOLE nonzero n=64 β=2.3 THICK ⟹ Z3 thick-only = OPPOSITE of thin-essential ⟹ signed cube
thin-vacuous. Level-set/poly-method SOS-from-power-sums=(pE_r/n)^{1/2r}=moment wall verbatim. Period-poly
root-bounds 2×-1e46× worse. Cumulants sub-Gaussian→Gaussian. UNIFIED: half-power gap lives ONLY in the
single-peak TAIL; bulk→Gaussian; only 3rd-order structural content Z3 vanishes in prize regime ⟹ NO finite-
order moment/cumulant (signed/abs, linear/nonlinear) sees the peak. Prize needs a TAIL-ONLY certificate not
factoring through finite moments.

## Conjecture round 3 C21-C28 — 0 close, all refuted/reduce
C21 metaplectic/Weil REFUTED (#distinct|η_b|²=#cosets+1, no μ-collapse); C22 Mahler/height REDUCE (M²/(n log m)
≈1.05-1.36=the prize); C23 automatic-2-adic-digits REFUTED (ballistic α≈0.97); C24 Sidon-except-neg→non-MDS
REDUCE (floor 0.75<1 but only enumerable n=8); C25 negative-dependence REFUTED (overshoot=1.0000 EVT spike
intact); C26 Cotlar block-orthogonality REFUTED (Gram 2.0-2.2, blocks REINFORCE); C27 p-adic kurtosis REDUCE
(κ≈2.8, 4th-moment blind to tail); **C28 cubic-doubling Re(η_b²·conj η_{2b}) — the sharp lesson**: genuinely
NON-telescoping (passes rule-5e) BUT recursion M(n)≤√2 M(n/2) violated 3/3 at β=4, AND argmax-b ≠ M's argmax-b.
⟹ NON-TELESCOPING IS NECESSARY BUT INSUFFICIENT: the open lever must ALSO pin its peak to M's peak. C28 proved
(a) avoid-q·E_r achievable, (b) peak-pinning is the obstruction.

CORE OPEN. Rule-5e lever sharpened: a nonlinear phase-aware aggregate that BOTH (a) avoids q·E_r AND (b) pins
peak to M's peak. [[arklib-444-canonical-dossier]]
