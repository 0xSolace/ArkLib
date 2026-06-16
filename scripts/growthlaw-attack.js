export const meta = {
  name: 'growthlaw-attack',
  description: 'Attack the δ* growth law from every angle: resolve the lalalune (m*~n/4 → Johnson) vs 0xSolace (c*/n→0 → capacity) CONFLICT (identical n≤32 data, opposite asymptotics) by deriving the over-det incidence DECAY RATE I(s) analytically (geometric→log→capacity vs arithmetic→n/4→Johnson), settle monomial-worst, and the window-empty consequence.',
  phases: [ { title: 'Decay' }, { title: 'Consequence' }, { title: 'Synthesis' } ],
}
const REPO='/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'
const CTX=`
THE GROWTH-LAW CONFLICT (#444): two careful brute-force analyses of m*=s*−k (s*=binding witness size = min{s: max-over-
far-directions over-det incidence I(s) ≤ budget=n}, ρ=1/4, k=n/4, char-0 p-independent) reach OPPOSITE asymptotics from
the SAME n≤32 data:
- lalalune (4708015568): fits m* = n/4+1−2(⌊log₂n⌋−3), GROWS ~n/4 ⟹ δ* = (1−ρ)−m*/n → 1−ρ−¼ = ½ = JOHNSON.
- 0xSolace (4707962768): same data (m*=3,4,3,4,5 @ n=8,12,16,20,32), reads c*=m* with c*/n→0 ⟹ δ* → CAPACITY.
Data: s* = 5,7,7,9,11,13,13 and m*=s*−k = 3,4,3,4,5,6,5 at n=8,12,16,20,24,28,32. STALLS at powers of 2 (s*: 7→7 at
n=16, 13→13 at n=32 = 2-adic signature). The decisive test (n=64: n/4-law⟹m*=11,s*=27; log-law⟹m*~6,s*~22) is
INFEASIBLE by brute force (C(64,27)~10^18) — THAT is why the conflict persists (scale-confounding: over n=8..32,
n/4∈[2,8] and log₂n∈[3,5] OVERLAP, so 7 points fit BOTH laws).

THE KEY ANALYTIC LEVER: m*=s*−k is determined by the DECAY RATE of the over-det incidence I(s) as s rises from k+2.
PROVEN: I(s=k+2) = edge ~ n³/32 (OverdetIncidenceMaxClosedForm, n·C(n/4,2)+1 for k=2; ~n^{k/2}-ish for k=n/4 — measured
89,457,1441 at n=16,24,32 for k=4-edge). Budget = n. So m*−2 = #(decrement steps) to bring I from ~n³ down to n:
  • GEOMETRIC decay I(s+1)≈c·I(s), c<1 const ⟹ m* ~ log(n²)/log(1/c) ~ LOG n ⟹ δ*→CAPACITY (0xSolace).
  • ARITHMETIC/SLOW decay (I drops by bounded AMOUNT, or plateaus near budget) ⟹ m* ~ n/4 ⟹ δ*→JOHNSON (lalalune).
EARLIER DECAY DATA (k=4 fixed, not k=n/4): n=24 I(s−k=2,3,4,5)=457,61,41,40 — FAST initial drop then NEARLY FLAT
(41→40, ×0.98) near budget ⟹ looks SLOW/arithmetic near the binding radius ⟹ supports lalalune. But that's k=4 not k=n/4.

CONSEQUENCE (why it matters): far-line δ* is an UPPER bound on true MCA δ* (epsMCA_ge_far_incidence, proven) AND
true δ* ≥ Johnson (list-decoding). So IF the over-det MONOMIAL far-line incidence governs AND monomials are the worst
direction (in-tree "monomial far-line IS the worst-case stack") AND m*~n/4 (lalalune): then true δ* squeezed Johnson ≤
true δ* ≤ far-line δ* → Johnson ⟹ true δ* → JOHNSON ⟹ the PRIZE WINDOW-INTERIOR is ASYMPTOTICALLY EMPTY (δ*=lower edge).
If 0xSolace (→capacity): window nonempty. So the growth law decides whether the window-interior conjecture is
asymptotically vacuous. (Caveat: the monomial far-line misses the agreement-SHARING ¬pairJointAgreesOn; the true MCA
incidence with sharing could differ.)

TOOLS (cd ${REPO}): rust engine scripts/rust-pg (curve mode = full I(s) decay; brute-force-limited to n≤32 at binding
radius); probes; in-tree OverdetIncidenceMaxClosedForm.lean, FarCosetExplosion.lean (epsMCA_ge_far_incidence), the
growth-law GPU data. HONESTY: reproducible probe or rigorous derivation; the asymptotic is scale-confounded — argue
the DECAY MECHANISM, not the n≤32 fit; final message = structured.
`
const F={type:'object',required:['angle','headline','result','evidence','honest_gap'],properties:{
 angle:{type:'string'}, headline:{type:'string'},
 result:{type:'string',enum:['decay-geometric-CAPACITY','decay-arithmetic-JOHNSON','decay-mixed','window-empty','window-nonempty','conflict-unresolvable-scaleconfound','reduces','inconclusive']},
 evidence:{type:'string'}, decay_law:{type:'string',description:'the derived/measured I(s) decay form + implied m* growth'}, honest_gap:{type:'string'}, next_step:{type:'string'} }}

phase('Decay')
const decay=[
 {k:'decay-curve-measure', p:`${CTX}\n\nMEASURE the over-det incidence I(s) FULL DECAY CURVE in the GROWTH-LAW setting (k=n/4, ρ=1/4), for n=16,24,32, via the rust engine curve mode (or a direct per-direction probe). For each n, tabulate I(s) for s=k+2, k+3, ..., up to the binding s* (where I≤n). Read off: is the decay near the budget GEOMETRIC (ratio I(s+1)/I(s) ≈ const <1 ⟹ m*~log n ⟹ capacity) or ARITHMETIC/PLATEAU (I drops by bounded amount / flattens ⟹ m*~n/4 ⟹ Johnson)? Fit both. The n=24 k=4 data (457,61,41,40, nearly flat near budget) suggests slow — confirm for k=n/4. This is the decisive measurement. Report the decay ratios + which law they support.`},
 {k:'decay-analytic-derive', p:`${CTX}\n\nDERIVE the over-det incidence I(s) decay law ANALYTICALLY. I(s) counts γ such that x^a+γx^b agrees with a deg<k poly on ≥s of the n points of μ_n. As s increases by 1, one more divided-difference condition is imposed. Each condition is (generically) codim-1, cutting the bad-γ count. Is the count reduction MULTIPLICATIVE (each condition kills a constant FRACTION ⟹ geometric ⟹ m*~log n) or does the count have a PLATEAU structure (the conditions become dependent / the antipodal-2-adic structure forces a slow polynomial decay ⟹ m*~n/4)? Use the proven edge I(k+2)~n³/32 and the antipodal/2-adic stall structure (lalalune's stalls at powers of 2). Derive I(s) for general s in the growth-law setting; settle the decay class. This SETTLES the conflict without needing n=64.`},
 {k:'monomial-worst-check', p:`${CTX}\n\nVERIFY/REFUTE that MONOMIAL directions (a,b) are the WORST far-line direction (give the largest incidence / smallest δ*) in the growth-law setting. The in-tree claim is "monomial far-line IS the worst-case stack." Check at n=16,24,32, k=n/4: compute the incidence for monomial vs non-monomial (e.g. binomial, trinomial) directions; is the monomial genuinely the max? This matters because the window-empty consequence requires monomials to govern. If non-monomials give LARGER incidence, the far-line δ* is even closer to/below Johnson; if monomials govern, the squeeze argument applies. Report whether monomials are worst.`},
 {k:'2adic-stall-mechanism', p:`${CTX}\n\nThe 2-ADIC STALL is the key structural feature: s* STALLS at powers of 2 (n=16: 7→7, n=32: 13→13). DERIVE why. At n=2^μ exactly, the worst direction / the incidence structure has extra symmetry (the full 2-power tower, the antipodal closure). Does the stall mean that AT THE PRIZE POINTS n=2^μ specifically, m* is RELATIVELY SMALL (s* stalled while k=n/4 grows) ⟹ δ*=(1−ρ)−m*/n is RELATIVELY LARGE (closer to capacity) at exact powers of 2? Compute m* ALONG the powers of 2 (n=8,16,32,64,128 via lalalune's law): m*=3,3,5,11,25. Does m*/n→1/4 (Johnson) along powers of 2 too, or does the stall keep m* sub-linear along the prize sequence specifically? This is the prize-relevant sub-question (the prize is at exact 2-powers).`},
]
const dr=(await parallel(decay.map(a=>()=>agent(a.p,{label:`d:${a.k}`,phase:'Decay',schema:F,model:'opus'}))) ).filter(Boolean)
log(`Decay: ${dr.length}/${decay.length}`)

phase('Consequence')
const dsum=dr.map(r=>`[${r.angle}] ${r.headline} → ${r.result} | decay: ${r.decay_law} | ${(r.evidence||'').slice(0,250)}`).join('\n\n')
const cons=(await parallel([
 {k:'window-empty-consequence', p:`${CTX}\n\nDECAY FINDINGS:\n${dsum}\n\nWork out the CONSEQUENCE rigorously. IF the decay analysis shows m*~n/4 (far-line monomial δ*→Johnson) AND monomials are worst: does it follow that the TRUE MCA δ*→Johnson (prize window asymptotically empty)? Carefully: far-line δ* is an UPPER bound on true δ* (epsMCA_ge_far_incidence), true δ*≥Johnson, so squeeze ⟹ true δ*→Johnson. BUT the monomial far-line MISSES the agreement-sharing (¬pairJointAgreesOn) — does the sharing requirement make the TRUE incidence SMALLER (so true δ* even closer to Johnson) or does the under-determined p-dependent (BGK) contribution add bad scalars that LIFT true δ* into the window? Resolve: is the window-interior conjecture asymptotically vacuous (δ*=Johnson) or is there a genuine under-det lift? This is the deepest consequence of the growth law.`},
 {k:'reconcile-both-comments', p:`${CTX}\n\nDECAY FINDINGS:\n${dsum}\n\nRECONCILE the two comments precisely. lalalune: m*~n/4→Johnson. 0xSolace: c*/n→0→capacity. They use IDENTICAL data. Is one MEASURABLY wrong, or is it genuine scale-confounding (both fit n≤32, undecidable asymptotically)? Check: 0xSolace's c*/n→0 REQUIRES c*=m* sub-linear; lalalune's n/4 makes c*/n→1/4. The data m*=3,4,3,4,5,6,5 — does it have slope (linear) or is it bounded-ish (log)? Compute the best-fit slope + the discriminating statistic. State definitively whether the conflict is RESOLVED (one wrong) or UNRESOLVABLE at feasible n (scale-confound), and if unresolvable, exactly what computation/derivation would settle it.`},
]).map(a=>()=>agent(a.p,{label:`c:${a.k}`,phase:'Consequence',schema:F,model:'opus'})) ).filter(Boolean)
log(`Consequence: ${cons.length}`)

phase('Synthesis')
const all=[...dr,...cons]
const allsum=all.map(r=>`[${r.angle}] ${r.result}: ${r.headline} | decay: ${r.decay_law||'-'} | gap: ${r.honest_gap}`).join('\n')
const synth=await agent(`${CTX}\n\nALL FINDINGS:\n${allsum}\n\nSYNTHESIZE (markdown for #444): (1) the over-det incidence DECAY law — geometric (→capacity, 0xSolace) or arithmetic/n/4 (→Johnson, lalalune) — and whether it's settled or scale-confounded. (2) The RECONCILIATION of the two comments (one wrong, or both scale-confounded). (3) Are monomials worst, and the 2-adic stall along the prize sequence. (4) The CONSEQUENCE: is the prize window-interior asymptotically empty (δ*→Johnson) or nonempty? Be ruthlessly honest about what's settled vs scale-confounded. End with the single computation/derivation that would definitively settle the growth law (and whether it's feasible).`,{label:'synthesis',phase:'Synthesis',model:'opus'})
return {synth, findings:all}
