export const meta = {
  name: 'all-open-angles',
  description: 'Attack ALL genuinely-open #444 angles: (A) under-det/agreement-sharing lift (does δ* enter the window or is it asymptotically empty), (B) orbit-count #orbits bound in |B|=(#orbits)·|G| (newest live structure), (C) ε*-slack extension past n=64, (D) window-empty meta-question, (E) Salié/2-power-order special structure. Each developed + adversarially checked.',
  phases: [ { title: 'Attack' }, { title: 'Adversary' }, { title: 'Synthesis' } ],
}
const REPO='/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'
const PG=REPO+'/ArkLib/Data/CodingTheory/ProximityGap'
const CTX=`
STATE (#444 prize δ*, explicit μ_n RS, n=2^μ thin n≤p^{1/4}, window (1−√ρ, 1−ρ−Θ(1/log n))). JUST ESTABLISHED:
the GROWTH LAW is resolved — the over-det MONOMIAL far-line incidence has a SAT-then-cliff staircase, cliff at
s_top≈n/2 (DFT-uncertainty: (k+2)-sparse fn can't vanish on >~n/2 pts), s* hugs the cliff ⟹ m*=s*−k~n/4 ⟹ over-det
monomial δ* → JOHNSON (lalalune right, 0xSolace's →capacity refuted; growth-law compute now EXHAUSTED per c.4710769390).
CONSEQUENCE: far-line δ* is a PROVEN upper bound on true MCA δ* (epsMCA_ge_far_incidence), true δ*≥Johnson; so IF
monomials govern + m*~n/4 then the over-det/combinatorial face is SQUEEZED to Johnson. The window-interior (if nonempty)
must therefore come from the UNDER-DETERMINED (s=k+1, p-DEPENDENT) / agreement-SHARING (¬pairJointAgreesOn) / BGK
contribution that the monomial proxy misses. THIS IS THE OPEN END.

WALLS (don't reduce here): BGK thin-subgroup sup-norm = effective Gauss/Jacobi equidist at fixed q (= Bourgain
incomplete-subgroup char sum, ⊇ Vinogradov least-QR, no √-cancellation for |H|≤p^{1/4}); deep-moment E_r at r≈log m;
the conservation law (√log m extreme-value is a 4th+-moment property). NON-√ ε*-slack pin works to n=64 (δ*=59/64
axiom-clean) but dies n≥128 (resultant √-envelope (n/4)(log₂2n+1) > 128). Fiber-product cohomology tautological
(T={(t−1)^n=1} 0-dim étale ⟹ no Deligne H_c). 79-conjecture loop: 0 survivors. 9 alien fields: all reduced.

NEWEST LIVE STRUCTURE (c.4710745854/4710790143/4710826866): the over-det incidence factors via a FREE MulAction:
|B| = (#orbits)·|G| (OrbitCountCrossingLaw), with fixed-point split I = z + S·O (z=[α=0∈B]∈{0,1}, S=orbit size
n/gcd(a−b,n), O=#orbits). The open part is bounding #orbits.

TOOLS (cd ${REPO}): rust engine scripts/rust-pg, probes, in-tree FarCosetExplosion/MCAWitnessSpread/OrbitCount*.lean,
the under-det incidence I(k+1)~Θ(C(n,k+1)). HONESTY: reproducible probe or rigorous argument; if an angle reduces to
the wall, say so with the mechanism; distinguish measured-small-n from proven; final message = structured data.
`
const F={type:'object',required:['angle','headline','result','evidence','honest_gap'],properties:{
 angle:{type:'string'}, headline:{type:'string'},
 result:{type:'string',enum:['window-lift-found','window-empty-confirmed','partial-advance','reduces-to-wall','refuted','inconclusive']},
 evidence:{type:'string'}, deltastar_verdict:{type:'string',description:'does this angle put δ* in the window, at Johnson, or reduce?'}, honest_gap:{type:'string'}, next_step:{type:'string'} }}

phase('Attack')
const angles=[
 {k:'A-underdet-sharing-lift', p:`${CTX}\n\nANGLE A (THE open end): does the UNDER-DETERMINED (s=k+1) + agreement-SHARING (¬pairJointAgreesOn) contribution LIFT true δ* strictly into the window, or does the true δ* ALSO collapse to Johnson (window asymptotically empty)? The over-det monomial face → Johnson (established). The under-det regime has I(k+1)~Θ(C(n,k+1))≫budget (doesn't bind for the monomial far-line). But the TRUE MCA event requires ¬pairJointAgreesOn (no pair of codewords jointly explains the witness) — this is NOT the monomial far-line. Compute the TRUE MCA δ* directly (the in-tree mcaDeltaStar via mcaEvent, not the far-line proxy) at n=12,16,20 (small, exact) and compare to Johnson: is true δ* STRICTLY above Johnson (window-lift) and does the gap (δ*−Johnson)·n grow or →const? If true δ*=Johnson+O(1/n)→Johnson, window empty; if the gap grows, lift found. This is the decisive measurement. Use the in-tree exact mcaDeltaStar computation.`},
 {k:'B-orbitcount-bound', p:`${CTX}\n\nANGLE B (newest live structure): bound #orbits in the crossing law |B|=(#orbits)·|G| / I=z+S·O. The over-det incidence factors via a free MulAction; the binding is governed by #orbits (O). Compute #orbits as a function of (n,k,direction) at the binding radius; is #orbits BOUNDED/poly (→ I≤budget → window δ*) or does it grow (→reduces)? Is the #orbits bound a NEW p-independent combinatorial object, or does it reduce to the same cliff/saturation (= the growth law = Johnson)? Specifically: does bounding #orbits give anything BEYOND the m*~n/4 growth-law result, or is it the same content re-expressed? Test n=16,24,32 via the orbit decomposition. Report whether #orbits is a genuinely new lever or reduces.`},
 {k:'C-epsslack-extend', p:`${CTX}\n\nANGLE C: extend the ε*-slack unconditional pin past n=64. The pin works because |N(collision resultant)|² ≤ landauSqEnvelope(n/2)=2^255 < q²=2^256 at n=64, but the envelope (4h)^h·2^{h-1} (h=n/2) grows superpolynomially, dying at n=128 (√-bits 287.5>128). Can a TIGHTER resultant bound rescue it? Options: (a) a sharper-than-Landau/AM-GM bound on |N| exploiting the SPECIFIC structure (the resultant is of a sparse difference P−Q vs Φ_s — is the generic Landau bound loose by a factor that, when removed, pushes the threshold to n=128, 256?); (b) a DIFFERENT resultant presentation with smaller height (e.g. factor out common structure); (c) does the resultant FACTOR so that only a small cofactor needs to beat q? Compute the ACTUAL |N| (not the envelope bound) at n=128 for the worst collision and compare to q²: is the true |N| actually below q² (envelope just loose) or genuinely above? This decides whether the non-√ pin can reach larger n.`},
 {k:'D-window-empty-meta', p:`${CTX}\n\nANGLE D (meta): is the prize window-interior ASYMPTOTICALLY EMPTY (true δ*→Johnson)? If the over-det face→Johnson AND the under-det/sharing contribution also →Johnson (angle A), then the window-interior conjecture (δ* strictly in (1−√ρ,1−ρ−Θ(1/log n))) would be asymptotically VACUOUS — the prize answer would be δ*=Johnson (the known unconditional bound). Examine the ABF26 conjecture statement: does it claim δ* STRICTLY interior, or δ*≥ some interior value? If the campaign's own data (true mcaDeltaStar at small n, the dilation-orbit list-size which a concurrent team measured GROWS ~n²) points to δ*→Johnson, that's a REFUTATION-flavored result (the window is empty, prize=Johnson), which is itself a valuable resolution. Adjudicate: is there ANY evidence true δ* stays STRICTLY interior as n→∞, or does everything point to →Johnson? Be careful and honest — this could reframe the whole prize.`},
 {k:'E-salie-2power', p:`${CTX}\n\nANGLE E: the Salié-sum / 2-power-order-character special structure. 2-power-order multiplicative characters generalize the quadratic character; quadratic-character incomplete sums = SALIÉ sums, which have EXPLICIT evaluation (√q with an explicit phase, NOT just a bound). Does the 2-power-order character χ (order m, but the RELEVANT twists χ^k of order dividing 2-power) make S(k)=Σ_{x∈μ_n}χ^k(x+1) admit a Salié-type EXPLICIT evaluation or a genuine √-cancellation that general-order characters lack? Salié works because the quadratic Gauss sum is explicit; does the 2-power tower of Gauss sums (Hasse-Davenport-related) give an explicit evaluation of S(k) for k a power of 2? Test: compute S(k) for k=2^j (2-power shifts) at n=16,32 — is there an explicit closed form / extra cancellation vs generic k? If 2-power k gives √n exactly, that's a partial prize (the 2-power-shift autocorrelations). Report.`},
]
const res=(await parallel(angles.map(a=>()=>agent(a.p,{label:`atk:${a.k}`,phase:'Attack',schema:F,model:'opus'}))) ).filter(Boolean)
log(`Attack: ${res.length}/${angles.length}; window-lift=${res.filter(r=>r.result==='window-lift-found').length} empty=${res.filter(r=>r.result==='window-empty-confirmed').length}`)

phase('Adversary')
const sum=res.map(r=>`[${r.angle}] ${r.headline} → ${r.result} | δ*: ${r.deltastar_verdict} | ${(r.evidence||'').slice(0,250)} | gap:${r.honest_gap}`).join('\n\n')
const V={type:'object',required:['claim','holds','why'],properties:{claim:{type:'string'},holds:{type:'boolean'},why:{type:'string'},correction:{type:'string'}}}
const adv=(await parallel(res.slice(0,5).map(r=>()=>agent(
 `${CTX}\n\nALL FINDINGS:\n${sum}\n\nADVERSARIALLY VERIFY: "${r.angle}: ${r.result} — ${r.headline}". Be a skeptic: if it claims a window-lift / partial advance / window-empty, check it rigorously (re-run probe at a different n/p; check it's not scale-confounded; check it doesn't reduce to the wall or to the already-established growth-law/Johnson result). For window-empty: is δ*→Johnson genuinely supported or is it small-n artifact (the campaign repeatedly found Johnson-vs-floor indistinguishable below n≈256)? Default to 'reduces/inconclusive' unless decisive. Corrected verdict.`,
 {label:`adv:${(r.angle||'x').slice(0,14)}`,phase:'Adversary',schema:V,model:'opus'}))) ).filter(Boolean)
log(`Adversary: ${adv.length}`)

phase('Synthesis')
const vs=adv.map(v=>`- "${v.claim}": holds=${v.holds} — ${v.why}${v.correction?' | CORR: '+v.correction:''}`).join('\n')
const synth=await agent(`${CTX}\n\nFINDINGS:\n${sum}\n\nVERDICTS:\n${vs}\n\nSYNTHESIZE (markdown for #444): for each open angle (A under-det/sharing lift, B orbit-count, C ε*-slack extension, D window-empty meta, E Salié/2-power): the honest verdict — does it put δ* in the window, confirm window-empty (δ*→Johnson), partially advance, or reduce? THE KEY QUESTION: after the growth-law resolution (over-det face→Johnson), is the prize window-interior asymptotically NONEMPTY (some contribution lifts δ* in) or EMPTY (δ*→Johnson, prize=Johnson)? Report any genuine partial advance (a window-lift at small n, a new bound, a 2-power exploit). Be ruthlessly honest. End with the single most promising remaining direction + concrete next step.`,{label:'synthesis',phase:'Synthesis',model:'opus'})
return {synth, findings:res, verds:adv}
