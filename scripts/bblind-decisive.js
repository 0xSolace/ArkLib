export const meta = {
  name: 'bblind-decisive',
  description: 'Pull the decisive open thread (lalalune 4708838551): the 1-D far-line incidence is B-BLIND (=n exactly, sees only L²/Parseval, not the sup B=wall). Is the genuine ≥2-D MCA incidence (witness sets size (1-δ)n) ALSO L²-measurable ⟹ δ* COMPUTABLE, BGK irrelevant — OR does it re-couple to the sup B ⟹ wall stays? Plus the MGF-hub crux + sharp resultant bound.',
  phases: [ { title: 'Attack' }, { title: 'Verify' }, { title: 'Synthesis' } ],
}
const REPO='/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'
const PG=REPO+'/ArkLib/Data/CodingTheory/ProximityGap'
const CTX=`
THE DECISIVE NEW THREAD (#444 comment 4708838551, lalalune): the campaign assumed δ* reduces to the SUP
B=max_{b≠0}‖η_b‖ (the BGK/Paley wall). But the natural EXACT bridge is proven SUP-BLIND:
 - 1-D far-line incidence I(s₀,s₁)=Σ_{b:b·s₁=0} conj(η_b)ψ(b·s₀); for s₁≠0 the annihilator b·s₁=0 over a field
   forces b=0 ⟹ I = |G| = n EXACTLY, CONSTANT across all far directions, INDEPENDENT of every η_b
   (RealizerL2NotSup.lean, axiom-clean; probe: RS[μ16,k4] incidence 9,89 identical across primes where B differs
   13.788 vs 14.011). So the 1-D incidence sees only the L²/Parseval mass Σ‖η_b‖²=qn (COMPUTABLE, avg √n), NEVER B.
THE DECISIVE OPEN QUESTION: is the genuine ≥2-D MCA incidence — the bad-scalar count over WITNESS SETS S of size
(1−δ)n, the actual prize object epsMCA — ALSO L²/average-measurable (⟹ δ* pinned by a COMPUTABLE quantity ≈√n, the
BGK wall IRRELEVANT to δ*, prize computable not wall-bound — MAJOR reframing) OR does it RE-COUPLE to the sup B (⟹
wall stays, but via a new sup-sensitive higher-order object)?

CONTEXT: epsMCA ≥ far-line-incidence/q = n/q (proven lower bound, FarCosetExplosion.epsMCA_ge_far_incidence). The
≥2-D MCA event (¬pairJointAgreesOn, agreement on size-(1−δ)n SET) involves MULTIPLE constraints, so it is a
HIGHER-ORDER incidence. Higher moments E_r=Σ_b|η_b|^{2r}/q DO see the sup B (max term dominates at depth r≈log q).
SO THE LIKELY ANSWER: the 1-D incidence is L²/sup-blind (Parseval), but the ≥2-D / r-th order incidence re-couples to
B at depth r — that re-coupling IS the deep-moment wall. BUT this must be CHECKED: maybe the MCA witness-set structure
keeps it L²-measurable (computable) — that would be the major reframing. The whole prize hinges on which.

ALSO (0xSolace 4708629955): the prize is welded to ONE open inequality — the even-moment MGF MGF(y*)≤q·exp(n y*²/2)
at y*²=2log q/n ⟺ char-p Wick A_r=Σ_b|η_b|^{2r}/q ≤ (2r−1)‼·n^r at depth r≈log q (NearRamanujanFromSaddle.lean,
C₀²→2β/(β−1)≈1.6). This is the cleanest single-inequality form of the wall.

TOOLS (cd ${REPO}): in-tree RealizerL2NotSup.lean, IncidencePeriodBridge.lean, FarCosetExplosion.lean,
MCAWitnessSpread.lean, NearRamanujanFromSaddle.lean; rust engine; probes. HONESTY: reproducible probe or rigorous
argument; the question is decisive so be rigorous about which branch (L²-computable vs re-couples-to-B); final = structured.
`
const F={type:'object',required:['angle','headline','result','evidence','honest_gap'],properties:{
 angle:{type:'string'}, headline:{type:'string'},
 result:{type:'string',enum:['L2-computable-MAJOR','re-couples-to-B-wall','partial','reduces','inconclusive']},
 evidence:{type:'string'}, decisive_verdict:{type:'string',description:'is the ≥2-D MCA incidence L²-computable (δ* not wall-bound) or re-couples to B (wall)?'}, honest_gap:{type:'string'}, next_step:{type:'string'} }}

phase('Attack')
const angles=[
 {k:'2D-incidence-L2-vs-B', p:`${CTX}\n\nTHE DECISIVE QUESTION: is the ≥2-D MCA incidence L²-measurable (computable) or does it re-couple to the sup B? Compute the 2-D incidence (witness pairs/sets, the actual epsMCA at radius δ) DIRECTLY for RS[μ_n,k] at n=8,12,16 across primes where B DIFFERS (the test lalalune used: pick primes with different max‖η_b‖). For the 1-D far-line it was CONSTANT (sup-blind, =n). For the genuine ≥2-D MCA epsMCA: is it ALSO constant across primes-with-different-B (⟹ L²/computable, MAJOR — δ* not wall-bound), or does it VARY with B (⟹ re-couples, wall stays)? This is the decisive measurement. Use the in-tree exact epsMCA / mcaEvent computation, NOT the far-line proxy. Report whether epsMCA tracks B or is B-independent.`},
 {k:'r-th-order-recoupling', p:`${CTX}\n\nDERIVE which order of incidence re-couples to B. The 1-D (single annihilator constraint) = n, sup-blind (only Parseval/L²=E_1). The r-th order incidence (r simultaneous constraints / agreement on a size-related set) = the r-th moment E_r=Σ_b|η_b|^{2r}/q. The sup B enters when the MAX term dominates the moment, i.e. at depth r≈log q (B^{2r} ≈ Σ|η_b|^{2r} when r large). QUESTION: at what order r does the MCA incidence at the WINDOW radius δ sit? If the binding witness size (1−δ)n corresponds to LOW order (r=O(1)), the incidence is L²-ish (computable, sub-B); if it corresponds to depth r≈log q, it sees B (wall). Map the MCA radius δ to the moment order r it probes. Does the WINDOW (δ just above Johnson) probe low-order (computable) or deep-order (wall)? This determines the answer.`},
 {k:'mgf-hub-crux', p:`${CTX}\n\nAttack the MGF-hub crux (0xSolace 4708629955): the prize = the single inequality A_r=Σ_b|η_b|^{2r}/q ≤ (2r−1)‼·n^r (char-p Wick) at depth r≈log q. This is the cleanest wall form. Is there ANY angle on THIS inequality that the deep-moment attacks missed? (a) The MGF form MGF(y)=Σ_r q E_r y^{2r}/(2r)! ≤ q exp(ny²/2) — is the MGF more tractable than the per-r moments (e.g. via a differential inequality / Grönwall on MGF(y))? (b) The constant C₀²→2β/(β−1) is FINITE absolute — does that finiteness itself constrain A_r? (c) Is the char-p Wick provable for r up to some depth < log q, and does the WINDOW only need that depth (connecting to the r-th-order angle)? Report any crack in the MGF inequality, even partial (a depth-r bound for r<log q).`},
 {k:'sharp-resultant-extend', p:`${CTX}\n\nThe SHARP general-r cyclotomic resultant bound |Res|²≤(4r)^{φ(n)} (0xSolace). I established the ε*-slack pin is n≤64 (Landau envelope tight). Does this SHARP general-r bound change that? Compute: with |Res|²≤(4r)^{φ(n)}, the slack condition is (4r)^{φ(n)}<q². At the prize, φ(n)=n/2, q≈n·2^128. Does the sharp bound let the unconditional pin reach n=128 or beyond for some r, or is it still n≤64? Is the (4r)^{φ(n)} genuinely sharper than the Landau 2^{255}-type envelope, or the same? Recompute the n where the slack survives with the sharp bound. Report whether the sharp resultant extends the unconditional pin.`},
]
const res=(await parallel(angles.map(a=>()=>agent(a.p,{label:`atk:${a.k}`,phase:'Attack',schema:F,model:'opus'}))) ).filter(Boolean)
log(`Attack: ${res.length}/${angles.length}; L2-computable=${res.filter(r=>r.result==='L2-computable-MAJOR').length}`)

phase('Verify')
const sum=res.map(r=>`[${r.angle}] ${r.headline} → ${r.result} | verdict: ${r.decisive_verdict} | ${(r.evidence||'').slice(0,250)} | gap:${r.honest_gap}`).join('\n\n')
const V={type:'object',required:['claim','holds','why'],properties:{claim:{type:'string'},holds:{type:'boolean'},why:{type:'string'},correction:{type:'string'}}}
const verds=(await parallel(res.slice(0,4).map(r=>()=>agent(
 `${CTX}\n\nALL FINDINGS:\n${sum}\n\nADVERSARIALLY VERIFY: "${r.angle}: ${r.result} — ${r.headline}". The decisive claim is whether the ≥2-D MCA incidence is L²-computable (δ* not wall-bound, MAJOR) or re-couples to B (wall). If a finding claims L²-computable, SCRUTINIZE HARD (re-run the cross-primes-with-different-B test; check it's the GENUINE epsMCA not the far-line proxy; check the window radius really probes low-order). If it claims re-couples, verify the B-dependence is real. Default to 're-couples-to-B (wall)' unless the L²-computable evidence is decisive. Corrected verdict.`,
 {label:`v:${(r.angle||'x').slice(0,14)}`,phase:'Verify',schema:V,model:'opus'}))) ).filter(Boolean)
log(`Verify: ${verds.length}`)

phase('Synthesis')
const vs=verds.map(v=>`- "${v.claim}": holds=${v.holds} — ${v.why}${v.correction?' | CORR: '+v.correction:''}`).join('\n')
const synth=await agent(`${CTX}\n\nFINDINGS:\n${sum}\n\nVERDICTS:\n${vs}\n\nSYNTHESIZE (markdown for #444): THE decisive answer — is the genuine ≥2-D MCA incidence (the prize δ* object) L²/average-COMPUTABLE (⟹ δ* pinned by a computable ≈√n quantity, BGK wall IRRELEVANT, prize computable — a MAJOR reframing) or does it RE-COUPLE to the sup B (⟹ wall stays)? State at which moment-order the re-coupling happens and whether the window radius probes it. Plus: any crack in the MGF-hub inequality, and whether the sharp resultant bound extends the n≤64 pin. Be ruthlessly honest — if it re-couples (wall stays), say so cleanly; if there's genuine L²-computability (even partial / for a sub-window), that's a MAJOR result — verify and state precisely. End with the verdict on whether δ* is wall-bound or computable.`,{label:'synthesis',phase:'Synthesis',model:'opus'})
return {synth, findings:res, verds}
