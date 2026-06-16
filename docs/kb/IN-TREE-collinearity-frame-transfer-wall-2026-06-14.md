# IN-TREE collinearity frame (CollinearityMatchingFrame.lean) hits the SAME exponential transfer wall, 2026-06-14

## What the concurrent swarm already formalized (axiom-clean)
CollinearityMatchingFrame.lean (commit eeeb68420, #357) proves the EXACT mechanism this attack targets:
- **collinear_iff_balanced (char-0):** a pencil exponent-triple of Γ_n (three close codewords on a line)
  satisfies the collinearity determinant equation IFF the sign-normalized 12-exponent family is
  ANTIPODALLY BALANCED (every residue fiber t<2^{m-1} matched by its antipodal t+2^{m-1}). So
  collinearity ⟺ antipodal balance — a pure ℕ matching condition. Clean, char-0.
- **collinear_iff_balanced_modp:** the SAME equivalence over F_p, BUT ONLY for
  **p > (2^{m-1}·12)^{2^{m-1}} = (6n)^{n/2}** (the transfer/height threshold).

## The transfer threshold is EXPONENTIAL ⟹ fails at prize field for n ≥ 64
log₂((6n)^{n/2}) = (n/2)·log₂(6n): n=16→52.7, n=32→121.4 (both <128, OK), n=64→274.7, n=128→613,
n=256→1355, ... (all ≫128). The prize field q~n·2^128 has log₂q≈128+m. So the FORMALIZED per-triple
mod-p collinearity transfer holds ONLY up to n≈32 at prize scale; for the realistic prize n (2^20–2^30)
the threshold is astronomically beyond 2^128. ⟹ at large prize n we CANNOT conclude char-p collinearity
from char-0 antipodal balance via this frame. This is the SAME height/BCHKS-1.12 wall as every other face.

## Honest implication (tempers the line-decoding route, does NOT yet kill it)
- The PER-TRIPLE collinearity criterion is char-0-exact but transfers to char-p only above an exponential
  threshold (crude height bound) — failing in the prize regime, exactly like the divided-difference
  height-rigidity and cliff-confinement char-uniformity thresholds found this session.
- BUT this is a CRUDE SUFFICIENT bound (worst-case 12-term L¹ height). Cliff-confinement showed char-
  uniformity holds FAR BELOW the crude norm bound (the actual bad primes are sporadic/sparse). So the
  GLOBAL bad-count (# mutually non-collinear close codewords) could STILL be char-uniform / ≤ budget at
  prize scale even though the per-triple transfer bound fails. THAT is the genuine open crux (fleet
  wf_7777e3f1 computing it).
- If the global bad-count IS controlled at prize scale ⟹ line-decoding escapes the count wall ⟹ prize.
  If it tracks the per-triple transfer failure ⟹ collinearity collapses to the same wall (gg25-gap leg's
  claim), and δ*_MCA = Johnson (no beyond-Johnson).

## The Elias distinction (why collinearity is a priori different from count)
ABF26 Lemma 3.7 (Elias volume bound): list size |Λ(C,δ)| ≥ Vol_q(δ,n)/q^{n-k} — FLOORS THE COUNT near
capacity (large). Johnson is provably TIGHT for the count of general/linear codes (Gur02/GS03); beyond-
Johnson count only for subspace-design/random RS. So the count route CANNOT beat Johnson for explicit RS
(matches the whole session). Elias floors the COUNT but says NOTHING about COLLINEARITY — so the line-
decoding bad-count is the only object not a-priori floored at Johnson. This is the structural reason to
keep pushing the collinearity route despite the per-triple transfer wall.
