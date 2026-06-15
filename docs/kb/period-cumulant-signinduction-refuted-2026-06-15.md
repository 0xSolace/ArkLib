# Cumulant sign-induction lead REFUTED; periods are asymptotically Gaussian (2026-06-15)

Pursued the direct-assault synth's #1 forward lead (κ₄<0 ⇒ κ₆<0 sign-induction ⟹ first unconditional deep-depth
advance). Computed standardized period cumulants κ_{2r}/n^r (prize-faithful: proper μ_n, p≡1 mod n, p≈n^4,
multi-prime, real periods since −1∈μ_n; /tmp/prize-research/cumulants.py):

| n  | κ₂/n  | κ₄/n²   | κ₆/n³   |
|----|-------|---------|---------|
| 16 | 1.000 | −0.190  | +0.141  |
| 32 | 1.000 | −0.0945 | +0.0211 |
(p-INDEPENDENT: identical across 6 primes at each n.)

FINDINGS:
- κ₄ = −3n EXACTLY (from the proven Sidon moment Σ|η_b|⁴=p(3n²−3n): κ₄/n²=−3/n; 16→−0.1875, 32→−0.094 ✓).
  Provable, no wall. So κ₄<0 (sub-Gaussian at order 4) is unconditional at β≥3.
- κ₆ > 0 (+0.141, +0.0211). ⟹ the sign-induction κ₄<0 ⇒ κ₆<0 is FALSE; cumulants ALTERNATE. The synth's
  "one honest inductive step into deep depth" is REFUTED at the first step. No clean cumulant-sign induction.
- BOTH standardized cumulants → 0 as n→∞ (κ₄/n²≈−3/n→0; κ₆/n³: 0.141→0.021→0). ⟹ the periods are
  ASYMPTOTICALLY GAUSSIAN (CLT), κ₄=−3n the leading sub-Gaussian correction. Max → √(2n log m) (Gumbel),
  bound TRUE (matches β=4 data M/√(2n log m)≈0.82-0.97). κ₆>0 is o(n³), dominated by κ₄<0 at the saddle
  t*~√(log m/n), so it does NOT break the bound — it only kills the naive induction.
- The p-independence of the standardized cumulants = the universal limiting distribution (the SU(n)-trace /
  Gauss-period measure from the arithmetic-dynamics angle), confirming the in-tree exchangeable-white-noise →
  Gaussian picture.

NET: the cumulant route gives NO clean inductive shortcut (κ₆>0). The bound is real (asymptotic Gaussianity);
the proof obstruction is making the CLT EFFECTIVE + UNIFORM at depth r≈log m for the single prize prime — the
deep-moment wall (BCHKS 1.12), not dodgeable by cumulant signs. Also: the direct-assault's δ_eff=1/2−2/r is
NOT a strict di-Benedetto improvement (almost-all-primes vs THE prize prime = different quantifier) — corrected.
