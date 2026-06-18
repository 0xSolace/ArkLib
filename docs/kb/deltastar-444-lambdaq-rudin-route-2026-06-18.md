# The Λ(q) / Rudin route — the prize is a Λ(p)-set inequality for μ_n (#444)

Attacking the phase-concentration open input via harmonic analysis. The period `η_b = Σ_{x∈μ_n} e_p(bx)`
is, as a function of the frequency `b ∈ F_p^*`, an **n-sparse trigonometric polynomial** (Fourier support
= the frequency set `μ_n`). The prize `M = ‖η‖_∞ ≤ C√(n·log m)` is, in this language, precisely a
**Λ(q) / Rudin inequality** for the frequency set `μ_n`:
> `‖η‖_{L^q(b)} ≤ C·√q·√n`  uniformly in `q`  ⟺  `μ_n` is a **Λ(q) set with bounded constant `C`**.

(Rudin's inequality: a SIDON set `S` satisfies `‖Σ_{s∈S} a_s e(sb)‖_q ≤ √q·‖a‖_2`. The sup-norm follows
by `‖η‖_∞ ≤ m^{1/q}·‖η‖_q`, optimized at `q = 2 log m`: `M ≤ √e·C·√n·√(2 log m) = C√(2e)·√(n log m)`.)

## Machine evidence (favorable — the constant is bounded AND decreasing)
The Λ(q) constant `‖η‖_q/(√q·√n)` (machine, `probe_rudin_lambdaq.py`):
| q | n=16 | n=32 |
|---|---|---|
| 2 | 0.707 | 0.704 |
| 4 | 0.647 | 0.646 |
| 8 | 0.601 | 0.611 |
| 16 | 0.548 | 0.571 |
**Bounded and DECREASING** (≤ 0.71) — so `μ_n` is empirically a Λ(q) set with a small uniform constant.
And `M/√(2n log m) = 0.77–0.85 < 1`. Strong evidence the prize (Λ(q)-boundedness) is TRUE.

## The status: μ_n is ALMOST Sidon (Sidon-except-negation)
`μ_n` is NOT additively Sidon (`E_2 = 3n²−3n > 2n²−n`; the excess `n²−2n` is the antipodal `x+(−x)=0`
structure), so Rudin's inequality does not apply verbatim. The prize is the Λ(q) bound for this
**almost-Sidon** set, whose constant is governed by the additive energy `E_r` (= the Wick/sub-Gaussian
structure). So the Λ(q) route IS the moment/energy route (`‖η‖_q^q ≤ Σ_b|η_b|^q ≤ m·(C√q√n)^q` ⟺
`E_r ≤ Wick`) — but stated in the **named, well-developed Λ(p)-set theory**.

## Why this matters (the external-math pointer)
This identifies the relevant EXTERNAL mathematics precisely: **Λ(p) sets for multiplicative subgroups**
(Rudin 1960; Bourgain's `Λ(p)` constructions; the Λ(p)-set problem for arithmetic sets). The question
"is a multiplicative subgroup `μ_n ⊂ F_p^*` a Λ(q) set with bounded constant for `q ≈ log m`?" is the
prize, and it is a recognized (hard) harmonic-analysis problem — the same BGK wall, but now with a named
home in the Λ(p)-set literature, where any genuine external breakthrough would live. NO fabricated closure;
the Λ(q)-boundedness is the open input, machine-favorable (constant ≤ 0.71, decreasing).

> Machine: `probe_rudin_lambdaq.py`. The Λ(q)→sup-norm optimization is the in-tree moment bridge
> (`_MomentSaddleValue`) in harmonic-analysis language.
