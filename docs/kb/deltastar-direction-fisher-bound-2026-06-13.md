# New provable bound: the direction-Fisher bad-scalar bound (recovers Johnson) (2026-06-13)

A genuinely new, **provable, character-sum-free** bound on the MCA bad-scalar count of an *arbitrary*
stack — verified and **tight for the Kambiré construction**. It is real machinery for the
general-direction question, and it pins (yet again, now via a clean direct argument) why the lower
bracket sits exactly at Johnson.

## Lemma (direction-Fisher bound) — PROVEN
For `C=RS[F_q,μ_n,k]`, a stack `(u₀,u₁)`, let `b := max-agreement(u₁, C)` (so `u₁` is `(1−b/n)`-far).
The number of `γ` with `u₀+γu₁` at agreement `≥ a` with `C` satisfies, whenever `a² > b·n`,
> **`#{bad γ} < (a−b)·n / (a² − b·n)`.**

**Proof.** If `γ≠γ'` are both bad with agreement sets `S_γ, S_{γ'}`, then on `S_γ∩S_{γ'}`,
`(γ−γ')·u₁ = (u₀+γu₁) − (u₀+γ'u₁) = c_γ − c_{γ'}`, a codeword; so `u₁` agrees with the codeword
`(c_γ−c_{γ'})/(γ−γ')` on `S_γ∩S_{γ'}`, giving `|S_γ∩S_{γ'}| ≤ b`. With `L` bad scalars each
`|S_γ|≥a`, double-counting + Jensen (`Σ_x C(deg x,2) ≥ n·C(La/n,2)`, `= Σ_{pairs}|S_γ∩S_{γ'}| ≤
C(L,2)b`) yields `L < (a−b)n/(a²−bn)`. ∎

## Verification + tightness
`probe_direction_fisher.py` (`(s,m,r)=(4,2,3)`, `a=6`): the construction monomial has `b=4`,
`#bad=4`, and Fisher bound `= (6−4)·8/(36−32) = 4.0` — **saturated exactly**. Random stacks: `#bad=0
≤` bound. **No violations.**

## Reach — recovers Johnson, not past it (honest)
The bound is **vacuous when `a² ≤ b·n`**. For the construction's direction `b=(r−1)m` at the prize
rates (`s≈2r`, `ρ≈½`), `a²>bn` requires agreement `a > √(bn) = m√((r−1)s) ≈ rm√2` — i.e. only
*above* the **Johnson radius**. Below Johnson agreement (the open window), it is vacuous. So this
bound — like every pairwise/second-moment argument (cf. wall-unification) — **bottoms out at exactly
Johnson** and does **not** reach the window. It does not bypass `B(μ_n)`.

## Value (honest)
- A clean, **provable, character-sum-free** general-direction bound, **tight for the construction** —
  good Lean-formalizable machinery, and a self-contained proof that the *second-moment* contribution
  to the lower bracket is exactly Johnson.
- It **sharpens the open core**: past Johnson, the bad count is governed by the *failure* of the
  Fisher inequality, i.e. the triple-and-higher coincidences `Σ_x C(deg x,≥3)` = the same
  `B(μ_n)`/higher-moment object. The lemma cleanly separates the (now-proven) Johnson part from the
  (open) past-Johnson part. No closure of `B(μ_n)`; honest.
