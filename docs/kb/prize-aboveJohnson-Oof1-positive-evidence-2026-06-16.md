# POSITIVE in-regime evidence: above-Johnson FRI soundness = O(1)/|F|, pinned by a 3-position witness (#444)

After the ground-truth pivot (capacity disproven; prize floor = above-Johnson `O(1)/|F|`, reduced by
ePrint 2026/861 to **Conjecture 7.1: FRI soundness dominated by 3-position sparse witnesses**), I built a
rigorous, coset-exhaustive reconstruction to attack Conj 7.1 directly. This is the campaign's first
**positive, in-regime** result — as opposed to the no-escape / BGK-wall findings (which were about the now
*disproven* capacity target).

## Method (rigorous, confound-free)
FRI folding and RS are `F`-linear and the honest fold of a codeword is a codeword, so the soundness
`ε(f) := #{λ : Fold[f,λ] close to RS'}` depends **only on the coset `f + RS_N`**, i.e. only on the syndrome
`s = H_N·f`. We therefore enumerate the **entire adversary space exactly** (all `q^{N−k}` syndromes), and
for each coset compute its **true** leader weight `w` (= distance to the code — controlling distance, which
fixes the weight-vs-distance confound) and its soundness at the **matched relative radius** (a coset at
relative distance `ζ=w/N` is a genuine violation only if `Fold[f,λ]` is within `ζ` of `RS'`, i.e.
`≤ w/2` positions). Exact folded distance via the `C(Np,2)` line-fits (`kp=2`). Probes:
`scripts/probes/probe_actionorbit_{coset_dominance,matched_soundness,qscaling_edge}.py`.

## What the metric audit showed (honesty)
- `ε₀` ("folds to an exact codeword") `≤ 1` above Johnson is **trivial linear algebra** (an affine line not
  inside a subspace meets it in `≤1` point) — not a soundness fact.
- `ε₁` (fixed "within 1 position") is **vacuous at high rate**: e.g. `RS[4,3]` has covering radius 1, so
  *every* word is within 1. The spurious `ε=q` "breaks" at `ρ=¾`/`w=4` are this covering-radius vacuity.
- The **only clean, non-vacuous, genuinely above-Johnson point** at `N=8, ρ=½` is the leader weight `w=3`
  (matched folded radius 1 < folded covering radius 2).

## The result (clean, q-independent)
Worst-case soundness over **genuine distance-3 leaders** (above-Johnson edge), RS`[8,4]`, single fold:

| q | 17 | 41 | 73 | 97 | 193 |
|---|----|----|----|----|-----|
| worst bad-count | **4** | **4** | **4** | **4** | **4** |
| `ε = count/q` | 0.235 | 0.098 | 0.055 | 0.041 | 0.021 |

- The **numerator is constant (4)** across an 11× field range (near-exhaustive ~168k genuine leaders per `q`;
  essentially exhaustive at `q=17` where it agrees with the full coset enumeration). Hence the above-Johnson
  worst-case soundness is **exactly `4/|F| = O(1)/|F|`** in this model — *the prize behavior*.
- The worst-case witness is `supp (0,1,2)` at **every** `q` — a **weight-3 ("3-position") leader**, exactly
  Conjecture 7.1's predicted dominating class.

## Honest scope
- **Reconstructed** model (not 2026/861's exact definitions of "3-position sparse witness" /
  "action-non-stabilised admissibility class" — those still need the Cloudflare-gated PDF).
- **Small instance** (`N=8`): the folded code `RS[4,2]` is coarse, so only the `w=3` edge is non-vacuous;
  the constant `4` and the consecutive-support witness are specific to this instance.
- This **corroborates** Conj 7.1 and the above-Johnson `O(1)/|F|` claim; it does **not** prove general-`N`
  `δ*`. But it is the first positive, in-regime signal, and it identifies the shape (constant numerator,
  3-position witness) a general proof must produce.

## Tie to the list-decoding grand challenge: δ* = the q-independent list-size transition
The FRI bad-count is governed by the **list size** `L(N,e) = max over words of #{RS codewords within rel
dist e}`. `L` is coset-invariant, so `L(N,e) = max over syndromes of #{weight-≤e vectors with that
syndrome}` — exactly computable. For dyadic RS`[8,4]` (ρ=½, Johnson 2.34 pos):

| radius `e` | 0 | 1 | 2 | **3** | 4 |
|---|---|---|---|---|---|
| max list `L` | 1 | 1 | 1 | **7** | 70 |
| rel | 0 | .125 | .25 | **.375** | .5 |

- The list is **uniquely decodable (L=1) up to the Johnson radius**, stays **O(1) (L=7) just above**
  Johnson, and blows up to 70 only at capacity (rel 0.5). So δ* (the radius where the list stops being
  O(1)) is **strictly above Johnson** for this dyadic family at N=8.
- `L(3)=7` is **q-independent** (verified q=17,41,73,…) — a **combinatorial constant**, NOT a field /
  character-sum quantity. This is exactly the prize's "does not reduce to hard open (number-theory) math"
  requirement: δ* here is a *combinatorial* list-size transition.
- The FRI bad-count `4 ≤` list size `7` — both O(1) at the edge — ties the **MCA** and **list-decoding**
  grand challenges to the same object.

## Honest open gap + next
- The above-Johnson `O(1)` region at N=8 **may be a finite-size effect**; the asymptotic δ* (whether
  `L(N, δN)` stays bounded for fixed `δ∈(Johnson, capacity)` as `N→∞`) is the hard, decisive question and
  N=8 cannot settle it. This is NOT yet a general-N pin of δ*.
- Two concrete routes:
  1. **Computational:** `L(N,e)` at N=16,32 via the MDS **coset weight distribution** (closed-form,
     avoids brute syndrome enumeration) or a compiled/GPU enumerator — detect the O(1)→growth transition.
  2. **Analytic:** derive the closed formula for the worst-case MDS coset list size `L(N,e)` (count of
     weight-≤e reps of the worst syndrome = 3-column dependencies among `H_N`'s columns `(1,x,x²,x³)`),
     giving δ* as the `e/N` where it transitions — and attempt the finite orbit-counting proof against the
     in-tree ACL / coset-closure bricks (action-orbit ↔ ACL).
- Exact Conj 7.1 statement still needs the gated 2026/861 PDF to align the model precisely.
