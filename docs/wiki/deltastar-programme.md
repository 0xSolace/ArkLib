# The δ* Programme

The mutual-correlated-agreement threshold programme: pin
`δ*(C, ε*) = sup{δ : ε_mca(C, δ) ≤ ε*}` for explicit smooth-domain Reed–Solomon
codes ([ABF26] Definition 4.3), with matching machine-checked bounds.

## Where everything is

| What | Where |
|---|---|
| Agent guide (build recipe, honesty rules, pitfalls, state of knowledge) | [`ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`](../../ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md) |
| Compiled campaign knowledge (#357, by theme) | [`docs/kb/deltastar-357-compiled-knowledge.md`](../kb/deltastar-357-compiled-knowledge.md) |
| Research map (papers + adjacent math + ranked attack vectors) | [`docs/kb/deltastar-research-map.md`](../kb/deltastar-research-map.md) |
| Refuted approaches with constraint lemmas | [`ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md`](../../ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md) |
| Probes (exact small-scale computation) | `scripts/probes/probe_*.py` |
| The nine-hypothesis methodology record | [`docs/wiki/deltastar-357-nine-hypotheses-2026-06-11.md`](deltastar-357-nine-hypotheses-2026-06-11.md) |

## The fast build path (mandatory)

The ProximityGap cone is 800+ files. **Never iterate with `lake build`** (3000+-job
trace + the build lock serializes all agents). Instead:

```bash
scripts/pg-warm.sh                 # once per session: pre-build substrate oleans
scripts/pg-iterate.sh <file>.lean  # per attempt: ~30-75s, lock-free, parallel-safe
./scripts/lake-locked.sh build <m> # only for full-module olean builds (serialized)
```

Develop in a detached `/tmp` worktree with `.lake` symlinked to the main checkout
(see the agent guide §2 for the concurrency hazards on this shared tree).

## The state in one paragraph

The granularity ladder gives δ* in closed form on every band with `3(j−1)+k ≤ n`;
exact pins exist at two instances (deepest window: `ε* ∈ [2/17, 7/17)` at
RS[F₁₇,⟨2⟩,4], maximal); the first exact explosion-band value (`7/17` at δ = 1/4)
is computed and its binding law (far-coset line incidence) formalized; the
production regime is bracketed `[(1−ρ)/3 unconditional · 1−√ρ−η modulo exactly
`CellPackageSupply`, 1]` with the numeric budget proven and the bad side provably
silent. The open core has four equivalent faces (Johnson supply, bad-side family,
sub-√q subgroup character sums, line–ball incidence) — see the agent guide §3.5.
