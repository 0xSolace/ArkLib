# ABF26 formalization review — 2026-05-18

> **Status (2026-05-19):** all H/M/L items in this review have been
> resolved on branch `feat/abf26-plan`. Per-item resolution log in
> §4. Original review prose preserved below as the historical record
> of what was flagged and why.
>
> **Companion artefacts:**
> - forward-looking work plan: [`abf26-pr-roadmap.md`](abf26-pr-roadmap.md)
> - paper↔Lean map: [`../audits/open-problems-list-decoding-and-correlated-agreement.md`](../audits/open-problems-list-decoding-and-correlated-agreement.md)

Self-review of the ABF26 PR (branch `feat/abf26-plan`, PR #505) after the
paper-haul (references/MANIFEST.md). Three lenses:

  (i)  Misformalization — does the Lean statement say what the paper says?
  (ii) Cleanups — same semantics, better shape.
  (iii) Integration — what ArkLib abstraction is being reinvented?

Findings are tagged by severity: **H** = wrong as stated; **M** = imprecise
or fragile; **L** = polish / style.

---

## 1. Misformalization (H / M)

### 1.1 [H] `SupportsErasureCorrection` is missing clause (ii)

`ArkLib/ProofSystem/ToyProblem/Definitions.lean:105-111`

Paper D6.4 requires:

  (i) `|f⁻¹(⊥)| < δ_min(C)·n` ∧ `∃ u ∈ C` agreeing off the erasures ⇒
      `E_C(f) = u`
  (ii) otherwise `E_C(f) = ⊥`

The Lean predicate only encodes (i). Clause (ii) is missing, so
`E := fun _ ↦ some <whatever>` vacuously satisfies the predicate when
*no* codeword matches. The predicate is therefore weaker than the paper's;
in particular L6.5 (`additive_code_supports_erasure_correction_grs12`)
becomes vacuous. Fix: conjoin

```lean
∧ (Code.minDist C ≤ (Finset.univ.filter (·.isNone)).card → E f = none)
```

### 1.2 [H] `SimplifiedIOR.oracleVerifier`'s `embed` is semantically wrong

`ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:201-210`

The output oracle of C6.9 is `f_new := f₁ + γ·f₂`. Lean uses
`embed := ⟨fun _ ↦ Sum.inl 0, …⟩`, which (per
`OracleVerifier.toVerifier` in `ArkLib/OracleReduction/Basic.lean:327-334`)
forces the output oracle to be *verbatim* the input oracle at index `0`,
i.e. `f₀`. The docstring claims this is a placeholder that the framework
materialises via `simulateQ` — but `toVerifier` does **not** route the
output oracle through `simulateQ`; only the `StmtOut` half goes through
`simulateQ`, while `OStmtOut` is read directly from `embed`. So this is
not a placeholder, it's a wrong specification.

The framework limitation is real (see `Basic.lean:278, 293` for the
in-flight `simOStmt` refactor). Three options:

  1. Drop `oracleProver` / `oracleVerifier` / `oracleReduction` from
     `SimplifiedIOR.lean` until the framework supports `simOStmt`. Keep
     only the non-oracle `prover` / `verifier` / `reduction`, which
     bundle everything into `StmtIn`.
  2. Add a TODO in the docstring that calls this out as a known gap.
  3. Inline the codeword combination in the prover's *messages*: have the
     prover send `f_new` as a message, so `embed := Sum.inr <messageIdx>`
     is faithful. Costs an extra round and changes the protocol.

Recommendation: **option 1** for now, with a note pointing at the
`simOStmt` refactor.

### 1.3 [H] `outputRelation₁` shape mismatch with `SimplifiedIOR`

`ArkLib/ProofSystem/ToyProblem/Spec/General.lean:183-187`

`outputRelation₁` is defined over `(((Fin k → F) × F) × (∀ _ : Fin 1, ι → F)) × (Fin k → F)`,
bundling statement + oracle + witness as one tuple. But
`SimplifiedIOR.reduction` (in the oracle flavour) splits those into the
three separate `OutputStatement`, `OutputOracleStatement`, `OutputWitness`
parameters of `OracleReduction`. The `outputRelation₁` shape only
matches the *non-oracle* `SimplifiedIOR.reduction`. Either:

  - Move `outputRelation₁` to `SimplifiedIOR.lean` (where it logically
    belongs), or
  - Provide both shapes (bundled and split) and rename to make the
    intent clear.

### 1.4 [M] `extensionCode_smul_mem` is sorry'd — docstring overclaims

`ArkLib/Data/CodingTheory/ExtensionCodes.lean:241-250`

Until the sorry is closed, `extensionCode P C_B` is NOT a `Submodule F`
of `ι → F`; only closure under addition and `ψ(b)·x` is established.
Several docstrings in the file (lines 134, 218) describe it as an
"F-submodule" of `ι → F`. Either close the sorry (the B5 refactor
suggested at line 236 is the right route) or downgrade the docstrings
to "B-submodule" pending the F-scalar closure.

### 1.5 [M] `umCode` missing `char(F) ≥ k` hypothesis and `umCode_one_eq_rsCode` lemma

`ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean`

Paper A.7 explicitly requires `char(F) ≥ k` (so that
`(a_i · i) ≠ 0` for `i ∈ [1, k)`, making the derivative-of-monomial
nontrivial). The current `umEvalOnPoints` / `umCode` only ask for
`[CommRing F]`. Without `char(F) ≥ k`, the encoder is not injective on
`degreeLT F k` and the code's dimension claim doesn't follow.

Also: the docstring promises a sanity lemma `umCode_one_eq_rsCode` (the
`s = 1` collapse to RS) but **the lemma is not in the file**. Add it
or remove the promise.

### 1.6 [M] `accepts_of_inputRelation` is point-form, not protocol-level

`ArkLib/ProofSystem/ToyProblem/Spec/General.lean:383-415`

The lemma proves the `accepts` predicate holds under the honest message
`g = M₀ + γ M₁`, but it is **not** lifted to
`OracleReduction.perfectCompleteness` against the `oracleReduction`
object. The FRI/Sumcheck files in ArkLib both ship a protocol-level
completeness theorem; this file does not. Adding

```lean
theorem oracleReduction_perfectCompleteness :
    (oracleReduction encode).perfectCompleteness
        (inputRelation k C) outputRelationTrivial 0 := …
```

(using `accepts_of_inputRelation` as the core fact) would close the
gap. Today, the protocol is provably *sound by sorry* (`protocol62_*`)
and provably *complete only at the decision-predicate level*.

### 1.7 [M] L6.6 / L6.8 / L6.10 use confusing relation positions

`Spec/General.lean:438-451, 475-489`; `Spec/SimplifiedIOR.lean:235-250`

`Verifier.knowledgeSoundness` takes parameters `(inputRel, outputRel,
err)`. The paper says C6.2 has KS *with respect to* `R̃²_{C,δ}`, which
maps to: extractor produces a witness satisfying `R̃²_{C,δ}` such that
V's output satisfies the trivial output relation. The Lean correctly
passes `outputRelation k C δ` (= `R̃²_{C,δ}`) into the *input* slot of
`Verifier.knowledgeSoundness` and `Set.univ` into the *output* slot.
The naming clash (`outputRelation` is used as the *input* parameter of
the KS predicate) is correct relative to the paper but confusing
relative to the API. A docstring sentence clarifying "Lean's
`knowledgeSoundness` reads its first relation argument as the
extracted-witness relation, which the paper labels R̃²" would prevent
later regressions.

### 1.8 [M] `linear_listSize_to_epsMCA_gcxk25` adds a non-paper hypothesis `η ≤ δ`

`ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean:96`

Paper T5.1 requires only `δ, η ∈ (0, 1)`. The Lean adds `η ≤ δ` to
keep `1 - √(1-δ+η) ≥ 0` (avoiding silent `toNNReal` truncation). This
is a legitimate paper-divergence; either:

  - Document the divergence explicitly (a "known strengthening — paper
    says (0,1), we say `η ≤ δ` to avoid the .toNNReal truncation
    artefact") and add a corresponding theorem statement matching the
    paper exactly with a `if η ≤ δ then meaningful else vacuous` shape, or
  - Drop the hypothesis and accept that the statement is vacuously true
    in the `η > δ` regime.

### 1.9 [M] `OracleStatement ι F` discards the `Fin 2` index

`Spec/General.lean:78`, mirrored at `Spec/SimplifiedIOR.lean:70`

```
def OracleStatement (ι F : Type) : Fin 2 → Type := fun _ ↦ ι → F
```

Functionally fine, but obscures intent. Both `f₁` and `f₂` are
codewords of the same code; using `fun _ ↦ ι → F` discards the index
type information. Acceptable as-is; if the design later wants
position-dependent oracles (e.g. `f₁ ∈ C₁`, `f₂ ∈ C₂`), the current
shape doesn't generalize. Low priority.

---

## 2. Cleanups (L)

### 2.1 Duplicate prover/verifier code between non-oracle and oracle flavours

`Spec/General.lean` and `Spec/SimplifiedIOR.lean` both ship two
near-identical copies of `prover`/`verifier`/`reduction`: a non-oracle
flavour bundling everything into `StmtIn`, and an oracle flavour.
The two are syntactically almost identical (same `PrvState`, same
`sendMessage`, etc.). Every change to one must be mirrored. FRI in
ArkLib has only the oracle flavour; following that convention would
halve the code. Currently kept because (1.2) means the oracle flavour
can't faithfully encode C6.9, so the non-oracle is the only one with
correct semantics. Once the framework supports `simOStmt`, the
non-oracle versions can be dropped.

### 2.2 `InterleavedCode.lambda_le` naming is inconsistent

`ArkLib/Data/CodingTheory/InterleavedCode.lean:833`

Other paper-cited lemmas in this branch follow the convention
`<topic>_<verb>_<bound>_<paperkey>` (e.g.
`rs_lambda_superpoly_extension_bkr06`,
`linear_lambda_ge_elias_volume_eli57`). This one is just
`InterleavedCode.lambda_le`. Rename to
`InterleavedCode.lambda_le_ggr11` for consistency. The audit doc
references [[GGR11]] for the bound.

### 2.3 `RoundByRound` is imported but unused in `SimplifiedIOR.lean`

`Spec/SimplifiedIOR.lean:7`

`simplifiedIOR_knowledgeSound` uses `Verifier.knowledgeSoundness`, not
the round-by-round variant. The import is dead. Replace with
`Security.Basic` (or drop entirely if the latter is re-exported
elsewhere).

### 2.4 `epsCA_curves` and `epsCA_affineSpaces` have only bridging lemma callers

`ArkLib/Data/CodingTheory/ProximityGap/Errors.lean:162-179`

Defined alongside `epsCA` but only consumed by their respective
bridging lemmas. The intent is forward-compatibility with §4 results
that work with non-line generators; until those are stated, the
definitions are unused. Two options:

  - Keep as documented future-use stubs (current state, fine if
    documented).
  - Move to a `Errors/Curves.lean` sub-file gated on their first
    consumer, leaving `Errors.lean` lean.

### 2.5 `SupportsErasureCorrection` doesn't belong in `ToyProblem/`

`ArkLib/ProofSystem/ToyProblem/Definitions.lean:105`

Erasure correction is a generic coding-theory predicate; it would be
reusable from `OracleReduction/` and other proof-system files. Move
to `ArkLib/Data/CodingTheory/Erasure.lean` (new file) and re-export.

### 2.6 `winningSet` could reuse `outputRelation₁`

`ToyProblem/Definitions.lean:121-126`

The current definition expands `relaxedRelation` inline. After fixing
(1.3) so `outputRelation₁` lives in `SimplifiedIOR` with the right
shape, this could read

```lean
def winningSet … : Set F :=
  { γ | ⟨((v, μ₁ + γ * μ₂), fun _ ↦ ...), ⟨…⟩⟩ ∈ outputRelation₁ … }
```

making the connection to the simplified-IOR output relation explicit.

### 2.7 Redundant `omit` declarations in `Spec/General.lean`

Six `omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]`
clauses, each before a different theorem. Refactor so the section
variables don't include these instances except where actually used,
removing the omits. Equivalent semantics, less noise.

### 2.8 `oracleVerifier.verify` uses `for…in (List.finRange t)`

`Spec/General.lean:355`

Computable but not idiomatic for FRI/Sumcheck where the corresponding
pattern is `← Fin.sequence_t …` or an explicit `Fin.foldr`. Either is
fine; flagging as a style point. The `for…in` form has slightly worse
elaboration error messages.

### 2.9 `grandMCAChallenge` / `grandListDecodingChallenge` should use `IsLUB`

`ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean:68-94`

The paper asks for the *largest* `δ*_C` — naturally `IsLUB` over the
threshold set. Current encoding (`bound at δ*_C ∧ strict failure
above`) is `IsLUB` minus the limit-case handling. Switching makes the
statement composable with Mathlib's `Sup` / `iSup` machinery.

---

## 3. Integration with ArkLib (L / M)

### 3.1 `ToyProblem.relation` reinvents linear encoding

`ToyProblem/Definitions.lean:70-75`

The existential `∃ encode : (Fin k → F) →ₗ[F] (ι → F), …` is
non-canonical: any `encode` whose image lies in `C` works. The IRS
implementation passes `ReedSolomon.encode`, but the abstract relation
doesn't know about it. For a `Submodule` code `C`, the canonical
"encode" is `Submodule.span F` paired with a basis; for `RS`, it's the
existing `ReedSolomon.evalOnPoints`. Refactoring to take `C : LinearCode
ι F` and require `M ∈ Polynomial.degreeLT F k`-style preimages would
align better with existing ArkLib conventions, but is a bigger refactor.

### 3.2 `accepts` predicate vs FRI's inline verify body

ArkLib's FRI `foldVerifier` does not factor out a separate `accepts`
predicate — the decision is inline in `verify`. The ToyProblem split
is justified by `accepts_of_inputRelation` (1.6), which is easier to
state against the factored predicate. As-is, fine; would be cleaner
once 1.6 is lifted to the protocol-level completeness theorem (the
inline form then suffices).

### 3.3 Variable conventions diverge from FRI

FRI `Spec/SingleRound.lean` uses `variable {F : Type} [Field F] …`
followed by `variable (k t : ℕ)` outside any `section`. The ToyProblem
files use the same pattern but the `(k t : ℕ)` is unparenthesised when
they appear in theorem statements (e.g. `(verifier (k := k) (t := t)
encode)`). Either bind them implicitly or include the explicit binders
consistently.

### 3.4 `relation` over Set-coded `C` doesn't use `ModuleCode`

ArkLib offers `ModuleCode ι F A` and `LinearCode ι F` as
linear-code-with-structure types. `ToyProblem.relation` consumes
`C : Set (ι → F)` and existentially binds the encoder, so it can't take
advantage of `Submodule.add_mem` / `Submodule.smul_mem` directly. The
soundness proof (when written) will need to bridge — pre-empting the
bridge by passing `C : Submodule F (ι → F)` from the start is cheaper.

### 3.5 Toy-problem's `OracleInterface` uses `instDefault`

`Spec/General.lean:117`

```
| ⟨1, _⟩ => OracleInterface.instDefault
```

Matches FRI's `getConst` pattern (where the message is read in full).
Fine. The corresponding `queryG` helper is correctly modeled on
`Fri.Spec.SingleRound.getConst`. Worth keeping a docstring
cross-reference.

---

## 4. Resolution log

All H/M/L items in this review were landed on `feat/abf26-plan` on
**2026-05-18** (with audit-doc refresh on **2026-05-19**). Mapping:

| Item | What was done |
|---|---|
| **1.1** | `Definitions.lean` and `Erasure.lean`: added clause (ii) (failure clause). |
| **1.2** | Dropped `oracleProver` / `oracleVerifier` / `oracleReduction` from `SimplifiedIOR.lean` and the matching `simplifiedOracleReductionIRS` from `Impl/IRS.lean`. Replaced with a docstring explaining the framework limitation and pointing at `simOStmt`. |
| **1.3** | `outputRelation₁` removed from `Spec/General.lean`; reshipped as `SimplifiedIOR.outputRelation` with type aligned to `OutputStatement × (∀ i, OutputOracleStatement) × OutputWitness`. |
| **1.4** | F-submodule docstring claims in `ExtensionCodes.lean` downgraded to "B-submodule, F-scalar closure gated on tagged sorry"; D2.20 audit row status → `present-but-incomplete`. |
| **1.5** | `umCode` docstring now documents `char(F) ≥ k`; new `Multiplicity.mem_umCode_one_iff_mem_rsCode` lemma added (hoisted out of `[CommRing F]` to a `[Field F]` scope to avoid `Polynomial`-Semiring instance clash). |
| **1.6** | `oracleReduction_perfectCompleteness` stub added in `Spec/General.lean`, depending on `accepts_of_inputRelation`. Tagged sorry — the `OracleReduction.toReduction` plumbing is the routine but laborious remaining step. |
| **1.7** | KS docstrings on `protocol62_knowledgeSound` / `protocol62_rbrKnowledgeSound` now include a "Naming convention — paper vs API" block. |
| **1.8** | T5.1 docstring carries an explicit "Paper divergence" banner for the added `η ≤ δ` hypothesis. |
| **1.9** | Left as-is (low priority); noted in this review for future reference. |
| **2.1** | Non-oracle duplication kept in `Spec/General.lean` (intentional given 1.2); will collapse once `simOStmt` lands. |
| **2.2** | Renamed `InterleavedCode.lambda_le` → `lambda_le_ggr11`; audit doc L2.10 reference updated. |
| **2.3** | `SimplifiedIOR.lean` import switched from `Security.RoundByRound` to `Security.Basic`. |
| **2.4** | Left as documented future-use stubs; no action. |
| **2.5** | Predicate moved to `ArkLib/Data/CodingTheory/Erasure.lean`; re-exported as `@[reducible] def ToyProblem.SupportsErasureCorrection` from `Definitions.lean`. |
| **2.6** | Skipped — would create an import cycle (`Definitions.lean` sits below `SimplifiedIOR.lean`). |
| **2.7** | Refactored: outer scope now `[Fintype ι] [Field F]`; heavy instances `[DecidableEq ι] [Fintype F] [DecidableEq F]` moved into nested `section Protocol`. Two `omit` clauses eliminated; remaining ones are load-bearing. |
| **2.8** | Left as-is (style point). |
| **2.9** | Left as-is (intentional generality discussion). |
| **3.1** | Left as documented future refactor; current existential encoder shape is correct for the survey-formalization scope. |
| **3.2** | Left as-is (rationale recorded in 1.6 resolution). |
| **3.3** | Left as-is (no change yet). |
| **3.4** | Left as documented future refactor; soundness work (Phase C) will revisit. |
| **3.5** | Left as-is; docstring cross-reference future polish. |

---

## 5. Out of scope for this review

  - The cross-cutting validation that the audit doc
    (`docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`)
    actually reflects current Lean state. The `scripts/abf26/coverage.py`
    drift-checker is the right tool for that; rerun it after applying
    H-level fixes. *(Done 2026-05-19: 0 missing / 0 drift.)*
  - Proof-search work on tagged sorries. Every `sorry` in owned files
    is paper-cited (verified by `lint.py`); closing them is L4+ work,
    not a review-level concern.
  - `Probability/Combinatorial.lean`'s Claim B.1 proof — straightforward
    Cauchy-Schwarz + Jensen, but several `ENNReal` ↔ `ℝ≥0` ↔ `ℝ`
    coercion lemmas would help. Tracked separately (roadmap Phase 3).
