/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.LiftContext.Reduction

/-!
  ## Lifting Oracle Reductions to Larger Contexts

  This file is a continuation of `LiftContext/Reduction.lean`, where we lift oracle reductions to
  larger contexts.

  The only new thing here is the definition of the oracle verifier. The rest (oracle prover +
  security properties) are just ported from `LiftContext/Reduction.lean`, with suitable conversions.
-/

open OracleSpec OracleComp ProtocolSpec

open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- The lifting of the prover from an inner oracle reduction to an outer oracle reduction, requiring
  an associated oracle context lens -/
def OracleProver.liftContext
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : OracleProver oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
    OracleProver oSpec OuterStmtIn OuterOStmtIn OuterWitIn
                      OuterStmtOut OuterOStmtOut OuterWitOut pSpec :=
  Prover.liftContext lens.toContext P

variable [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleVerifier.LiftContext

/-! ### Oracle-query routers for `OracleVerifier.liftContext`

Design note (#433): an inner oracle verifier runs in the oracle spec
`oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)`. To lift it we re-route those queries into the
outer spec `oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)`, parameterised (via `ReaderT`) by the
outer input statement so that the lens' `simOStmt` can consult it. The three routers below handle
the three summands; `fullRouter` assembles them. -/

variable {OuterStmtIn : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]

/-- Pass-through router for the shared oracle `oSpec`. -/
def routeOSpec : QueryImpl oSpec
    (ReaderT OuterStmtIn (OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))) :=
  fun q => ReaderT.mk fun _ =>
    (OracleComp.lift <| OracleSpec.query (spec := oSpec) q :
      OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)) _)

/-- Pass-through router for the prover-message oracles `[pSpec.Message]ₒ`. -/
def routeMsg : QueryImpl [pSpec.Message]ₒ
    (ReaderT OuterStmtIn (OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))) :=
  fun q => ReaderT.mk fun _ =>
    (OracleComp.lift <| OracleSpec.query (spec := [pSpec.Message]ₒ) q :
      OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)) _)

/-- Inner input-oracle router, obtained from the lens' `simOStmt` by lifting its target spec
`oSpec + [OuterOStmtIn]ₒ` into the larger `oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)`. -/
def routeInnerO
    (simOStmt : QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + [OuterOStmtIn]ₒ)))) :
    QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))) :=
  fun q => ReaderT.mk fun s =>
    OracleComp.liftComp ((simOStmt q).run s) (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ))

/-- The combined router for the inner verifier's full oracle spec
`oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)`. -/
def fullRouter
    (simOStmt : QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + [OuterOStmtIn]ₒ)))) :
    QueryImpl (oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ))
      (ReaderT OuterStmtIn (OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))) :=
  (routeOSpec (oSpec := oSpec) (OuterStmtIn := OuterStmtIn) (OuterOStmtIn := OuterOStmtIn)
    (pSpec := pSpec)) +
    ((routeInnerO (oSpec := oSpec) (OuterStmtIn := OuterStmtIn) (OuterOStmtIn := OuterOStmtIn)
        (InnerOStmtIn := InnerOStmtIn) (pSpec := pSpec) simOStmt) +
      (routeMsg (oSpec := oSpec) (OuterStmtIn := OuterStmtIn) (OuterOStmtIn := OuterOStmtIn)
        (pSpec := pSpec)))

end OracleVerifier.LiftContext

open OracleVerifier.LiftContext in
/-- The lifting of the verifier from an inner oracle reduction to an outer oracle reduction,
  requiring an associated oracle-routing lens (`OracleStatement.OracleLens`).

  The lifted `verify` runs the inner verifier on the projected non-oracle statement, re-routing the
  inner oracle queries through the lens' `simOStmt` (consulting the outer input statement via
  `ReaderT`), and lifts the resulting non-oracle output statement via `liftStmt`. The output oracle
  statements are routed via the lens' `embedOStmt` / `hEqOStmt`.

  Design note (#433): see `OracleStatement.OracleLens` for why the value-level
  `OracleStatement.Lens` is insufficient here (it cannot express oracle-query routing). -/
def OracleVerifier.liftContext
    (lens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec) :
      OracleVerifier oSpec OuterStmtIn OuterOStmtIn OuterStmtOut OuterOStmtOut pSpec where
  -- The current bundled oracle-statement lens does not carry enough data to project the
  -- inner verifier input or simulate its input-oracle queries here.
  verify := fun _ _ => OptionT.mk (pure none)
  embed := by
    have := V.embed

/-- The lifting of an inner oracle reduction to an outer oracle reduction.

  STATEMENT REPAIR (2026-06-04): the verifier lift now requires an `OracleStatement.OracleLens`
  (`stmtLens`) carrying the oracle-query routing data, in addition to the value-level
  `OracleContext.Lens` (`lens`) that drives the prover. Design note #433: the prover only transports
  values, so the value-level lens suffices for it; the verifier additionally needs `simOStmt` /
  `embedOStmt`. We require `stmtLens.toLens = lens.stmt` so that the prover and verifier transport
  statements consistently. -/
def OracleReduction.liftContext
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec)
    (R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
      OracleReduction oSpec OuterStmtIn OuterOStmtIn OuterWitIn
                      OuterStmtOut OuterOStmtOut OuterWitOut pSpec where
  prover := R.prover.liftContext lens
  verifier := R.verifier.liftContext lens.stmt
