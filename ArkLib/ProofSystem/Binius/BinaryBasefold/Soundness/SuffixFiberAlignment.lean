/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims

/-!
# Suffix/fiber alignment compatibility module

The suffix/fiber alignment theorem is now proved directly in
`Soundness/QueryPhasePrelims.lean` by using the value-level transport lemma from
`Soundness/SuffixAlignCore.lean`. This module remains as a stable import path and keeps a
focused axiom audit for the public alignment theorem.
-/

#print axioms Binius.BinaryBasefold.previousSuffix_eq_getFiberPoint_extractMiddleFinMask
