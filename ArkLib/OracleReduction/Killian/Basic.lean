/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import ArkLib.CommitmentScheme.Basic
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# The Killian Transformation

This file is to describe the Killian transformation ([Killian '92], [SNARGs book Chapter 20]).
This transformation converts a Probabilistically Checkable Proof (PCP) into an succinct interactive argument/Sigma protocol using Merkle trees. This can then be made non-interactive using the Fiat-Shamir transformation, (these two transformations together are referred to by the SNARGs book as the "Micali transformation" [Micali '00]).

The

-/
