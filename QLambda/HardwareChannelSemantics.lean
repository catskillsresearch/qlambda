/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import QLambda.HardwareChannel.Config
import QLambda.HardwareChannel.Identity
import QLambda.HardwareChannel.Spines
import QLambda.HardwareChannel.UnderFrame
import QLambda.HardwareChannel.FunApp
import QLambda.HardwareChannel.Closed
import QLambda.HardwareChannel.Fundamental
import QLambda.HardwareChannel.Productive

/-!
# Proof-only channel semantics for the hardware CEK machine

`HardwareOperational.Config` remains the executable machine with normalized
states and positive-only measurement transitions.  This module supplies the
state-independent proof semantics needed by the TT channel model.  Its states
are subnormalized, so every physical branch exists, including a zero branch.
No normalization or positivity test is performed in this layer.

## Organization

The development is layered under `QLambda/HardwareChannel/`:

* `Config` — configurations, trees, relations, base completeness
* `Identity` — unique-successor identity-step transfers
* `Spines` — `NoApp` / `AdminNoApp` / `FunAppFrag` / `Produces` and stack spines
* `UnderFrame` — under-frame lemmas and closed special cases
  (empty-stack admin completeness lives here with the proofs that use it)
* `FunApp` — fragment inductions under residual frames
* `Closed` — closed `Produces` / `FunAppFrag` theorems and token adequacy
* `Fundamental` — path-indexed fundamental theorem and closed-term
  completeness under branch-complete evaluation derivations
* `Productive` — automatic `PathChannelEvaluation` for `Productive 0`
  closed applications (measure-Z / probability arguments included)

All layers contribute to the shared namespace
`QLambda.HardwareChannelSemantics`.
-/
