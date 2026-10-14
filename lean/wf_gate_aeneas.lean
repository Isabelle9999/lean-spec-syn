-- Aeneas-only half of the well-formedness gate: sent alongside wf_gate.lean (and
-- before the `lss_wf_gate` invocation) for the rust track only, never for
-- lean-native -- unlike wf_gate.lean, this one genuinely needs Aeneas imported.
--
-- Result/Error/ControlFlow derive BEq but not DecidableEq upstream (Aeneas/Std/
-- Primitives.lean) -- none of that gives `Decidable (a = b)`. these are the
-- "instances supplied for WP.spec, Result, ControlFlow" the gate needs so real
-- postconditions (`... = ok x`, loop results) are Decidable without the
-- candidate itself having to restate it. harmless to redeclare every gate call:
-- never persisted (python never saves the env this runs against).
deriving instance DecidableEq for Aeneas.Std.Error
deriving instance DecidableEq for Aeneas.Std.Result
deriving instance DecidableEq for Aeneas.Std.ControlFlow
