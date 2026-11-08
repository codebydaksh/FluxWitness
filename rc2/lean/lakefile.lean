import Lake
open Lake DSL
package floatlib_workspace
require floatlib from git "https://github.com/lean-dojo/FloatLib.git" @ "8c8871576a941a86e73dcf0882702b823139aa93"
lean_lib proofs
lean_lib FloatLibWorkspace
@[default_target] lean_lib BenchmarkNativeHalf

lean_lib C2DecodedStep

lean_lib C3DriverLoop

lean_lib C4Reference

lean_lib C2RoundingConstruction

lean_lib ReleaseAudit
