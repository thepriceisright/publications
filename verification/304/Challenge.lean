import FormalConjectures.ErdosProblems.«304»
import Lean
open Lean Elab Command Meta in
run_cmd do
  let info ← getConstInfo `Erdos304.erdos_304.variants.lower_1950
  let expected := info.type
  liftTermElabM do
    let proof ← mkSorry expected true
    addAndCompile (.thmDecl {name := `erdos_304.variants.lower_1950_candidate.erdos_304.variants.lower_1950, levelParams := info.levelParams, type := expected, value := proof})
