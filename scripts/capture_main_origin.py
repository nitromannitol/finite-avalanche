#!/usr/bin/env python3
"""Generate the Lean program that captures Main's literal semantic environment.

Run the emitted file using the project's pinned Lean environment. Its output goes
under .lake/main-origin-capture; it never overwrites the reviewed comparator.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def emit(destination):
    source = (ROOT / 'FiniteAvalanchesAudit/MainOrigin/Challenge.lean').read_text()
    literal = source[source.index('open Lean Elab Command\n\nnamespace MainComparatorLiteral'):
                     source.index('end MainComparatorLiteral') + len('end MainComparatorLiteral')]
    dependencies = source[source.index('/-- All kernel constant references'):
                          source.index('def declarationDependencies')]
    destination.write_text('import FiniteAvalanchesCurrent.RegisteredPast.Main\n\n' + literal +
                           '\n\nnamespace CaptureMainOrigin\n\n' + dependencies + PROGRAM)


PROGRAM = r'''
open MainComparatorLiteral

def mainName : Name := `FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

def project (n : Name) : Bool :=
  n.toString.startsWith "FiniteAvalanches" || n.toString.startsWith "LatticeProb" ||
    n.toString.startsWith "CurrentSource" || n.toString.startsWith "CurrentRegisteredPast" ||
    n.toString.startsWith "CurrentMain"

def structural (ci : ConstantInfo) : Array Name := Id.run do
  match ci with
  | .inductInfo v => return (v.all ++ v.ctors ++ v.all.map (·.str "rec")).toArray
  | .ctorInfo v => return #[v.name, v.induct]
  | .recInfo v =>
    let mut result := #[v.name] ++ v.all.toArray
    for rule in v.rules do
      result := result.push rule.ctor ++ kernelDependencies rule.rhs
    return result
  | .defnInfo v => return v.all.toArray
  | .thmInfo v => return v.all.toArray
  | .opaqueInfo v => return v.all.toArray
  | _ => return #[ci.name]

def bodyDependencies (ci : ConstantInfo) : Array Name :=
  match ci.value? true with
  | some e => kernelDependencies e
  | none => #[]

def textNames (ns : Array Name) : Json := toJson (ns.map Name.toString)

def outputLines (path : System.FilePath) (lines : Array Json) : IO Unit := do
  let h ← IO.FS.Handle.mk path .write
  for line in lines do h.putStr (line.compress ++ "\n")

run_cmd do
  let env ← getEnv
  let some (.thmInfo main) := env.find? mainName | throwError "MAIN_NOT_THEOREM"
  let mainAxioms ← collectAxioms mainName
  let primitives : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let retained := mainAxioms.filter (fun n => !primitives.contains n) |>.qsort (fun a b => a.toString < b.toString)
  let mut pending := kernelDependencies main.type ++ retained
  let mut seen : Std.HashSet Name := {}
  let mut owned : Std.HashSet Name := {}
  let mut boundary : Std.HashSet Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "MISSING_CAPTURE_DEPENDENCY {n}"
    if project (moduleOf env n) then
      if n == mainName then throwError "MAIN_PROOF_REACHED"
      owned := owned.insert n
      pending := pending ++ kernelDependencies ci.type ++ bodyDependencies ci ++ structural ci
    else
      boundary := boundary.insert n
  let constants := owned.toArray.qsort Name.lt
  let boundaries := boundary.toArray.qsort Name.lt
  let mut state : DagState := {}
  let (mainRoot, next) ← liftIO <| (encode main.type).run state
  state := next
  let mainNodes := state.nodes
  let mut rows : Array Json := #[]
  let mut axiomUnion : Std.HashSet Name := {}
  let mut ownedAxioms : Array Name := #[]
  let mut bodies := 0
  let mut rules := 0
  let mut nested := 0
  for n in constants do
    let some ci := env.find? n | throwError "OWNED_CONSTANT_MISSING {n}"
    let (j, next) ← liftIO <| (constantJson ci).run state
    state := next
    let rebuilt ← liftIO <| IO.ofExcept (decodeConstant state.restored j)
    unless sameConstant ci rebuilt do throwError "CAPTURE_ROUNDTRIP_FAILED {n}"
    if ci.hasValue true then bodies := bodies + 1
    if ci.isAxiom then ownedAxioms := ownedAxioms.push n
    if let .recInfo v := ci then rules := rules + v.rules.length
    if let .inductInfo v := ci then nested := nested + v.numNested
    let axs ← collectAxioms n
    for a in axs do axiomUnion := axiomUnion.insert a
    rows := rows.push <| Json.mkObj [
      ("constant", j), ("module", toJson (moduleOf env n).toString),
      ("type_dependencies", textNames (kernelDependencies ci.type)),
      ("body_dependencies", textNames (bodyDependencies ci)),
      ("structural_dependencies", textNames (structural ci)),
      ("actual_axioms", textNames axs)]
  let mut targets : Array Json := #[]
  for n in retained do
    let some ci := env.find? n | throwError "RETAINED_CONSTANT_MISSING {n}"
    unless ci.isAxiom do throwError "RETAINED_CONSTANT_NOT_AXIOM {n}"
    let (root, next) ← liftIO <| (encode ci.type).run state
    state := next
    targets := targets.push <| Json.mkObj [
      ("name", nameJson n), ("display_name", toJson n.toString),
      ("levels", namesJson ci.levelParams), ("type_root", toJson root)]
  let boundaryRows := boundaries.map fun n => Json.mkObj [
    ("name", nameJson n), ("display_name", toJson n.toString),
    ("module", toJson (moduleOf env n).toString)]
  let summary := Json.mkObj [
    ("schema", toJson "main-comparator-full-constantinfo-dag-v1"),
    ("status", toJson "ACTUAL_DAG_CAPTURE_ONLY_NOT_COMPARATOR_APPROVAL"),
    ("main_name", nameJson mainName), ("main_levels", namesJson main.levelParams),
    ("main_type_root", toJson mainRoot), ("main_proof_serialized", toJson false),
    ("owned_constants", toJson constants.size), ("boundary_constants", toJson boundaries.size),
    ("owned_axioms", textNames ownedAxioms), ("retained_count", toJson retained.size),
    ("retained_targets", .arr targets), ("actual_main_axioms", textNames mainAxioms),
    ("semantic_actual_axioms", textNames (axiomUnion.toArray.qsort Name.lt)),
    ("primitive_axioms", textNames primitives), ("nodes", toJson state.nodes.size),
    ("whole_types_roundtripped", toJson constants.size), ("whole_bodies_roundtripped", toJson bodies),
    ("recursor_rules", toJson rules), ("nested_inductives", toJson nested),
    ("syntax_metadata", toJson state.metadataSyntaxCount), ("eliminated_inputs", toJson (#[] : Array String)),
    ("declaration_identity", toJson "all ConstantInfo fields; Expr.equal for every type/body/rule"),
    ("future_gates", toJson #["fresh Mathlib-only kernel replay", "whole-declaration identity against the actual environment", "independent source/definition review", "actual pinned comparator and kernels"])]
  let mainType := Json.mkObj [("schema", toJson "literal-main-type-subdag-v1"),
    ("root", toJson mainRoot), ("levels", namesJson main.levelParams),
    ("original_root", toJson mainRoot),
    ("original_node_indices", toJson (Array.range mainNodes.size)),
    ("only_numeric_child_indices_rewritten", toJson true)]
  let dir : System.FilePath := ".lake/main-origin-capture"
  liftIO <| IO.FS.createDirAll dir
  liftIO <| outputLines (dir / "nodes.jsonl") state.nodes
  liftIO <| outputLines (dir / "declarations.jsonl") rows
  liftIO <| outputLines (dir / "main-type-nodes.jsonl") mainNodes
  liftIO <| IO.FS.writeFile (dir / "main-type.json") (mainType.pretty ++ "\n")
  liftIO <| IO.FS.writeFile (dir / "boundary.json") ((Json.arr boundaryRows).pretty ++ "\n")
  liftIO <| IO.FS.writeFile (dir / "SUMMARY.json") (summary.pretty ++ "\n")
  logInfo m!"CAPTURE: {constants.size} declarations, {retained.size} assumptions, {state.nodes.size} nodes"

end CaptureMainOrigin
'''


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', nargs='?', type=Path, help='Lean file to generate')
    parser.add_argument('--normalize', type=Path, help='format a completed capture directory')
    args = parser.parse_args()
    if args.normalize:
        path = args.normalize / 'main-type.json'
        data = json.loads(path.read_text())
        ordered = {key: data[key] for key in ('schema', 'root', 'levels', 'original_root',
                                               'original_node_indices', 'only_numeric_child_indices_rewritten')}
        path.write_text(json.dumps(ordered, indent=2) + '\n')
    elif args.output:
        emit(args.output)
    else:
        parser.error('supply an output file or --normalize')
