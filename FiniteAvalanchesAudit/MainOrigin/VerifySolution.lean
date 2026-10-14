import FiniteAvalanchesAudit.MainOrigin.Solution

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let directory := MainComparatorReplay.captureDirectory
  let raw ← liftIO <| IO.FS.readFile (directory / "SUMMARY.json")
  let summary ← liftIO <| IO.ofExcept (Json.parse raw)
  let nodes ← liftIO <| MainComparatorReplay.readNodes (directory / "nodes.jsonl")
  let (constants, _) ← liftIO <| MainComparatorReplay.readConstants (directory / "declarations.jsonl") nodes
  let mainType ← liftIO <| IO.ofExcept (MainComparatorLiteral.expression nodes
    (← liftIO <| IO.ofExcept (summary.getObjVal? "main_type_root")))
  let levels ← liftIO <| IO.ofExcept (MainComparatorLiteral.names
    (← liftIO <| IO.ofExcept (summary.getObjVal? "main_levels")))
  let targets ← liftIO <| IO.ofExcept (summary.getObjValAs? (Array Json) "retained_targets")
  let retained ← liftIO <| IO.ofExcept <| targets.mapM fun row => do
    MainComparatorLiteral.decodeName (← row.getObjVal? "name")
  unless retained.size == 22 && (Std.HashSet.ofArray retained).size == 22 do
    throwError "PAIR_RETAINED_TARGETS_NOT_EXACT_22"
  let targetName := `FiniteAvalanchesAudit.MainOrigin.finite_avalanches_origin
  let some (.thmInfo target) := env.find? targetName | throwError "PAIR_TARGET_NOT_THEOREM"
  unless target.levelParams == levels && target.type.equal mainType do
    throwError "PAIR_FULL_MAIN_TYPE_OR_UNIVERSES_DIFFER_FROM_ACTUAL_CAPTURE"
  for ci in constants do
    let some actual := env.find? ci.name | throwError "PAIR_SEMANTIC_CONSTANT_MISSING {ci.name}"
    unless MainComparatorLiteral.sameConstant actual ci do
      throwError "PAIR_COMPLETE_SEMANTIC_CONSTANTINFO_DIFFERS {ci.name}"
  for row in targets do
    let n ← liftIO <| IO.ofExcept (MainComparatorLiteral.decodeName
      (← liftIO <| IO.ofExcept (row.getObjVal? "name")))
    let expectedLevels ← liftIO <| IO.ofExcept (MainComparatorLiteral.names
      (← liftIO <| IO.ofExcept (row.getObjVal? "levels")))
    let expected ← liftIO <| IO.ofExcept (MainComparatorLiteral.expression nodes
      (← liftIO <| IO.ofExcept (row.getObjVal? "type_root")))
    let some (.axiomInfo actual) := env.find? n | throwError "PAIR_RETAINED_TARGET_NOT_AXIOM {n}"
    unless actual.levelParams == expectedLevels && actual.type.equal expected do
      throwError "PAIR_EXACT_RETAINED_ASSERTION_TYPE_DIFFERS {n}"
  let semanticAxioms ← liftIO <| IO.ofExcept (summary.getObjValAs? (Array String) "semantic_actual_axioms")
  let mut semanticUnion : Std.HashSet Name := {}
  for ci in constants do
    let axs ← collectAxioms ci.name
    for ax in axs do
      unless MainComparatorReplay.primitives.contains ax || retained.contains ax do
        throwError "PAIR_SEMANTIC_AXIOM_OUTSIDE_PRIMITIVES_PLUS_22 {ci.name} {ax}"
      semanticUnion := semanticUnion.insert ax
  unless (semanticUnion.toArray.map Name.toString).qsort (· < ·) == semanticAxioms.qsort (· < ·) do
    throwError "PAIR_SEMANTIC_AXIOM_UNION_DIFFERS_FROM_ACTUAL_CAPTURE"
  let some (.thmInfo anchor) := env.find? MainComparatorReplay.mainName
    | throwError "SOLUTION_FROZEN_ANCHOR_MISSING"
  unless target.levelParams == anchor.levelParams && target.type.equal anchor.type do
    throwError "SOLUTION_FULL_TARGET_TYPE_DIFFERS_FROM_FROZEN_MAIN"
  if target.value.hasSorry then throwError "SOLUTION_TARGET_HAS_HOLE"
  for (n, ci) in env.constants.toList do
    if MainComparatorReplay.moduleOf env n != `FiniteAvalanchesAudit.MainOrigin.Solution then continue
    if ci.isAxiom then throwError "SOLUTION_INTRODUCED_LOCAL_AXIOM {n}"
    let mut used := MainComparatorReplay.kernelDependencies ci.type
    if let some body := ci.value? true then used := used ++ MainComparatorReplay.kernelDependencies body
    if let .recInfo r := ci then
      for rule in r.rules do used := used ++ MainComparatorReplay.kernelDependencies rule.rhs
    if used.contains `sorryAx then throwError "SOLUTION_LOCAL_DECLARATION_HAS_HOLE {n}"

  let targetAxioms ← collectAxioms targetName
  for ax in targetAxioms do
    unless MainComparatorReplay.primitives.contains ax || retained.contains ax do
      throwError "PAIR_TARGET_UNEXPECTED_AXIOM {ax}"
  unless (targetAxioms.map Name.toString).qsort (· < ·) == (← liftIO <| IO.ofExcept (summary.getObjValAs? (Array String) "actual_main_axioms")).qsort (· < ·) do
    throwError "SOLUTION_AXIOMS_DIFFER_FROM_CAPTURED_CURRENT_MAIN"
  let result := Json.mkObj [
    ("status", toJson "PAIR_TYPE_AND_SEMANTIC_KERNEL_CHECK_ONLY_NOT_COMPARATOR_APPROVAL"),
    ("mode", toJson "SOLUTION"), ("full_main_type_equal", toJson true),
    ("universe_parameters_equal", toJson true), ("exact_retained_assertion_types", toJson retained.size),
    ("whole_constantinfo_comparisons", toJson constants.size),
    ("actual_semantic_axioms", toJson (semanticUnion.toArray.qsort Name.lt |>.map Name.toString)),
    ("target_actual_axioms", toJson (targetAxioms.map Name.toString)),
    ("sole_intentional_challenge_hole_checked", toJson false),
    ("comparator_pass", toJson false)]
  let output : System.FilePath := "audit/main-comparator/verify-solution"
  liftIO <| IO.FS.createDirAll output
  liftIO <| IO.FS.writeFile (output / "SUMMARY.json") (result.pretty ++ "\n")
  logInfo m!"PAIR_SOLUTION_KERNEL_CHECK full MAIN type and complete meaning declarations match; all22 assertions; comparator pending"

#print axioms FiniteAvalanchesAudit.MainOrigin.finite_avalanches_origin
