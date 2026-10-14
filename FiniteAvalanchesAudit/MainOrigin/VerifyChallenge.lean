import FiniteAvalanchesAudit.MainOrigin.Challenge

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
  if env.contains MainComparatorReplay.mainName then throwError "CHALLENGE_IMPORTED_OR_ADDED_ORIGINAL_MAIN_PROOF"
  unless target.value.hasNonSyntheticSorry && !target.value.hasSyntheticSorry do
    throwError "CHALLENGE_TARGET_DOES_NOT_HAVE_ONLY_INTENTIONAL_HOLE"
  let mut holeOwners : Array Name := #[]
  let mut localAxioms : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if MainComparatorReplay.moduleOf env n != `FiniteAvalanchesAudit.MainOrigin.Challenge then continue
    if ci.isAxiom then localAxioms := localAxioms.push n
    let mut used := MainComparatorReplay.kernelDependencies ci.type
    if let some body := ci.value? true then used := used ++ MainComparatorReplay.kernelDependencies body
    if let .recInfo r := ci then
      for rule in r.rules do used := used ++ MainComparatorReplay.kernelDependencies rule.rhs
    if used.contains `sorryAx then holeOwners := holeOwners.push n
  unless holeOwners == #[targetName] do throwError "CHALLENGE_NOT_EXACTLY_ONE_TARGET_LEVEL_HOLE {holeOwners}"
  unless localAxioms.qsort Name.lt == retained.qsort Name.lt do
    throwError "CHALLENGE_LOCAL_AXIOMS_ARE_NOT_EXACTLY_THE_RETAINED_22"
  let productionPrefixes := #["FiniteAvalanches", "FiniteAvalanchesFrozen", "FiniteAvalanchesProofs", "FiniteAvalanchesCurrent", "CurrentSource", "CurrentRegisteredPast", "LatticeProb"]
  for m in env.header.moduleNames do
    let moduleName := m.toString
    if productionPrefixes.any (fun namespacePrefix => moduleName == namespacePrefix || moduleName.startsWith (namespacePrefix ++ ".")) then
      throwError "CHALLENGE_IMPORTED_PROJECT_OR_LP_MODULE {m}"
    if moduleName == "FiniteAvalanchesAudit" || moduleName.startsWith "FiniteAvalanchesAudit." then
      unless m == `FiniteAvalanchesAudit.MainOrigin.Challenge do
        throwError "CHALLENGE_IMPORTED_UNREVIEWED_AUDIT_MODULE {m}"

  let targetAxioms ← collectAxioms targetName
  for ax in targetAxioms do
    unless MainComparatorReplay.primitives.contains ax || retained.contains ax || ax == `sorryAx do
      throwError "PAIR_TARGET_UNEXPECTED_AXIOM {ax}"
  let result := Json.mkObj [
    ("status", toJson "PAIR_TYPE_AND_SEMANTIC_KERNEL_CHECK_ONLY_NOT_COMPARATOR_APPROVAL"),
    ("mode", toJson "CHALLENGE"), ("full_main_type_equal", toJson true),
    ("universe_parameters_equal", toJson true), ("exact_retained_assertion_types", toJson retained.size),
    ("whole_constantinfo_comparisons", toJson constants.size),
    ("actual_semantic_axioms", toJson (semanticUnion.toArray.qsort Name.lt |>.map Name.toString)),
    ("target_actual_axioms", toJson (targetAxioms.map Name.toString)),
    ("sole_intentional_challenge_hole_checked", toJson true),
    ("comparator_pass", toJson false)]
  let output : System.FilePath := "audit/main-comparator/verify-challenge"
  liftIO <| IO.FS.createDirAll output
  liftIO <| IO.FS.writeFile (output / "SUMMARY.json") (result.pretty ++ "\n")
  logInfo m!"PAIR_CHALLENGE_KERNEL_CHECK full MAIN type and complete meaning declarations match; all22 assertions; comparator pending"

#print axioms FiniteAvalanchesAudit.MainOrigin.finite_avalanches_origin
