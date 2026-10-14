import Mathlib
import FiniteAvalanchesCurrent.RegisteredPast.Main
import FiniteAvalanches.External.AllMinorsMatrixTree
import FiniteAvalanches.External.ArcStraightening
import FiniteAvalanches.External.BarlowMassonAdjacentPath
import FiniteAvalanches.External.ClassicalBeurling
import FiniteAvalanches.External.ColoredWilson
import FiniteAvalanches.External.DiskAlternation
import FiniteAvalanches.External.GeometricDual
import FiniteAvalanches.External.KenyonWilsonPairingGroves
import FiniteAvalanches.External.LyonsProjectionDomination
import FiniteAvalanches.External.OuterFaceRedrawing
import FiniteAvalanches.External.PlaneDualBondCycle
import FiniteAvalanches.External.PlaneDualConnected
import FiniteAvalanches.External.PlaneEdgeChartIncidence
import FiniteAvalanches.External.PlanePuncturedChartFaceTransport
import FiniteAvalanches.External.PlanePuncturedFaceTransport
import FiniteAvalanches.External.PlaneTreeComplement
import FiniteAvalanches.External.PlaneVertexFaceStar
import FiniteAvalanches.External.SandpileLimit
import FiniteAvalanches.External.TwoPoleTopology
import FiniteAvalanches.External.WiredUstDualLaw
import FiniteAvalanches.External.WiredUstOneEnd
import FiniteAvalanches.External.WiredUstWeakLimit


/-!
Literal kernel data for the independent MAIN comparator.
The structural expression encoder/decoder preserves the captured kernel data.
No semantic constant is synthesized here. Every serialized node is immediately
decoded and checked using Expr.equal (including binder names and metadata).
-/

open Lean Elab Command

namespace MainComparatorLiteral

partial def decodeName (j : Json) : Except String Name := do
  let a ← j.getArr?
  match a.toList with
  | [.str "anonymous"] => return .anonymous
  | [.str "str", p, s] => return .str (← decodeName p) (← s.getStr?)
  | [.str "num", p, n] => return .num (← decodeName p) (← n.getNat?)
  | _ => throw "INVALID_DAG_NAME"

partial def decodeLevel (j : Json) : Except String Level := do
  let a ← j.getArr?
  match a.toList with
  | [.str "zero"] => return .zero
  | [.str "succ", u] => return .succ (← decodeLevel u)
  | [.str "max", u, v] => return .max (← decodeLevel u) (← decodeLevel v)
  | [.str "imax", u, v] => return .imax (← decodeLevel u) (← decodeLevel v)
  | [.str "param", n] => return .param (← decodeName n)
  | [.str "mvar", _] => throw "UNSOLVED_DAG_UNIVERSE_MVAR"
  | _ => throw "INVALID_DAG_LEVEL"

def decodeData (j : Json) : Except String DataValue := do
  let a ← j.getArr?
  match a.toList with
  | [.str "string", s] => return .ofString (← s.getStr?)
  | [.str "bool", b] => return .ofBool (← b.getBool?)
  | [.str "name", n] => return .ofName (← decodeName n)
  | [.str "nat", n] => return .ofNat (← n.getNat?)
  | [.str "int", n] => return .ofInt (← n.getInt?)
  | _ => throw "INVALID_DAG_METADATA_OR_SYNTAX"

def decodeBinder (j : Json) : Except String BinderInfo := do
  let s ← j.getStr?
  for bi in [BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    if s == reprStr bi then return bi
  throw "INVALID_DAG_BINDER"

def decodeNode (prior : Array Expr) (j : Json) : Except String Expr := do
  let child (x : Json) : Except String Expr := do
    let i ← x.getNat?
    if h : i < prior.size then return prior[i] else throw "DAG_FORWARD_OR_MISSING_REFERENCE"
  let a ← j.getArr?
  match a.toList with
  | [.str "bvar", n] => return .bvar (← n.getNat?)
  | [.str "sort", u] => return .sort (← decodeLevel u)
  | [.str "const", n, us] =>
    let levels ← (← us.getArr?).toList.mapM decodeLevel
    return .const (← decodeName n) levels
  | [.str "app", f, x] => return .app (← child f) (← child x)
  | [.str "lam", n, t, b, bi] =>
    return .lam (← decodeName n) (← child t) (← child b) (← decodeBinder bi)
  | [.str "forallE", n, t, b, bi] =>
    return .forallE (← decodeName n) (← child t) (← child b) (← decodeBinder bi)
  | [.str "letE", n, t, v, b, nd] =>
    return .letE (← decodeName n) (← child t) (← child v) (← child b) (← nd.getBool?)
  | [.str "natVal", n] => return .lit (.natVal (← n.getNat?))
  | [.str "strVal", s] => return .lit (.strVal (← s.getStr?))
  | [.str "mdata", entries, b] =>
    let pairs ← (← entries.getArr?).toList.mapM fun p => do
      let pair ← p.getArr?
      match pair.toList with
      | [n, v] => return (← decodeName n, ← decodeData v)
      | _ => throw "INVALID_DAG_METADATA_PAIR"
    return .mdata { entries := pairs } (← child b)
  | [.str "proj", n, i, b] => return .proj (← decodeName n) (← i.getNat?) (← child b)
  | _ => throw "INVALID_DAG_EXPR_CONSTRUCTOR"


def nameJson : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", nameJson p, toJson s]
  | .num p n => Json.arr #[toJson "num", nameJson p, toJson n]

def levelJson : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ u => Json.arr #[toJson "succ", levelJson u]
  | .max u v => Json.arr #[toJson "max", levelJson u, levelJson v]
  | .imax u v => Json.arr #[toJson "imax", levelJson u, levelJson v]
  | .param n => Json.arr #[toJson "param", nameJson n]
  | .mvar n => Json.arr #[toJson "mvar", nameJson n.name]

def dataJson : DataValue → Except String Json
  | .ofString s => pure (Json.arr #[toJson "string", toJson s])
  | .ofBool b => pure (Json.arr #[toJson "bool", toJson b])
  | .ofName n => pure (Json.arr #[toJson "name", nameJson n])
  | .ofNat n => pure (Json.arr #[toJson "nat", toJson n])
  | .ofInt n => pure (Json.arr #[toJson "int", toJson n])
  | .ofSyntax _ => throw "DAG_SYNTAX_METADATA_NOT_SUPPORTED"

structure DagState where
  cache : ExprStructMap Nat := {}
  nodes : Array Json := #[]
  restored : Array Expr := #[]
  metadataSyntaxCount : Nat := 0
  deriving Inhabited

abbrev DagM := StateT DagState IO

def remember (e rebuilt : Expr) (node : Json) : DagM Nat := do
  unless e.equal rebuilt do throw (IO.userError "DAG_STRUCTURAL_ROUNDTRIP_FAILURE")
  let decoded ← IO.ofExcept (decodeNode (← get).restored node)
  unless e.equal decoded do throw (IO.userError "DAG_JSON_NODE_ROUNDTRIP_FAILURE")
  let s ← get
  let i := s.nodes.size
  set ({ s with
    cache := s.cache.insert ⟨e⟩ i
    nodes := s.nodes.push node
    restored := s.restored.push decoded } : DagState)
  return i

def restored (i : Nat) : DagM Expr := return (← get).restored[i]!

partial def encode (e : Expr) : DagM Nat := do
  if let some i := (← get).cache.get? ⟨e⟩ then return i
  return ← match e with
  | .bvar n => remember e (.bvar n) (Json.arr #[toJson "bvar", toJson n])
  | .fvar _ => throw (IO.userError "DAG_UNCLOSED_FVAR")
  | .mvar _ => throw (IO.userError "DAG_UNSOLVED_MVAR")
  | .sort u => remember e (.sort u) (Json.arr #[toJson "sort", levelJson u])
  | .const n us =>
    remember e (.const n us)
      (Json.arr #[toJson "const", nameJson n, Json.arr (us.toArray.map levelJson)])
  | .app f a =>
    let fi ← encode f; let ai ← encode a
    remember e (.app (← restored fi) (← restored ai))
      (Json.arr #[toJson "app", toJson fi, toJson ai])
  | .lam n t b bi =>
    let ti ← encode t; let ri ← encode b
    remember e (.lam n (← restored ti) (← restored ri) bi)
      (Json.arr #[toJson "lam", nameJson n, toJson ti, toJson ri, toJson (reprStr bi)])
  | .forallE n t b bi =>
    let ti ← encode t; let ri ← encode b
    remember e (.forallE n (← restored ti) (← restored ri) bi)
      (Json.arr #[toJson "forallE", nameJson n, toJson ti, toJson ri, toJson (reprStr bi)])
  | .letE n t v b nd =>
    let ti ← encode t; let vi ← encode v; let ri ← encode b
    remember e (.letE n (← restored ti) (← restored vi) (← restored ri) nd)
      (Json.arr #[toJson "letE", nameJson n, toJson ti, toJson vi, toJson ri, toJson nd])
  | .lit (.natVal n) => remember e (.lit (.natVal n)) (Json.arr #[toJson "natVal", toJson n])
  | .lit (.strVal s) => remember e (.lit (.strVal s)) (Json.arr #[toJson "strVal", toJson s])
  | .mdata md b =>
    let ri ← encode b
    let count := md.entries.countP (fun (_, v) => match v with | .ofSyntax _ => true | _ => false)
    if count != 0 then throw (IO.userError "DAG_SYNTAX_METADATA_NOT_SUPPORTED")
    modify fun s => { s with metadataSyntaxCount := s.metadataSyntaxCount + count }
    let entries ← IO.ofExcept <| md.entries.toArray.mapM fun (n, v) => do
      return Json.arr #[nameJson n, ← dataJson v]
    remember e (.mdata md (← restored ri))
      (Json.arr #[toJson "mdata", Json.arr entries, toJson ri])
  | .proj n i b =>
    let ri ← encode b
    remember e (.proj n i (← restored ri))
      (Json.arr #[toJson "proj", nameJson n, toJson i, toJson ri])


def namesJson (ns : List Name) : Json := .arr (ns.toArray.map nameJson)

def hintsJson : ReducibilityHints → Json
  | .abbrev => .arr #[toJson "abbrev"]
  | .opaque => .arr #[toJson "opaque"]
  | .regular height => .arr #[toJson "regular", toJson height.toNat]

def safetyJson : DefinitionSafety → Json
  | .safe => toJson "safe"
  | .unsafe => toJson "unsafe"
  | .partial => toJson "partial"

def constantJson (ci : ConstantInfo) : DagM Json := do
  let ty ← encode ci.type
  let base := [
    ("name", nameJson ci.name),
    ("display_name", toJson ci.name.toString),
    ("levels", namesJson ci.levelParams),
    ("type_root", toJson ty)]
  let obj (kind : String) (fields : List (String × Json)) :=
    Json.mkObj (base ++ [("kind", toJson kind)] ++ fields)
  match ci with
  | .axiomInfo v => return obj "axiom" [("isUnsafe", toJson v.isUnsafe)]
  | .defnInfo v =>
    let body ← encode v.value
    return obj "definition" [("value_root", toJson body),
      ("hints", hintsJson v.hints), ("safety", safetyJson v.safety),
      ("all", namesJson v.all)]
  | .thmInfo v =>
    let body ← encode v.value
    return obj "theorem" [("value_root", toJson body), ("all", namesJson v.all)]
  | .opaqueInfo v =>
    let body ← encode v.value
    return obj "opaque" [("value_root", toJson body),
      ("isUnsafe", toJson v.isUnsafe), ("all", namesJson v.all)]
  | .inductInfo v =>
    return obj "inductive" [("numParams", toJson v.numParams),
      ("numIndices", toJson v.numIndices), ("all", namesJson v.all),
      ("ctors", namesJson v.ctors), ("numNested", toJson v.numNested),
      ("isRec", toJson v.isRec), ("isUnsafe", toJson v.isUnsafe),
      ("isReflexive", toJson v.isReflexive)]
  | .ctorInfo v =>
    return obj "constructor" [("induct", nameJson v.induct),
      ("cidx", toJson v.cidx), ("numParams", toJson v.numParams),
      ("numFields", toJson v.numFields), ("isUnsafe", toJson v.isUnsafe)]
  | .recInfo v =>
    let mut rules : Array Json := #[]
    for rule in v.rules do
      let rhs ← encode rule.rhs
      rules := rules.push (Json.mkObj [("ctor", nameJson rule.ctor),
        ("nfields", toJson rule.nfields), ("rhs_root", toJson rhs)])
    return obj "recursor" [("all", namesJson v.all),
      ("numParams", toJson v.numParams), ("numIndices", toJson v.numIndices),
      ("numMotives", toJson v.numMotives), ("numMinors", toJson v.numMinors),
      ("rules", .arr rules), ("k", toJson v.k), ("isUnsafe", toJson v.isUnsafe)]
  | .quotInfo v =>
    let kind := match v.kind with
      | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
    return obj "quotient" [("quotient_kind", toJson kind)]

def field (j : Json) (key : String) : Except String Json := j.getObjVal? key

def names (j : Json) : Except String (List Name) := do
  (← j.getArr?).toList.mapM decodeName

def expression (prior : Array Expr) (j : Json) : Except String Expr := do
  let i ← j.getNat?
  match prior[i]? with
  | some e => return e
  | none => throw s!"DECLARATION_MISSING_EXPRESSION_ROOT {i}"

def decodeHints (j : Json) : Except String ReducibilityHints := do
  match (← j.getArr?).toList with
  | [.str "abbrev"] => return .abbrev
  | [.str "opaque"] => return .opaque
  | [.str "regular", height] =>
    let n ← height.getNat?
    if n > 4294967295 then throw "REDUCIBILITY_HEIGHT_OVERFLOW"
    return .regular n.toUInt32
  | _ => throw "INVALID_REDUCIBILITY_HINT"

def decodeSafety (j : Json) : Except String DefinitionSafety := do
  match ← j.getStr? with
  | "safe" => return .safe
  | "unsafe" => return .unsafe
  | "partial" => return .partial
  | _ => throw "INVALID_DEFINITION_SAFETY"

def decodeConstantVal (prior : Array Expr) (j : Json) : Except String ConstantVal := do
  return {
    name := ← decodeName (← field j "name"),
    levelParams := ← names (← field j "levels"),
    type := ← expression prior (← field j "type_root") }

def decodeRule (prior : Array Expr) (j : Json) : Except String RecursorRule := do
  return {
    ctor := ← decodeName (← field j "ctor"),
    nfields := ← (← field j "nfields").getNat?,
    rhs := ← expression prior (← field j "rhs_root") }

def decodeConstant (prior : Array Expr) (j : Json) : Except String ConstantInfo := do
  let cv ← decodeConstantVal prior j
  match ← (← field j "kind").getStr? with
  | "axiom" =>
    return .axiomInfo { cv with isUnsafe := ← (← field j "isUnsafe").getBool? }
  | "definition" =>
    return .defnInfo { cv with
      value := ← expression prior (← field j "value_root"),
      hints := ← decodeHints (← field j "hints"),
      safety := ← decodeSafety (← field j "safety"),
      all := ← names (← field j "all") }
  | "theorem" =>
    return .thmInfo { cv with
      value := ← expression prior (← field j "value_root"),
      all := ← names (← field j "all") }
  | "opaque" =>
    return .opaqueInfo { cv with
      value := ← expression prior (← field j "value_root"),
      isUnsafe := ← (← field j "isUnsafe").getBool?,
      all := ← names (← field j "all") }
  | "inductive" =>
    return .inductInfo { cv with
      numParams := ← (← field j "numParams").getNat?,
      numIndices := ← (← field j "numIndices").getNat?,
      all := ← names (← field j "all"), ctors := ← names (← field j "ctors"),
      numNested := ← (← field j "numNested").getNat?,
      isRec := ← (← field j "isRec").getBool?,
      isUnsafe := ← (← field j "isUnsafe").getBool?,
      isReflexive := ← (← field j "isReflexive").getBool? }
  | "constructor" =>
    return .ctorInfo { cv with
      induct := ← decodeName (← field j "induct"),
      cidx := ← (← field j "cidx").getNat?,
      numParams := ← (← field j "numParams").getNat?,
      numFields := ← (← field j "numFields").getNat?,
      isUnsafe := ← (← field j "isUnsafe").getBool? }
  | "recursor" =>
    return .recInfo { cv with
      all := ← names (← field j "all"),
      numParams := ← (← field j "numParams").getNat?,
      numIndices := ← (← field j "numIndices").getNat?,
      numMotives := ← (← field j "numMotives").getNat?,
      numMinors := ← (← field j "numMinors").getNat?,
      rules := ← (← (← field j "rules").getArr?).toList.mapM (decodeRule prior),
      k := ← (← field j "k").getBool?,
      isUnsafe := ← (← field j "isUnsafe").getBool? }
  | "quotient" =>
    let kind ← match ← (← field j "quotient_kind").getStr? with
      | "type" => pure QuotKind.type | "ctor" => pure QuotKind.ctor
      | "lift" => pure QuotKind.lift | "ind" => pure QuotKind.ind
      | _ => throw "INVALID_QUOTIENT_KIND"
    return .quotInfo { cv with kind }
  | tag => throw s!"INVALID_CONSTANT_KIND {tag}"

def sameConstantVal (a b : ConstantVal) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type

def sameRules (a b : List RecursorRule) : Bool :=
  a.length == b.length && (a.zip b).all (fun (x, y) =>
    x.ctor == y.ctor && x.nfields == y.nfields && x.rhs.equal y.rhs)

/-- Whole ConstantInfo identity, using Expr.equal rather than alpha-insensitive BEq Expr. -/
def sameConstant (a b : ConstantInfo) : Bool :=
  sameConstantVal a.toConstantVal b.toConstantVal && match a, b with
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe
  | .defnInfo x, .defnInfo y =>
    x.value.equal y.value && x.hints == y.hints && x.safety == y.safety && x.all == y.all
  | .thmInfo x, .thmInfo y => x.value.equal y.value && x.all == y.all
  | .opaqueInfo x, .opaqueInfo y =>
    x.value.equal y.value && x.isUnsafe == y.isUnsafe && x.all == y.all
  | .inductInfo x, .inductInfo y =>
    x.numParams == y.numParams && x.numIndices == y.numIndices && x.all == y.all &&
    x.ctors == y.ctors && x.numNested == y.numNested && x.isRec == y.isRec &&
    x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
  | .ctorInfo x, .ctorInfo y =>
    x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams &&
    x.numFields == y.numFields && x.isUnsafe == y.isUnsafe
  | .recInfo x, .recInfo y =>
    x.all == y.all && x.numParams == y.numParams && x.numIndices == y.numIndices &&
    x.numMotives == y.numMotives && x.numMinors == y.numMinors &&
    sameRules x.rules y.rules && x.k == y.k && x.isUnsafe == y.isUnsafe
  | .quotInfo x, .quotInfo y =>
    match x.kind, y.kind with
    | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
    | _, _ => false
  | _, _ => false

def declarationOf (infos : Std.HashMap Name ConstantInfo) (ci : ConstantInfo) :
    Except String Declaration := do
  match ci with
  | .axiomInfo v => return .axiomDecl v
  | .defnInfo v => return .defnDecl v
  | .thmInfo v => return .thmDecl v
  | .opaqueInfo v => return .opaqueDecl v
  | .inductInfo v =>
    let mut types : List InductiveType := []
    for n in v.all do
      let some (.inductInfo iv) := infos[n]?
        | throw s!"MISSING_FULL_INDUCTIVE_BLOCK {n}"
      unless iv.levelParams == v.levelParams && iv.numParams == v.numParams &&
          iv.all == v.all && iv.isUnsafe == v.isUnsafe do
        throw s!"INCONSISTENT_MUTUAL_INDUCTIVE_BLOCK {n}"
      let mut ctors : List Constructor := []
      for cn in iv.ctors do
        let some (.ctorInfo cv) := infos[cn]?
          | throw s!"MISSING_FULL_CONSTRUCTOR {cn}"
        unless cv.induct == n do throw s!"CONSTRUCTOR_WRONG_INDUCTIVE {cn}"
        ctors := ctors ++ [{ name := cv.name, type := cv.type }]
      types := types ++ [{ name := iv.name, type := iv.type, ctors }]
    return .inductDecl v.levelParams v.numParams types v.isUnsafe
  | .ctorInfo _ | .recInfo _ => throw "KERNEL_GENERATED_CONSTANT_NOT_STANDALONE"
  | .quotInfo _ => throw "QUOTIENT_MUST_BE_THE_PINNED_MATHLIB_BOUNDARY"

end MainComparatorLiteral


/-!
Mathlib-boundary preflight for the literal MAIN semantics, without a MAIN proof
or theorem hole. This is a replay check, not the eventual Challenge module.
The compiler parent must pin the capture inputs before executing this query.
-/

open Lean Elab Command
open MainComparatorLiteral

namespace MainComparatorReplay

def captureDirectory : System.FilePath :=
  "FiniteAvalanchesAudit/MainOrigin/semantic-data"

def outputDirectory : System.FilePath :=
  "audit/main-comparator/challenge-replay"

def mainName : Name := `FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin

def primitives : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

def isProjectModule (n : Name) : Bool :=
  n.toString.startsWith "FiniteAvalanches" || n.toString.startsWith "LatticeProb"

def readNodes (path : System.FilePath) : IO (Array Expr) := do
  let h ← IO.FS.Handle.mk path .read
  let mut expressions : Array Expr := #[]
  while true do
    let line ← h.getLine
    if line.isEmpty then break
    let j ← IO.ofExcept (Json.parse line)
    let e ← IO.ofExcept (MainComparatorLiteral.decodeNode expressions j)
    expressions := expressions.push e
  return expressions

def readConstants (path : System.FilePath) (nodes : Array Expr) :
    IO (Array ConstantInfo × Std.HashMap Name ConstantInfo) := do
  let h ← IO.FS.Handle.mk path .read
  let mut constants : Array ConstantInfo := #[]
  let mut byName : Std.HashMap Name ConstantInfo := {}
  while true do
    let line ← h.getLine
    if line.isEmpty then break
    let row ← IO.ofExcept (Json.parse line)
    let ci ← IO.ofExcept (MainComparatorLiteral.decodeConstant nodes (← IO.ofExcept (row.getObjVal? "constant")))
    if byName.contains ci.name then throw (IO.userError s!"DUPLICATE_LITERAL_CONSTANT {ci.name}")
    if ci.name == mainName then throw (IO.userError "MAIN_PROOF_PRESENT_IN_REPLAY_CAPTURE")
    if ci.isUnsafe || ci.isPartial then throw (IO.userError s!"UNSAFE_LITERAL_CONSTANT {ci.name}")
    byName := byName.insert ci.name ci
    constants := constants.push ci
  return (constants, byName)

/-- All kernel constant references, including the structure named by Expr.proj. -/
def kernelDependencies (e : Expr) : Array Name := Id.run do
  let mut pending := #[e]
  let mut seen : ExprStructMap Unit := {}
  let mut names : Std.HashSet Name := {}
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    if seen.contains ⟨current⟩ then continue
    seen := seen.insert ⟨current⟩ ()
    match current with
    | .const n _ => names := names.insert n
    | .proj n _ body =>
      names := names.insert n
      pending := pending.push body
    | .lam _ domain body _ | .forallE _ domain body _ =>
      pending := pending.push domain |>.push body
    | .letE _ type value body _ =>
      pending := pending.push type |>.push value |>.push body
    | .app fn arg => pending := pending.push fn |>.push arg
    | .mdata _ body => pending := pending.push body
    | _ => pure ()
  return names.toArray.qsort Name.lt

def declarationDependencies (d : Declaration) : Array Name := Id.run do
  let mut names : Std.HashSet Name := {}
  let all ← d.foldExprM (fun acc e => pure (acc ++ kernelDependencies e)) #[]
  for n in all do names := names.insert n
  return names.toArray.qsort Name.lt

end MainComparatorReplay


open Lean Elab Term

/-- Return the exact closed, captured proposition without a mathematical alias. -/
elab (name := mainLiteralStatement) "literal_main_statement" : term => do
  let directory := MainComparatorReplay.captureDirectory
  let nodes ← _root_.liftM (m := IO) (n := Lean.Elab.Term.TermElabM) <| MainComparatorReplay.readNodes (directory / "main-type-nodes.jsonl")
  let raw ← _root_.liftM (m := IO) (n := Lean.Elab.Term.TermElabM) <| IO.FS.readFile (directory / "main-type.json")
  let summary ← _root_.liftM (m := IO) (n := Lean.Elab.Term.TermElabM) <| IO.ofExcept (Json.parse raw)
  let levels ← _root_.liftM (m := IO) (n := Lean.Elab.Term.TermElabM) <| IO.ofExcept (MainComparatorLiteral.names
    (← _root_.liftM (m := IO) (n := Lean.Elab.Term.TermElabM) <| IO.ofExcept (summary.getObjVal? "levels")))
  unless levels.isEmpty do throwError "LITERAL_MAIN_UNIVERSES_NOT_EMPTY"
  let result ← _root_.liftM (m := IO) (n := Lean.Elab.Term.TermElabM) <| IO.ofExcept (MainComparatorLiteral.expression nodes
    (← _root_.liftM (m := IO) (n := Lean.Elab.Term.TermElabM) <| IO.ofExcept (summary.getObjVal? "root")))
  if result.hasFVar || result.hasMVar || result.hasLooseBVars then
    throwError "LITERAL_MAIN_TYPE_NOT_CLOSED"
  return result

theorem FiniteAvalanchesAudit.MainOrigin.finite_avalanches_origin : literal_main_statement := by
  exact FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin
