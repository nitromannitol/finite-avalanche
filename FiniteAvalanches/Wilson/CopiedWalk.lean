import FiniteAvalanches.Wilson.LoopErasure
import FiniteAvalanches.Trees.Joining
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Uniform

/-! Wilson exploration on individual copies of a finite loopless multigraph.
The walk continues by legal ordinary transitions at every vertex. Only first-hit
paths are attached, and complete paths remain separate from erased branches. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open Quiver MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open scoped Classical ENNReal
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

abbrev Incident (v : V) := {e : E // G.left e = v ∨ G.right e = v}
abbrev Letter := (v : V) → Incident G v
abbrev Driver := ℕ → Letter G

instance incidentFintype (v : V) : Fintype (Incident G v) :=
  inferInstanceAs (Fintype {e : E // G.left e = v ∨ G.right e = v})
instance letterFintype : Fintype (Letter G) := inferInstanceAs (Fintype ((v : V) → Incident G v))
instance letterMeasurableSpace : MeasurableSpace (Letter G) := ⊤
instance letterMeasurableSingletonClass : MeasurableSingletonClass (Letter G) := ⟨fun _ => trivial⟩

def other (v : V) (e : Incident G v) : V :=
  if G.left e.val = v then G.right e.val else G.left e.val

theorem other_spec (v : V) (e : Incident G v) :
    (G.left e.val = v ∧ G.right e.val = other G v e) ∨
      (G.right e.val = v ∧ G.left e.val = other G v e) := by
  by_cases h : G.left e.val = v
  · exact Or.inl ⟨h, by simp [other, h]⟩
  · exact Or.inr ⟨e.property.resolve_left h, by simp [other, h]⟩

abbrev pathQuiver : Quiver (ULift.{0} V) :=
  copiedQuiver (fun e : E => (ULift.up (G.left e), ULift.up (G.right e)))
abbrev Trace (a b : V) := @Path (ULift.{0} V) (pathQuiver G) (ULift.up a) (ULift.up b)

def arrow (v : V) (a : Letter G) :
    @Quiver.Hom (ULift.{0} V) (pathQuiver G) (ULift.up v) (ULift.up (other G v (a v))) :=
  ⟨(a v).val, by
    rcases other_spec G v (a v) with h | h
    · exact Or.inl (Prod.ext (congrArg ULift.up h.1) (congrArg ULift.up h.2))
    · exact Or.inr (Prod.ext (congrArg ULift.up h.2) (congrArg ULift.up h.1))⟩

def position (x : V) (ω : Driver G) : ℕ → V
  | 0 => x
  | n + 1 => other G (position x ω n) (ω n (position x ω n))

def walkPath (x : V) (ω : Driver G) : (n : ℕ) → Trace G x (position G x ω n) :=
  letI := pathQuiver G
  fun n => match n with
  | 0 => .nil
  | n + 1 => (walkPath x ω n).cons (arrow G (position G x ω n) (ω n))

def packedPath (x : V) (ω : Driver G) (n : ℕ) : Σ b : V, Trace G x b :=
  ⟨position G x ω n, walkPath G x ω n⟩

def pathCopies {a : ULift.{0} V} : {b : ULift.{0} V} → @Path (ULift.{0} V) (pathQuiver G) a b → Finset E :=
  letI := pathQuiver G
  fun p => match p with
  | .nil => ∅
  | .cons p e => insert e.val (pathCopies p)

def pathCopyList {a : ULift.{0} V} : {b : ULift.{0} V} → @Path (ULift.{0} V) (pathQuiver G) a b → List E :=
  letI := pathQuiver G
  fun p => match p with
  | .nil => []
  | .cons p e => pathCopyList p ++ [e.val]

variable {I : Type}

abbrev Record := V × List V × List I
structure State where
  roots : Set V
  roots_nonempty : roots.Nonempty
  edges : Finset E
  history : List (Record (V := V) (I := I))

omit [Fintype V] [Fintype E] in
@[ext] theorem State.ext {s t : State (V := V) (E := E) (I := I)}
    (hr : s.roots = t.roots) (he : s.edges = t.edges) (hh : s.history = t.history) : s = t := by
  cases s; cases t; cases hr; cases he; cases hh; rfl

abbrev Roots := {R : Set V // R.Nonempty}

def initialState (R : Roots (V := V)) : State (V := V) (E := E) (I := I) :=
  ⟨R.val, R.property, ∅, []⟩

def hits (B : Set V) (x : V) (ω : Driver G) : Prop := ∃ n, position G x ω n ∈ B

def attachAt (ι : E ↪ I) (s : State (V := V) (E := E) (I := I)) (x : V) (ω : Driver G) (n : ℕ) : State (V := V) (E := E) (I := I) :=
  letI := pathQuiver G
  let p := packedPath G x ω n
  { roots := s.roots ∪ {v | ULift.up v ∈ (loopErase p.2).vertices}
    roots_nonempty := s.roots_nonempty.mono Set.subset_union_left
    edges := s.edges ∪ pathCopies G (loopErase p.2)
    history := s.history ++ [(x, p.2.vertices.map ULift.down, (pathCopyList G p.2).map ι)] }

def query (ι : E ↪ I) (s : State (V := V) (E := E) (I := I)) (x : V) (ω : Driver G) : Option (State (V := V) (E := E) (I := I)) :=
  if x ∈ s.roots then some s
  else if h : hits G s.roots x ω then some (attachAt G ι s x ω (Nat.find h)) else none

/-- Skips and repeated queries consume their own row, just as successful queries do. -/
def explore (ι : E ↪ I) (s : State (V := V) (E := E) (I := I)) :
    List V → (ℕ → Driver G) → Option (State (V := V) (E := E) (I := I))
  | [], _ => some s
  | x :: xs, ω => (query G ι s x (ω 0)).bind (fun t => explore ι t xs (fun i => ω (i + 1)))

/-- No walk alphabet or probability kernel is formed in the all-root case. -/
def allRootResult [Nonempty V] : State (V := V) (E := E) (I := I) :=
  initialState ⟨Set.univ, by obtain ⟨v⟩ := ‹Nonempty V›; exact ⟨v, Set.mem_univ v⟩⟩

theorem explore_all_roots (ι : E ↪ I) (s : State (V := V) (E := E) (I := I)) (hs : s.roots = Set.univ)
    (order : List V) (ω : ℕ → Driver G) : explore G ι s order ω = some s := by
  induction order generalizing ω with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ∈ s.roots := hs ▸ Set.mem_univ x
    simp only [explore, query, if_pos hx, Option.bind_some]
    exact ih _

theorem incident_nonempty [Nontrivial V]
    (hconn : ∀ x y, G.reaches Finset.univ x y) (v : V) : Nonempty (Incident G v) := by
  obtain ⟨w, hw⟩ := exists_ne v
  rcases (hconn v w).cases_head with he | ⟨z, hz, _⟩
  · exact False.elim (hw he.symm)
  · obtain ⟨e, _, h | h⟩ := hz
    · exact ⟨⟨e, Or.inl h.1⟩⟩
    · exact ⟨⟨e, Or.inr h.1⟩⟩

/-- Each vertex receives an independent uniform incident-copy choice. Existence is
proved from connectedness and nontriviality before forming the uniform PMF. -/
def uniformLetterLaw [Nontrivial V] (hconn : ∀ x y, G.reaches Finset.univ x y) : Measure (Letter G) := by
  letI (v : V) : Nonempty (Incident G v) := incident_nonempty G hconn v
  exact (PMF.uniformOfFintype (Letter G)).toMeasure

/-- IID rows of IID legal letters. The letter law is explicit data; it is not a tree law. -/
def driversLaw (μ : Measure (Letter G)) : Measure (ℕ → Driver G) :=
  Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ))

end
end FiniteAvalanches.Wilson.CopiedNetwork
