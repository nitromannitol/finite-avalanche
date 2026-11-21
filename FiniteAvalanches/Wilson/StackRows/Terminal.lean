import FiniteAvalanches.Wilson.StackRows.Law
import FiniteAvalanches.Wilson.CyclePopping.TerminalTrace
import FiniteAvalanches.Wilson.CyclePopping.SingletonRootTrees
import FiniteAvalanches.Wilson.CyclePopping.ErasureDepartures
import FiniteAvalanches.Trees.Existence

/-! On stacks whose cycle popping terminates, the stack protocol started from one root
attaches loop-erased branches made of terminal arrows only, so its output edges are the
copies of the terminal arrows. Hence the stack protocol samples the uniform spanning tree
of copies. The loop-erased walk of the stack driver is the image of the loop-erased stack
trace under the prefunctor sending an instruction to its copy; loop erasure commutes with
prefunctors which are injective on vertices. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CopiedNetwork

open Quiver MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

section Naturality

variable {V W : Type*} [Quiver V] [Quiver W] [DecidableEq V] [DecidableEq W]
variable (F : V ⥤q W)

omit [DecidableEq V] [DecidableEq W] in
theorem mapPath_vertices {a b : V} (p : Path a b) :
    (F.mapPath p).vertices = p.vertices.map F.obj := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [Prefunctor.mapPath_cons, Path.vertices_cons, Path.vertices_cons, ih, List.map_concat]

variable (hF : Function.Injective F.obj)
include hF

theorem prefixTo_mapPath {a b : V} (p : Path a b) (v : V) (hv : v ∈ p.vertices)
    (hv' : F.obj v ∈ (F.mapPath p).vertices) :
    prefixTo (F.mapPath p) (F.obj v) hv' = F.mapPath (prefixTo p v hv) := by
  induction p generalizing v with
  | nil =>
    obtain rfl : v = a := by simpa using hv
    rw [prefixTo_self, prefixTo_self]
  | @cons b c p e ih =>
    by_cases hcv : c = v
    · subst hcv
      rw [prefixTo_self, prefixTo_self]
    · have hmem : v ∈ p.vertices := by
        rw [Path.vertices_cons, List.concat_eq_append, List.mem_append] at hv
        rcases hv with hv | hv
        · exact hv
        · exact absurd (List.mem_singleton.mp hv).symm hcv
      have hmem' : F.obj v ∈ (F.mapPath p).vertices := by
        rw [mapPath_vertices]
        exact List.mem_map_of_mem hmem
      have hne : F.obj c ≠ F.obj v := fun h => hcv (hF h)
      calc prefixTo (F.mapPath (p.cons e)) (F.obj v) hv' =
            prefixTo (F.mapPath p) (F.obj v) hmem' :=
          prefixTo_cons_of_ne (F.mapPath p) (F.map e) hv' hne hmem'
        _ = F.mapPath (prefixTo p v hmem) := ih v hmem hmem'
        _ = F.mapPath (prefixTo (p.cons e) v hv) := by rw [prefixTo_cons_of_ne p e hv hcv hmem]

/-- Loop erasure commutes with prefunctors injective on vertices. -/
theorem loopErase_mapPath {a b : V} (p : Path a b) :
    loopErase (F.mapPath p) = F.mapPath (loopErase p) := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
    rw [Prefunctor.mapPath_cons, loopErase_cons_eq, loopErase_cons_eq]
    have hmem : F.obj c ∈ (loopErase (F.mapPath p)).vertices ↔ c ∈ (loopErase p).vertices := by
      rw [ih, mapPath_vertices]
      constructor
      · intro h
        obtain ⟨y, hy, hyc⟩ := List.mem_map.mp h
        exact hF hyc ▸ hy
      · exact List.mem_map_of_mem
    by_cases hc : c ∈ (loopErase p).vertices
    · rw [dif_pos (hmem.mpr hc), dif_pos hc]
      have key : ∀ (q : Path a b) (hq : loopErase (F.mapPath p) = F.mapPath q)
          (h : F.obj c ∈ (loopErase (F.mapPath p)).vertices) (h' : c ∈ q.vertices),
          prefixTo (loopErase (F.mapPath p)) (F.obj c) h = F.mapPath (prefixTo q c h') := by
        intro q hq h h'
        revert h
        rw [hq]
        intro h
        exact prefixTo_mapPath F hF q c h' h
      exact key _ ih _ hc
    · rw [dif_neg (fun h => hc (hmem.mp h)), dif_neg hc, ih]
      rfl

end Naturality

variable {V E I : Type} [Fintype V] [Fintype E] (G : Multigraph V E) (ι : E ↪ I)

/-- An instruction viewed as an arrow of the copied path quiver. -/
def instructionArrow {v w : V}
    (e : @Quiver.Hom V (instructionQuiver (incidentCopyHead G)) v w) :
    @Quiver.Hom (ULift.{0} V) (pathQuiver G) (ULift.up v) (ULift.up w) :=
  ⟨e.val.val, by
    rcases incidentCopy_endpoints G v e.val with h | h
    · exact Or.inl (Prod.ext (congrArg ULift.up h.1) (congrArg ULift.up (h.2.trans e.property)))
    · exact Or.inr (Prod.ext (congrArg ULift.up (h.2.trans e.property)) (congrArg ULift.up h.1))⟩

/-- The prefunctor sending an instruction to its copy. -/
def instructionPrefunctor :
    @Prefunctor V (instructionQuiver (incidentCopyHead G)) (ULift.{0} V) (pathQuiver G) :=
  @Prefunctor.mk V (instructionQuiver (incidentCopyHead G)) (ULift.{0} V) (pathQuiver G)
    ULift.up (fun e => instructionArrow G e)

/-- The walk of the stack driver is the image of the stack trace. -/
theorem packedPath_stackDriver (σ : CopyStacks G) (k : Cursor V) (x : V) (n : ℕ) :
    letI : Quiver V := instructionQuiver (incidentCopyHead G)
    letI : Quiver (ULift.{0} V) := pathQuiver G
    packedPath G x (stackDriver G σ k x) n =
      ⟨(stackTrace G σ k x n).1, (instructionPrefunctor G).mapPath (stackTrace G σ k x n).2⟩ := by
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  letI : Quiver (ULift.{0} V) := pathQuiver G
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : ∀ (P Q : Σ b : V, Trace G x b) (c : Letter G), P = Q →
        (⟨other G P.1 (c P.1), P.2.cons (arrow G P.1 c)⟩ : Σ b : V, Trace G x b) =
        ⟨other G Q.1 (c Q.1), Q.2.cons (arrow G Q.1 c)⟩ := by
      rintro P Q c rfl
      rfl
    exact hstep (packedPath G x (stackDriver G σ k x) n)
      ⟨(stackTrace G σ k x n).1, (instructionPrefunctor G).mapPath (stackTrace G σ k x n).2⟩
      (stackDriver G σ k x n) ih

/-- The edges attached by a stack walk are the copies of its loop-erased trace. -/
theorem attachAt_stackDriver_edges (s : State (V := V) (E := E) (I := I)) (σ : CopyStacks G)
    (k : Cursor V) (x : V) (n : ℕ) :
    letI : Quiver V := instructionQuiver (incidentCopyHead G)
    letI : Quiver (ULift.{0} V) := pathQuiver G
    (attachAt G ι s x (stackDriver G σ k x) n).edges =
      s.edges ∪ pathCopies G ((instructionPrefunctor G).mapPath
        (loopErase (stackTrace G σ k x n).2)) := by
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  letI : Quiver (ULift.{0} V) := pathQuiver G
  change s.edges ∪ pathCopies G (loopErase (packedPath G x (stackDriver G σ k x) n).2) = _
  rw [packedPath_stackDriver]
  change s.edges ∪ pathCopies G (loopErase ((instructionPrefunctor G).mapPath
    (stackTrace G σ k x n).2)) = _
  rw [loopErase_mapPath (instructionPrefunctor G) ULift.up_injective]

/-- The roots after a stack walk are the old roots and the vertices of the loop-erased
trace. -/
theorem attachAt_stackDriver_roots (s : State (V := V) (E := E) (I := I)) (σ : CopyStacks G)
    (k : Cursor V) (x : V) (n : ℕ) :
    letI : Quiver V := instructionQuiver (incidentCopyHead G)
    (attachAt G ι s x (stackDriver G σ k x) n).roots =
      s.roots ∪ {v | v ∈ (loopErase (stackTrace G σ k x n).2).vertices} := by
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  letI : Quiver (ULift.{0} V) := pathQuiver G
  change s.roots ∪ {v | ULift.up v ∈ (loopErase (packedPath G x (stackDriver G σ k x) n).2).vertices} = _
  rw [packedPath_stackDriver]
  change s.roots ∪ {v | ULift.up v ∈ (loopErase ((instructionPrefunctor G).mapPath
    (stackTrace G σ k x n).2)).vertices} = _
  rw [loopErase_mapPath (instructionPrefunctor G) ULift.up_injective, mapPath_vertices]
  ext v
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨y, hy, hyv⟩ := List.mem_map.mp h
      exact Or.inr (ULift.up_injective hyv ▸ hy)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (List.mem_map_of_mem h)

/-- The copies of a path of selected instructions are the selected copies at its
departures. -/
theorem pathCopies_mapPath_of_selected (σ : CopyStacks G) (t : Cursor V) {x y : V}
    (p : @Quiver.Path V (instructionQuiver (incidentCopyHead G)) x y) :
    letI : Quiver V := instructionQuiver (incidentCopyHead G)
    letI : Quiver (ULift.{0} V) := pathQuiver G
    selected (instructionArrowStacks (incidentCopyHead G) (fun v i => σ (v, i))) t p →
      pathCopies G ((instructionPrefunctor G).mapPath p) =
        ((departures p).map (fun v => (σ (v, t v)).val)).toFinset := by
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  letI : Quiver (ULift.{0} V) := pathQuiver G
  induction p with
  | nil => intro _; rfl
  | @cons b c p e ih =>
    rintro ⟨hp, he⟩
    change insert (instructionArrow G e).val (pathCopies G ((instructionPrefunctor G).mapPath p)) = _
    rw [ih hp, departures_cons, List.map_append, List.toFinset_append, List.map_singleton,
      List.toFinset_cons, List.toFinset_nil, Finset.union_insert, Finset.union_empty]
    congr 1
    have h2 := (Sigma.mk.inj_iff.mp he).2
    have h1 := (Sigma.mk.inj_iff.mp he).1
    change (e.val).val = (σ (b, t b)).val
    subst h1
    have h3 := eq_of_heq h2
    rw [← h3]

end
end FiniteAvalanches.Wilson.CopiedNetwork
