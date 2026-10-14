import FiniteAvalanches.Trees.CurrentCopyTail
import FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices
import FiniteAvalanches.Probability.CurrentUniformEventCounts
import FiniteAvalanches.Trees.Lattice.PastCylinderLimit

/-! Source copied-edge errors are grouped at their actual original tail sites.
Choice is confined to a proved unique valid tail; no nonpath tail is defined. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors
open LatticeProb FiniteAvalanches Sandpile Components Trees.Lattice
open CurrentPastVertices Trees.Multigraph.CurrentCopyTail CurrentPastCylinder
open scoped Classical BigOperators
noncomputable section

/-- Each selected source copy has one actual active tail in the original site family. -/
theorem source_unique_tail (N r : ℕ) (hr : 2 ≤ r) (hrN : r ≤ N)
    (t : (WiredTrees.graph N).SpanningTree) (e : FiniteWired.Edge N)
    (heS : e ∈ sourceEdges N r hrN)
    (heP : e ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none) :
    ∃! a : FiniteWired.Active N, FiniteWired.site a ∈ sourceVertices r ∧
      some a ∈ (WiredTrees.graph N).componentAfter t.val e (some (origin N)) ∧
      ((WiredTrees.graph N).left e = some a ∨ (WiredTrees.graph N).right e = some a) := by
  obtain ⟨u, v, hep, hu, hv⟩ := sourceEdges_endpoints_in_vertices hr hrN heS
  have hel : (WiredTrees.graph N).left e = some u := congrArg Prod.fst hep
  have her : (WiredTrees.graph N).right e = some v := congrArg Prod.snd hep
  obtain ⟨x, hx, hunique⟩ := existsUnique_tail (WiredTrees.graph N) t
    (some (origin N)) none e heP
  obtain ⟨a, hxa⟩ : ∃ a : FiniteWired.Active N, x = some a := by
    rcases hx.2 with hx | hx
    · exact ⟨u, hx.symm.trans hel⟩
    · exact ⟨v, hx.symm.trans her⟩
  subst x
  have ha : FiniteWired.site a ∈ sourceVertices r := by
    rcases hx.2 with hx | hx
    · exact (Option.some.inj (hel.symm.trans hx)) ▸ hu
    · exact (Option.some.inj (her.symm.trans hx)) ▸ hv
  refine ⟨a, ⟨ha, hx⟩, ?_⟩
  rintro b ⟨_hb, hb⟩
  exact Option.some.inj (hunique (some b) hb)

/-- The active tail has exactly this outgoing copy and this whole origin-side past. -/
theorem source_tail_parent_and_past (N : ℕ)
    (t : (WiredTrees.graph N).SpanningTree) (e : FiniteWired.Edge N)
    (heP : e ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none)
    (a : FiniteWired.Active N)
    (ha : some a ∈ (WiredTrees.graph N).componentAfter t.val e (some (origin N)) ∧
      ((WiredTrees.graph N).left e = some a ∨ (WiredTrees.graph N).right e = some a)) :
    e = (WiredTrees.graph N).parentEdge t none (some a) (by simp) ∧
      (WiredTrees.graph N).past t none (some a) (by simp) =
        (WiredTrees.graph N).componentAfter t.val e (some (origin N)) :=
  ⟨copy_eq_parent _ t _ _ e heP (some a) ha.1 ha.2 (by simp),
    past_eq_source_component _ t _ _ e heP (some a) ha.1 ha.2 (by simp)⟩

/-- The existential finite past event is precisely the genuine past at this active
vertex. Every other witness for its original site is the SAME active vertex. -/
theorem finitePastEvent_at_active (N : ℕ) (a : FiniteWired.Active N)
    (W : Finset (Site 2)) (t : (WiredTrees.graph N).SpanningTree) :
    t ∈ finitePastEvent (FiniteWired.site a) W N ↔
      (WiredTrees.graph N).past t none (some a) (by simp) ⊆ activeLift N (W : Set (Site 2)) := by
  constructor
  · rintro ⟨b, hb, hp⟩
    have he : b = a := FiniteWired.site_injective N hb
    subst b
    exact hp
  · intro hp
    exact ⟨a, rfl, hp⟩

/-- The sink exclusion and the active site bijection match the same full cut set. -/
theorem insideVertex_eq_activeLift (N : ℕ) (W : Finset (Site 2)) :
    {v : FiniteWired.Vertex N | insideVertex W v} = activeLift N (W : Set (Site 2)) := by
  ext v
  cases v with
  | none => simp only [insideVertex, Set.mem_setOf_eq, sink_not_mem_activeLift]
  | some a => simp only [insideVertex, Set.mem_setOf_eq, some_mem_activeLift, Finset.mem_coe]

/-- Escape of the origin-side cut component implies escape of this same tail's past. -/
theorem cut_escape_implies_tail_escape (N M : ℕ)
    (t : (WiredTrees.graph N).SpanningTree) (e : FiniteWired.Edge N)
    (heP : e ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none)
    (a : FiniteWired.Active N)
    (ha : some a ∈ (WiredTrees.graph N).componentAfter t.val e (some (origin N)) ∧
      ((WiredTrees.graph N).left e = some a ∨ (WiredTrees.graph N).right e = some a))
    (hbad : ¬cutSites (origin N) t e ⊆ boxSites M) :
    t ∉ finitePastEvent (FiniteWired.site a) (boxSites M) N := by
  intro hgood
  have hp := (finitePastEvent_at_active N a (boxSites M) t).mp hgood
  rw [(source_tail_parent_and_past N t e heP a ha).2,
    ← insideVertex_eq_activeLift N (boxSites M)] at hp
  exact hbad ((cutSites_subset_iff (origin N) t e heP (boxSites M)).mpr hp)

/-- The injection maps actual qualifying edge COPIES to actual qualifying original
sites. Different copies at the same tail contradict parent-copy uniqueness. -/
theorem source_error_count_le_vertex_count (N r M : ℕ) (hr : 2 ≤ r) (hrN : r ≤ N)
    (t : (WiredTrees.graph N).SpanningTree) :
    ((sourceEdges N r hrN).filter (fun e =>
      e ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
        ¬cutSites (origin N) t e ⊆ boxSites M)).card ≤
    ((sourceVertices r).filter (fun x => t ∉ finitePastEvent x (boxSites M) N)).card := by
  let A := (sourceEdges N r hrN).filter (fun e =>
    e ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
      ¬cutSites (origin N) t e ⊆ boxSites M)
  let B := (sourceVertices r).filter (fun x => t ∉ finitePastEvent x (boxSites M) N)
  have htail (e : A) := source_unique_tail N r hr hrN t e.val
    (Finset.mem_filter.mp e.property).1 (Finset.mem_filter.mp e.property).2.1
  let a (e : A) : FiniteWired.Active N := (htail e).choose
  have ha (e : A) := (htail e).choose_spec.1
  let f : A → B := fun e => ⟨FiniteWired.site (a e), Finset.mem_filter.mpr
    ⟨(ha e).1, cut_escape_implies_tail_escape N M t e.val
      (Finset.mem_filter.mp e.property).2.1 (a e) (ha e).2
      (Finset.mem_filter.mp e.property).2.2⟩⟩
  have hf : Function.Injective f := by
    intro e d heq
    have hs : FiniteWired.site (a e) = FiniteWired.site (a d) := congrArg Subtype.val heq
    have had : a e = a d := FiniteWired.site_injective N hs
    apply Subtype.ext
    apply copies_eq_of_same_tail (WiredTrees.graph N) t (some (origin N)) none e.val d.val
      (Finset.mem_filter.mp e.property).2.1 (Finset.mem_filter.mp d.property).2.1 (some (a e))
      (ha e).2
    · rw [had]
      exact (ha d).2
    · simp
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Current source332–337: aggregate every copied-edge error at its true original
outgoing tail. No caller supplies a past, probability or counting estimate. -/
theorem source_edge_error_sum_le_vertex_past_sum (N r M : ℕ)
    (hr : 2 ≤ r) (hrN : r ≤ N) :
    ∑ e ∈ sourceEdges N r hrN, (WiredTrees.law N).real
      {t | e ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
        ¬cutSites (origin N) t e ⊆ boxSites M} ≤
    ∑ x ∈ sourceVertices r, (WiredTrees.law N).real
      ((finitePastEvent x (boxSites M) N)ᶜ) := by
  change ∑ e ∈ sourceEdges N r hrN, (uniformMeasure (WiredTrees.graph N).SpanningTree).real
    {t | e ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
      ¬cutSites (origin N) t e ⊆ boxSites M} ≤
    ∑ x ∈ sourceVertices r, (uniformMeasure (WiredTrees.graph N).SpanningTree).real
      ((finitePastEvent x (boxSites M) N)ᶜ)
  exact CurrentUniformEventCounts.uniform_event_sum_le _ _ _ _ _
    (fun t => by
      simpa only [Set.mem_setOf_eq, Set.mem_compl_iff] using
        source_error_count_le_vertex_count N r M hr hrN t)

end
end FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.source_unique_tail
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.source_unique_tail

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.source_tail_parent_and_past
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.source_tail_parent_and_past

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.finitePastEvent_at_active
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.finitePastEvent_at_active

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.insideVertex_eq_activeLift
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.insideVertex_eq_activeLift

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.cut_escape_implies_tail_escape
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.cut_escape_implies_tail_escape

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.source_error_count_le_vertex_count
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.source_error_count_le_vertex_count

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.source_edge_error_sum_le_vertex_past_sum
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentTailErrors.source_edge_error_sum_le_vertex_past_sum
