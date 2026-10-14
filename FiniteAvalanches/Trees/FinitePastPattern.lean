import FiniteAvalanches.Trees.CutComponents

/-! The finite-tree part of the incident-edge union in incoming main.tex177.
Original edge copies and the same finite tree support are retained throughout. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Multigraph.CurrentPastPattern

open FiniteAvalanches.Trees.RootedPaths
open scoped Classical

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
variable (G : Multigraph V E)

/-- Selected original copies with at least one endpoint in the given support. -/
def incidentEdges (F : Set V) (s : Finset E) : Finset E :=
  s.filter fun e => G.left e ∈ F ∨ G.right e ∈ F

omit [DecidableEq E] in
theorem mem_incidentEdges (F : Set V) (s : Finset E) (e : E) :
    e ∈ incidentEdges G F s ↔ e ∈ s ∧ (G.left e ∈ F ∨ G.right e ∈ F) :=
  Finset.mem_filter

/-- Exactly the inside tree and the unique outgoing copy occur at a cut support. -/
theorem incident_edges_eq_insert_internal (t : G.SpanningTree) (F : Set V) (e : E)
    (hc : G.cut_components F t.val e) :
    incidentEdges G F t.val = insert e (G.internalEdges F (t.val.erase e)) := by
  ext f
  constructor
  · intro hf
    obtain ⟨hft, hl | hr⟩ := Finset.mem_filter.mp hf
    · by_cases hfe : f = e
      · exact Finset.mem_insert.mpr (Or.inl hfe)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hfe, hft⟩, hl,
            (hc.2.2.1 f (Finset.mem_erase.mpr ⟨hfe, hft⟩)).mp hl⟩))
    · by_cases hfe : f = e
      · exact Finset.mem_insert.mpr (Or.inl hfe)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hfe, hft⟩,
            (hc.2.2.1 f (Finset.mem_erase.mpr ⟨hfe, hft⟩)).mpr hr, hr⟩))
  · intro hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · refine Finset.mem_filter.mpr ⟨hc.1, ?_⟩
      rcases hc.2.1 with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    · obtain ⟨hf, hl, _hr⟩ := Finset.mem_filter.mp hf
      exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hf).2, Or.inl hl⟩

/-- The literal one-exit pattern forces its complete support to be the cut component. -/
theorem component_eq_of_incident_pattern (t : G.SpanningTree) (F : Set V)
    (H : Finset E) (hH : G.is_tree F H) (x : V) (hx : x ∈ F) (e : E)
    (he : (G.left e = x ∧ G.right e ∉ F) ∨
      (G.right e = x ∧ G.left e ∉ F))
    (hpattern : incidentEdges G F t.val = insert e H) :
    G.componentAfter t.val e x = F := by
  have heH : e ∉ H := by
    intro heH
    have hs := hH.2.1 e heH
    rcases he with h | h
    · exact h.2 hs.2
    · exact h.2 hs.1
  have hHsub : H ⊆ t.val.erase e := by
    intro f hf
    have hi : f ∈ incidentEdges G F t.val := by
      rw [hpattern]
      exact Finset.mem_insert_of_mem hf
    refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_filter.mp hi).1⟩
    intro hfe
    exact heH (hfe ▸ hf)
  have hside : ∀ f ∈ t.val.erase e, G.left f ∈ F ↔ G.right f ∈ F := by
    intro f hf
    have hfe := (Finset.mem_erase.mp hf).1
    have hft := (Finset.mem_erase.mp hf).2
    have hm (hinc : G.left f ∈ F ∨ G.right f ∈ F) : f ∈ H := by
      have hi : f ∈ incidentEdges G F t.val := Finset.mem_filter.mpr ⟨hft, hinc⟩
      rw [hpattern] at hi
      exact (Finset.mem_insert.mp hi).resolve_left hfe
    exact ⟨fun hl => (hH.2.1 f (hm (Or.inl hl))).2,
      fun hr => (hH.2.1 f (hm (Or.inr hr))).1⟩
  ext y
  constructor
  · intro hy
    exact (G.reaches_mem_iff hside hy).mp hx
  · intro hy
    exact G.reaches_mono hHsub (hH.2.2.1 x hx y hy)

/-- The author's finite union representation, retaining the original spanning tree,
root and individual outgoing edge copy. No cut or component equality is an input. -/
theorem past_subset_iff_exists_incident_tree (t : G.SpanningTree) (r x : V)
    (hne : x ≠ r) (W : Finset V) (hr : r ∉ W) :
    G.past t r x hne ⊆ (W : Set V) ↔
      ∃ F : Finset V, F ⊆ W ∧ x ∈ F ∧ ∃ H : Finset E,
        G.is_tree (F : Set V) H ∧ ∃ e : E,
          ((G.left e = x ∧ G.right e ∉ F) ∨
            (G.right e = x ∧ G.left e ∉ F)) ∧
          incidentEdges G (F : Set V) t.val = insert e H := by
  constructor
  · intro hW
    let C := G.past t r x hne
    let F := (Set.toFinite C).toFinset
    have hFC : (F : Set V) = C := Set.Finite.coe_toFinset _
    have hx : x ∈ C := Relation.ReflTransGen.refl
    let e := G.parentEdge t r x hne
    have he := G.parentEdge_spec t r x hne
    have hc : G.cut_components C t.val e :=
      G.cut_components_at_source t e he.1 x
    let H := G.internalEdges C (t.val.erase e)
    have hH : G.is_tree C H := G.is_tree_internalEdges ⟨x, hx⟩ hc.2.2.1
      hc.2.2.2.1 (G.is_forest_mono (Finset.erase_subset _ _) t.property.2.2.2)
    refine ⟨F, ?_, ?_, H, ?_, e, ?_, ?_⟩
    · intro y hy
      exact hW ((Set.Finite.mem_toFinset _).mp hy)
    · exact (Set.Finite.mem_toFinset _).mpr hx
    · simpa only [hFC] using hH
    · rcases he.2 with h | h
      · refine Or.inl ⟨h.1, ?_⟩
        rw [← hFC] at hc
        rcases hc.2.1 with hl | hr'
        · exact hl.2
        · exact False.elim (hr'.1 (h.1 ▸ (hFC ▸ hx)))
      · refine Or.inr ⟨h.1, ?_⟩
        rw [← hFC] at hc
        rcases hc.2.1 with hl | hr'
        · exact False.elim (hl.2 (h.1 ▸ (hFC ▸ hx)))
        · exact hr'.1
    · calc
        incidentEdges G (F : Set V) t.val = incidentEdges G C t.val :=
          congrArg (fun A : Set V => incidentEdges G A t.val) hFC
        _ = insert e H := incident_edges_eq_insert_internal G t C e hc
  · rintro ⟨F, hFW, hxF, H, hH, e, he, hpattern⟩
    have heT : e ∈ t.val := by
      have hi : e ∈ incidentEdges G (F : Set V) t.val := by
        rw [hpattern]
        exact Finset.mem_insert_self _ _
      exact ((mem_incidentEdges G (F : Set V) t.val e).mp hi).1
    have hcomp := component_eq_of_incident_pattern G t (F : Set V) H hH x hxF e he hpattern
    have hc : G.cut_components (F : Set V) t.val e := by
      rw [← hcomp]
      exact G.cut_components_at_source t e heT x
    let p : G.CutTree (F : Set V) := ⟨(t.val, e), t.property, hc⟩
    have hrF : r ∉ (F : Set V) := fun h => hr (hFW h)
    have hve : G.left e = x ∨ G.right e = x := he.imp And.left And.left
    have hpast : G.past t r x hne = (F : Set V) := by
      rw [G.past_eq_descendants]
      exact G.descendants_eq_cut p r x hrF hxF hve
    rw [hpast]
    exact hFW

end

end FiniteAvalanches.Trees.Multigraph.CurrentPastPattern
