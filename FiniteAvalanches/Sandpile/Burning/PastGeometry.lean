module

public import FiniteAvalanches.Sandpile.Burning.TreeInverse

@[expose] public section

/-! The actual union of rooted pasts determines its own sink exclusion and held
inclusion. Its complement is closed under root paths, and every tree copy crossing
its boundary enters at a held vertex. No such geometry is supplied as an input. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open FiniteAvalanches.Trees.RootedPaths
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

/-- Literal union of outgoing-edge pasts, including each held vertex itself. -/
def treePastUnion (t : (copiedTreeGraph G).SpanningTree) (B : Finset (SourceVertex s)) : Finset V :=
  Finset.univ.filter fun x => ∃ b ∈ B,
    x ∈ (copiedTreeGraph G).past t s b.val (source_vertex_ne_sink s b)

theorem mem_tree_past_union (t : (copiedTreeGraph G).SpanningTree)
    (B : Finset (SourceVertex s)) (x : V) :
    x ∈ treePastUnion G s t B ↔ ∃ b ∈ B,
      ancestor ((copiedTreeGraph G).toSimple_isTree t.property) s b.val x := by
  simp only [treePastUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    FiniteAvalanches.Trees.Multigraph.past_eq_descendants,
    FiniteAvalanches.Trees.Multigraph.descendants, Set.mem_setOf_eq]

theorem tree_past_union_avoids_sink (t : (copiedTreeGraph G).SpanningTree)
    (B : Finset (SourceVertex s)) : s ∉ treePastUnion G s t B := by
  intro hs
  obtain ⟨b, hb, ha⟩ := (mem_tree_past_union G s t B s).mp hs
  exact source_vertex_ne_sink s b (ancestor_antisymm _ ha (ancestor_root _ s b.val))

theorem held_subset_tree_past_union (t : (copiedTreeGraph G).SpanningTree)
    (B : Finset (SourceVertex s)) : B.image Subtype.val ⊆ treePastUnion G s t B := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
  exact (mem_tree_past_union G s t B b.val).mpr ⟨b, hb, ancestor_refl _ s b.val⟩

theorem tree_past_union_empty (t : (copiedTreeGraph G).SpanningTree) :
    treePastUnion G s t ∅ = ∅ := by simp [treePastUnion]

/-- Every vertex of a root path to the complement remains in the complement. -/
theorem root_path_avoids_tree_past_union (t : (copiedTreeGraph G).SpanningTree)
    (B : Finset (SourceVertex s)) (x : V) (hx : x ∉ treePastUnion G s t B)
    (z : V) (hz : z ∈ (path ((copiedTreeGraph G).toSimple_isTree t.property) s x).support) :
    z ∉ treePastUnion G s t B := by
  intro ha
  obtain ⟨b, hb, hba⟩ := (mem_tree_past_union G s t B z).mp ha
  exact hx ((mem_tree_past_union G s t B x).mpr ⟨b, hb, ancestor_trans _ hba hz⟩)

/-- The inside endpoint of an actual crossing tree copy belongs to the held set. -/
theorem tree_past_union_crossing_held (t : (copiedTreeGraph G).SpanningTree)
    (B : Finset (SourceVertex s)) (x y : V)
    (ha : (copiedTreeGraph G).adjacent t.val x y)
    (hx : x ∈ treePastUnion G s t B) (hy : y ∉ treePastUnion G s t B) :
    x ∈ B.image Subtype.val := by
  let hT := (copiedTreeGraph G).toSimple_isTree t.property
  have hnot : x ∉ (path hT s y).support := root_path_avoids_tree_past_union G s t B y hy x
    |>.mt (fun h => h hx)
  have hadj : ((copiedTreeGraph G).toSimple t.val).Adj y x :=
    (copiedTreeGraph G).adjacent_symm ha
  have hp : path hT s x = (path hT s y).concat hadj :=
    path_eq hT _ ((path_isPath hT s y).concat hnot hadj)
  obtain ⟨b, hb, hbx⟩ := (mem_tree_past_union G s t B x).mp hx
  change b.val ∈ (path hT s x).support at hbx
  rw [hp, SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hbx
  rcases hbx with hby | he
  · exact False.elim (hy ((mem_tree_past_union G s t B y).mpr ⟨b, hb, hby⟩))
  · exact he ▸ Finset.mem_image_of_mem Subtype.val hb

end
end FiniteAvalanches.Sandpile.Burning
