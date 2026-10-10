module

public import FiniteAvalanches.Sandpile.Burning.SpanningTree

@[expose] public section

/-! Root distance is the length of the unique simple path in the actual copied
spanning tree. Its unique original parent copy is already certified by the
canonical tree API before rank-defined heights are introduced. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open FiniteAvalanches.Trees.RootedPaths
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

/-- Actual tree distance to the sink, without an artificial distance witness. -/
def treeDistance (t : (copiedTreeGraph G).SpanningTree) (v : V) : ℕ :=
  (path ((copiedTreeGraph G).toSimple_isTree t.property) v s).length

omit [DecidableEq V] in
theorem tree_distance_sink (t : (copiedTreeGraph G).SpanningTree) :
    treeDistance G s t s = 0 := by
  unfold treeDistance
  rw [path_eq _ SimpleGraph.Walk.nil SimpleGraph.Walk.IsPath.nil]
  rfl

theorem tree_distance_pos (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    0 < treeDistance G s t v.val := by
  have hn := source_vertex_ne_sink s v
  have hh : treeDistance G s t v.val ≠ 0 := fun hz =>
    hn (SimpleGraph.Walk.eq_of_length_eq_zero hz)
  omega

theorem tree_parent_distance (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    treeDistance G s t
      (path ((copiedTreeGraph G).toSimple_isTree t.property) v.val s).snd + 1 =
      treeDistance G s t v.val := by
  let hT := (copiedTreeGraph G).toSimple_isTree t.property
  obtain ⟨b, hab, q, hp⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne
    (source_vertex_ne_sink s v) (path hT v.val s)
  have hq := path_isPath hT v.val s
  rw [hp, SimpleGraph.Walk.cons_isPath_iff] at hq
  have he := path_eq hT q hq.1
  change (path hT (path hT v.val s).snd s).length + 1 = (path hT v.val s).length
  rw [hp, SimpleGraph.Walk.snd_cons, he]
  rfl

/-- All original incident copies to the immediately preceding distance layer. -/
def treeParentCopies (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) : Finset E :=
  incidentInto G (Finset.univ.filter fun w => treeDistance G s t w + 1 =
    treeDistance G s t v.val) v.val

theorem tree_parent_mem (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    (copiedTreeGraph G).parentEdge t s v.val (source_vertex_ne_sink s v) ∈
      treeParentCopies G s t v := by
  have hp := (copiedTreeGraph G).parentEdge_spec t s v.val (source_vertex_ne_sink s v)
  have hd := tree_parent_distance G s t v
  simp only [treeParentCopies, incidentInto, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hp.2 with hp | hp
  · exact Or.inl ⟨hp.1, by rw [show G.right _ = _ from hp.2]; exact hd⟩
  · exact Or.inr ⟨hp.1, by rw [show G.left _ = _ from hp.2]; exact hd⟩

def treeParent (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    {e : E // e ∈ treeParentCopies G s t v} :=
  ⟨(copiedTreeGraph G).parentEdge t s v.val (source_vertex_ne_sink s v), tree_parent_mem G s t v⟩

/-- Original copies are ranked by the fixed E order, not by endpoint pairs. -/
def treeParentOrder (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    Fin (treeParentCopies G s t v).card ≃o {e : E // e ∈ treeParentCopies G s t v} :=
  (treeParentCopies G s t v).orderIsoOfFin rfl

def treeBase (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) : ℕ :=
  degreeInto G (Finset.univ.filter fun w => treeDistance G s t v.val ≤ treeDistance G s t w) v.val

def treePreviousDegree (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) : ℕ :=
  degreeInto G (Finset.univ.filter fun w =>
    treeDistance G s t v.val ≤ treeDistance G s t w + 1) v.val

theorem tree_height_interval (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    treeBase G s t v + (treeParentCopies G s t v).card = treePreviousDegree G s t v := by
  let A := Finset.univ.filter fun w => treeDistance G s t v.val ≤ treeDistance G s t w
  let B := Finset.univ.filter fun w => treeDistance G s t w + 1 = treeDistance G s t v.val
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    omega
  have hu : A ∪ B = Finset.univ.filter fun w =>
      treeDistance G s t v.val ≤ treeDistance G s t w + 1 := by
    ext w
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  change degreeInto G A v.val + degreeInto G B v.val = _
  rw [← degree_into_union G hd, hu]
  rfl

theorem tree_previous_degree_le (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    treePreviousDegree G s t v ≤ degree G v.val :=
  degree_into_le_degree G _ _

/-- Every nonsink height equals its actual late-neighbor degree plus parent-copy rank. -/
def treeHeights (t : (copiedTreeGraph G).SpanningTree) : SourceHeights G s := fun v =>
  ⟨treeBase G s t v + ((treeParentOrder G s t v).symm (treeParent G s t v)).val, by
    have hi := ((treeParentOrder G s t v).symm (treeParent G s t v)).isLt
    have hd := tree_height_interval G s t v
    have he := tree_previous_degree_le G s t v
    omega⟩

theorem tree_heights_interval (t : (copiedTreeGraph G).SpanningTree) (v : SourceVertex s) :
    treeBase G s t v ≤ (treeHeights G s t v).val ∧
      (treeHeights G s t v).val < treePreviousDegree G s t v := by
  have hi := ((treeParentOrder G s t v).symm (treeParent G s t v)).isLt
  have hd := tree_height_interval G s t v
  change treeBase G s t v ≤ treeBase G s t v + _ ∧
    treeBase G s t v + _ < treePreviousDegree G s t v
  omega

theorem tree_heights_noForbidden (t : (copiedTreeGraph G).SpanningTree) :
    noForbidden G (Finset.univ.erase s) (treeHeights G s t) := by
  intro A hA
  obtain ⟨v, hv, hmin⟩ := A.exists_min_image (fun v => treeDistance G s t v.val) hA.1
  have hs : A.image Subtype.val ⊆ Finset.univ.filter fun w =>
      treeDistance G s t v.val ≤ treeDistance G s t w := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmin x hx⟩
  have hd := degree_into_mono G hs v.val
  have hh := (tree_heights_interval G s t v).1
  have hf := hA.2 v hv
  change (treeHeights G s t v).val < degreeInto G (A.image Subtype.val) v.val at hf
  change degreeInto G _ v.val ≤ treeBase G s t v at hd
  omega

end
end FiniteAvalanches.Sandpile.Burning
