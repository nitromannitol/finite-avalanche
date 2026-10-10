import FiniteAvalanches.Trees.Past
import Mathlib.Data.Fintype.Card

/-! Fixed original-copy insertion and deletion across all source supports.
This is finite graph infrastructure, without a tree-tail assertion. -/
namespace FiniteAvalanches.Trees.Multigraph
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
variable (G : Multigraph V E)

omit [DecidableEq E] in
/-- A finite copied path from the inside to the outside has a crossing copy. -/
theorem exists_crossing_of_reaches {F : Finset E} {C : Set V} {o y : V}
    (hp : G.reaches F o y) (ho : o ∈ C) (hy : y ∉ C) :
    ∃ f ∈ F, G.crosses C f := by
  by_contra hn
  have hs : ∀ f ∈ F, G.left f ∈ C ↔ G.right f ∈ C := by
    intro f hf
    have hc : ¬G.crosses C f := fun hc => hn ⟨f, hf, hc⟩
    constructor
    · intro hl
      by_contra hr
      exact hc (Or.inl ⟨hl, hr⟩)
    · intro hr
      by_contra hl
      exact hc (Or.inr ⟨hl, hr⟩)
  exact hy ((G.reaches_mem_iff hs hp).mp ho)

/-- The literal deletion component recovers the complete designated support. -/
theorem componentAfter_eq_of_cut {C : Set V} {t : Finset E} {f : E} {o : V}
    (hc : G.cut_components C t f) (ho : o ∈ C) :
    G.componentAfter t f o = C := by
  ext x
  constructor
  · intro hx
    exact (G.reaches_mem_iff hc.2.2.1 hx).mp ho
  · intro hx
    exact hc.2.2.2.1 o ho x hx

theorem cut_components_compl {C : Set V} {t : Finset E} {f : E}
    (hc : G.cut_components C t f) : G.cut_components Cᶜ t f := by
  refine ⟨hc.1, ?_, fun e he => not_congr (hc.2.2.1 e he), hc.2.2.2.2, ?_⟩
  · rcases hc.2.1 with h | h
    · exact Or.inr ⟨by simpa only [Set.mem_compl_iff, not_not] using h.1, h.2⟩
    · exact Or.inl ⟨h.1, by simpa only [Set.mem_compl_iff, not_not] using h.2⟩
  · simpa only [compl_compl] using hc.2.2.2.1

/-- Every actual tree copy has exactly two deletion components; the component
of any prescribed vertex is one of them, without selecting a new forest. -/
theorem cut_components_at_source (t : G.SpanningTree) (f : E) (hf : f ∈ t.val)
    (o : V) : G.cut_components (G.componentAfter t.val f o) t.val f := by
  let C := G.componentAfter t.val f (G.left f)
  have hc : G.cut_components C t.val f :=
    G.cut_components_componentAfter t f hf (G.left f) (G.right f) (Or.inl ⟨rfl, rfl⟩)
  by_cases ho : o ∈ C
  · rw [G.componentAfter_eq_of_cut hc ho]
    exact hc
  · have hd := G.cut_components_compl hc
    rw [G.componentAfter_eq_of_cut hd ho]
    exact hd

/-- All supports containing the source and excluding the sink, not only connected ones. -/
abbrev SourceCutSupport (o r : V) := {C : Set V // o ∈ C ∧ r ∉ C}

/-- Both actual component-tree subsets and a fixed original crossing copy. -/
abbrev FixedEdgeForest (o r : V) (f : E) :=
  (C : SourceCutSupport o r) ×
    {_p : G.ComponentTree C.val × G.ComponentTree C.valᶜ // G.crosses C.val f}

/-- Deletion separates source and sink. This is the literal tree-path edge criterion. -/
abbrev SeparatingTree (o r : V) (f : E) :=
  {t : G.SpanningTree // f ∈ t.val ∧ ¬G.reaches (t.val.erase f) o r}

def insertFixedEdge (o r : V) (f : E) (p : G.FixedEdgeForest o r f) :
    G.SeparatingTree o r f := by
  let t : G.SpanningTree := ⟨insert f (p.2.val.1.val ∪ p.2.val.2.val),
    G.is_tree_insert_union_of_crosses p.2.val.1.property p.2.val.2.property p.2.property⟩
  have hc := G.cut_components_insert_union p.2.val.1.property p.2.val.2.property p.2.property
  refine ⟨t, Finset.mem_insert_self _ _, ?_⟩
  intro h
  exact p.1.property.2 ((G.reaches_mem_iff hc.2.2.1 h).mp p.1.property.1)

theorem componentAfter_insertFixedEdge (o r : V) (f : E)
    (p : G.FixedEdgeForest o r f) :
    G.componentAfter (G.insertFixedEdge o r f p).val.val f o = p.1.val :=
  G.componentAfter_eq_of_cut
    (G.cut_components_insert_union p.2.val.1.property p.2.val.2.property p.2.property)
    p.1.property.1

def deleteFixedEdge (o r : V) (f : E) (t : G.SeparatingTree o r f) :
    G.FixedEdgeForest o r f := by
  let C : SourceCutSupport o r :=
    ⟨G.componentAfter t.val.val f o, Relation.ReflTransGen.refl, t.property.2⟩
  let q : G.CutTree C.val := ⟨(t.val.val, f), t.val.property,
    G.cut_components_at_source t.val f t.property.1 o⟩
  let p := G.split C.val q
  exact ⟨C, ⟨(⟨p.val.1, p.property.1⟩, ⟨p.val.2.1, p.property.2.1⟩),
    p.property.2.2⟩⟩

theorem insertFixedEdge_injective (o r : V) (f : E) :
    Function.Injective (G.insertFixedEdge o r f) := by
  intro p q h
  have hC : p.1 = q.1 := Subtype.ext (by
    rw [← G.componentAfter_insertFixedEdge o r f p,
      ← G.componentAfter_insertFixedEdge o r f q, h])
  rcases p with ⟨C, p⟩
  rcases q with ⟨D, q⟩
  dsimp only at hC
  subst D
  apply congrArg (Sigma.mk C)
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    have hi := congrArg (fun t : G.SeparatingTree o r f => G.internalEdges C.val t.val.val) h
    simpa only [insertFixedEdge, G.internalEdges_insert_union
      p.val.1.property.2.1 p.val.2.property.2.1 p.property,
      G.internalEdges_insert_union q.val.1.property.2.1 q.val.2.property.2.1 q.property] using hi
  · apply Subtype.ext
    have hi := congrArg (fun t : G.SeparatingTree o r f => G.internalEdges C.valᶜ t.val.val) h
    have hp : G.internalEdges C.valᶜ (insert f (p.val.1.val ∪ p.val.2.val)) = p.val.2.val := by
      rw [Finset.union_comm]
      exact G.internalEdges_insert_union p.val.2.property.2.1
        (by simpa only [compl_compl] using p.val.1.property.2.1)
        (G.cut_components_compl (G.cut_components_insert_union
          p.val.1.property p.val.2.property p.property)).2.1
    have hq : G.internalEdges C.valᶜ (insert f (q.val.1.val ∪ q.val.2.val)) = q.val.2.val := by
      rw [Finset.union_comm]
      exact G.internalEdges_insert_union q.val.2.property.2.1
        (by simpa only [compl_compl] using q.val.1.property.2.1)
        (G.cut_components_compl (G.cut_components_insert_union
          q.val.1.property q.val.2.property q.property)).2.1
    simpa only [insertFixedEdge, hp, hq] using hi

theorem insert_deleteFixedEdge (o r : V) (f : E) (t : G.SeparatingTree o r f) :
    G.insertFixedEdge o r f (G.deleteFixedEdge o r f t) = t := by
  apply Subtype.ext
  apply Subtype.ext
  change insert f (G.internalEdges (G.componentAfter t.val.val f o) (t.val.val.erase f) ∪
    G.internalEdges (G.componentAfter t.val.val f o)ᶜ (t.val.val.erase f)) = t.val.val
  rw [G.internalEdges_union_compl
    (G.cut_components_at_source t.val f t.property.1 o).2.2.1,
    Finset.insert_erase t.property.1]

/-- Insertion and literal deletion are global inverses, preserving both copied subsets. -/
def fixedEdgeForestEquiv (o r : V) (f : E) :
    G.FixedEdgeForest o r f ≃ G.SeparatingTree o r f where
  toFun := G.insertFixedEdge o r f
  invFun := G.deleteFixedEdge o r f
  left_inv _ := G.insertFixedEdge_injective o r f (G.insert_deleteFixedEdge o r f _)
  right_inv := G.insert_deleteFixedEdge o r f

end
end FiniteAvalanches.Trees.Multigraph
