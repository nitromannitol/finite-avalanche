import FiniteAvalanches.Sandpile.Components.Graphs

/-! Component height bounds equal the actual degrees of the induced copied-edge graphs. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Degree on every vertex of the literal induced graph, including its sink. -/
def graphDegree {N : ℕ} (V : Set (FiniteWired.Vertex N)) (v : V) : ℕ :=
  Fintype.card {e : InducedEdge V // (inducedGraph V).left e = v ∨ (inducedGraph V).right e = v}

def graphIncidentEquiv {N : ℕ} (V : Set (FiniteWired.Vertex N))
    (x : FiniteWired.Active N) (hx : some x ∈ V) :
    {e : InducedEdge V //
      ((inducedGraph V).left e).val = some x ∨ ((inducedGraph V).right e).val = some x} ≃
    {e : InducedEdge V //
      (inducedGraph V).left e = ⟨some x, hx⟩ ∨ (inducedGraph V).right e = ⟨some x, hx⟩} where
  toFun e := ⟨e.val, e.property.elim (fun h => Or.inl (Subtype.ext h))
    (fun h => Or.inr (Subtype.ext h))⟩
  invFun e := ⟨e.val, e.property.elim (fun h => Or.inl (congrArg Subtype.val h))
    (fun h => Or.inr (congrArg Subtype.val h))⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem graph_degree_some {N : ℕ} (V : Set (FiniteWired.Vertex N))
    (x : FiniteWired.Active N) (hx : some x ∈ V) :
    graphDegree V ⟨some x, hx⟩ = inducedDegree V x := by
  rw [graphDegree, induced_degree_eq_graph_degree,
    Fintype.card_congr (graphIncidentEquiv V x hx)]

theorem inner_graph_degree_eq {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (v : insideSupport C) :
    graphDegree (insideSupport C) v = degree C.val ((insideVertexEquiv C v).val) := by
  rcases v with ⟨_ | x, hx⟩
  · exact hx.elim
  · exact (graph_degree_some (insideSupport C) x hx).trans (inner_degree_eq C ⟨x, hx⟩)

theorem outer_graph_degree_eq {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (v : {v : outsideSupport C // v ≠ outerRoot C}) :
    graphDegree (outsideSupport C) v.val = 4 - degree C.val ((outerVertexEquiv C v).val) := by
  rcases v with ⟨⟨_ | x, hx⟩, hv⟩
  · exact (hv (Subtype.ext rfl)).elim
  · exact (graph_degree_some (outsideSupport C) x hx).trans (outer_degree_eq C ⟨x, hx⟩)

/-- Stable fields on the actual inner graph, with its source sink removed. -/
abbrev InnerGraphField {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  (v : {v : insideSupport C // v ≠ innerRoot C}) → Fin (graphDegree (insideSupport C) v.val)
/-- Stable fields on the actual outer graph, with the canonical none sink removed. -/
abbrev OuterGraphField {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  (v : {v : outsideSupport C // v ≠ outerRoot C}) → Fin (graphDegree (outsideSupport C) v.val)

/-- Every inner coordinate and its entire Fin degree bound agree with the induced graph. -/
def innerFieldGraphEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    InnerGraphField C ≃ InnerField o C :=
  (innerVertexEquiv C).piCongr (fun v =>
    finCongr (inner_graph_degree_eq C v.val))

/-- Every outer coordinate and its entire Fin degree bound agree with the induced graph. -/
def outerFieldGraphEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    OuterGraphField C ≃ OuterField C :=
  (outerVertexEquiv C).piCongr (fun v => finCongr (outer_graph_degree_eq C v))

/-- Forbidden-subconfiguration degrees are literal original copy counts for every subset. -/
theorem allowedOn_iff_copy_test {N : ℕ} {V : Finset Site2} (hV : V ⊆ boxSites N)
    (r : {x : Site2 // x ∈ V} → ℕ) :
    allowedOn V r ↔ ∀ (A : Finset Site2) (hA : A ⊆ V),
      ¬(A.Nonempty ∧ ∀ (x : Site2) (hx : x ∈ A),
        r ⟨x, hA hx⟩ < inducedDegree {v | insideVertex A v}
          (FiniteWired.activeOfSite N x ((mem_box_sites N x).mp (hV (hA hx))))) := by
  have hd : ∀ (A : Finset Site2) (hA : A ⊆ V) (x : Site2) (hx : x ∈ A),
      inducedDegree {v | insideVertex A v}
        (FiniteWired.activeOfSite N x ((mem_box_sites N x).mp (hV (hA hx)))) = degree A x := by
    intro A hA x hx
    exact internal_copy_degree (hA.trans hV) _ hx
  constructor
  · intro ha A hA hf
    apply ha A hA
    exact ⟨hf.1, fun x hx => by simpa only [hd A hA x hx] using hf.2 x hx⟩
  · intro ha A hA hf
    apply ha A hA
    exact ⟨hf.1, fun x hx => by simpa only [hd A hA x hx] using hf.2 x hx⟩

/-- The inner allowed predicate uses the actual induced graph for every source-free subset. -/
theorem inner_allowed_copy_test {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (r : InnerField o C) :
    allowedOn (C.val.erase (FiniteWired.site o)) (fun x => (r x).val) ↔
      ∀ (A : Finset Site2) (hA : A ⊆ C.val.erase (FiniteWired.site o)),
        ¬(A.Nonempty ∧ ∀ (x : Site2) (hx : x ∈ A),
          (r ⟨x, hA hx⟩).val < inducedDegree {v | insideVertex A v}
            (FiniteWired.activeOfSite N x ((mem_box_sites N x).mp
              (C.property.1 (Finset.mem_erase.mp (hA hx)).2)))) :=
  allowedOn_iff_copy_test ((Finset.erase_subset _ _).trans C.property.1) _

/-- The outer allowed predicate uses all actual outside subsets, with no missing vertices. -/
theorem outer_allowed_copy_test {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (r : OuterField C) :
    allowedOn (boxSites N \ C.val) (fun x => (r x).val) ↔
      ∀ (A : Finset Site2) (hA : A ⊆ boxSites N \ C.val),
        ¬(A.Nonempty ∧ ∀ (x : Site2) (hx : x ∈ A),
          (r ⟨x, hA hx⟩).val < inducedDegree {v | insideVertex A v}
            (FiniteWired.activeOfSite N x ((mem_box_sites N x).mp
              (Finset.mem_sdiff.mp (hA hx)).1))) :=
  allowedOn_iff_copy_test Finset.sdiff_subset _

end
end FiniteAvalanches.Sandpile.Components
