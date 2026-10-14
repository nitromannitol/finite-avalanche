import FiniteAvalanches.Sandpile.Components.Incident

/-! Literal induced copied-edge graphs and their field vertex carriers. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Trees
open scoped Classical
noncomputable section

/-- Restriction retains the actual original copies with both endpoints in the support. -/
abbrev InducedEdge {N : ℕ} (V : Set (FiniteWired.Vertex N)) :=
  {e : FiniteWired.Edge N //
    (FiniteWired.endpoints e).1 ∈ V ∧ (FiniteWired.endpoints e).2 ∈ V}

def inducedGraph {N : ℕ} (V : Set (FiniteWired.Vertex N)) :
    Multigraph V (InducedEdge V) where
  left e := ⟨(FiniteWired.endpoints e.val).1, e.property.1⟩
  right e := ⟨(FiniteWired.endpoints e.val).2, e.property.2⟩
  loopless e he := FiniteWired.endpoints_ne e.val (congrArg Subtype.val he)

abbrev insideSupport {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Set (FiniteWired.Vertex N) := {v | insideVertex C.val v}
abbrev outsideSupport {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Set (FiniteWired.Vertex N) := {v | outsideVertex C.val v}

/-- The inside sink is the actual source. -/
def innerRoot {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) : insideSupport C :=
  ⟨some o, C.property.2⟩
/-- The outside sink is the original canonical none vertex. -/
def outerRoot {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) : outsideSupport C :=
  ⟨none, True.intro⟩

/-- Exactly the lattice vertices of C, including the source. -/
def insideVertexEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    insideSupport C ≃ {x : Site2 // x ∈ C.val} where
  toFun v := match v with
    | ⟨none, hv⟩ => hv.elim
    | ⟨some x, hx⟩ => ⟨FiniteWired.site x, hx⟩
  invFun x := ⟨some (FiniteWired.activeOfSite N x.val
    ((mem_box_sites N _).mp (C.property.1 x.property))), x.property⟩
  left_inv v := by
    rcases v with ⟨_ | x, hv⟩
    · exact hv.elim
    · apply Subtype.ext
      apply congrArg some
      apply FiniteWired.site_injective N
      rfl
  right_inv x := Subtype.ext rfl

/-- Removing the actual source leaves exactly the inner field domain. -/
def innerVertexEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    {v : insideSupport C // v ≠ innerRoot C} ≃
      {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)} where
  toFun v := ⟨(insideVertexEquiv C v.val).val, Finset.mem_erase.mpr ⟨by
    intro he
    apply v.property
    apply (insideVertexEquiv C).injective
    apply Subtype.ext
    exact he, (insideVertexEquiv C v.val).property⟩⟩
  invFun x := ⟨(insideVertexEquiv C).symm ⟨x.val, (Finset.mem_erase.mp x.property).2⟩, by
    intro he
    apply (Finset.mem_erase.mp x.property).1
    have hh := congrArg (fun v => (insideVertexEquiv C v).val) he
    rw [Equiv.apply_symm_apply] at hh
    change x.val = FiniteWired.site o at hh
    exact hh⟩
  left_inv v := by
    apply Subtype.ext
    exact (insideVertexEquiv C).symm_apply_apply v.val
  right_inv x := by
    apply Subtype.ext
    exact congrArg (fun y : {x : Site2 // x ∈ C.val} => y.val)
      ((insideVertexEquiv C).apply_symm_apply ⟨x.val, (Finset.mem_erase.mp x.property).2⟩)

/-- Removing none leaves exactly the active complement, with no off-volume sites. -/
def outerVertexEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    {v : outsideSupport C // v ≠ outerRoot C} ≃
      {x : Site2 // x ∈ boxSites N \ C.val} where
  toFun v := match v with
    | ⟨⟨none, _⟩, hv⟩ => (hv (Subtype.ext rfl)).elim
    | ⟨⟨some x, hx⟩, _⟩ =>
        ⟨FiniteWired.site x, Finset.mem_sdiff.mpr ⟨site_mem_box x, hx⟩⟩
  invFun x := ⟨⟨some (FiniteWired.activeOfSite N x.val
    ((mem_box_sites N _).mp (Finset.mem_sdiff.mp x.property).1)),
      (Finset.mem_sdiff.mp x.property).2⟩, by
        intro he
        have hh := congrArg Subtype.val he
        cases hh⟩
  left_inv v := by
    rcases v with ⟨⟨_ | x, hx⟩, hv⟩
    · exact (hv (Subtype.ext rfl)).elim
    · apply Subtype.ext
      apply Subtype.ext
      apply congrArg some
      apply FiniteWired.site_injective N
      rfl
  right_inv x := Subtype.ext rfl

/-- Degree counts original copies, rather than identifying parallel edges. -/
def inducedDegree {N : ℕ} (V : Set (FiniteWired.Vertex N)) (x : FiniteWired.Active N) : ℕ :=
  (inducedIncidentCopies V x).card

theorem inner_degree_eq {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (x : {x : FiniteWired.Active N // FiniteWired.site x ∈ C.val}) :
    inducedDegree (insideSupport C) x.val = degree C.val (FiniteWired.site x.val) := by
  rw [inducedDegree, ← inner_incident_copies_eq C x, card_inner_incident_copies]

theorem outer_degree_eq {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (x : {x : FiniteWired.Active N // FiniteWired.site x ∉ C.val}) :
    inducedDegree (outsideSupport C) x.val = 4 - degree C.val (FiniteWired.site x.val) := by
  rw [inducedDegree, ← outer_incident_copies_eq C x, card_outer_incident_copies]

/-- The endpoint-filter degree is exactly the incidence degree in the subtype graph. -/
def inducedIncidentEquiv {N : ℕ} (V : Set (FiniteWired.Vertex N))
    (x : FiniteWired.Active N) :
    {e : FiniteWired.Edge N // e ∈ inducedIncidentCopies V x} ≃
      {e : InducedEdge V //
        ((inducedGraph V).left e).val = some x ∨ ((inducedGraph V).right e).val = some x} where
  toFun e := by
    have he := (Finset.mem_filter.mp e.property).2
    exact ⟨⟨e.val, he.2⟩, he.1⟩
  invFun e := ⟨e.val.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.property, e.val.property⟩⟩
  left_inv e := Subtype.ext rfl
  right_inv e := by
    apply Subtype.ext
    exact Subtype.ext rfl

theorem induced_degree_eq_graph_degree {N : ℕ}
    (V : Set (FiniteWired.Vertex N)) (x : FiniteWired.Active N) :
    inducedDegree V x = Fintype.card {e : InducedEdge V //
      ((inducedGraph V).left e).val = some x ∨ ((inducedGraph V).right e).val = some x} := by
  rw [← Fintype.card_congr (inducedIncidentEquiv V x)]
  exact (Fintype.card_coe _).symm

                                                                                          
theorem internal_copy_degree {N : ℕ} {A : Finset Site2} (hA : A ⊆ boxSites N)
    (x : FiniteWired.Active N) (hx : FiniteWired.site x ∈ A) :
    inducedDegree {v | insideVertex A v} x = degree A (FiniteWired.site x) := by
  let C : ComponentShape x := ⟨A, hA, hx⟩
  exact inner_degree_eq C ⟨x, hx⟩

/-- The two supports partition all original vertices; none is always outside. -/
theorem inside_complement {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    (insideSupport C)ᶜ = outsideSupport C := by
  ext v
  cases v <;> simp [insideSupport, outsideSupport, insideVertex, outsideVertex]

/-- Component trees use ordinary spanning-tree edge subsets of the canonical copied graph. -/
abbrev InnerTrees {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  (WiredTrees.graph N).ComponentTree (insideSupport C)
abbrev OuterTrees {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  (WiredTrees.graph N).ComponentTree (outsideSupport C)

end
end FiniteAvalanches.Sandpile.Components
