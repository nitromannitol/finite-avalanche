import FiniteAvalanches.Sandpile.Components.TreeMass

/-! Exact support carriers for the finite reciprocal sum. Every source-containing
lattice shape corresponds to one set of original vertices excluding the sink. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open MeasureTheory
open scoped Classical
noncomputable section

abbrev SourceSupport {N : ℕ} (o : FiniteWired.Active N) :=
  {D : Set (FiniteWired.Vertex N) // some o ∈ D ∧ none ∉ D}

def shapeOfSupport {N : ℕ} {o : FiniteWired.Active N} (D : SourceSupport o) :
    ComponentShape o :=
  ⟨((Finset.univ : Finset (FiniteWired.Active N)).filter fun x => some x ∈ D.val).image
      FiniteWired.site, by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact site_mem_box y, by
    exact Finset.mem_image.mpr ⟨o, Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.property.1⟩, rfl⟩⟩

theorem mem_shape_of_support {N : ℕ} {o : FiniteWired.Active N}
    (D : SourceSupport o) (x : FiniteWired.Active N) :
    FiniteWired.site x ∈ (shapeOfSupport D).val ↔ some x ∈ D.val := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    have hxy : y = x := FiniteWired.site_injective N he
    subst y
    exact (Finset.mem_filter.mp hy).2
  · intro hx
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

theorem inside_shape_of_support {N : ℕ} {o : FiniteWired.Active N}
    (D : SourceSupport o) : insideSupport (shapeOfSupport D) = D.val := by
  ext v
  cases v with
  | none => exact iff_of_false (by simp [insideSupport, insideVertex]) D.property.2
  | some x => exact mem_shape_of_support D x

theorem shape_of_inside_support {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) :
    shapeOfSupport ⟨insideSupport C, C.property.2, by simp [insideSupport, insideVertex]⟩ = C := by
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hy).2
  · intro x hx
    let y := FiniteWired.activeOfSite N x ((mem_box_sites N x).mp (C.property.1 hx))
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

/-- Both inverses retain the entire original vertex support. -/
def shapeSupportEquiv {N : ℕ} (o : FiniteWired.Active N) :
    ComponentShape o ≃ SourceSupport o where
  toFun C := ⟨insideSupport C, C.property.2, by simp [insideSupport, insideVertex]⟩
  invFun := shapeOfSupport
  left_inv := shape_of_inside_support
  right_inv D := Subtype.ext (inside_shape_of_support D)

def markedSites {N : ℕ} (S : Finset (FiniteWired.Active N)) : Finset Site2 :=
  S.image FiniteWired.site

def markedVertices {N : ℕ} (S : Finset (FiniteWired.Active N)) : Set (FiniteWired.Vertex N) :=
  {v | ∃ x ∈ S, some x = v}

theorem marked_subset_iff {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (C : ComponentShape o) :
    markedSites S ⊆ C.val ↔ markedVertices S ⊆ insideSupport C := by
  constructor
  · rintro h v ⟨x, hx, rfl⟩
    exact h (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact h ⟨y, hy, rfl⟩

abbrev PositiveCoreShape {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N)) :=
  {C : ComponentShape o // markedSites S ⊆ C.val ∧
    0 < Fintype.card (InnerTrees C) ∧ 0 < Fintype.card (OuterTrees C)}

/-- The positive core range is precisely the range in ordinary-tree counting. -/
def positiveSupportEquiv {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (ho : o ∈ S) :
    PositiveCoreShape o S ≃ (WiredTrees.graph N).PositiveSupport none (markedVertices S) where
  toFun C := ⟨insideSupport C.val, (marked_subset_iff S C.val).mp C.property.1,
    by simp [insideSupport, insideVertex], C.property.2.1, by
      simpa only [inside_complement] using C.property.2.2⟩
  invFun D := by
    let A : SourceSupport o := ⟨D.val, D.property.1 ⟨o, ho, rfl⟩, D.property.2.1⟩
    refine ⟨shapeOfSupport A, ?_, ?_, ?_⟩
    · apply (marked_subset_iff S (shapeOfSupport A)).mpr
      rw [inside_shape_of_support]
      exact D.property.1
    · change 0 < Fintype.card ((WiredTrees.graph N).ComponentTree (insideSupport (shapeOfSupport A)))
      rw [inside_shape_of_support]
      exact D.property.2.2.1
    · change 0 < Fintype.card ((WiredTrees.graph N).ComponentTree (outsideSupport (shapeOfSupport A)))
      rw [← inside_complement, inside_shape_of_support]
      exact D.property.2.2.2
  left_inv C := by
    apply Subtype.ext
    exact shape_of_inside_support C.val
  right_inv D := by
    apply Subtype.ext
    exact inside_shape_of_support _

theorem marked_vertices_nonempty {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (ho : o ∈ S) : (markedVertices S).Nonempty :=
  ⟨some o, o, ho, rfl⟩

/-- The actual core-event mass is exactly the coefficient in the reciprocal sum. -/
theorem integral_reciprocal_eq_core_mass {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (ho : o ∈ S) :
    (∫ t, WiredTrees.reciprocal N (markedVertices S) (marked_vertices_nonempty S ho) t
      ∂WiredTrees.law N) =
      ∑ C : PositiveCoreShape o S,
        (puncturedCountingMeasure o).real (coreEvent C.val) *
          ((WiredTrees.graph N).componentLaw (positiveSupportEquiv S ho C)).real
            ((WiredTrees.graph N).insideContact (positiveSupportEquiv S ho C)) := by
  rw [WiredTrees.reciprocal_identity]
  rw [← Equiv.sum_comp (positiveSupportEquiv S ho)]
  apply Finset.sum_congr rfl
  intro C _
  rw [core_event_tree_mass_compl]
  rfl


end
end FiniteAvalanches.Sandpile.Components
