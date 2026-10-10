import FiniteAvalanches.Trees.ForestProjection.Uniform

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.Trees.Multigraph
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- The source color event on original copied subsets. -/
def forestColorEvent (C : Set V) (H : Set (Set V)) : Set (Finset E) :=
  {F | G.oneVertices F C ∈ H}

/-- A color-upward event extends to an increasing copied-edge event. -/
theorem forestColorEvent_increasing (C : Set V) (H : Set (Set V))
    (hH : ∀ U ∈ H, ∀ W : Set V, U ⊆ W → W ∈ H) :
    ∀ F ∈ G.forestColorEvent C H, ∀ e : E, insert e F ∈ G.forestColorEvent C H := by
  intro F hF e
  apply hH _ hF
  rintro v ⟨r, hr, hvr⟩
  exact ⟨r, hr, G.reaches_mono (Finset.subset_insert e F) hvr⟩

/-- A rooted forest has complementary zero and one color sets. -/
theorem oneVertices_eq_compl_zeroVertices (A C : Set V) (hAC : Disjoint A C)
    (F : G.RootedForest (A ∪ C)) : G.oneVertices F.val C = (G.oneVertices F.val A)ᶜ := by
  ext v
  constructor
  · rintro ⟨c, hc, hvc⟩ ⟨a, ha, hva⟩
    obtain ⟨r, _, _, hu⟩ := F.property.2 v
    have heq : a = c := (hu a (Or.inl ha) hva).trans (hu c (Or.inr hc) hvc).symm
    exact Set.disjoint_left.mp hAC ha (heq ▸ hc)
  · intro hnot
    obtain ⟨r, hr, hvr, _⟩ := F.property.2 v
    rcases hr with ha | hc
    · exact False.elim (hnot ⟨r, ha, hvr⟩)
    · exact ⟨r, hc, hvr⟩

/-- For removal of one roots, the complement of the color event is increasing in zero edges. -/
def forestZeroComplementEvent (A : Set V) (H : Set (Set V)) : Set (Finset E) :=
  {F | (G.oneVertices F A)ᶜ ∉ H}

theorem forestZeroComplementEvent_increasing (A : Set V) (H : Set (Set V))
    (hH : ∀ U ∈ H, ∀ W : Set V, U ⊆ W → W ∈ H) :
    ∀ F ∈ G.forestZeroComplementEvent A H, ∀ e : E,
      insert e F ∈ G.forestZeroComplementEvent A H := by
  intro F hF e hnew
  apply hF
  apply hH _ hnew
  apply Set.compl_subset_compl.mpr
  rintro v ⟨a, ha, hva⟩
  exact ⟨a, ha, G.reaches_mono (Finset.subset_insert e F) hva⟩

/-- The increasing zero event is exactly the complementary source color event on actual forests. -/
theorem forestZeroComplementEvent_on_rootedForest (A C : Set V) (hAC : Disjoint A C)
    (H : Set (Set V)) (F : G.RootedForest (A ∪ C)) :
    F.val ∈ G.forestZeroComplementEvent A H ↔ G.oneVertices F.val C ∉ H := by
  change (G.oneVertices F.val A)ᶜ ∉ H ↔ _
  rw [← G.oneVertices_eq_compl_zeroVertices A C hAC F]

/-- Transport of the actual original-forest uniform count to the exact source color probability. -/
theorem sum_uniformRootedForestMass_colorEvent (A C : Set V) (hR : (A ∪ C).Nonempty)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) (H : Set (Set V)) :
    ∑ F : Finset E, Set.indicator (G.forestColorEvent C H)
      (G.uniformRootedForestMass (A ∪ C) hR hconn) F =
      (Nat.card {F : G.RootedForest (A ∪ C) // G.oneVertices F.val C ∈ H} : ℝ) /
        Nat.card (G.RootedForest (A ∪ C)) :=
  G.sum_uniformRootedForestMass_event (A ∪ C) hR hconn _

end FiniteAvalanches.Trees.Multigraph
