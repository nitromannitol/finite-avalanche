import FiniteAvalanches.Trees.ForestProjection.Dpp
import FiniteAvalanches.Trees.ForestProjection.ColorComplements
import FiniteAvalanches.External.LyonsProjectionDomination

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.External

/-- Both finite forest color comparisons, using the original copied-forest uniform counts. -/
theorem finite_forest_color_monotonicity {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E)
    (_hconn : ∀ x y : V, G.reaches Finset.univ x y)
    (A C : Set V) (_hAC : Disjoint A C) (_hA : A.Nonempty) (_hC : C.Nonempty) :
  (∀ (C' : Set V), C' ⊆ C → C'.Nonempty →
    ∀ (H : Set (Set V)), (∀ U ∈ H, ∀ W : Set V, U ⊆ W → W ∈ H) →
      (Nat.card {F : G.RootedForest (A ∪ C') | G.oneVertices F.val C' ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A ∪ C')) ≤
        (Nat.card {F : G.RootedForest (A ∪ C) | G.oneVertices F.val C ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A ∪ C))) ∧
  (∀ (A' : Set V), A ⊆ A' → Disjoint A' C →
    ∀ (H : Set (Set V)), (∀ U ∈ H, ∀ W : Set V, U ⊆ W → W ∈ H) →
      (Nat.card {F : G.RootedForest (A' ∪ C) | G.oneVertices F.val C ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A' ∪ C)) ≤
        (Nat.card {F : G.RootedForest (A ∪ C) | G.oneVertices F.val C ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A ∪ C))) := by
  letI : Fintype {v : V // v ∈ A ∪ C} :=
      @Subtype.fintype V (fun v => v ∈ A ∪ C)
        (fun v => Classical.propDecidable (v ∈ A ∪ C)) inferInstance
  have hc := G.supportGraph_preconnected_of_reaches _hconn
  have hRold : (A ∪ C).Nonempty := _hA.mono Set.subset_union_left
  constructor
  · intro C' hCC' _hC' H hH
    letI : Fintype {v : V // v ∈ A ∪ C'} :=
      @Subtype.fintype V (fun v => v ∈ A ∪ C')
        (fun v => Classical.propDecidable (v ∈ A ∪ C')) inferInstance
    have hRnew : (A ∪ C').Nonempty := _hA.mono Set.subset_union_left
    have hAC' : Disjoint A C' := _hAC.mono_right hCC'
    have hle := G.range_rootProjection_antitone
      (Set.toFinset_subset_toFinset.mpr (Set.union_subset_union (by rfl) hCC'))
      (Set.toFinset_nonempty.mpr hRnew) (Set.toFinset_nonempty.mpr hRold) hc
    have hd := lyons_nestedProjectionDomination
      (G.rootProjection (A ∪ C).toFinset (Set.toFinset_nonempty.mpr hRold) hc)
      (G.rootProjection (A ∪ C').toFinset (Set.toFinset_nonempty.mpr hRnew) hc)
      (G.rootProjection_transpose (A ∪ C).toFinset (Set.toFinset_nonempty.mpr hRold) hc)
      (G.rootProjection_idempotent (A ∪ C).toFinset (Set.toFinset_nonempty.mpr hRold) hc)
      (G.rootProjection_transpose (A ∪ C').toFinset (Set.toFinset_nonempty.mpr hRnew) hc)
      (G.rootProjection_idempotent (A ∪ C').toFinset (Set.toFinset_nonempty.mpr hRnew) hc)
      hle
      (G.uniformRootedForestMass (A ∪ C) hRold _hconn)
      (G.uniformRootedForestMass (A ∪ C') hRnew _hconn)
      (G.uniformRootedForestMass_nonneg (A ∪ C) hRold _hconn)
      (G.uniformRootedForestMass_nonneg (A ∪ C') hRnew _hconn)
      (G.uniformRootedForestMass_set_inclusion_det (A ∪ C) hRold _hconn)
      (G.uniformRootedForestMass_set_inclusion_det (A ∪ C') hRnew _hconn)
    have h := hd.1 (G.forestZeroComplementEvent A H)
      (G.forestZeroComplementEvent_increasing A H hH)
    rw [G.sum_uniformRootedForestMass_zeroComplementEvent A C _hAC hRold _hconn H,
      G.sum_uniformRootedForestMass_zeroComplementEvent A C' hAC' hRnew _hconn H] at h
    change
      (Nat.card {F : G.RootedForest (A ∪ C') // G.oneVertices F.val C' ∈ H} : ℝ) /
        Nat.card (G.RootedForest (A ∪ C')) ≤
      (Nat.card {F : G.RootedForest (A ∪ C) // G.oneVertices F.val C ∈ H} : ℝ) /
        Nat.card (G.RootedForest (A ∪ C))
    linarith only [h]
  · intro A' hAA' _hA'C H hH
    letI : Fintype {v : V // v ∈ A' ∪ C} :=
      @Subtype.fintype V (fun v => v ∈ A' ∪ C)
        (fun v => Classical.propDecidable (v ∈ A' ∪ C)) inferInstance
    have hRmore : (A' ∪ C).Nonempty := (_hA.mono hAA').mono Set.subset_union_left
    have hle := G.range_rootProjection_antitone
      (Set.toFinset_subset_toFinset.mpr (Set.union_subset_union hAA' (by rfl)))
      (Set.toFinset_nonempty.mpr hRold) (Set.toFinset_nonempty.mpr hRmore) hc
    have hd := lyons_nestedProjectionDomination
      (G.rootProjection (A' ∪ C).toFinset (Set.toFinset_nonempty.mpr hRmore) hc)
      (G.rootProjection (A ∪ C).toFinset (Set.toFinset_nonempty.mpr hRold) hc)
      (G.rootProjection_transpose (A' ∪ C).toFinset (Set.toFinset_nonempty.mpr hRmore) hc)
      (G.rootProjection_idempotent (A' ∪ C).toFinset (Set.toFinset_nonempty.mpr hRmore) hc)
      (G.rootProjection_transpose (A ∪ C).toFinset (Set.toFinset_nonempty.mpr hRold) hc)
      (G.rootProjection_idempotent (A ∪ C).toFinset (Set.toFinset_nonempty.mpr hRold) hc)
      hle
      (G.uniformRootedForestMass (A' ∪ C) hRmore _hconn)
      (G.uniformRootedForestMass (A ∪ C) hRold _hconn)
      (G.uniformRootedForestMass_nonneg (A' ∪ C) hRmore _hconn)
      (G.uniformRootedForestMass_nonneg (A ∪ C) hRold _hconn)
      (G.uniformRootedForestMass_set_inclusion_det (A' ∪ C) hRmore _hconn)
      (G.uniformRootedForestMass_set_inclusion_det (A ∪ C) hRold _hconn)
    have h := hd.1 (G.forestColorEvent C H)
      (G.forestColorEvent_increasing C H hH)
    rw [G.sum_uniformRootedForestMass_colorEvent A' C hRmore _hconn H,
      G.sum_uniformRootedForestMass_colorEvent A C hRold _hconn H] at h
    exact h

end FiniteAvalanches.Trees.Multigraph
