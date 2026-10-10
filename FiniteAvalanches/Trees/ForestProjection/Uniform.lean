import FiniteAvalanches.Wilson.RootContraction.Equivalence
import FiniteAvalanches.Trees.ForestProjection.Incidence
import FiniteAvalanches.Trees.Existence
import FiniteAvalanches.Trees.Measure

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Electrical
open FiniteAvalanches.Wilson.CopiedNetwork
open FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Actual connected copied graphs have an actual forest for every nonempty root set. -/
theorem nonempty_rootedForest (R : Set V) (hR : R.Nonempty)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) : Nonempty (G.RootedForest R) := by
  let roots : Roots (V := V) := ⟨R, hR⟩
  have hquot := FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient.graph_connected G roots hconn
  haveI : Nonempty ((graph G roots).SpanningTree) :=
    (graph G roots).nonempty_spanning_tree hquot
  obtain ⟨t⟩ := (inferInstance : Nonempty ((graph G roots).SpanningTree))
  exact ⟨⟨liftCopies G roots t.val, rooted_forest_of_tree G roots t.property⟩⟩

/-- Uniform mass on original copied subsets, using the original rooted-forest count. -/
def uniformRootedForestMass (R : Set V) (_hR : R.Nonempty)
    (_hconn : ∀ x y : V, G.reaches Finset.univ x y) (F : Finset E) : ℝ :=
  if G.is_rooted_forest R F then (Nat.card (G.RootedForest R) : ℝ)⁻¹ else 0

theorem uniformRootedForestMass_nonneg (R : Set V) (hR : R.Nonempty)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) (F : Finset E) :
    0 ≤ G.uniformRootedForestMass R hR hconn F := by
  unfold uniformRootedForestMass
  split_ifs <;> positivity

/-- The literal mass formula equals the sum of the actual uniform forest atoms over an edge event. -/
theorem sum_uniformRootedForestMass_event (R : Set V) (hR : R.Nonempty)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) (ev : Set (Finset E)) :
    ∑ F : Finset E, Set.indicator ev (G.uniformRootedForestMass R hR hconn) F =
      (Nat.card {F : G.RootedForest R // F.val ∈ ev} : ℝ) /
        Nat.card (G.RootedForest R) := by
  classical
  simp only [Set.indicator, uniformRootedForestMass]
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.filter_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv]
  congr 1
  rw [Nat.card_eq_fintype_card]
  have he : {F : G.RootedForest R // F.val ∈ ev} ≃
      {F : Finset E // F ∈ Finset.univ.filter (fun F => F ∈ ev ∧ G.is_rooted_forest R F)} :=
    { toFun := fun F => ⟨F.val.val, by simp [F.val.property, F.property]⟩
      invFun := fun F => ⟨⟨F.val, (Finset.mem_filter.mp F.property).2.2⟩,
        (Finset.mem_filter.mp F.property).2.1⟩
      left_inv := fun F => rfl
      right_inv := fun F => rfl }
  rw [Fintype.card_congr he, Fintype.card_coe]

/-- The original normalizer is positive, not an assumed sampler-existence condition. -/
theorem rootedForest_count_pos (R : Set V) (hR : R.Nonempty)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) :
    0 < Nat.card (G.RootedForest R) := by
  haveI := G.nonempty_rootedForest R hR hconn
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos

theorem sum_uniformRootedForestMass (R : Set V) (hR : R.Nonempty)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) :
    ∑ F : Finset E, G.uniformRootedForestMass R hR hconn F = 1 := by
  have h := G.sum_uniformRootedForestMass_event R hR hconn Set.univ
  simp only [Set.indicator_univ] at h
  have he : {F : G.RootedForest R // F.val ∈ (Set.univ : Set (Finset E))} ≃
      G.RootedForest R := Equiv.subtypeUnivEquiv (fun F => Set.mem_univ F.val)
  rw [Nat.card_congr he] at h
  rw [h, div_self]
  exact_mod_cast Nat.ne_of_gt (G.rootedForest_count_pos R hR hconn)

/-- Source connectivity supplies the support-graph premise used by the actual projection. -/
theorem supportGraph_preconnected_of_reaches
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) :
    (supportGraph G.left G.right).Preconnected := by
  intro x y
  induction hconn x y with
  | refl => exact .rfl
  | @tail u v _ hadj ih =>
    obtain ⟨e, _, h | h⟩ := hadj
    · exact ih.trans (SimpleGraph.Adj.reachable ⟨by
        intro huv; exact G.loopless e (h.1.trans (huv.trans h.2.symm)), e, Or.inl h⟩)
    · exact ih.trans (SimpleGraph.Adj.reachable ⟨by
        intro huv; exact G.loopless e (h.2.trans (huv.symm.trans h.1.symm)), e, Or.inr h⟩)

end FiniteAvalanches.Trees.Multigraph
