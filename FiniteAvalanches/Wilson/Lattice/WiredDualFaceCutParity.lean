import FiniteAvalanches.Wilson.Lattice.WiredDualFaceCorners
import FiniteAvalanches.Wilson.Lattice.FiniteCutParityLocal
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceEuler
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceWeakLimit

/-! Cut parity and complementary tree duality for the wired square. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open scoped Classical BigOperators

noncomputable section

local instance decEqWiredEdgeDualFaceCutParity (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- A face copy crosses a set exactly when its two specified endpoints lie on opposite sides. -/
theorem wiredDualFaceGraph_crosses_of_endpoints (B : ℕ) (D : Set (WiredDualFace B))
    (e : FiniteWired.Edge B) (a b : WiredDualFace B)
    (h : s((wiredDualFaceGraph B).left e, (wiredDualFaceGraph B).right e) = s(a, b)) :
    (wiredDualFaceGraph B).crosses D e ↔ (a ∈ D ∧ b ∉ D) ∨ (a ∉ D ∧ b ∈ D) := by
  rcases Sym2.eq_iff.mp h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simp only [Multigraph.crosses, hl, hr]
  · simp only [Multigraph.crosses, hl, hr]
    tauto

/-- A dual cut has even incidence at every active wired vertex. -/
theorem even_wiredDualFaceCut_incident_active (B : ℕ) (D : Set (WiredDualFace B))
    (x : FiniteWired.Active B) :
    Even (dualCutIncidentCopies (WiredTrees.graph B) (wiredDualFaceGraph B) D (some x)).card := by
  let S : Finset FiniteWired.Direction := Finset.univ.filter
    (fun d => (wiredDualFaceGraph B).crosses D (FiniteWired.directionEdge x d))
  have hcard : S.card = (dualCutIncidentCopies (WiredTrees.graph B) (wiredDualFaceGraph B) D (some x)).card := by
    apply Finset.card_bij (fun d _ => FiniteWired.directionEdge x d)
    · intro d hd
      have hcross := (Finset.mem_filter.mp hd).2
      have hinc := FiniteAvalanches.Sandpile.Components.direction_edge_incident x d
      simp only [dualCutIncidentCopies, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hcross, hinc⟩
    · intro a ha b hb h
      exact FiniteAvalanches.Sandpile.Components.direction_edge_injective x h
    · intro e he
      have he' : (wiredDualFaceGraph B).crosses D e ∧
          ((WiredTrees.graph B).left e = some x ∨ (WiredTrees.graph B).right e = some x) := by
        simpa only [dualCutIncidentCopies, Finset.mem_filter, Finset.mem_univ, true_and] using he
      have hi : FiniteAvalanches.Sandpile.Components.incident x e := he'.2
      obtain ⟨d, hd⟩ := FiniteAvalanches.Sandpile.Components.exists_direction_of_incident x e hi
      refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hd⟩
      rw [hd]
      exact he'.1
  rw [← hcard]
  have h0t := wiredDualFaceGraph_crosses_of_endpoints B D (FiniteWired.directionEdge x (0, true)) _ _
    (wiredDualFaceGraph_direction_zero_true B x)
  have h0f := wiredDualFaceGraph_crosses_of_endpoints B D (FiniteWired.directionEdge x (0, false)) _ _
    (wiredDualFaceGraph_direction_zero_false B x)
  have h1t := wiredDualFaceGraph_crosses_of_endpoints B D (FiniteWired.directionEdge x (1, true)) _ _
    (wiredDualFaceGraph_direction_one_true B x)
  have h1f := wiredDualFaceGraph_crosses_of_endpoints B D (FiniteWired.directionEdge x (1, false)) _ _
    (wiredDualFaceGraph_direction_one_false B x)
  dsimp only [S]
  rw [Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, Fintype.sum_bool]
  rw [h0t, h0f, h1t, h1f]
  by_cases ha : wiredDualFaceCorner B x false false ∈ D <;>
  by_cases hb : wiredDualFaceCorner B x true false ∈ D <;>
  by_cases hc : wiredDualFaceCorner B x false true ∈ D <;>
  by_cases hd : wiredDualFaceCorner B x true true ∈ D <;>
    simp [ha, hb, hc, hd] <;> norm_num

/-- A dual face cut has even incidence at every wired vertex, including the sink. -/
theorem even_wiredDualFaceCut_incident (B : ℕ) (D : Set (WiredDualFace B))
    (v : FiniteWired.Vertex B) :
    Even (dualCutIncidentCopies (WiredTrees.graph B) (wiredDualFaceGraph B) D v).card := by
  cases v with
  | some x => exact even_wiredDualFaceCut_incident_active B D x
  | none =>
    apply even_dualCutIncidentCopies_of_others (WiredTrees.graph B) (wiredDualFaceGraph B) D none
    intro v hv
    cases v with
    | none => exact (hv rfl).elim
    | some x => exact even_wiredDualFaceCut_incident_active B D x

/-- Every wired cut meets every face-square cut in an even number of copies. -/
theorem wiredDualFace_even_commonCuts (B : ℕ) (C : Set (FiniteWired.Vertex B))
    (D : Set (WiredDualFace B)) :
    Even (commonCutCopies (WiredTrees.graph B) (wiredDualFaceGraph B) C D).card :=
  even_commonCutCopies_of_even_incidence (WiredTrees.graph B) (wiredDualFaceGraph B) D
    (even_wiredDualFaceCut_incident B D) C

/-- Complementing original wired copies bijects wired trees with face-square trees. -/
def wiredDualFaceTreeEquiv (B : ℕ) :
    (WiredTrees.graph B).SpanningTree ≃ (wiredDualFaceGraph B).SpanningTree := by
  letI : Nonempty (WiredDualFace B) := ⟨wiredDualFaceOrigin B⟩
  have hG : ∀ x y, (WiredTrees.graph B).reaches Finset.univ x y := by
    intro x y
    have h := (WiredTrees.rowTree B).property.2.2.1 x (Set.mem_univ _) y (Set.mem_univ _)
    exact (WiredTrees.graph B).reaches_mono (Finset.subset_univ _) h
  exact dualTreeEquivOfEvenCuts (WiredTrees.graph B) (wiredDualFaceGraph B) hG
    (wiredDualFaceGraph_connected B) (wiredDualFace_even_commonCuts B) (wiredDualFace_euler_count B)

/-- The finite dual tree uses exactly the original copies absent from the wired tree. -/
theorem wiredDualFaceTreeEquiv_copies (B : ℕ) (t : (WiredTrees.graph B).SpanningTree) :
    (wiredDualFaceTreeEquiv B t).val = t.valᶜ := rfl

/-- The dual of every weak wired square-lattice UST limit has the same law. -/
theorem wiredLimit_self_dual (ν : ProbabilityMeasure EdgeField)
    (hν : Filter.Tendsto finiteProbability Filter.atTop (nhds ν)) :
    (ν : MeasureTheory.Measure EdgeField).map dualField = (ν : MeasureTheory.Measure EdgeField) :=
  wiredLimit_dual_of_face_tree_equivs ν hν wiredDualFaceTreeEquiv wiredDualFaceTreeEquiv_copies

end
end FiniteAvalanches.Wilson.Lattice
