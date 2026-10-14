import FiniteAvalanches.Sandpile.Burning.SourceFields
import FiniteAvalanches.Electrical.Network

/-! Wiring ANY finite vertex subset retains every touching original edge copy.
An actual original walk projects to a walk with outside-only steps collapsed. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E)

theorem retained_all_iff (A : Finset V) (e : E) :
    retained G A A e ↔ G.left e ∈ A ∨ G.right e ∈ A := by
  by_cases hl : G.left e ∈ A <;> by_cases hr : G.right e ∈ A <;> simp [retained, hl, hr]

theorem held_projection_step (s : V) (A : Finset V) (hs : s ∉ A) {x y : V}
    (h : G.adjacent Finset.univ x y) :
    (heldGraph G s A A hs (fun _ h => h)).reaches Finset.univ
      (projectVertex A x) (projectVertex A y) := by
  obtain ⟨e, _, he⟩ := h
  by_cases hret : retained G A A e
  · apply Relation.ReflTransGen.single
    refine ⟨⟨e, hret⟩, Finset.mem_univ _, ?_⟩
    rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact Or.inl ⟨congrArg (projectVertex A) hl, congrArg (projectVertex A) hr⟩
    · exact Or.inr ⟨congrArg (projectVertex A) hr, congrArg (projectVertex A) hl⟩
  · have hne := not_or.mp (mt (retained_all_iff G A e).mpr hret)
    rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · have hx : x ∉ A := fun hx => hne.1 (hl.symm ▸ hx)
      have hy : y ∉ A := fun hy => hne.2 (hr.symm ▸ hy)
      simp only [projectVertex, dif_neg hx, dif_neg hy]
      exact Relation.ReflTransGen.refl
    · have hx : x ∉ A := fun hx => hne.2 (hr.symm ▸ hx)
      have hy : y ∉ A := fun hy => hne.1 (hl.symm ▸ hy)
      simp only [projectVertex, dif_neg hx, dif_neg hy]
      exact Relation.ReflTransGen.refl

theorem held_projection_reach (s : V) (A : Finset V) (hs : s ∉ A) {x y : V}
    (h : G.reaches Finset.univ x y) :
    (heldGraph G s A A hs (fun _ h => h)).reaches Finset.univ
      (projectVertex A x) (projectVertex A y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact ih.trans (held_projection_step G s A hs h)

omit [DecidableEq V] in
theorem reaches_support {x y : V} (h : G.reaches Finset.univ x y) :
    (FiniteAvalanches.Electrical.supportGraph G.left G.right).Reachable x y := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail y z _ h ih =>
    obtain ⟨e, _, he⟩ := h
    have hn : y ≠ z := by
      intro h
      rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · exact G.loopless e (hl.trans (h.trans hr.symm))
      · exact G.loopless e (hl.trans (h.symm.trans hr.symm))
    exact ih.trans (SimpleGraph.Adj.reachable ⟨hn, e, he⟩)

/-- No connectedness of A or cardinality/nonemptiness premise is needed. -/
theorem held_all_connected (s : V) (A : Finset V) (hs : s ∉ A)
    (hc : ∀ x, G.reaches Finset.univ x s) :
    (FiniteAvalanches.Electrical.supportGraph
      (heldGraph G s A A hs (fun _ h => h)).left
      (heldGraph G s A A hs (fun _ h => h)).right).Preconnected := by
  let H := heldGraph G s A A hs (fun _ h => h)
  have hr : ∀ v : Option (InducedVertex A), H.reaches Finset.univ v none := by
    intro v
    cases v with
    | none => exact Relation.ReflTransGen.refl
    | some v =>
      have h := held_projection_reach G s A hs (hc v.val)
      have hv : projectVertex A v.val = some v :=
        (project_vertex_eq_some_iff A v.val v).mpr rfl
      simpa only [hv, held_graph_sink s A hs] using h
  intro x y
  exact (reaches_support H (hr x)).trans (reaches_support H (hr y)).symm

end
end FiniteAvalanches.Sandpile.Burning
