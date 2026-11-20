import FiniteAvalanches.Support.Plane.SelectedSimplePath

/-!
# Dual reachability across a primal cut

Edge-path duality turns the failure of a primal path across a vertex cut into a
dual walk using only the other crossing copies.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E]

/-- An edge crosses a vertex set when its endpoints lie on opposite sides. -/
def CopiedGraph.Crosses (J : CopiedGraph V E) (A : Finset V) (e : E) : Prop :=
  (J.left e ∈ A ∧ J.right e ∉ A) ∨ (J.right e ∈ A ∧ J.left e ∉ A)

omit [Fintype V] [Fintype E] in
/-- A copied walk using noncrossing edges stays on the same side of the cut. -/
theorem CopiedGraph.mem_iff_of_reaches_not_crossing (J : CopiedGraph V E)
    (A : Finset V) (S : Finset E) (hS : ∀ e ∈ S, ¬ J.Crosses A e)
    {x y : V} (h : J.reaches S x y) : x ∈ A ↔ y ∈ A := by
  induction h with
  | refl => rfl
  | @tail u v _ hadj ih =>
    obtain ⟨e, he, hend⟩ := hadj
    have hn := hS e he
    have heq : J.left e ∈ A ↔ J.right e ∈ A := by
      by_contra h
      apply hn
      by_cases hl : J.left e ∈ A
      · have hr : J.right e ∉ A := by
          intro hr
          exact h ⟨fun _ => hr, fun _ => hl⟩
        exact Or.inl ⟨hl, hr⟩
      · have hr : J.right e ∈ A := by
          by_contra hr
          exact h ⟨fun ha => (hl ha).elim, fun ha => (hr ha).elim⟩
        exact Or.inr ⟨hr, hl⟩
    exact ih.trans (hend.elim (fun h => by simpa only [h.1, h.2] using heq)
      (fun h => by simpa only [h.1, h.2] using heq.symm))

/-- The dual endpoints of a crossing edge are joined by the other crossing edges. -/
theorem dual_reaches_other_cut_edges {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) (A : Finset V) (e : E) (he : J.Crosses A e) :
    let K : CopiedGraph (Face D) E :=
      ⟨fun f => negativeChartFace D f (charts f), fun f => positiveChartFace D f (charts f)⟩
    K.reaches ((Finset.univ.filter fun f => J.Crosses A f).erase e) (K.left e) (K.right e) := by
  classical
  letI : Nonempty E := ⟨e⟩
  let S : Finset E := Finset.univ.filter (fun f => ¬ J.Crosses A f)
  have heS : e ∉ S := by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
  have hnot : ¬ J.reaches S (J.left e) (J.right e) := by
    intro h
    have hside := J.mem_iff_of_reaches_not_crossing A S (by
      intro f hf
      exact (Finset.mem_filter.mp hf).2) h
    rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact hr (hside.mp hl)
    · exact hl (hside.mpr hr)
  have h := not_not.mp (mt (edge_path_duality D charts S e heS).mpr hnot)
  have hset : Sᶜ.erase e = (Finset.univ.filter fun f => J.Crosses A f).erase e := by
    ext f
    simp only [Finset.mem_erase, Finset.mem_compl, S, Finset.mem_filter, Finset.mem_univ,
      true_and, not_not]
  rw [hset] at h
  exact h

end FiniteAvalanches.Electrical.StatementGeometry
