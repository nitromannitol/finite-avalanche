import FiniteAvalanches.Electrical.Plane.UnitBoundary

/-! A finite strictly increasing unit flow is exactly one ordered simple copied path. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- Finite strict height increase terminates at the sink; each step names an actual selected copy. -/
theorem exists_forwardPath_of_unitBoundary {V E : Type*} [Fintype V]
    (a b : E → V) (S : Finset E) (H : V → ℝ) (s t : V)
    (hi : ∀ e ∈ S, H (a e) < H (b e))
    (hB : ∀ x, unitBoundary a b S x = (if s = x then 1 else 0)-(if t = x then 1 else 0)) :
    ∃ p : ForwardPath a b s t, ∀ e ∈ p.edges, e ∈ S := by
  let r : V → V → Prop := fun x y => H y < H x
  letI : IsTrans V r := ⟨fun _ _ _ hxy hyz => lt_trans hyz hxy⟩
  letI : Std.Irrefl r := ⟨fun x => lt_irrefl (H x)⟩
  have hwf := Finite.wellFounded_of_trans_of_irrefl r
  have hp (x : V) : x = s ∨ (∃ e ∈ S, b e = x) →
      ∃ p : ForwardPath a b x t, ∀ e ∈ p.edges, e ∈ S := by
    induction x using hwf.induction with
    | h x ih =>
      intro hx
      by_cases hxt : x = t
      · subst x
        exact ⟨.nil t,fun e he => (List.not_mem_nil he).elim⟩
      · obtain ⟨e,he,hax⟩ := exists_outgoing_of_unitBoundary a b S s t x hB hxt hx
        subst x
        obtain ⟨p,hp⟩ := ih (b e) (hi e he) (Or.inr ⟨e,he,rfl⟩)
        refine ⟨.cons e p,?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact he
        · exact hp z hz
  exact hp s (Or.inl rfl)

/-- Subtracting the actual extracted path leaves a balanced increasing flow, which has no copies. -/
theorem exists_forwardPath_exhausting_unitBoundary {V E : Type*} [Fintype V]
    (a b : E → V) (S : Finset E) (H : V → ℝ) (s t : V)
    (hi : ∀ e ∈ S, H (a e) < H (b e))
    (hB : ∀ x, unitBoundary a b S x = (if s = x then 1 else 0)-(if t = x then 1 else 0)) :
    ∃ p : ForwardPath a b s t,
      p.edges.Nodup ∧ p.vertices.Nodup ∧ p.edges.toFinset = S := by
  obtain ⟨p,hp⟩ := exists_forwardPath_of_unitBoundary a b S H s t hi hB
  have hinc : ∀ e ∈ p.edges, H (a e) < H (b e) := fun e he => hi e (hp e he)
  have hnodup := p.edges_nodup H hinc
  have hP : p.edges.toFinset ⊆ S := by
    intro e he
    exact hp e (List.mem_toFinset.mp he)
  have hbP (x : V) : unitBoundary a b p.edges.toFinset x =
      (if s = x then 1 else 0)-(if t = x then 1 else 0) := by
    rw [unitBoundary,List.sum_toFinset _ hnodup]
    exact p.sum_incidence x
  have hR : S \ p.edges.toFinset = ∅ := by
    apply eq_empty_of_unitBoundary_zero a b _ H
    · intro e he
      exact hi e (Finset.mem_sdiff.mp he).1
    · intro x
      rw [unitBoundary,Finset.sum_sdiff_eq_sub hP]
      change unitBoundary a b S x-unitBoundary a b p.edges.toFinset x = 0
      rw [hB x,hbP x,sub_self]
  have heq : p.edges.toFinset = S := by
    apply Finset.Subset.antisymm hP
    exact Finset.sdiff_eq_empty_iff_subset.mp hR
  exact ⟨p,hnodup,p.vertices_nodup H hinc,heq⟩

end FiniteAvalanches.Electrical.Plane
