import FiniteAvalanches.Trees.Lattice.RayObjects

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb SimpleGraph
open scoped Classical
noncomputable section

/-- The literal outgoing-edge past consists exactly of vertices whose ray visits the vertex. -/
theorem mem_rayPast_iff_ray_passes (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x z : Site 2) :
    z ∈ rayPast ω hT hEnd x ↔ x ∈ Set.range (infiniteRay ω hT hEnd z) := by
  let r := infiniteRay ω hT hEnd z
  let D := cutGraph ω (outgoingLatticeEdge ω hT hEnd x)
  have hrAdj := (infiniteRay_isSimpleRay ω hT hEnd z).2.2
  have hrInj := infiniteRay_injective ω hT hEnd z
  constructor
  · intro hz
    by_contra hnot
    have hcut : ∀ i, D.Adj (r i) (r (i + 1)) := by
      intro i
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hrAdj i, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      rcases Sym2.eq_iff.mp heq with h | h
      · exact hnot ⟨i, h.1⟩
      · exact hnot ⟨i + 1, h.2⟩
    have hreach : ∀ i, D.Reachable (r i) z := by
      intro i
      induction i with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ i ih => exact (hcut i).symm.reachable.trans ih
    have hinf : (rayPast ω hT hEnd x).Infinite := by
      apply (Set.infinite_range_of_injective hrInj).mono
      rintro _ ⟨i, rfl⟩
      apply (mem_rayPast_iff ω hT hEnd x (r i)).mpr
      exact (hreach i).trans ((mem_rayPast_iff ω hT hEnd x z).mp hz)
    exact hinf (rayPast_finite ω hT hEnd x)
  · rintro ⟨n, hn⟩
    have hcut : ∀ i < n, D.Adj (r i) (r (i + 1)) := by
      intro i hi
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hrAdj i, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      rcases Sym2.eq_iff.mp heq with h | h
      · have hieq := hrInj (h.1.trans hn.symm)
        omega
      · have hnext : r (i + 1 + 1) = infiniteDirection ω hT hEnd x := by
          change infiniteRay ω hT hEnd z (i + 1 + 1) = infiniteDirection ω hT hEnd x
          rw [infiniteRay_succ]
          exact congrArg (infiniteDirection ω hT hEnd) h.2
        have hieq := hrInj (h.1.trans hnext.symm)
        omega
    have hreach : ∀ i ≤ n, D.Reachable z (r i) := by
      intro i
      induction i with
      | zero => intro _; exact SimpleGraph.Reachable.refl _
      | succ i ih =>
        intro hi
        exact (ih (by omega)).trans (hcut i (by omega)).reachable
    apply (mem_rayPast_iff ω hT hEnd x z).mpr
    have hp := hreach n le_rfl
    rw [show r n = x from hn] at hp
    exact hp

/-- Every source lies in the finite past of the actual first common ancestor. -/
theorem sources_mem_common_ancestor_past (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (S : Finset (Site 2)) (hS : S.Nonempty) :
    (S : Set (Site 2)) ⊆ rayPast ω hT hEnd (commonRayAncestor ω hT hEnd S hS) := by
  intro x hx
  apply (mem_rayPast_iff_ray_passes ω hT hEnd _ x).mpr
  exact ((commonRayAncestor_characterization ω hT hEnd S hS _).mp rfl).1 x hx

end
end FiniteAvalanches.Trees.Lattice
