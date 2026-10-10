import FiniteAvalanches.Electrical.Reference.CopyErasure
import FiniteAvalanches.Trees.ForestProjection.Deletion

set_option autoImplicit false
namespace JointMarkedDeletion
open LatticeProb FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

theorem marked_mem_primal (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    marked.val ∈ primalCopies D P := by
  have hne : alpha D P ≠ beta D P := by intro h; cases h
  rw [primalCopies, Finset.mem_filter, mem_domainCopies]
  rcases marked.property with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · refine ⟨Or.inr ?_, ?_⟩
    · obtain ⟨x,hx,he⟩ := Finset.mem_image.mp ((project_eq_beta_iff D P _).mp hb)
      exact he ▸ x.property
    · rw [ha,hb]; exact hne
  · refine ⟨Or.inl ?_, ?_⟩
    · obtain ⟨x,hx,he⟩ := Finset.mem_image.mp ((project_eq_beta_iff D P _).mp ha)
      exact he ▸ x.property
    · rw [ha,hb]; exact hne.symm

def markedPrimalCopy (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    PrimalCopy D P := ⟨marked.val, marked_mem_primal D P marked⟩

/-- The marked copy joins two distinct roots, so every actual rooted forest omits it. -/
theorem marked_not_selected (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (F : (primalGraph D P).RootedForest ({alpha D P,beta D P} : Set (Vertex D P))) :
    markedPrimalCopy D P marked ∉ F.val := by
  intro he
  obtain ⟨r,_,_,hu⟩ := F.property.2 (alpha D P)
  have ha : alpha D P = r := hu _ (by simp) .refl
  have hb : beta D P = r := hu _ (by simp)
    (.single ⟨markedPrimalCopy D P marked, he, by
      rcases marked.property with h | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h2,h1⟩⟩)
  have heq : alpha D P = beta D P := ha.trans hb.symm
  cases heq

/-- Deleting that original copy leaves the entire uniform forest sample carrier. -/
def markedDeletionForestEquiv (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    ((primalGraph D P).edgeSubgraph (Finset.univ.erase (markedPrimalCopy D P marked))).RootedForest
      ({alpha D P,beta D P} : Set (Vertex D P)) ≃
    (primalGraph D P).RootedForest ({alpha D P,beta D P} : Set (Vertex D P)) :=
  ((primalGraph D P).edgeSubgraphRootedForestEquiv _ _).trans
    (Equiv.ofBijective Subtype.val (by
      constructor
      · exact Subtype.val_injective
      · intro F
        refine ⟨⟨F, ?_⟩, rfl⟩
        intro e he
        exact Finset.mem_erase.mpr ⟨by
          intro h
          exact marked_not_selected D P marked F (h ▸ he), Finset.mem_univ _⟩))

theorem marked_deletion_card (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    Nat.card (((primalGraph D P).edgeSubgraph (Finset.univ.erase (markedPrimalCopy D P marked))).RootedForest
      ({alpha D P,beta D P} : Set (Vertex D P))) =
    Nat.card ((primalGraph D P).RootedForest ({alpha D P,beta D P} : Set (Vertex D P))) :=
  Nat.card_congr (markedDeletionForestEquiv D P marked)

end
end JointMarkedDeletion
