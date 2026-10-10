import FiniteAvalanches.Trees.Lattice.Space
import FiniteAvalanches.Model.FiniteWired
import Mathlib.Combinatorics.SimpleGraph.Ends.Properties

/-! Full-carrier characterizations of the literal selected graph and its ends.
Local finiteness is derived from its actual lattice-neighbor set. These facts
supply the graph adapter for standard UST inputs without proving those inputs. -/
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem toGraph_edgeSet (ω : EdgeField) :
    (toGraph ω).edgeSet = {e | ∃ h : e ∈ (lattice 2).edgeSet, ω ⟨e, h⟩ = true} := by
  ext e
  refine Sym2.inductionOn e ?_
  intro x y
  rfl

theorem edge_mem_toGraph_iff (ω : EdgeField) (e : LatticeEdge) :
    e.val ∈ (toGraph ω).edgeSet ↔ ω e = true := by
  rw [toGraph_edgeSet]
  constructor
  · rintro ⟨_, hω⟩
    exact hω
  · intro hω
    exact ⟨e.property, hω⟩

theorem toGraph_injective : Function.Injective toGraph := by
  intro ω ω' h
  funext e
  have he : (ω e = true) ↔ ω' e = true := by
    rw [← edge_mem_toGraph_iff, ← edge_mem_toGraph_iff, h]
  cases hω : ω e <;> cases hω' : ω' e <;> simp_all

theorem neighborSet_subset_lattice_neighbors (ω : EdgeField) (x : Site 2) :
    (toGraph ω).neighborSet x ⊆ (nbrFinset x : Set (Site 2)) :=
  fun y hy => (FiniteWired.mem_neighbors_iff x y).mpr (toGraph_le_lattice ω hy)

theorem neighborSet_finite (ω : EdgeField) (x : Site 2) :
    ((toGraph ω).neighborSet x).Finite :=
  (nbrFinset x).finite_toSet.subset (neighborSet_subset_lattice_neighbors ω x)

instance toGraph_locallyFinite (ω : EdgeField) : (toGraph ω).LocallyFinite :=
  fun x => (neighborSet_finite ω x).fintype

theorem isTree_iff_connected_acyclic (ω : EdgeField) :
    IsTree ω ↔ (toGraph ω).Connected ∧ (toGraph ω).IsAcyclic :=
  SimpleGraph.isTree_iff (toGraph ω)

theorem oneEnded_iff_existsUnique_end (ω : EdgeField) :
    OneEnded ω ↔ ∃! _e : (toGraph ω).end, True := by
  constructor
  · rintro ⟨hne, hsub⟩
    obtain ⟨e⟩ := hne
    exact ⟨e, trivial, fun f _ => hsub.elim f e⟩
  · rintro ⟨e, _, hu⟩
    exact ⟨⟨e⟩, ⟨fun f g => (hu f trivial).trans (hu g trivial).symm⟩⟩

end
end FiniteAvalanches.Trees.Lattice
