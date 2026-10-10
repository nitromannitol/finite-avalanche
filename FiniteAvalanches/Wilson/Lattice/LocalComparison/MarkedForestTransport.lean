import FiniteAvalanches.Wilson.Lattice.LocalComparison.MarkedDeletion
import FiniteAvalanches.Trees.CopiedTreeTransport
import FiniteAvalanches.Probability.UniformMap

set_option autoImplicit false
namespace LocalMarkedForest
open LatticeProb FiniteAvalanches FiniteAvalanches.Trees
open FiniteAvalanches.Electrical.Plane.SourceLattice MeasureTheory
open scoped Classical
noncomputable section

abbrev deletedCopies (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :=
  Finset.univ.erase (JointMarkedDeletion.markedPrimalCopy D P marked)

local instance retainedDecidableEq (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) := Classical.decEq _

local instance deletedDecidableEq (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) : DecidableEq (deletedCopies D P marked) := Classical.decEq _

/-- Reindex surviving copies by their identical original ID, retaining parallel copies. -/
def retainedCopyEquiv (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    Copy D P marked ≃ deletedCopies D P marked where
  toFun e := ⟨⟨e.val, by
    have he : e.val ∈ (primalCopies D P).erase marked.val := by
      simpa only [retainedCopies_eq_primal_erase] using e.property
    exact (Finset.mem_erase.mp he).2⟩, by
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      have he : e.val ∈ (primalCopies D P).erase marked.val := by
        simpa only [retainedCopies_eq_primal_erase] using e.property
      exact (Finset.mem_erase.mp he).1 (congrArg Subtype.val h)⟩
  invFun c := ⟨c.val.val, by
    rw [retainedCopies_eq_primal_erase]
    exact Finset.mem_erase.mpr ⟨fun h =>
      (Finset.mem_erase.mp c.property).1 (Subtype.ext h), c.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem retained_endpoints (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (e : Copy D P marked) :
    ((primalGraph D P).edgeSubgraph (deletedCopies D P marked)).left
        (retainedCopyEquiv D P marked e) = (StatementTypes.graph D P marked).left e ∧
    ((primalGraph D P).edgeSubgraph (deletedCopies D P marked)).right
        (retainedCopyEquiv D P marked e) = (StatementTypes.graph D P marked).right e :=
  ⟨rfl, rfl⟩

theorem retained_reaches_iff (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (F : Finset (Copy D P marked)) (x y : Vertex D P) :
    ((primalGraph D P).edgeSubgraph (deletedCopies D P marked)).reaches
        (F.image (retainedCopyEquiv D P marked)) x y ↔
      (StatementTypes.graph D P marked).reaches F x y :=
  Multigraph.copiedEquiv_reaches_iff (StatementTypes.graph D P marked)
    ((primalGraph D P).edgeSubgraph (deletedCopies D P marked)) (Equiv.refl _)
    (retainedCopyEquiv D P marked) (fun e => Or.inl (retained_endpoints D P marked e)) F x y

theorem retained_forest_iff (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (F : Finset (Copy D P marked)) :
    ((primalGraph D P).edgeSubgraph (deletedCopies D P marked)).is_rooted_forest
        ({alpha D P, beta D P} : Set (Vertex D P)) (F.image (retainedCopyEquiv D P marked)) ↔
      (StatementTypes.graph D P marked).is_rooted_forest
        ({alpha D P, beta D P} : Set (Vertex D P)) F := by
  have hf := Multigraph.copiedEquiv_forest_iff (StatementTypes.graph D P marked)
    ((primalGraph D P).edgeSubgraph (deletedCopies D P marked)) (Equiv.refl _)
    (retainedCopyEquiv D P marked) (fun e => Or.inl (retained_endpoints D P marked e)) F
  constructor
  · rintro ⟨h, hr⟩
    exact ⟨hf.mp h, by simpa only [retained_reaches_iff] using hr⟩
  · rintro ⟨h, hr⟩
    exact ⟨hf.mpr h, by simpa only [retained_reaches_iff] using hr⟩

def reindexForestEquiv (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    (StatementTypes.graph D P marked).RootedForest ({alpha D P, beta D P} : Set (Vertex D P)) ≃
      ((primalGraph D P).edgeSubgraph (deletedCopies D P marked)).RootedForest
        ({alpha D P, beta D P} : Set (Vertex D P)) where
  toFun F := ⟨F.val.image (retainedCopyEquiv D P marked),
    (retained_forest_iff D P marked F.val).mpr F.property⟩
  invFun F := ⟨F.val.image (retainedCopyEquiv D P marked).symm, by
    apply (retained_forest_iff D P marked _).mp
    simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id'] using F.property⟩
  left_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply, Finset.image_id']
  right_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id']

/-- The marked-deletion proof is consumed internally; it is never a law premise. -/
def referencePrimalEquiv (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    (StatementTypes.graph D P marked).RootedForest ({alpha D P, beta D P} : Set (Vertex D P)) ≃
      (primalGraph D P).RootedForest ({alpha D P, beta D P} : Set (Vertex D P)) :=
  (reindexForestEquiv D P marked).trans
    (JointMarkedDeletion.markedDeletionForestEquiv D P marked)

theorem referencePrimalEquiv_reaches (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P)
    (F : (StatementTypes.graph D P marked).RootedForest
      ({alpha D P, beta D P} : Set (Vertex D P))) (x y : Vertex D P) :
    (primalGraph D P).reaches (referencePrimalEquiv D P marked F).val x y ↔
      (StatementTypes.graph D P marked).reaches F.val x y := by
  change (primalGraph D P).reaches
    (Multigraph.liftEdgeSubset (deletedCopies D P marked)
      (F.val.image (retainedCopyEquiv D P marked))) x y ↔ _
  rw [← Multigraph.edgeSubgraph_reaches_iff, retained_reaches_iff]

theorem full_denominator (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    Nat.card ((StatementTypes.graph D P marked).RootedForest
      ({alpha D P, beta D P} : Set (Vertex D P))) =
      Nat.card ((primalGraph D P).RootedForest ({alpha D P, beta D P} : Set (Vertex D P))) :=
  Nat.card_congr (referencePrimalEquiv D P marked)

/-- Every nonroot color event is transported with the full uniform denominator. -/
theorem color_event_count (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (S : Set (Vertex D P → Bool)) :
    (Nat.card {F : (StatementTypes.graph D P marked).RootedForest
      ({alpha D P, beta D P} : Set (Vertex D P)) |
      (fun x => decide ((StatementTypes.graph D P marked).reaches F.val x (beta D P))) ∈ S} : ℝ) /
      Nat.card ((StatementTypes.graph D P marked).RootedForest
        ({alpha D P, beta D P} : Set (Vertex D P))) =
    (Nat.card {F : (primalGraph D P).RootedForest ({alpha D P, beta D P} : Set (Vertex D P)) |
      (fun x => decide ((primalGraph D P).reaches F.val x (beta D P))) ∈ S} : ℝ) /
      Nat.card ((primalGraph D P).RootedForest ({alpha D P, beta D P} : Set (Vertex D P))) := by
  have hc (F : (StatementTypes.graph D P marked).RootedForest
      ({alpha D P, beta D P} : Set (Vertex D P))) :
      (fun x => decide ((StatementTypes.graph D P marked).reaches F.val x (beta D P))) =
      (fun x => decide ((primalGraph D P).reaches
        (referencePrimalEquiv D P marked F).val x (beta D P))) := by
    funext x
    exact Bool.decide_congr (referencePrimalEquiv_reaches D P marked F x (beta D P)).symm
  have hcount := Nat.card_congr ((referencePrimalEquiv D P marked).subtypeEquiv
    (p := fun F => (fun x => decide ((StatementTypes.graph D P marked).reaches F.val x (beta D P))) ∈ S)
    (q := fun F => (fun x => decide ((primalGraph D P).reaches F.val x (beta D P))) ∈ S)
    (fun F => by rw [hc F]))
  rw [full_denominator]
  congr 1
  exact_mod_cast hcount

end
end LocalMarkedForest
