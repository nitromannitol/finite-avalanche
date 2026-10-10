import FiniteAvalanches.Trees.Lattice.RayPast
import FiniteAvalanches.Trees.Lattice.BundledRays
import FiniteAvalanches.Trees.Lattice.InfiniteLawProperties

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb SimpleGraph CategoryTheory FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

/-- In the actual locally finite connected graph, its unique end characterizes
exactly one infinite component after every finite vertex deletion. -/
theorem unique_infinite_components_of_oneEnded (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) :
    ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite := by
  let G := toGraph ω
  let F := G.componentComplFunctor
  letI : Fact G.Preconnected := ⟨hT.connected.preconnected⟩
  obtain ⟨e₀⟩ := hOne.1
  have hML : F.IsMittagLeffler :=
    F.isMittagLeffler_of_exists_finite_range (fun j => ⟨j, 𝟙 j, Set.toFinite _⟩)
  letI : ∀ j, Nonempty (F.toEventualRanges.obj j) := F.toEventualRanges_nonempty hML
  intro K
  refine ⟨e₀.val (Opposite.op K), G.end_componentCompl_infinite e₀ (Opposite.op K), ?_⟩
  intro C hC
  have hCev : C ∈ F.eventualRange (Opposite.op K) :=
    (G.infinite_iff_in_eventualRange C).mp hC
  obtain ⟨s, hs⟩ := F.toEventualRanges.eval_section_surjective_of_surjective
    (F.surjective_toEventualRanges hML) (Opposite.op K) ⟨C, hCev⟩
  let e : G.end := F.toEventualRangesSectionsEquiv s
  have heC : e.val (Opposite.op K) = C := congrArg Subtype.val hs
  have he : e = e₀ := hOne.2.elim e e₀
  rw [he] at heC
  exact heC.symm

/-- The finite-complement and actual inverse-system definitions of one end agree. -/
theorem oneEnded_iff_unique_infinite_components (ω : EdgeField) (hT : IsTree ω) :
    OneEnded ω ↔ ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite :=
  ⟨unique_infinite_components_of_oneEnded ω hT, oneEnded_of_unique_infinite_components ω hT⟩

/-- The unique selected neighbor toward the actual tree end. -/
def towardEnd (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω) (x : Site 2) : Site 2 :=
  infiniteDirection ω hT (unique_infinite_components_of_oneEnded ω hT hOne) x

theorem towardEnd_characterization (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x y : Site 2) :
    y = towardEnd ω hT hOne x ↔ (toGraph ω).Adj x y ∧
      (((toGraph ω).deleteEdges {s(x, y)}).connectedComponentMk y).supp.Infinite :=
  infiniteDirection_characterization ω hT (unique_infinite_components_of_oneEnded ω hT hOne) x y

/-- The actual unique infinite simple ray oriented toward the tree end. -/
def orientedRay (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω) (x : Site 2) : SimpleRay :=
  bundledInfiniteRay ω hT (unique_infinite_components_of_oneEnded ω hT hOne) x

theorem orientedRay_characterization (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x : Site 2) (r : SimpleRay) :
    r = orientedRay ω hT hOne x ↔ r.vertex 0 = x ∧
      ∀ n, ω ⟨s(r.vertex n, r.vertex (n + 1)), r.adjacent n⟩ = true := by
  unfold orientedRay
  rw [bundledInfiniteRay_characterization]
  exact and_congr_right (fun _ => forall_congr' (fun n => toGraph_adj_iff ω (r.adjacent n)))

theorem existsUnique_orientedRay (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x : Site 2) :
    ∃! r : SimpleRay, r.vertex 0 = x ∧
      ∀ n, ω ⟨s(r.vertex n, r.vertex (n + 1)), r.adjacent n⟩ = true := by
  refine ⟨orientedRay ω hT hOne x, (orientedRay_characterization ω hT hOne x _).mp rfl, ?_⟩
  intro r hr
  exact (orientedRay_characterization ω hT hOne x r).mpr hr

/-- The first vertex common to all rays from the actual finite nonempty source set. -/
def earliestCommonAncestor (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω)
    (S : Finset (Site 2)) (hS : S.Nonempty) : Site 2 :=
  commonRayAncestor ω hT (unique_infinite_components_of_oneEnded ω hT hOne) S hS

theorem earliestCommonAncestor_characterization (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) (c : Site 2) :
    c = earliestCommonAncestor ω hT hOne S hS ↔
      (∀ x ∈ S, c ∈ (orientedRay ω hT hOne x).vertices) ∧
      ∀ d : Site 2, (∀ x ∈ S, d ∈ (orientedRay ω hT hOne x).vertices) →
        d ∈ (orientedRay ω hT hOne c).vertices :=
  commonRayAncestor_characterization ω hT (unique_infinite_components_of_oneEnded ω hT hOne) S hS c

theorem earliestCommonAncestor_unique (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) :
    ∃! c : Site 2,
      (∀ x ∈ S, c ∈ (orientedRay ω hT hOne x).vertices) ∧
      ∀ d : Site 2, (∀ x ∈ S, d ∈ (orientedRay ω hT hOne x).vertices) →
        d ∈ (orientedRay ω hT hOne c).vertices :=
  existsUnique_common_ray_ancestor ω hT (unique_infinite_components_of_oneEnded ω hT hOne) S hS

theorem earliestCommonAncestor_tails (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) :
    ∀ x ∈ S, ∃ n : ℕ, ∀ k : ℕ,
      (orientedRay ω hT hOne x).vertex (n + k) =
        (orientedRay ω hT hOne (earliestCommonAncestor ω hT hOne S hS)).vertex k :=
  commonRayAncestor_tails ω hT (unique_infinite_components_of_oneEnded ω hT hOne) S hS

/-- The original selected lattice edge out of a vertex toward the unique end. -/
def outgoingEdge (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω) (x : Site 2) : LatticeEdge :=
  outgoingLatticeEdge ω hT (unique_infinite_components_of_oneEnded ω hT hOne) x

theorem outgoingEdge_selected (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x : Site 2) : ω (outgoingEdge ω hT hOne x) = true :=
  outgoingLatticeEdge_selected ω hT (unique_infinite_components_of_oneEnded ω hT hOne) x

/-- The literal vertex component after deleting that vertex's actual outgoing edge. -/
def vertexPast (ω : EdgeField) (hT : IsTree ω) (hOne : OneEnded ω) (x : Site 2) : Set (Site 2) :=
  rayPast ω hT (unique_infinite_components_of_oneEnded ω hT hOne) x

theorem vertexPast_eq_cutComponent (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x : Site 2) :
    vertexPast ω hT hOne x = cutComponent ω (outgoingEdge ω hT hOne x) x := rfl

theorem vertexPast_characterization (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x z : Site 2) :
    z ∈ vertexPast ω hT hOne x ↔ x ∈ (orientedRay ω hT hOne z).vertices :=
  mem_rayPast_iff_ray_passes ω hT (unique_infinite_components_of_oneEnded ω hT hOne) x z

theorem vertexPast_finite (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (x : Site 2) : (vertexPast ω hT hOne x).Finite :=
  rayPast_finite ω hT (unique_infinite_components_of_oneEnded ω hT hOne) x

theorem sources_mem_earliestCommonAncestor_past (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (S : Finset (Site 2)) (hS : S.Nonempty) :
    (S : Set (Site 2)) ⊆ vertexPast ω hT hOne (earliestCommonAncestor ω hT hOne S hS) :=
  sources_mem_common_ancestor_past ω hT (unique_infinite_components_of_oneEnded ω hT hOne) S hS

end
end FiniteAvalanches.Trees.Lattice

namespace FiniteAvalanches.Trees.Lattice.SourceObjectConsumer
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice FiniteAvalanches.External
open scoped Classical
noncomputable section

/-- One actual UST support witness supplies all sources, ancestors and finite pasts. -/
theorem squareLatticeUST_source_objects :
    ∀ᵐ ω ∂(squareLatticeUST : Measure EdgeField), ∃ hT : IsTree ω, ∃ hOne : OneEnded ω,
      (∀ x : Site 2, ∃! r : SimpleRay, r.vertex 0 = x ∧
        ∀ n, ω ⟨s(r.vertex n, r.vertex (n + 1)), r.adjacent n⟩ = true) ∧
      ∀ (S : Finset (Site 2)) (hS : S.Nonempty),
        let c := earliestCommonAncestor ω hT hOne S hS
        let C := vertexPast ω hT hOne c
        C.Finite ∧ (S : Set (Site 2)) ⊆ C ∧ ω (outgoingEdge ω hT hOne c) = true ∧
          ∀ x ∈ S, ∃ n : ℕ, ∀ k : ℕ,
            (orientedRay ω hT hOne x).vertex (n + k) = (orientedRay ω hT hOne c).vertex k := by
  filter_upwards [squareLatticeUST_ae_tree_oneEnded] with ω hω
  refine ⟨hω.1, hω.2, existsUnique_orientedRay ω hω.1 hω.2, ?_⟩
  intro S hS
  exact ⟨vertexPast_finite ω hω.1 hω.2 _, sources_mem_earliestCommonAncestor_past ω hω.1 hω.2 S hS,
    outgoingEdge_selected ω hω.1 hω.2 _, earliestCommonAncestor_tails ω hω.1 hω.2 S hS⟩

end
end FiniteAvalanches.Trees.Lattice.SourceObjectConsumer

set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000

#check @FiniteAvalanches.Trees.Lattice.unique_infinite_components_of_oneEnded
#check @FiniteAvalanches.Trees.Lattice.orientedRay_characterization
#check @FiniteAvalanches.Trees.Lattice.existsUnique_orientedRay
#check @FiniteAvalanches.Trees.Lattice.earliestCommonAncestor_characterization
#check @FiniteAvalanches.Trees.Lattice.earliestCommonAncestor_unique
#check @FiniteAvalanches.Trees.Lattice.vertexPast_characterization
#check @FiniteAvalanches.Trees.Lattice.vertexPast_finite
#check @FiniteAvalanches.Trees.Lattice.SourceObjectConsumer.squareLatticeUST_source_objects

open Lean Elab Command in
run_cmd do
  let primitives := #[`propext, `Classical.choice, `Quot.sound]
  let registered := #[`FiniteAvalanches.External.square_lattice_wired_ust_weak_limit,
    `FiniteAvalanches.External.square_lattice_wired_ust_one_tree_one_end]
  let pure := #[`FiniteAvalanches.Trees.Lattice.unique_infinite_components_of_oneEnded,
    `FiniteAvalanches.Trees.Lattice.oneEnded_iff_unique_infinite_components,
    `FiniteAvalanches.Trees.Lattice.towardEnd_characterization,
    `FiniteAvalanches.Trees.Lattice.orientedRay_characterization,
    `FiniteAvalanches.Trees.Lattice.existsUnique_orientedRay,
    `FiniteAvalanches.Trees.Lattice.earliestCommonAncestor_characterization,
    `FiniteAvalanches.Trees.Lattice.earliestCommonAncestor_unique,
    `FiniteAvalanches.Trees.Lattice.earliestCommonAncestor_tails,
    `FiniteAvalanches.Trees.Lattice.outgoingEdge_selected,
    `FiniteAvalanches.Trees.Lattice.vertexPast_eq_cutComponent,
    `FiniteAvalanches.Trees.Lattice.vertexPast_characterization,
    `FiniteAvalanches.Trees.Lattice.vertexPast_finite,
    `FiniteAvalanches.Trees.Lattice.sources_mem_earliestCommonAncestor_past]
  for name in pure do
    let axs ← Lean.collectAxioms name
    for ax in axs do
      unless primitives.contains ax do throwError "Nonprimitive {ax} in {name}"
    logInfo m!"PURE_SOURCE_CLOSURE {name}: {axs.toList}"
  let name := `FiniteAvalanches.Trees.Lattice.SourceObjectConsumer.squareLatticeUST_source_objects
  let axs ← Lean.collectAxioms name
  for ax in axs do
    unless primitives.contains ax || registered.contains ax do throwError "Unregistered {ax} in {name}"
  logInfo m!"ACTUAL_UST_CONSUMER_CLOSURE {name}: {axs.toList}"
