import FiniteAvalanches.Trees.Lattice.ReciprocalCertificate
import FiniteAvalanches.Trees.Lattice.OriginalContactCount

set_option autoImplicit false
open scoped Classical
noncomputable section
namespace ReciprocalCertificate14
open LatticeProb FiniteAvalanches FiniteAvalanches.Trees
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice TreeMeasurability11

/-- The second finite determination step of `fv:tree-continuity`, manuscript459:
all objects and the positive original-copy denominator are literally preserved. -/
theorem reciprocal_finite_certificate (T : EndedTree) (S : Finset (Site 2))
    (hS : S.Nonempty) :
    let K := connectingSites T.val T.property.1 T.property.2 S hS
    let c := earliestCommonAncestor T.val T.property.1 T.property.2 S hS
    let C := vertexPast T.val T.property.1 T.property.2 c
    ∃ (F : Finset LatticeEdge) (R : ℕ), ∀ N ≥ R,
      ∀ t : (WiredTrees.graph N).SpanningTree,
      (∀ f ∈ F, wiredField t f = T.val f) →
      ∃ (hN : ∀ x ∈ S, FiniteWired.inBox N x) (hcN : FiniteWired.inBox N c)
        (hne : (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
          (finiteMarks_nonempty N S hS hN) ≠ none),
        (WiredTrees.graph N).span t (finiteMarks N S) = activeLift N K ∧
        (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
          (finiteMarks_nonempty N S hS hN) = some (FiniteWired.activeOfSite N c hcN) ∧
        (WiredTrees.graph N).descendants t none
          ((WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
            (finiteMarks_nonempty N S hS hN)) = activeLift N C ∧
        (WiredTrees.graph N).past t none
          ((WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
            (finiteMarks_nonempty N S hS hN)) hne = activeLift N C ∧
        ((WiredTrees.graph N).admissibleEdges
          ((WiredTrees.graph N).descendants t none
            ((WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
              (finiteMarks_nonempty N S hS hN)))
          ((WiredTrees.graph N).span t (finiteMarks N S))).card =
            sourceBoundaryCount T.val T.property.1 T.property.2 S hS ∧
        1 ≤ sourceBoundaryCount T.val T.property.1 T.property.2 S hS ∧
        finiteZN N S hS t = infiniteReciprocal S hS T := by
  dsimp only
  obtain ⟨F,R,hFR⟩ := ancestor_past_span_certificate T S hS
  refine ⟨F,R,?_⟩
  intro N hRN t hmatch
  obtain ⟨hN,hcN,hbox,hspan,hanc,hdesc⟩ := hFR N hRN t hmatch
  have hne : (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) ≠ none := by rw [hanc]; exact Option.some_ne_none _
  have hpast := (WiredTrees.graph N).past_eq_descendants t none
    ((WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN)) hne
  let C := vertexPast T.val T.property.1 T.property.2
    (earliestCommonAncestor T.val T.property.1 T.property.2 S hS)
  have hC : C.Finite := vertexPast_finite T.val T.property.1 T.property.2 _
  have hKC : connectingSites T.val T.property.1 T.property.2 S hS ⊆ hC.toFinset := by
    intro x hx
    exact hC.mem_toFinset.mpr (connectingSites_subset_past T.val T.property.1 T.property.2 S hS hx)
  have hcount : ((WiredTrees.graph N).admissibleEdges
      ((WiredTrees.graph N).descendants t none ((WiredTrees.graph N).ancestorOf t none
        (finiteMarks N S) (finiteMarks_nonempty N S hS hN)))
      ((WiredTrees.graph N).span t (finiteMarks N S))).card =
        sourceBoundaryCount T.val T.property.1 T.property.2 S hS := by
    rw [hspan, hdesc]
    have he : (hC.toFinset : Set (Site 2)) = C := hC.coe_toFinset
    change ((WiredTrees.graph N).admissibleEdges (activeLift N C)
      (activeLift N (connectingSites T.val T.property.1 T.property.2 S hS))).card = _
    rw [← he]
    have h := original_contact_count N (connectingSites T.val T.property.1 T.property.2 S hS)
      hC.toFinset hKC (fun z hz => hbox z (hC.mem_toFinset.mp hz))
    change ((WiredTrees.graph N).admissibleEdges (activeLift N (hC.toFinset : Set (Site 2)))
      (activeLift N (connectingSites T.val T.property.1 T.property.2 S hS))).card =
        FiniteAvalanches.Wilson.Lattice.contacts
          (connectingSites T.val T.property.1 T.property.2 S hS) (fun y => decide (y ∉ C))
    simpa only [hC.mem_toFinset] using h
  refine ⟨hN,hcN,hne,hspan,hanc,hdesc,hpast.trans hdesc,hcount,
    sourceBoundaryCount_ge_one T.val T.property.1 T.property.2 S hS,?_⟩
  rw [finiteZN_inside N S hS hN t, if_pos hne, hcount, one_div]
  rfl

/-- Deterministic local convergence of actual finite wired trees gives eventual
literal equality, without a coupling axiom or any probability-limit premise. -/
theorem reciprocal_eventually_eq (T : EndedTree) (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : ∀ N : ℕ, (WiredTrees.graph N).SpanningTree)
    (hlocal : ∀ f : LatticeEdge, ∀ᶠ N : ℕ in Filter.atTop,
      wiredField (t N) f = T.val f) :
    ∀ᶠ N : ℕ in Filter.atTop, finiteZN N S hS (t N) = infiniteReciprocal S hS T := by
  obtain ⟨F,R,hFR⟩ := reciprocal_finite_certificate T S hS
  have hF : ∀ᶠ N : ℕ in Filter.atTop, ∀ f ∈ F, wiredField (t N) f = T.val f :=
    (Filter.eventually_all_finset F).mpr (fun f _ => hlocal f)
  filter_upwards [hF, Filter.eventually_ge_atTop R] with N hmatch hRN
  obtain ⟨_,_,_,_,_,_,_,_,_,hZ⟩ := hFR N hRN (t N) hmatch
  exact hZ

#print axioms reciprocal_finite_certificate
#print axioms reciprocal_eventually_eq
end ReciprocalCertificate14
