import FiniteAvalanches.Electrical.PairContact.Ordered
import FiniteAvalanches.Electrical.Trees.CopiedTreeExistence

/-! The ordered-angle identity with its positive full-copy tree denominator. -/
namespace FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical
open scoped Classical BigOperators

theorem ordered_tree_pair_contacts {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Drawing J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m+1) → V) (hp : Function.Injective p)
    (θ : Fin (m+1) → ℝ) (hθ : StrictMono θ)
    (hspan : θ (Fin.last m) < θ 0 + 2 * Real.pi)
    (hpoint : ∀ k, D.point (p k) = (Real.cos (θ k),Real.sin (θ k)))
    (copies : Fin m → E)
    (hends : ∀ k, (J.left (copies k) = p k.castSucc ∧ J.right (copies k) = p k.succ) ∨
      (J.right (copies k) = p k.castSucc ∧ J.left (copies k) = p k.succ)) :
    letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
    0 < Fintype.card J.SpanningTree ∧ (Fintype.card J.SpanningTree : ℝ) ≠ 0 ∧
    ∀ (i j : Fin m), i.val < j.val →
    let G := groundedGreen J.left J.right (p (Fin.last m)) hc
    (∑ T : J.SpanningTree, J.pathIndicator T (p 0) (p (Fin.last m)) (copies i) *
      J.pathIndicator T (p 0) (p (Fin.last m)) (copies j)) / (Fintype.card J.SpanningTree : ℝ) =
      G (p 0) (p i.castSucc) * (G (p i.succ) (p j.castSucc)-G (p i.succ) (p j.succ)) -
      G (p 0) (p i.succ) * (G (p i.castSucc) (p j.castSucc)-G (p i.castSucc) (p j.succ)) -
      G (p 0) (p j.castSucc) * (G (p i.castSucc) (p j.succ)-G (p i.succ) (p j.succ)) +
      G (p 0) (p j.succ) * (G (p i.castSucc) (p j.castSucc)-G (p i.succ) (p j.castSucc)) := by
  letI : Nonempty V := ⟨p 0⟩
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  have htree : Nonempty J.SpanningTree := J.nonempty_spanningTree_of_reaches
    (fun x y => J.reaches_univ_of_supportGraph_reachable (hc x y))
  have hcount : 0 < Fintype.card J.SpanningTree := Fintype.card_pos_iff.mpr htree
  refine ⟨hcount, ?_, ?_⟩
  · exact_mod_cast Nat.ne_of_gt hcount
  · intro i j hij
    have hformula := PairFormula.Complete.pair_contact_of_ordered_angles_all
      J D hc hvertices hedges m p hp θ hθ hspan hpoint i j hij copies hends
    have enumeration_eq : ∀ enumeration : Fintype J.SpanningTree,
        enumeration = Fintype.ofFinite J.SpanningTree := fun enumeration => Subsingleton.elim enumeration _
    have univ_eq : ∀ enumeration : Fintype J.SpanningTree,
        @Finset.univ J.SpanningTree enumeration =
          @Finset.univ J.SpanningTree (Fintype.ofFinite J.SpanningTree) := by
      intro enumeration
      exact congrArg (fun f : Fintype J.SpanningTree => @Finset.univ J.SpanningTree f)
        (enumeration_eq enumeration)
    have card_eq : ∀ enumeration : Fintype J.SpanningTree,
        @Fintype.card J.SpanningTree enumeration =
          @Fintype.card J.SpanningTree (Fintype.ofFinite J.SpanningTree) := by
      intro enumeration
      exact congrArg (fun f : Fintype J.SpanningTree => @Fintype.card J.SpanningTree f)
        (enumeration_eq enumeration)
    simpa only [univ_eq, card_eq] using hformula

end FiniteAvalanches.Electrical.StatementGeometry
