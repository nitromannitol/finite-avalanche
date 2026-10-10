import FiniteAvalanches.Electrical.Geometry.BoundaryCutOrder
import FiniteAvalanches.Electrical.Trees.CopyDirections

/-! Original unordered two-copy contacts are actual three-component grove counts. -/
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph.TwoCopy
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

/-- The geometric boundary direction determines the ordered deletion event,
independently of either copy's endpoint storage orientation. -/
theorem boundary_contacts_iff_orderedCut (D : Drawing J)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m+1) → V) (θ : Fin (m+1) → ℝ)
    (hθ : StrictMono θ) (hspan : θ (Fin.last m) < θ 0 + 2 * Real.pi)
    (hpoint : ∀ k, D.point (p k) = (Real.cos (θ k),Real.sin (θ k)))
    (i j : Fin m) (hij : i < j) (e f : E) (hef : e ≠ f)
    (hei : (J.left e = p i.castSucc ∧ J.right e = p i.succ) ∨
      (J.right e = p i.castSucc ∧ J.left e = p i.succ))
    (hfj : (J.left f = p j.castSucc ∧ J.right f = p j.succ) ∨
      (J.right f = p j.castSucc ∧ J.left f = p j.succ))
    (T : J.SpanningTree) :
    let rev := boundaryDirections J e f (p i.castSucc) (p j.castSucc)
    let H := reorient J rev
    bothOnPath J T (p 0) (p (Fin.last m)) e f ↔
      orderedCut H (reorientTreeEquiv J rev T) (p 0) (p (Fin.last m)) e f := by
  dsimp only
  let rev := boundaryDirections J e f (p i.castSucc) (p j.castSucc)
  let H := reorient J rev
  let TH := reorientTreeEquiv J rev T
  have ends := boundaryDirections_endpoints J e f hef _ _ _ _ hei hfj
  have ha : H.left e = p i.castSucc := ends.1
  have hb : H.right e = p i.succ := ends.2.1
  have hc : H.left f = p j.castSucc := ends.2.2.1
  have hd : H.right f = p j.succ := ends.2.2.2
  constructor
  · intro h
    have hi := Drawing.TwoCopy.boundary_copy_forward D T hvertices hedges m p θ hθ hspan
      hpoint i e hei h.1.1 h.1.2
    have hj := Drawing.TwoCopy.boundary_copy_forward D T hvertices hedges m p θ hθ hspan
      hpoint j f hfj h.2.1 h.2.2
    have ho := Drawing.TwoCopy.boundary_copies_increasing D T hvertices hedges m p θ hθ hspan
      hpoint i j hij e f hef hei hfj h.1.1 h.2.1 h.1.2
    have hu : H.reaches (TH.val.erase e) (p 0) (H.left e) := by
      rw [ha]
      change (reorient J rev).reaches (T.val.erase e) (p 0) (p i.castSucc)
      rw [reorient_reaches]
      exact hi.1
    have hv : H.reaches (TH.val.erase e) (H.right e) (p (Fin.last m)) := by
      rw [hb]
      change (reorient J rev).reaches (T.val.erase e) (p i.succ) (p (Fin.last m))
      rw [reorient_reaches]
      exact hi.2
    have hfu : H.reaches (TH.val.erase f) (p 0) (H.left f) := by
      rw [hc]
      change (reorient J rev).reaches (T.val.erase f) (p 0) (p j.castSucc)
      rw [reorient_reaches]
      exact hj.1
    have hs : ¬H.reaches (TH.val.erase f) (p 0) (p (Fin.last m)) := by
      change ¬(reorient J rev).reaches (T.val.erase f) (p 0) (p (Fin.last m))
      rw [reorient_reaches]
      exact h.2.2
    have horder : ¬H.reaches (TH.val.erase e) (p 0) (H.left f) := by
      rw [hc]
      change ¬(reorient J rev).reaches (T.val.erase e) (p 0) (p j.castSucc)
      rw [reorient_reaches]
      exact ho
    exact ⟨h.1.1,h.2.1,two_erased_pairings_of_cuts H TH (p 0) (p (Fin.last m))
      e f hef h.1.1 h.2.1 hu hv hfu hs horder⟩
  · intro h
    have hs := orderedCut_implies_bothOnPath H TH (p 0) (p (Fin.last m)) e f hef h
    change bothOnPath (reorient J rev) TH (p 0) (p (Fin.last m)) e f at hs
    simp only [bothOnPath,reorient_reaches] at hs
    exact hs

/-- Bijection on ALL original copied trees and ALL groves, not a selected family.
Its maps delete/reinsert exactly the same two original IDs. -/
def boundaryContactGroveEquiv (D : Drawing J)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m+1) → V) (θ : Fin (m+1) → ℝ)
    (hθ : StrictMono θ) (hspan : θ (Fin.last m) < θ 0 + 2 * Real.pi)
    (hpoint : ∀ k, D.point (p k) = (Real.cos (θ k),Real.sin (θ k)))
    (i j : Fin m) (hij : i < j) (e f : E) (hef : e ≠ f)
    (hei : (J.left e = p i.castSucc ∧ J.right e = p i.succ) ∨
      (J.right e = p i.castSucc ∧ J.left e = p i.succ))
    (hfj : (J.left f = p j.castSucc ∧ J.right f = p j.succ) ∨
      (J.right f = p j.castSucc ∧ J.left f = p j.succ)) :
    {T : J.SpanningTree // bothOnPath J T (p 0) (p (Fin.last m)) e f} ≃
      PathGrove J (p 0) (p i.castSucc) (p i.succ) (p j.castSucc) (p j.succ) (p (Fin.last m)) := by
  let rev := boundaryDirections J e f (p i.castSucc) (p j.castSucc)
  let H := reorient J rev
  have ends := boundaryDirections_endpoints J e f hef _ _ _ _ hei hfj
  let et : {T : J.SpanningTree // bothOnPath J T (p 0) (p (Fin.last m)) e f} ≃
      {T : H.SpanningTree // orderedCut H T (p 0) (p (Fin.last m)) e f} :=
    (reorientTreeEquiv J rev).subtypeEquiv
    (fun T => boundary_contacts_iff_orderedCut J D hvertices hedges m p θ hθ hspan hpoint
      i j hij e f hef hei hfj T)
  let ef := orderedCutGroveEquiv H (p 0) (p (Fin.last m)) e f hef
  have eg : PathGrove H (p 0) (H.left e) (H.right e) (H.left f) (H.right f) (p (Fin.last m)) ≃
      PathGrove J (p 0) (p i.castSucc) (p i.succ) (p j.castSucc) (p j.succ) (p (Fin.last m)) := by
    rw [ends.1,ends.2.1,ends.2.2.1,ends.2.2.2]
    exact (reorientGroveEquiv J rev _ _ _ _ _ _).symm
  exact et.trans (ef.trans eg)

/-- Raw unordered indicator product counts every original tree exactly once. -/
theorem contact_sum_eq_card (u v : V) (e f : E) :
    (∑ T : J.SpanningTree, J.pathIndicator T u v e * J.pathIndicator T u v f) =
      (Nat.card {T : J.SpanningTree // bothOnPath J T u v e f} : ℝ) := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro T _
  simp only [pathIndicator,bothOnPath]
  split_ifs <;> simp_all

/-- Exact two-boundary-copy source average with the original full-tree denominator.
All three within-block coincidences and either endpoint storage orientation are retained. -/
theorem boundary_contact_average_eq_grove_ratio (D : Drawing J)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m+1) → V) (θ : Fin (m+1) → ℝ)
    (hθ : StrictMono θ) (hspan : θ (Fin.last m) < θ 0 + 2 * Real.pi)
    (hpoint : ∀ k, D.point (p k) = (Real.cos (θ k),Real.sin (θ k)))
    (i j : Fin m) (hij : i < j) (e f : E) (hef : e ≠ f)
    (hei : (J.left e = p i.castSucc ∧ J.right e = p i.succ) ∨
      (J.right e = p i.castSucc ∧ J.left e = p i.succ))
    (hfj : (J.left f = p j.castSucc ∧ J.right f = p j.succ) ∨
      (J.right f = p j.castSucc ∧ J.left f = p j.succ)) :
    (∑ T : J.SpanningTree, J.pathIndicator T (p 0) (p (Fin.last m)) e *
      J.pathIndicator T (p 0) (p (Fin.last m)) f) / (Fintype.card J.SpanningTree : ℝ) =
      (Nat.card (PathGrove J (p 0) (p i.castSucc) (p i.succ) (p j.castSucc)
        (p j.succ) (p (Fin.last m))) : ℝ) / (Fintype.card J.SpanningTree : ℝ) := by
  rw [contact_sum_eq_card,Nat.card_congr (boundaryContactGroveEquiv J D hvertices hedges
    m p θ hθ hspan hpoint i j hij e f hef hei hfj)]

omit [Fintype V] [Fintype E] in
/-- Swapping the two named contacts changes neither the unordered event nor its count. -/
theorem bothOnPath_swap (T : J.SpanningTree) (u v : V) (e f : E) :
    bothOnPath J T u v e f ↔ bothOnPath J T u v f e := and_comm

omit [Fintype V] [Fintype E] in
/-- Repeated-copy contact is the single-copy event, not a two-edge deletion. -/
theorem repeated_contact (T : J.SpanningTree) (u v : V) (e : E) :
    J.pathIndicator T u v e * J.pathIndicator T u v e = J.pathIndicator T u v e := by
  simp only [pathIndicator]
  split_ifs <;> norm_num

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph.TwoCopy
