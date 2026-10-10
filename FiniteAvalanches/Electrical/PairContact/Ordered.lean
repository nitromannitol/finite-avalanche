import FiniteAvalanches.Electrical.PairContact.PendantCancellation
import FiniteAvalanches.Electrical.Geometry.Pendants.SourceAngles
import FiniteAvalanches.Electrical.Trees.BoundaryPairingCount
import FiniteAvalanches.Electrical.PairContact.DeterminantAlgebra

/-! The original two-copy contact/Green identity, with every terminal coincidence retained. -/
namespace FiniteAvalanches.Electrical.PairFormula.Complete
open FiniteAvalanches.Electrical.StatementGeometry
open CopiedGraph.TwoCopy
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

/-- All indices in one original angular window; the auxiliary six-leaf drawing is derived. -/
theorem pair_contact_of_ordered_angles_all (D : Drawing J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m+1) → V) (hp : Function.Injective p)
    (θ : Fin (m+1) → ℝ) (hθ : StrictMono θ)
    (hspan : θ (Fin.last m) < θ 0 + 2 * Real.pi)
    (hpoint : ∀ k, D.point (p k) = (Real.cos (θ k),Real.sin (θ k)))
    (i j : Fin m) (hij : i.val < j.val)
    (copies : Fin m → E)
    (hends : ∀ k, (J.left (copies k) = p k.castSucc ∧ J.right (copies k) = p k.succ) ∨
      (J.right (copies k) = p k.castSucc ∧ J.left (copies k) = p k.succ)) :
    let G := groundedGreen J.left J.right (p (Fin.last m)) hc
    (∑ T : J.SpanningTree, J.pathIndicator T (p 0) (p (Fin.last m)) (copies i) *
      J.pathIndicator T (p 0) (p (Fin.last m)) (copies j)) / (Fintype.card J.SpanningTree : ℝ) =
      G (p 0) (p i.castSucc) * (G (p i.succ) (p j.castSucc)-G (p i.succ) (p j.succ)) -
      G (p 0) (p i.succ) * (G (p i.castSucc) (p j.castSucc)-G (p i.castSucc) (p j.succ)) -
      G (p 0) (p j.castSucc) * (G (p i.castSucc) (p j.succ)-G (p i.succ) (p j.succ)) +
      G (p 0) (p j.succ) * (G (p i.castSucc) (p j.castSucc)-G (p i.succ) (p j.castSucc)) := by
  intro G
  let x := SixLeaf.sourceSix p i j
  obtain ⟨l,D',_,_,_,_,hv',he',horder⟩ := SixLeaf.source_ordered_six_leaf_drawing
    D p θ hθ hspan hpoint hvertices hedges i j hij
  have hcount := signed_difference_eq_original_grove J x D' hv' he' horder
  have h1 := signed_ratio_all_terminal_coincidences J hc x true
  have h2 := signed_ratio_all_terminal_coincidences J hc x false
  have ha : x ∘ triple124 = (![p (Fin.last m),p 0,p i.succ] : Fin 3 → V) := by
    funext k; fin_cases k <;> rfl
  have hb : x ∘ triple356 = (![p i.castSucc,p j.castSucc,p j.succ] : Fin 3 → V) := by
    funext k; fin_cases k <;> rfl
  have hm : matching162345 = pathPairing := by ext k; fin_cases k <;> rfl
  rw [boundary_pair_contact_count J D hvertices hedges m p hp θ hθ hspan hpoint
    i j hij (copies i) (copies j) (hends i) (hends j), ← hm, ← ha, ← hb, ← hcount, sub_div]
  rw [Nat.card_eq_fintype_card] at h1 h2
  dsimp only at h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
  rw [h1,h2]
  have h := groundedGreen_resistanceMinors_sub J hc x
  simpa [x,SixLeaf.sourceSix,G,pairResistance] using h

end
end FiniteAvalanches.Electrical.PairFormula.Complete
