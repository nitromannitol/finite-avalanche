import FiniteAvalanches.Electrical.Trees.BoundaryGroveCount
import FiniteAvalanches.Electrical.Trees.PathGrovePairing

/-! The exact original-tree two-boundary-copy event reduces to the canonical KW grove count. -/
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph.TwoCopy
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

omit [Fintype V] [Fintype E] in
/-- Distinct boundary positions have distinct original IDs, in either storage orientation. -/
theorem boundary_copies_ne (m : ℕ) (p : Fin (m+1) → V) (hp : Function.Injective p)
    (i j : Fin m) (hij : i < j) (e f : E)
    (he : (J.left e = p i.castSucc ∧ J.right e = p i.succ) ∨
      (J.right e = p i.castSucc ∧ J.left e = p i.succ))
    (hf : (J.left f = p j.castSucc ∧ J.right f = p j.succ) ∨
      (J.right f = p j.castSucc ∧ J.left f = p j.succ)) : e ≠ f := by
  intro h
  subst f
  rcases he with ⟨ai,bi⟩ | ⟨bi,ai⟩ <;> rcases hf with ⟨aj,bj⟩ | ⟨bj,aj⟩
  · have h := congrArg Fin.val (hp (ai.symm.trans aj)); exact (ne_of_lt hij) (Fin.ext h)
  · have ha := congrArg Fin.val (hp (ai.symm.trans aj))
    have hb := congrArg Fin.val (hp (bi.symm.trans bj))
    simp only [Fin.val_castSucc,Fin.val_succ] at ha hb
    omega
  · have ha := congrArg Fin.val (hp (ai.symm.trans aj))
    have hb := congrArg Fin.val (hp (bi.symm.trans bj))
    simp only [Fin.val_castSucc,Fin.val_succ] at ha hb
    omega
  · have h := congrArg Fin.val (hp (bi.symm.trans bj)); exact (ne_of_lt hij) (Fin.ext h)

                                                                          
                                                                                 
theorem boundary_pair_contact_count (D : Drawing J)
    (hvertices : ∀ x, D.point x ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (m : ℕ) (p : Fin (m+1) → V) (hp : Function.Injective p)
    (θ : Fin (m+1) → ℝ) (hθ : StrictMono θ)
    (hspan : θ (Fin.last m) < θ 0 + 2 * Real.pi)
    (hpoint : ∀ k, D.point (p k) = (Real.cos (θ k),Real.sin (θ k)))
    (i j : Fin m) (hij : i < j) (e f : E)
    (hei : (J.left e = p i.castSucc ∧ J.right e = p i.succ) ∨
      (J.right e = p i.castSucc ∧ J.left e = p i.succ))
    (hfj : (J.left f = p j.castSucc ∧ J.right f = p j.succ) ∨
      (J.right f = p j.castSucc ∧ J.left f = p j.succ)) :
    (∑ T : J.SpanningTree, J.pathIndicator T (p 0) (p (Fin.last m)) e *
      J.pathIndicator T (p 0) (p (Fin.last m)) f) / (Fintype.card J.SpanningTree : ℝ) =
      (Nat.card (J.PairingGrove (![p (Fin.last m),p 0,p i.succ] : Fin 3 → V)
        (![p i.castSucc,p j.castSucc,p j.succ] : Fin 3 → V) pathPairing) : ℝ) /
          (Fintype.card J.SpanningTree : ℝ) := by
  rw [boundary_contact_average_eq_grove_ratio J D hvertices hedges m p θ hθ hspan hpoint
    i j hij e f (boundary_copies_ne J m p hp i j hij e f hei hfj) hei hfj]
  rw [Nat.card_congr (pathGrovePairingEquiv J (p 0) (p i.castSucc) (p i.succ)
    (p j.castSucc) (p j.succ) (p (Fin.last m)))]

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph.TwoCopy
