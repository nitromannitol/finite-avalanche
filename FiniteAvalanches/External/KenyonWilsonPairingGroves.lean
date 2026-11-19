import FiniteAvalanches.Electrical.Trees.PairingRelabel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Proposed standard external: Kenyon--Wilson (2009), arXiv:0811.1766v1,
Theorem 8.1 with C = D = empty, composed with Appendix B, Theorem B.3.
The uncrossed-grove partition function cancels; the denominator below is the
spanning-tree partition function. Unit conductances make partition functions
literal counts of subsets of the original copied-edge carrier.

This exact command requires independent native statement/definition review and
parent registration. It is not the unproved-in-v1 tripartite formula (10), and
it contains no planar cancellation or paper contact-probability conclusion.
-/
namespace FiniteAvalanches.External
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical BigOperators

/-- General signed pairing-grove/tree ratio, KW2009 Theorems 8.1 and B.3.
No embedding or noncrossing assertion is included in this classical input. -/
theorem kenyonWilson_pairingGroves_resistanceMinor
    {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)
    (hc : (supportGraph J.left J.right).Preconnected) (ground : V)
    {k : ℕ} (hk : 0 < k) (a b : Fin k → V)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ r s, a r ≠ b s) :
    let G := groundedGreen J.left J.right ground hc
    (∑ π : Equiv.Perm (Fin k),
      (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℝ) *
        (Nat.card (J.PairingGrove a b π) : ℝ)) /
      (Nat.card J.SpanningTree : ℝ) =
    ((Matrix.of fun r s : Fin k =>
      (Polynomial.X : Polynomial ℝ) - Polynomial.C
        ((G (a r) (a r) + G (b s) (b s) - 2*G (a r) (b s))/2)).det).coeff 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hle : n + 1 ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective a ha
  let d := Fintype.card V - (n + 1)
  have hcard : Fintype.card V = d + (n + 1) := by dsimp [d]; omega
  let ρ : V ≃ Fin (d + (n + 1)) := Fintype.equivFinOfCardEq hcard
  let K := J.relabel ρ
  let hc' := J.relabel_preconnected ρ hc
  have h := FiniteAvalanches.Electrical.pairingGroves_eq_resistanceDet_fin K hc' (ρ ground)
    (ρ ∘ a) (ρ ∘ b) (ρ.injective.comp ha) (ρ.injective.comp hb)
  have hgrove (π : Equiv.Perm (Fin (n + 1))) :
      Nat.card (K.PairingGrove (ρ ∘ a) (ρ ∘ b) π) = Nat.card (J.PairingGrove a b π) :=
    (Nat.card_congr (J.pairingGroveRelabelEquiv ρ a b ha π)).symm
  have htree : Nat.card K.SpanningTree = Nat.card J.SpanningTree :=
    (Nat.card_congr (J.treeVertexEquiv K ρ (fun _ => rfl) (fun _ => rfl))).symm
  have hgreen (x y : V) : groundedGreen K.left K.right (ρ ground) hc' (ρ x) (ρ y) =
      groundedGreen J.left J.right ground hc x y :=
    J.groundedGreen_relabel ρ ground hc hc' x y
  simp only [Function.comp_apply, hgrove, htree, hgreen] at h
  have hne : (Nat.card J.SpanningTree : ℝ) ≠ 0 :=
    ne_of_gt (FiniteAvalanches.Electrical.Ratio.copied_tree_count_pos J ground hc)
  exact (div_eq_iff hne).2 h

end FiniteAvalanches.External
