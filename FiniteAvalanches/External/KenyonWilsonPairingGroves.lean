import FiniteAvalanches.Electrical.Trees.PairingGroves
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
axiom kenyonWilson_pairingGroves_resistanceMinor
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
        ((G (a r) (a r) + G (b s) (b s) - 2*G (a r) (b s))/2)).det).coeff 1

end FiniteAvalanches.External
