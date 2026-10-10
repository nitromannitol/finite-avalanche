import FiniteAvalanches.Electrical.PairContact.GroveTransport
import FiniteAvalanches.Electrical.PairContact.GreenTransport
import FiniteAvalanches.Electrical.PairContact.SignedCounts

/-! KW signed-minor identity transported through all six fresh unit pendant leaves. -/
namespace FiniteAvalanches.Electrical.PairFormula
open FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

/-- Every simultaneous original-terminal coincidence is retained in the signed identity.
Fresh leaves, their forced unit copies and their resistance coefficients are proved transports. -/
theorem signed_ratio_all_terminal_coincidences
    (hc : (supportGraph J.left J.right).Preconnected) (x : Fin 6 → V) (first : Bool) :
    let U := if first then triple124 else triple123
    let W := if first then triple356 else triple456
    let G := groundedGreen J.left J.right (x 0) hc
    signedGroveSum J x U W / (Nat.card J.SpanningTree : ℝ) =
      ((Matrix.of fun r s : Fin 3 => (Polynomial.X : Polynomial ℝ)-Polynomial.C
        ((G (x (U r)) (x (U r))+G (x (W s)) (x (W s))-
          2*G (x (U r)) (x (W s)))/2)).det).coeff 1 := by
  intro U W G
  have hu : Function.Injective U := by
    cases first <;> exact (by
      obtain ⟨ha,_,_,_,hb,_,_,_⟩ := source_triples_complete
      first | exact ha | exact hb)
  have hw : Function.Injective W := by
    cases first <;> exact (by
      obtain ⟨_,ha,_,_,_,hb,_,_⟩ := source_triples_complete
      first | exact ha | exact hb)
  have hd : Disjoint (Set.range U) (Set.range W) := by
    cases first <;> exact (by
      obtain ⟨_,_,ha,_,_,_,hb,_⟩ := source_triples_complete
      first | exact ha | exact hb)
  let L := J.withPendants x
  have hlc : (supportGraph L.left L.right).Preconnected :=
    pendant_preconnected J.left J.right x hc
  have hab : ∀ r s, ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ U) r ≠ ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ W) s := by
    intro r s h
    exact Set.disjoint_left.mp hd ⟨r,rfl⟩ ⟨s,(Sum.inr.inj h).symm⟩
  have h := FiniteAvalanches.External.kenyonWilson_pairingGroves_resistanceMinor L hlc
    (Sum.inl (x 0)) (by decide : 0 < 3) ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ U) ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ W)
    (Sum.inr_injective.comp hu) (Sum.inr_injective.comp hw) hab
  have hs : (∑ π : Equiv.Perm (Fin 3), ((Equiv.Perm.sign π : ℤ) : ℝ) *
      (Nat.card (L.PairingGrove ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ U) ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ W) π) : ℝ)) =
      signedGroveSum J x U W := by
    apply Finset.sum_congr rfl
    intro π _
    rw [show Nat.card (L.PairingGrove ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ U) ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ W) π) =
      Nat.card (J.PairingGrove (x ∘ U) (x ∘ W) π) from all_six_grove_count J x first π]
  rw [hs,show Nat.card L.SpanningTree = Nat.card J.SpanningTree from all_six_tree_count J x] at h
  have hm := all_six_minor_coeff J.left J.right hc x U W hd
  exact h.trans hm

end
end FiniteAvalanches.Electrical.PairFormula
