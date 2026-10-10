import FiniteAvalanches.Electrical.Trees.Pendants.Counts
import FiniteAvalanches.Electrical.PairContact.Combinatorics

/-! All six literal fresh leaves: original copied-grove and whole-tree counts. -/
namespace FiniteAvalanches.Electrical.PairFormula
open FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

/-- All six fresh leaves occur in exactly one of the two source triples and force their copies. -/
def allSixPairingEquiv (x : Fin 6 → V) (first : Bool) (π : Equiv.Perm (Fin 3)) :
    let U := if first then triple124 else triple123
    let W := if first then triple356 else triple456
    J.PairingGrove (x ∘ U) (x ∘ W) π ≃
      (J.withPendants x).PairingGrove ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ U) ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ W) π := by
  intro U W
  have hdis : Disjoint (Set.range U) (Set.range W) := by
    cases first <;> exact (by
      obtain ⟨_,_,ha,_,_,_,hb,_⟩ := source_triples_complete
      first | exact ha | exact hb)
  have hcover : ∀ k, ∃ r, U r = k ∨ W r = k := by
    intro k
    have hh : Set.range U ∪ Set.range W = Set.univ := by
      cases first <;> exact (by
        obtain ⟨_,_,_,ha,_,_,_,hb⟩ := source_triples_complete
        first | exact ha | exact hb)
    have hk : k ∈ Set.range U ∪ Set.range W := hh.symm ▸ Set.mem_univ k
    rcases hk with ⟨r,hr⟩ | ⟨r,hr⟩
    · exact ⟨r,Or.inl hr⟩
    · exact ⟨r,Or.inr hr⟩
  have roots : ∀ k : Fin 6, ∃ r,
      (((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ U) r = Sum.inr k ∧ ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ W) (π r) ≠ Sum.inr k) ∨
      (((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ W) (π r) = Sum.inr k ∧ ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ U) r ≠ Sum.inr k) := by
    intro k
    obtain ⟨r,hr | hr⟩ := hcover k
    · refine ⟨r,Or.inl ⟨congrArg Sum.inr hr,?_⟩⟩
      intro he
      exact Set.disjoint_left.mp hdis ⟨r,hr⟩ ⟨π r,Sum.inr.inj he⟩
    · refine ⟨π.symm r,Or.inr ⟨?_,?_⟩⟩
      · change Sum.inr (W (π (π.symm r))) = Sum.inr k
        rw [π.apply_symm_apply,hr]
      · intro he
        exact Set.disjoint_left.mp hdis ⟨π.symm r,Sum.inr.inj he⟩ ⟨r,hr⟩
  exact J.pendantPairingEquiv x ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ U) ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ W) π roots

omit [Fintype V] [Fintype E] in
/-- No conductance factor or copy multiplicity changes in either signed source minor. -/
theorem all_six_grove_count (x : Fin 6 → V) (first : Bool) (π : Equiv.Perm (Fin 3)) :
    let U := if first then triple124 else triple123
    let W := if first then triple356 else triple456
    Nat.card ((J.withPendants x).PairingGrove ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ U) ((Sum.inr : Fin 6 → V ⊕ Fin 6) ∘ W) π) =
      Nat.card (J.PairingGrove (x ∘ U) (x ∘ W) π) :=
  Nat.card_congr (allSixPairingEquiv J x first π).symm

omit [Fintype V] [Fintype E] in
/-- Entire original tree normalization, including empty and disconnected zero carriers. -/
theorem all_six_tree_count (x : Fin 6 → V) :
    Nat.card (J.withPendants x).SpanningTree = Nat.card J.SpanningTree :=
  J.pendantTree_count x

end
end FiniteAvalanches.Electrical.PairFormula
