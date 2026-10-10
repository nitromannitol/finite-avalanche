import FiniteAvalanches.Electrical.PairContact.Combinatorics
import FiniteAvalanches.External.KenyonWilsonPairingGroves

/-! Signed grove cancellation on the full original-copy carrier. -/
namespace FiniteAvalanches.Electrical.PairFormula
open FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

/-- Every component has a terminal; all terminal connections are prescribed. -/
abbrev TerminalRelationForests (x : Fin 6 → V) (pairs : Finset (Sym2 (Fin 6))) :=
  {F : Finset E //
    (∀ e ∈ F, ¬J.reaches (F.erase e) (J.left e) (J.right e)) ∧
    (∀ y, ∃ i, J.reaches F y (x i)) ∧
    (∀ i j, J.reaches F (x i) (x j) ↔ i=j ∨ s(i,j) ∈ pairs)}

private def sourceLeft (first : Bool) : Fin 3 → Fin 6 :=
  if first then triple124 else triple123
private def sourceRight (first : Bool) : Fin 3 → Fin 6 :=
  if first then triple356 else triple456

private theorem source_pair_relations (first : Bool) (p : Equiv.Perm (Fin 3)) :
    let U := sourceLeft first
    let W := sourceRight first
    let R := fun i j => i = j ∨ s(i,j) ∈ matchingPairs U W p
    (∀ r s, R (U r) (U s) ↔ r = s) ∧
    (∀ r s, R (U r) (W s) ↔ s = p r) ∧
    (∀ r s, R (W r) (U s) ↔ r = p s) ∧
    (∀ r s, R (W r) (W s) ↔ r = s) ∧
    (∀ i, ∃ r, U r = i ∨ W r = i) := by
  revert first p
  decide

/-- Both maps retain exactly the same finite subset of the original copied edge IDs. -/
def sourcePairingGroveEquiv (x : Fin 6 → V) (first : Bool) (p : Equiv.Perm (Fin 3)) :
    J.PairingGrove (x ∘ sourceLeft first) (x ∘ sourceRight first) p ≃
      TerminalRelationForests J x (matchingPairs (sourceLeft first) (sourceRight first) p) where
  toFun F := by
    let U := sourceLeft first
    let W := sourceRight first
    obtain ⟨raa,rab,rba,rbb,cover⟩ := source_pair_relations first p
    have aa (r s : Fin 3) : J.reaches F.val (x (U r)) (x (U s)) ↔ r = s := by
      constructor
      · intro h
        by_contra hne
        exact F.property.2.2.2 r s hne h
      · rintro rfl
        exact Relation.ReflTransGen.refl
    have ab (r s : Fin 3) : J.reaches F.val (x (U r)) (x (W s)) ↔ s = p r :=
      F.property.2.2.1 r s
    have ba (r s : Fin 3) : J.reaches F.val (x (W r)) (x (U s)) ↔ r = p s :=
      ⟨fun h => (ab s r).mp (J.grove_reaches_symm h),
        fun h => J.grove_reaches_symm ((ab s r).mpr h)⟩
    have bb (r s : Fin 3) : J.reaches F.val (x (W r)) (x (W s)) ↔ r = s := by
      constructor
      · intro h
        have hr := (ab (p.symm r) r).mpr (p.apply_symm_apply r).symm
        have hs := (ab (p.symm s) s).mpr (p.apply_symm_apply s).symm
        exact p.symm.injective ((aa (p.symm r) (p.symm s)).mp
          (hr.trans (h.trans (J.grove_reaches_symm hs))))
      · rintro rfl
        exact Relation.ReflTransGen.refl
    refine ⟨F.val,F.property.1,?_,?_⟩
    · intro y
      obtain ⟨r,hr|hr⟩ := F.property.2.1 y
      · exact ⟨U r,hr⟩
      · exact ⟨W r,hr⟩
    · intro i j
      obtain ⟨r,hi|hi⟩ := cover i <;> obtain ⟨s,hj|hj⟩ := cover j
      · subst i; subst j; exact (aa r s).trans (raa r s).symm
      · subst i; subst j; exact (ab r s).trans (rab r s).symm
      · subst i; subst j; exact (ba r s).trans (rba r s).symm
      · subst i; subst j; exact (bb r s).trans (rbb r s).symm
  invFun F := by
    obtain ⟨raa,rab,_,_,cover⟩ := source_pair_relations first p
    refine ⟨F.val,F.property.1,?_,?_,?_⟩
    · intro y
      obtain ⟨i,hi⟩ := F.property.2.1 y
      obtain ⟨r,hr|hr⟩ := cover i
      · refine ⟨r,Or.inl ?_⟩
        change J.reaches F.val y (x (sourceLeft first r))
        rw [hr]
        exact hi
      · refine ⟨r,Or.inr ?_⟩
        change J.reaches F.val y (x (sourceRight first r))
        rw [hr]
        exact hi
    · intro r s
      exact (F.property.2.2 _ _).trans (rab r s)
    · intro r s hne hrs
      exact hne ((raa r s).mp ((F.property.2.2 _ _).mp hrs))
  left_inv _ := by
    apply Subtype.ext
    generalize source_pair_relations first p = h
    rcases h with ⟨_,_,_,_,_⟩
    rfl
  right_inv _ := by
    apply Subtype.ext
    generalize source_pair_relations first p = h
    rcases h with ⟨_,_,_,_,_⟩
    rfl


/-- The complete signed sum, with no planar deletion of unwanted terms in its definition. -/
def signedGroveSum (x : Fin 6 → V) (U W : Fin 3 → Fin 6) : ℝ :=
  ∑ p : Equiv.Perm (Fin 3), ((Equiv.Perm.sign p : ℤ) : ℝ) *
    (Nat.card (J.PairingGrove (x ∘ U) (x ∘ W) p) : ℝ)

/-- Subtraction isolates 16|23|45; zero crossing terms follow from the actual drawing. -/
theorem signed_grove_difference (D : Drawing J) (x : Fin 6 → V)
    (hvertices : ∀ v, D.point v ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (horder : cyclic_order D x) :
    signedGroveSum J x triple124 triple356 - signedGroveSum J x triple123 triple456 =
      (Nat.card (J.PairingGrove (x ∘ triple124) (x ∘ triple356) matching162345) : ℝ) := by
  have h := congrArg (fun a : ℤ => (a : ℝ))
    (signed_noncrossing_difference (fun pairs => (Nat.card (TerminalRelationForests J x pairs) : ℤ)))
  push_cast at h
  have he (first : Bool) :
      signedGroveSum J x (sourceLeft first) (sourceRight first) =
      ∑ p : Equiv.Perm (Fin 3), if triple_noncrossing (sourceLeft first) (sourceRight first) p then
        ((Equiv.Perm.sign p : ℤ) : ℝ) *
          (Nat.card (TerminalRelationForests J x
            (matchingPairs (sourceLeft first) (sourceRight first) p)) : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases hn : triple_noncrossing (sourceLeft first) (sourceRight first) p
    · rw [if_pos hn, ← Nat.card_congr (sourcePairingGroveEquiv J x first p)]
    · rw [if_neg hn, D.card_pairing_grove_eq_zero_of_crossing x hvertices hedges horder
        (sourceLeft first) (sourceRight first) p hn]
      simp only [Nat.cast_zero,mul_zero]
  rw [show signedGroveSum J x triple124 triple356 = _ from he true,
    show signedGroveSum J x triple123 triple456 = _ from he false]
  have hp : Nat.card (J.PairingGrove (x ∘ triple124) (x ∘ triple356) matching162345) =
      Nat.card (TerminalRelationForests J x (matchingPairs triple124 triple356 matching162345)) :=
    Nat.card_congr (sourcePairingGroveEquiv J x true matching162345)
  rw [hp]
  exact h

/-- KW8.1+B.3 on both complete signed sums, sharing the full copied-tree denominator. -/
theorem signed_ratios (hc : (supportGraph J.left J.right).Preconnected)
    (x : Fin 6 → V) (hx : Function.Injective x) :
    let G := fun r s => groundedGreen J.left J.right (x 0) hc (x r) (x s)
    signedGroveSum J x triple124 triple356 / (Nat.card J.SpanningTree : ℝ) =
      ((Matrix.of fun r s : Fin 3 => (Polynomial.X : Polynomial ℝ)-Polynomial.C
        ((G (triple124 r) (triple124 r)+G (triple356 s) (triple356 s)-
          2*G (triple124 r) (triple356 s))/2)).det).coeff 1 ∧
    signedGroveSum J x triple123 triple456 / (Nat.card J.SpanningTree : ℝ) =
      ((Matrix.of fun r s : Fin 3 => (Polynomial.X : Polynomial ℝ)-Polynomial.C
        ((G (triple123 r) (triple123 r)+G (triple456 s) (triple456 s)-
          2*G (triple123 r) (triple456 s))/2)).det).coeff 1 := by
  intro G
  obtain ⟨hu,hw,hd,_,hu',hw',hd',_⟩ := source_triples_complete
  have dis (U W : Fin 3 → Fin 6) (h : Disjoint (Set.range U) (Set.range W)) :
      ∀ r s, (x ∘ U) r ≠ (x ∘ W) s := by
    intro r s heq
    exact Set.disjoint_left.mp h ⟨r,rfl⟩ ⟨s,(hx heq).symm⟩
  constructor
  · exact FiniteAvalanches.External.kenyonWilson_pairingGroves_resistanceMinor
      J hc (x 0) (by decide : 0 < 3) (x ∘ triple124) (x ∘ triple356)
      (hx.comp hu) (hx.comp hw) (dis _ _ hd)
  · exact FiniteAvalanches.External.kenyonWilson_pairingGroves_resistanceMinor
      J hc (x 0) (by decide : 0 < 3) (x ∘ triple123) (x ∘ triple456)
      (hx.comp hu') (hx.comp hw') (dis _ _ hd')

end
end FiniteAvalanches.Electrical.PairFormula
