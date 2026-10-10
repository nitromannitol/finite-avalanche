import FiniteAvalanches.Electrical.Trees.Pendants.Reachability

/-! Literal pendant deletion/lifting equivalences for trees and the source's paired groves. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E K : Type} [Fintype K]
noncomputable local instance : DecidableEq (E ⊕ K) := Classical.decEq _

omit [Fintype K] in
/-- Pairing a fresh terminal with a different vertex forces its unique incident copy. -/
theorem pendant_forced_pairing (J : CopiedGraph V E) (z : K → V)
    {n : ℕ} {A B : Fin n → V ⊕ K} {π : Equiv.Perm (Fin n)}
    (F : (J.withPendants z).PairingGrove A B π)
    (roots : ∀ k, ∃ r, (A r = Sum.inr k ∧ B (π r) ≠ Sum.inr k) ∨
      (B (π r) = Sum.inr k ∧ A r ≠ Sum.inr k)) :
    ∀ k, Sum.inr k ∈ F.val := by
  intro k
  by_contra hk
  obtain ⟨r,⟨ha,hb⟩ | ⟨hb,ha⟩⟩ := roots k
  · have h := (F.property.2.2.1 r (π r)).mpr rfl
    rw [ha] at h
    exact hb (J.pendant_missing_isolated z k hk h)
  · have h := pendant_reaches_reverse _ ((F.property.2.2.1 r (π r)).mpr rfl)
    rw [hb] at h
    exact ha (J.pendant_missing_isolated z k hk h)

/-- Delete the fresh copies, or add them all; the original identifiers never change. -/
def pendantPairingEquiv (J : CopiedGraph V E) (z : K → V)
    {n : ℕ} (A B : Fin n → V ⊕ K) (π : Equiv.Perm (Fin n))
    (roots : ∀ k, ∃ r, (A r = Sum.inr k ∧ B (π r) ≠ Sum.inr k) ∨
      (B (π r) = Sum.inr k ∧ A r ≠ Sum.inr k)) :
    J.PairingGrove (pendantCollapse z ∘ A) (pendantCollapse z ∘ B) π ≃
      (J.withPendants z).PairingGrove A B π where
  toFun F := by
    let S := pendantLift (K:=K) F.val
    have hs (k : K) : Sum.inr k ∈ S := pendantLift_mem_fresh _ k
    have reach (x y : V ⊕ K) : (J.withPendants z).reaches S x y ↔
        J.reaches F.val (pendantCollapse z x) (pendantCollapse z y) := by
      simpa only [S,pendantLift_toLeft] using J.pendant_reach_iff z S hs x y
    refine ⟨S,?_,?_,?_,?_⟩
    · apply (J.pendant_forest_iff z S).mpr
      simpa only [S,pendantLift_toLeft] using F.property.1
    · intro y
      obtain ⟨r,hr | hr⟩ := F.property.2.1 (pendantCollapse z y)
      · exact ⟨r,Or.inl ((reach y (A r)).mpr hr)⟩
      · exact ⟨r,Or.inr ((reach y (B r)).mpr hr)⟩
    · intro r s
      exact (reach (A r) (B s)).trans (F.property.2.2.1 r s)
    · intro r s hne h
      exact F.property.2.2.2 r s hne ((reach (A r) (A s)).mp h)
  invFun F := by
    have hs := J.pendant_forced_pairing z F roots
    have reach (x y : V ⊕ K) := J.pendant_reach_iff z F.val hs x y
    refine ⟨F.val.toLeft,(J.pendant_forest_iff z F.val).mp F.property.1,?_,?_,?_⟩
    · intro y
      obtain ⟨r,hr | hr⟩ := F.property.2.1 (Sum.inl y)
      · exact ⟨r,Or.inl ((reach (Sum.inl y) (A r)).mp hr)⟩
      · exact ⟨r,Or.inr ((reach (Sum.inl y) (B r)).mp hr)⟩
    · intro r s
      exact (reach (A r) (B s)).symm.trans (F.property.2.2.1 r s)
    · intro r s hne h
      exact F.property.2.2.2 r s hne ((reach (A r) (A s)).mpr h)
  left_inv F := Subtype.ext (pendantLift_toLeft F.val)
  right_inv F := Subtype.ext (pendantLift_project F.val (J.pendant_forced_pairing z F roots))

omit [Fintype K] in
/-- Every tree contains every fresh pendant copy. -/
theorem pendant_forced_tree (J : CopiedGraph V E) (z : K → V)
    (T : (J.withPendants z).SpanningTree) : ∀ k, Sum.inr k ∈ T.val := by
  intro k
  by_contra hk
  have h := J.pendant_missing_isolated z k hk
    (T.property.2.1 (Sum.inr k) (Sum.inl (z k)))
  exact Sum.inl_ne_inr h

/-- The tree bijection preserves each original loop and parallel-copy identifier literally. -/
def pendantTreeEquiv (J : CopiedGraph V E) (z : K → V) :
    J.SpanningTree ≃ (J.withPendants z).SpanningTree where
  toFun T := by
    let S := pendantLift (K:=K) T.val
    have hs (k : K) : Sum.inr k ∈ S := pendantLift_mem_fresh _ k
    refine ⟨S,?_,?_,?_⟩
    · obtain ⟨v,_⟩ := T.property.1
      exact ⟨Sum.inl v,Set.mem_univ _⟩
    · intro x y
      apply (J.pendant_reach_iff z S hs x y).mpr
      simpa only [S,pendantLift_toLeft] using
        T.property.2.1 (pendantCollapse z x) (pendantCollapse z y)
    · apply (J.pendant_forest_iff z S).mpr
      simpa only [S,pendantLift_toLeft] using T.property.2.2
  invFun T := by
    have hs := J.pendant_forced_tree z T
    refine ⟨T.val.toLeft,?_,?_,(J.pendant_forest_iff z T.val).mp T.property.2.2⟩
    · obtain ⟨v,_⟩ := T.property.1
      exact ⟨pendantCollapse z v,Set.mem_univ _⟩
    · intro x y
      exact (J.pendant_reach_iff z T.val hs (Sum.inl x) (Sum.inl y)).mp
        (T.property.2.1 (Sum.inl x) (Sum.inl y))
  left_inv T := Subtype.ext (pendantLift_toLeft T.val)
  right_inv T := Subtype.ext (pendantLift_project T.val (J.pendant_forced_tree z T))

theorem pendantTree_count (J : CopiedGraph V E) (z : K → V) :
    Nat.card (J.withPendants z).SpanningTree = Nat.card J.SpanningTree :=
  Nat.card_congr (J.pendantTreeEquiv z).symm


end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
