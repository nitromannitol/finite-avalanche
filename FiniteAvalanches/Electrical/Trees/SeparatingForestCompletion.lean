import FiniteAvalanches.Electrical.Trees.TwoCopyGroves

/-! Completing a separating two-root forest along a prescribed boundary suffix. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- Every vertex belongs to exactly one of two rooted components; every copy is acyclic. -/
abbrev TwoRootForest (J : CopiedGraph V E) (u v : V) := {F : Finset E //
  (∀ e ∈ F, ¬J.reaches (F.erase e) (J.left e) (J.right e)) ∧
    ∀ x, ∃ r ∈ ({u, v} : Set V), J.reaches F x r ∧
      ∀ r' ∈ ({u, v} : Set V), J.reaches F x r' → r' = r}

omit [Fintype V] [Fintype E] in
theorem twoRootForest_roots_separated (J : CopiedGraph V E) (u v : V) (hne : u ≠ v)
    (F : J.TwoRootForest u v) : ¬J.reaches F.val u v := by
  intro h
  obtain ⟨r, _, _, hu⟩ := F.property.2 u
  exact hne ((hu u (Or.inl rfl) .refl).trans (hu v (Or.inr rfl) h).symm)

omit [Fintype V] [Fintype E] in
/-- Adding any original copy between the two components gives a full spanning tree. -/
theorem twoRootForest_insert_tree (J : CopiedGraph V E) (u v : V)
    (F : J.TwoRootForest u v) (e : E)
    (hsep : ¬J.reaches F.val (J.left e) (J.right e)) :
    (Set.univ : Set V).Nonempty ∧ (∀ x y, J.reaches (insert e F.val) x y) ∧
      ∀ f ∈ insert e F.val, ¬J.reaches ((insert e F.val).erase f) (J.left f) (J.right f) := by
  obtain ⟨r, hr, hl, _⟩ := F.property.2 (J.left e)
  obtain ⟨s, hs, ht, _⟩ := F.property.2 (J.right e)
  have hrs : r ≠ s := by
    intro heq
    exact hsep (hl.trans (heq ▸ TwoCopy.reaches_symm J ht))
  have lift {x y : V} (h : J.reaches F.val x y) : J.reaches (insert e F.val) x y :=
    TwoCopy.reaches_mono J (Finset.subset_insert _ _) h
  have hedge : J.reaches (insert e F.val) (J.left e) (J.right e) :=
    .single ⟨e, Finset.mem_insert_self _ _, Or.inl ⟨rfl, rfl⟩⟩
  have huv : J.reaches (insert e F.val) u v := by
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
    · exact (hrs rfl).elim
    · exact ((TwoCopy.reaches_symm J (lift hl)).trans hedge).trans (lift ht)
    · exact ((TwoCopy.reaches_symm J (lift ht)).trans
        (TwoCopy.reaches_symm J hedge)).trans (lift hl)
    · exact (hrs rfl).elim
  have cover (x : V) : J.reaches (insert e F.val) x u := by
    obtain ⟨r, hr, hx, _⟩ := F.property.2 x
    rcases hr with rfl | rfl
    · exact lift hx
    · exact (lift hx).trans (TwoCopy.reaches_symm J huv)
  exact ⟨⟨u, Set.mem_univ _⟩,
    fun x y => (cover x).trans (TwoCopy.reaches_symm J (cover y)),
    TwoCopy.forest_insert J F.property.1 e hsep⟩

omit [Fintype V] [Fintype E] in
/-- A separating forest has a missing component-crossing copy on every actual suffix path. -/
theorem exists_suffix_crossing_copy (J : CopiedGraph V E) (m : ℕ)
    (vertices : Fin (m + 1) → V) (copies : Fin m → E)
    (hends : ∀ k : Fin m,
      (J.left (copies k) = vertices k.castSucc ∧ J.right (copies k) = vertices k.succ) ∨
      (J.right (copies k) = vertices k.castSucc ∧ J.left (copies k) = vertices k.succ))
    (i : Fin (m + 1)) (F : Finset E)
    (hsep : ¬J.reaches F (vertices i) (vertices (Fin.last m))) :
    ∃ k : Fin m, i.val ≤ k.val ∧ ¬J.reaches F (J.left (copies k)) (J.right (copies k)) := by
  by_contra hnot
  have steps (k : Fin m) (hk : i.val ≤ k.val) :
      J.reaches F (vertices k.castSucc) (vertices k.succ) := by
    have h : J.reaches F (J.left (copies k)) (J.right (copies k)) := by
      by_contra hn
      exact hnot ⟨k, hk, hn⟩
    rcases hends k with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact ha ▸ hb ▸ h
    · exact ha ▸ hb ▸ TwoCopy.reaches_symm J h
  have walk : ∀ n : ℕ, ∀ hn : n ≤ m, i.val ≤ n →
      J.reaches F (vertices i) (vertices ⟨n, Nat.lt_succ_of_le hn⟩) := by
    intro n
    induction n with
    | zero =>
      intro hn hi
      have he : i = ⟨0, Nat.lt_succ_of_le hn⟩ := Fin.ext (Nat.le_zero.mp hi)
      rw [he]
      exact .refl
    | succ n ih =>
      intro hn hi
      by_cases he : i.val = n + 1
      · rw [show i = ⟨n + 1, Nat.lt_succ_of_le hn⟩ from Fin.ext he]
        exact .refl
      · have hi' : i.val ≤ n := by omega
        have hnm : n < m := by omega
        exact (ih (Nat.le_of_lt hnm) hi').trans (steps ⟨n, hnm⟩ hi')
  exact hsep (walk m (le_refl m) (Nat.le_of_lt_succ i.isLt))

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
