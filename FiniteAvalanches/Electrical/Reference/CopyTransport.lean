import FiniteAvalanches.Electrical.Trees.TwoCopyGroves
import FiniteAvalanches.Electrical.Geometry.CopiedGraphConnectivity

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E A : Type} [Fintype V] [Fintype E] [Fintype A]

omit [Fintype V] [Fintype E] [Fintype A] in
/-- Inclusion preserves every original copied walk, in both directions. -/
theorem reaches_image_iff (J : CopiedGraph V E) (K : CopiedGraph V A)
    (f : A → E) (hl : ∀ a, J.left (f a) = K.left a)
    (hr : ∀ a, J.right (f a) = K.right a) (S : Finset A) (x y : V) :
    J.reaches (S.image f) x y ↔ K.reaches S x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hadj ih =>
      obtain ⟨e, he, hends⟩ := hadj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact ih.tail ⟨a, ha, by simpa only [hl, hr] using hends⟩
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hadj ih =>
      obtain ⟨a, ha, hends⟩ := hadj
      exact ih.tail ⟨f a, Finset.mem_image_of_mem f ha,
        by simpa only [hl, hr] using hends⟩

omit [Fintype V] [Fintype E] [Fintype A] in
/-- Tree restriction/inclusion changes neither vertices nor the selected original IDs. -/
theorem tree_image_iff (J : CopiedGraph V E) (K : CopiedGraph V A)
    (f : A → E) (hf : Function.Injective f)
    (hl : ∀ a, J.left (f a) = K.left a)
    (hr : ∀ a, J.right (f a) = K.right a) (S : Finset A) :
    ((Set.univ : Set V).Nonempty ∧ (∀ x y, J.reaches (S.image f) x y) ∧
      ∀ e ∈ S.image f, ¬J.reaches ((S.image f).erase e) (J.left e) (J.right e)) ↔
    ((Set.univ : Set V).Nonempty ∧ (∀ x y, K.reaches S x y) ∧
      ∀ a ∈ S, ¬K.reaches (S.erase a) (K.left a) (K.right a)) := by
  have reach := reaches_image_iff J K f hl hr
  constructor
  · rintro ⟨hne, hc, ht⟩
    refine ⟨hne, fun x y => (reach S x y).mp (hc x y), ?_⟩
    intro a ha h
    apply ht (f a) (Finset.mem_image_of_mem f ha)
    rw [← Finset.image_erase hf]
    rw [hl, hr]
    exact (reach (S.erase a) _ _).mpr h
  · rintro ⟨hne, hc, ht⟩
    refine ⟨hne, fun x y => (reach S x y).mpr (hc x y), ?_⟩
    intro e he h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    apply ht a ha
    rw [← Finset.image_erase hf, hl, hr] at h
    exact (reach (S.erase a) _ _).mp h

omit [Fintype V] [Fintype E] in
/-- Replacing one selected tree copy succeeds exactly when the new copy crosses its cut. -/
theorem tree_exchange_iff (J : CopiedGraph V E) (T : J.SpanningTree)
    (e f : E) (he : e ∈ T.val) (hf : f ∉ T.val) :
    ((Set.univ : Set V).Nonempty ∧
      (∀ x y, J.reaches (insert f (T.val.erase e)) x y) ∧
      ∀ a ∈ insert f (T.val.erase e),
        ¬J.reaches ((insert f (T.val.erase e)).erase a) (J.left a) (J.right a)) ↔
      ¬J.reaches (T.val.erase e) (J.left f) (J.right f) := by
  let F := T.val.erase e
  have hfF : f ∉ F := fun h => hf (Finset.mem_of_mem_erase h)
  constructor
  · intro h
    have hh := h.2.2 f (Finset.mem_insert_self f F)
    change ¬J.reaches ((insert f F).erase f) (J.left f) (J.right f) at hh
    rw [Finset.erase_insert hfF] at hh
    exact hh
  · intro hsep
    have cover (x : V) : J.reaches F (J.left e) x ∨ J.reaches F (J.right e) x := by
      have h := T.property.2.1 (J.left e) x
      rw [← Finset.insert_erase he, TwoCopy.reaches_insert_iff J] at h
      rcases h with h | ⟨_, h⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact (T.property.2.2 e he h).elim
    have bridge : J.reaches (insert f F) (J.left e) (J.right e) := by
      rcases cover (J.left f) with hl | hl <;>
        rcases cover (J.right f) with hr | hr
      · exact (hsep ((TwoCopy.reaches_symm J hl).trans hr)).elim
      · exact (TwoCopy.reaches_insert_iff J F f _ _).mpr
          (Or.inr (Or.inl ⟨hl, TwoCopy.reaches_symm J hr⟩))
      · exact (TwoCopy.reaches_insert_iff J F f _ _).mpr
          (Or.inr (Or.inr ⟨hr, TwoCopy.reaches_symm J hl⟩))
      · exact (hsep ((TwoCopy.reaches_symm J hl).trans hr)).elim
    refine ⟨T.property.1, ?_, ?_⟩
    · intro x y
      have conn (z : V) : J.reaches (insert f F) (J.left e) z := by
        rcases cover z with hz | hz
        · exact TwoCopy.reaches_mono J (Finset.subset_insert _ _) hz
        · exact bridge.trans (TwoCopy.reaches_mono J (Finset.subset_insert _ _) hz)
      exact (TwoCopy.reaches_symm J (conn x)).trans (conn y)
    · apply TwoCopy.forest_insert J _ f hsep
      intro a ha h
      apply T.property.2.2 a (Finset.mem_of_mem_erase ha)
      exact TwoCopy.reaches_mono J
        (by
          intro b hb
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hb).1,
            Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)⟩) h

omit [Fintype V] in
/-- A complement bijection exchanges primal fundamental cuts with dual fundamental paths. -/
theorem complement_exchange {W : Type}
    (G : CopiedGraph V E) (K : CopiedGraph W E)
    (hcomp : ∀ S : Finset E,
      ((Set.univ : Set V).Nonempty ∧ (∀ x y, G.reaches S x y) ∧
        ∀ a ∈ S, ¬G.reaches (S.erase a) (G.left a) (G.right a)) ↔
      ((Set.univ : Set W).Nonempty ∧ (∀ x y, K.reaches Sᶜ x y) ∧
        ∀ a ∈ Sᶜ, ¬K.reaches (Sᶜ.erase a) (K.left a) (K.right a)))
    (T : G.SpanningTree) (U : K.SpanningTree) (hU : U.val = T.valᶜ)
    (e f : E) (he : e ∈ T.val) (hf : f ∉ T.val) :
    ¬G.reaches (T.val.erase e) (G.left f) (G.right f) ↔
      ¬K.reaches (U.val.erase f) (K.left e) (K.right e) := by
  have hfU : f ∈ U.val := by rw [hU]; exact Finset.mem_compl.mpr hf
  have heU : e ∉ U.val := by rw [hU]; exact Finset.notMem_compl.mpr he
  have swap : (insert f (T.val.erase e))ᶜ = insert e (U.val.erase f) := by
    rw [hU]
    ext a
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_erase]
    by_cases hae : a = e <;> by_cases haf : a = f
    · subst a
      exact (hf (haf ▸ he)).elim
    · subst a
      simp [haf]
    · subst a
      simp [hae]
    · simp [hae, haf]
  have hc := hcomp (insert f (T.val.erase e))
  rw [swap] at hc
  exact (tree_exchange_iff G T e f he hf).symm.trans
    (hc.trans (tree_exchange_iff K U f e hfU heU))

omit [Fintype V] [Fintype E] in
/-- The unoriented original-copy path event is invariant under exchanging its terminals. -/
theorem pathIndicator_swap (J : CopiedGraph V E) (T : J.SpanningTree)
    (u v : V) (e : E) : J.pathIndicator T u v e = J.pathIndicator T v u e := by
  have hi : (e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v) ↔
      (e ∈ T.val ∧ ¬J.reaches (T.val.erase e) v u) :=
    and_congr_right (fun _ => not_congr
      ⟨fun h => TwoCopy.reaches_symm J h, fun h => TwoCopy.reaches_symm J h⟩)
  unfold pathIndicator
  by_cases h : e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v
  · rw [if_pos h, if_pos (hi.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hi.mpr h'))]
end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
