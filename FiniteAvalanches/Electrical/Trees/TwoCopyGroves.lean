import FiniteAvalanches.Electrical.Geometry.DiskDrawing
import Mathlib.Data.Fintype.BigOperators

/-! Deleting and reattaching two original copies on their literal three-component carrier. -/
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
namespace TwoCopy
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

/-- Three spanning components with terminal blocks `{u,a}`, `{b,c}`, `{d,v}`.
The terminals within a block may coincide; different blocks cannot coincide. -/
abbrev PathGrove (u a b c d v : V) := {F : Finset E //
  (∀ e ∈ F, ¬J.reaches (F.erase e) (J.left e) (J.right e)) ∧
  (∀ x, J.reaches F x a ∨ J.reaches F x b ∨ J.reaches F x d) ∧
  ¬J.reaches F a b ∧ ¬J.reaches F a d ∧ ¬J.reaches F b d ∧
  J.reaches F u a ∧ J.reaches F b c ∧ J.reaches F d v}

/-- Literal directed, ordered use: deleting both copies leaves the three path segments. -/
def orderedCut (T : J.SpanningTree) (u v : V) (e f : E) : Prop :=
  e ∈ T.val ∧ f ∈ T.val ∧
  J.reaches ((T.val.erase e).erase f) u (J.left e) ∧
  J.reaches ((T.val.erase e).erase f) (J.right e) (J.left f) ∧
  J.reaches ((T.val.erase e).erase f) (J.right f) v

/-- Unordered use is exactly the two original-copy tree-path separation events. -/
def bothOnPath (T : J.SpanningTree) (u v : V) (e f : E) : Prop :=
  (e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v) ∧
  (f ∈ T.val ∧ ¬J.reaches (T.val.erase f) u v)

omit [Fintype V] [Fintype E] in
theorem reaches_symm {F : Finset E} {x y : V} (h : J.reaches F x y) :
    J.reaches F y x := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hyz ih =>
    obtain ⟨e,he,hh⟩ := hyz
    exact Relation.ReflTransGen.head ⟨e,he,hh.elim
      (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)⟩ ih

omit [Fintype V] [Fintype E] in
theorem reaches_mono {F H : Finset E} (hFH : F ⊆ H) {x y : V}
    (h : J.reaches F x y) : J.reaches H x y := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail ⟨h.choose,hFH h.choose_spec.1,h.choose_spec.2⟩

omit [Fintype V] [Fintype E] in
theorem reaches_insert_iff (F : Finset E) (e : E) (x y : V) :
    J.reaches (insert e F) x y ↔ J.reaches F x y ∨
      (J.reaches F x (J.left e) ∧ J.reaches F (J.right e) y) ∨
      (J.reaches F x (J.right e) ∧ J.reaches F (J.left e) y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl .refl
    | @tail z y _ h ih =>
      obtain ⟨f,hf,hends⟩ := h
      rcases Finset.mem_insert.mp hf with rfl | hf
      · rcases hends with hends | hends
        · rw [← hends.1] at ih
          rw [← hends.2]
          rcases ih with h | ⟨h,_⟩ | ⟨h,_⟩
          · exact Or.inr (Or.inl ⟨h,.refl⟩)
          · exact Or.inr (Or.inl ⟨h,.refl⟩)
          · exact Or.inl h
        · rw [← hends.1] at ih
          rw [← hends.2]
          rcases ih with h | ⟨h,_⟩ | ⟨h,_⟩
          · exact Or.inr (Or.inr ⟨h,.refl⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h,.refl⟩)
      · have hs : J.reaches F z y := .single ⟨f,hf,hends⟩
        exact ih.imp (fun h => h.trans hs)
          (fun h => h.imp (fun h => ⟨h.1,h.2.trans hs⟩) (fun h => ⟨h.1,h.2.trans hs⟩))
  · intro h
    have mono {z w : V} (h : J.reaches F z w) : J.reaches (insert e F) z w :=
      reaches_mono J (Finset.subset_insert _ _) h
    have step : J.reaches (insert e F) (J.left e) (J.right e) :=
      .single ⟨e,Finset.mem_insert_self _ _,Or.inl ⟨rfl,rfl⟩⟩
    rcases h with h | ⟨h,k⟩ | ⟨h,k⟩
    · exact mono h
    · exact ((mono h).trans step).trans (mono k)
    · exact ((mono h).trans (reaches_symm J step)).trans (mono k)

omit [Fintype V] [Fintype E] in
theorem forest_insert {F : Finset E}
    (hF : ∀ f ∈ F, ¬J.reaches (F.erase f) (J.left f) (J.right f))
    (e : E) (hsep : ¬J.reaches F (J.left e) (J.right e)) :
    ∀ f ∈ insert e F, ¬J.reaches ((insert e F).erase f) (J.left f) (J.right f) := by
  have he : e ∉ F := fun he => hsep (.single ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩)
  intro f hf h
  by_cases hfe : f = e
  · subst f
    exact hsep (by simpa [he] using h)
  · have hfF := (Finset.mem_insert.mp hf).resolve_left hfe
    have h' : J.reaches (insert e (F.erase f)) (J.left f) (J.right f) := by
      simpa only [Finset.erase_insert_of_ne (Ne.symm hfe)] using h
    have mono {x y : V} (h : J.reaches (F.erase f) x y) : J.reaches F x y :=
      reaches_mono J (Finset.erase_subset _ _) h
    have step : J.reaches F (J.left f) (J.right f) :=
      .single ⟨f,hfF,Or.inl ⟨rfl,rfl⟩⟩
    rcases (reaches_insert_iff J _ _ _ _).mp h' with h' | ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact hF f hfF h'
    · exact hsep (((reaches_symm J (mono ha)).trans step).trans (reaches_symm J (mono hb)))
    · exact hsep (reaches_symm J
        (((reaches_symm J (mono hb)).trans step).trans (reaches_symm J (mono ha))))

omit [Fintype V] [Fintype E] in
theorem delete_two_grove (T : J.SpanningTree) (u v : V) (e f : E) (hef : e ≠ f)
    (h : orderedCut J T u v e f) :
    ∃ F : PathGrove J u (J.left e) (J.right e) (J.left f) (J.right f) v,
      F.val = (T.val.erase e).erase f := by
  let F := (T.val.erase e).erase f
  have monoE {x y : V} (hr : J.reaches F x y) : J.reaches (T.val.erase e) x y :=
    reaches_mono J (Finset.erase_subset _ _) hr
  have monoF {x y : V} (hr : J.reaches F x y) : J.reaches (T.val.erase f) x y :=
    reaches_mono J (by intro a ha; simp only [F,Finset.mem_erase] at ha ⊢; exact ⟨ha.1,ha.2.2⟩) hr
  have hab : ¬J.reaches F (J.left e) (J.right e) :=
    fun hr => T.property.2.2 e h.1 (monoE hr)
  have hbd : ¬J.reaches F (J.right e) (J.right f) := by
    intro hr
    exact T.property.2.2 f h.2.1 (monoF ((reaches_symm J h.2.2.2.1).trans hr))
  have had : ¬J.reaches F (J.left e) (J.right f) := by
    intro hr
    have step : J.reaches (T.val.erase e) (J.left f) (J.right f) :=
      .single ⟨f,Finset.mem_erase.mpr ⟨hef.symm,h.2.1⟩,Or.inl ⟨rfl,rfl⟩⟩
    exact T.property.2.2 e h.1 (((monoE hr).trans (reaches_symm J step)).trans
      (reaches_symm J (monoE h.2.2.2.1)))
  have cover (x : V) : J.reaches F (J.left e) x ∨
      J.reaches F (J.right e) x ∨ J.reaches F (J.right f) x := by
    have hr := T.property.2.1 (J.left e) x
    induction hr with
    | refl => exact Or.inl .refl
    | @tail z y _ hz ih =>
      obtain ⟨a,ha,he⟩ := hz
      by_cases hae : a = e
      · subst a
        rcases he with he | he
        · rw [← he.2]; exact Or.inr (Or.inl .refl)
        · rw [← he.2]; exact Or.inl .refl
      · by_cases haf : a = f
        · subst a
          rcases he with he | he
          · rw [← he.2]; exact Or.inr (Or.inr .refl)
          · rw [← he.2]; exact Or.inr (Or.inl h.2.2.2.1)
        · have hs : J.reaches F z y :=
            .single ⟨a,Finset.mem_erase.mpr ⟨haf,Finset.mem_erase.mpr ⟨hae,ha⟩⟩,he⟩
          exact ih.imp (fun hr => hr.trans hs)
            (fun hr => hr.imp (fun hr => hr.trans hs) (fun hr => hr.trans hs))
  refine ⟨⟨F,?_,?_,hab,had,hbd,h.2.2⟩,rfl⟩
  · intro a ha hr
    apply T.property.2.2 a (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha))
    exact reaches_mono J (by intro b hb; simp only [F,Finset.mem_erase] at hb ⊢; tauto) hr
  · intro x
    exact (cover x).imp (reaches_symm J) (fun hr => hr.imp (reaches_symm J) (reaches_symm J))

/-- Reattachment joins precisely the three actual components, even when terminals coincide. -/
def reattach (u v : V) (e f : E)
    (F : PathGrove J u (J.left e) (J.right e) (J.left f) (J.right f) v) :
    J.SpanningTree := by
  have hab := F.property.2.2.1
  have had := F.property.2.2.2.1
  have hbd := F.property.2.2.2.2.1
  have hbc := F.property.2.2.2.2.2.2.1
  have hsep : ¬J.reaches (insert e F.val) (J.left f) (J.right f) := by
    intro h
    rcases (reaches_insert_iff J _ _ _ _).mp h with hr | ⟨hca,hbd'⟩ | ⟨hcb,had'⟩
    · exact hbd (hbc.trans hr)
    · exact hbd hbd'
    · exact had had'
  have forest := forest_insert J (forest_insert J F.property.1 e hab) f hsep
  have cover (x : V) : J.reaches (insert f (insert e F.val)) x (J.left e) := by
    have mono {x y : V} (h : J.reaches F.val x y) :
        J.reaches (insert f (insert e F.val)) x y :=
      reaches_mono J (fun _ ha => by simp [ha]) h
    have stepE : J.reaches (insert f (insert e F.val)) (J.left e) (J.right e) :=
      .single ⟨e,by simp,Or.inl ⟨rfl,rfl⟩⟩
    have stepF : J.reaches (insert f (insert e F.val)) (J.left f) (J.right f) :=
      .single ⟨f,by simp,Or.inl ⟨rfl,rfl⟩⟩
    rcases F.property.2.1 x with ha | hb | hd
    · exact mono ha
    · exact (mono hb).trans (reaches_symm J stepE)
    · exact ((mono hd).trans (reaches_symm J stepF)).trans
        ((reaches_symm J (mono hbc)).trans (reaches_symm J stepE))
  exact ⟨insert f (insert e F.val),⟨J.left e,Set.mem_univ _⟩,
    fun x y => (cover x).trans (reaches_symm J (cover y)),forest⟩

omit [Fintype V] [Fintype E] in
theorem grove_copies_absent (u v : V) (e f : E)
    (F : PathGrove J u (J.left e) (J.right e) (J.left f) (J.right f) v) :
    e ∉ F.val ∧ f ∉ F.val := by
  constructor
  · intro he
    exact F.property.2.2.1 (.single ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩)
  · intro hf
    exact F.property.2.2.2.2.1
      (F.property.2.2.2.2.2.2.1.tail ⟨f,hf,Or.inl ⟨rfl,rfl⟩⟩)

/-- The forward map deletes exactly `e,f`; the inverse inserts exactly those same IDs. -/
def orderedCutGroveEquiv (u v : V) (e f : E) (hef : e ≠ f) :
    {T : J.SpanningTree // orderedCut J T u v e f} ≃
      PathGrove J u (J.left e) (J.right e) (J.left f) (J.right f) v where
  toFun T := ⟨(T.val.val.erase e).erase f,
    by
      obtain ⟨F,hF⟩ := delete_two_grove J T.val u v e f hef T.property
      rw [← hF]
      exact F.property⟩
  invFun F := by
    have hn := grove_copies_absent J u v e f F
    have hval : (((reattach J u v e f F).val.erase e).erase f) = F.val := by
      change ((insert f (insert e F.val)).erase e).erase f = F.val
      ext a; simp; aesop
    exact ⟨reattach J u v e f F,by
      refine ⟨by simp [reattach],by simp [reattach],?_⟩
      rw [hval]
      exact F.property.2.2.2.2.2⟩
  left_inv T := by
    apply Subtype.ext; apply Subtype.ext
    change insert f (insert e ((T.val.val.erase e).erase f)) = T.val.val
    ext a
    by_cases hae : a = e
    · subst a; simp [T.property.1]
    by_cases haf : a = f
    · subst a; simp [T.property.2.1]
    simp [hae,haf]
  right_inv F := by
    apply Subtype.ext
    have hn := grove_copies_absent J u v e f F
    change ((insert f (insert e F.val)).erase e).erase f = F.val
    ext a; simp only [Finset.mem_erase,Finset.mem_insert]; aesop

omit [Fintype V] [Fintype E] in
theorem orderedCut_implies_bothOnPath (T : J.SpanningTree) (u v : V) (e f : E)
    (hef : e ≠ f) (h : orderedCut J T u v e f) : bothOnPath J T u v e f := by
  have monoE {x y : V} (hr : J.reaches ((T.val.erase e).erase f) x y) :
      J.reaches (T.val.erase e) x y := reaches_mono J (Finset.erase_subset _ _) hr
  have monoF {x y : V} (hr : J.reaches ((T.val.erase e).erase f) x y) :
      J.reaches (T.val.erase f) x y := reaches_mono J
        (by intro a ha; simp only [Finset.mem_erase] at ha ⊢; exact ⟨ha.1,ha.2.2⟩) hr
  have hev : J.reaches (T.val.erase e) (J.right e) v :=
    ((monoE h.2.2.2.1).tail ⟨f,Finset.mem_erase.mpr ⟨hef.symm,h.2.1⟩,
      Or.inl ⟨rfl,rfl⟩⟩).trans (monoE h.2.2.2.2)
  have hfu : J.reaches (T.val.erase f) u (J.left f) :=
    ((monoF h.2.2.1).tail ⟨e,Finset.mem_erase.mpr ⟨hef,h.1⟩,
      Or.inl ⟨rfl,rfl⟩⟩).trans (monoF h.2.2.2.1)
  refine ⟨⟨h.1,?_⟩,⟨h.2.1,?_⟩⟩
  · intro hr
    exact T.property.2.2 e h.1
      (((reaches_symm J (monoE h.2.2.1)).trans hr).trans (reaches_symm J hev))
  · intro hr
    exact T.property.2.2 f h.2.1
      (((reaches_symm J hfu).trans hr).trans (reaches_symm J (monoF h.2.2.2.2)))

omit [Fintype V] [Fintype E] in
/-- This normalization is the full original tree carrier, including a zero denominator. -/
theorem orderedCut_count (u v : V) (e f : E) (hef : e ≠ f) :
    Nat.card {T : J.SpanningTree // orderedCut J T u v e f} =
      Nat.card (PathGrove J u (J.left e) (J.right e) (J.left f) (J.right f) v) :=
  Nat.card_congr (orderedCutGroveEquiv J u v e f hef)

end
end TwoCopy
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
