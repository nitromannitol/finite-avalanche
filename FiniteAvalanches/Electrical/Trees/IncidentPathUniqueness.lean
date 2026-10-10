import FiniteAvalanches.Electrical.Reference.CopyTransport

/-! A tree path beginning at a vertex uses at most one copied edge incident to it. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type}

/-- A walk in a component avoiding a vertex avoids each edge incident to that vertex. -/
theorem reaches_erase_incident_of_not_reaches (J : CopiedGraph V E)
    (A : Finset E) (p x y : V) (f : E)
    (hf : J.left f = p ∨ J.right f = p) (hx : ¬J.reaches A x p)
    (h : J.reaches A x y) : J.reaches (A.erase f) x y := by
  induction h with
  | refl => exact .refl
  | @tail z y hprev hadj ih =>
    obtain ⟨e, he, hends⟩ := hadj
    have hef : e ≠ f := by
      intro heq
      subst e
      have hwhole := hprev.tail ⟨f, he, hends⟩
      rcases hf with hfp | hfp <;> rcases hends with hh | hh
      · exact hx ((hh.1.symm.trans hfp) ▸ hprev)
      · exact hx ((hh.2.symm.trans hfp) ▸ hwhole)
      · exact hx ((hh.2.symm.trans hfp) ▸ hwhole)
      · exact hx ((hh.1.symm.trans hfp) ▸ hprev)
    exact ih.tail ⟨e, Finset.mem_erase.mpr ⟨hef, he⟩, hends⟩

/-- Two selected edges at the first vertex cannot both separate the same tree path. -/
theorem tree_path_incident_unique (J : CopiedGraph V E) (T : J.SpanningTree)
    (p q : V) (e f : E) (he : e ∈ T.val)
    (hep : J.left e = p ∨ J.right e = p)
    (hfp : J.left f = p ∨ J.right f = p)
    (hecut : ¬J.reaches (T.val.erase e) p q)
    (hfcut : ¬J.reaches (T.val.erase f) p q) : e = f := by
  by_contra hef
  have monotone {x y : V} (h : J.reaches ((T.val.erase e).erase f) x y) :
      J.reaches (T.val.erase f) x y :=
    TwoCopy.reaches_mono J (by
      intro a ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha)⟩) h
  have conn := T.property.2.1 p q
  rw [← Finset.insert_erase he, TwoCopy.reaches_insert_iff J] at conn
  have heF : e ∈ T.val.erase f := Finset.mem_erase.mpr ⟨hef, he⟩
  rcases hep with hep | hep
  · have hother : J.reaches (T.val.erase e) (J.right e) q := by
      rcases conn with h | ⟨_, h⟩ | ⟨h, _⟩
      · exact (hecut h).elim
      · exact h
      · exfalso
        apply T.property.2.2 e he
        rwa [hep]
    have hotherp : ¬J.reaches (T.val.erase e) (J.right e) p := by
      intro h
      apply T.property.2.2 e he
      rw [hep]
      exact TwoCopy.reaches_symm J h
    have havoid := reaches_erase_incident_of_not_reaches J (T.val.erase e)
      p (J.right e) q f hfp hotherp hother
    have hedge : J.reaches (T.val.erase f) p (J.right e) :=
      .single ⟨e, heF, Or.inl ⟨hep, rfl⟩⟩
    exact hfcut (hedge.trans (monotone havoid))
  · have hother : J.reaches (T.val.erase e) (J.left e) q := by
      rcases conn with h | ⟨h, _⟩ | ⟨_, h⟩
      · exact (hecut h).elim
      · exfalso
        apply T.property.2.2 e he
        rw [hep]
        exact TwoCopy.reaches_symm J h
      · exact h
    have hotherp : ¬J.reaches (T.val.erase e) (J.left e) p := by
      intro h
      apply T.property.2.2 e he
      rwa [hep]
    have havoid := reaches_erase_incident_of_not_reaches J (T.val.erase e)
      p (J.left e) q f hfp hotherp hother
    have hedge : J.reaches (T.val.erase f) p (J.left e) :=
      .single ⟨e, heF, Or.inr ⟨hep, rfl⟩⟩
    exact hfcut (hedge.trans (monotone havoid))

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
