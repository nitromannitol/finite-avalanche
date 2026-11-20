import FiniteAvalanches.Support.Plane.ArcAccess.PathQuotient

/-!
# Reducing a path by a maximal loop cancellation

A monotone collapsing map satisfying the indicated fiber condition produces an
injective path in the original path's image.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.ArcAccess

open Set

/-- A suitable collapsing map for a maximal loop cancellation yields an
injective path with the same endpoints contained in the original path. -/
theorem exists_injective_path_of_loop_collapse
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (S : Set (unitInterval × unitInterval)) (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S)
    (g : unitInterval → unitInterval) (hg : Continuous g) (hmono : Monotone g)
    (hg0 : g 0 = 0) (hg1 : g 1 = 1)
    (hflat : ∀ v ∈ S, g v.1 = g v.2)
    (hsep : ∀ s t : unitInterval,
      (∀ v ∈ S, s ∉ Ioo v.1 v.2) → (∀ v ∈ S, t ∉ Ioo v.1 v.2) →
      g s = g t → p s = p t) :
    ∃ q : Path x y, Function.Injective q ∧ range q ⊆ range p := by
  classical
  let F : Set unitInterval := {t | ∀ v ∈ S, t ∉ Ioo v.1 v.2}
  have hF : IsClosed F := by
    have heq : F = (⋃ v ∈ S, Ioo v.1 v.2)ᶜ := by
      ext t
      simp only [F, mem_setOf_eq, mem_compl_iff, mem_iUnion, not_exists]
    rw [heq]
    exact (isOpen_iUnion fun v => isOpen_iUnion fun _ => isOpen_Ioo).isClosed_compl
  have h0 : (0 : unitInterval) ∈ F := by
    intro v hv hmem
    exact (not_lt_of_ge bot_le) hmem.1
  have h1 : (1 : unitInterval) ∈ F := by
    intro v hv hmem
    exact (not_lt_of_ge le_top) hmem.2
  have hendpoint : ∀ v ∈ S, v.1 ∈ F := by
    intro v hv w hw hmem
    by_cases heq : v = w
    · subst w
      exact (lt_irrefl v.1) hmem.1
    · rcases hS.separated_of_maximal p hmax hv hw heq with hlt | hlt
      · exact (not_lt_of_ge (le_trans (le_of_lt (hS.1 v hv).1) (le_of_lt hlt))) hmem.1
      · exact (not_lt_of_ge hlt.le) hmem.2
  have hsurj : ∀ u : unitInterval, ∃ t ∈ F, g t = u := by
    intro u
    have hu : u ∈ Icc (g 0) (g 1) := by rw [hg0, hg1]; exact ⟨bot_le, le_top⟩
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from bot_le)
      hg.continuousOn hu
    by_cases htF : t ∈ F
    · exact ⟨t, htF, ht⟩
    · have hex : ∃ v ∈ S, t ∈ Ioo v.1 v.2 := by
        by_contra hn
        apply htF
        intro v hv htv
        exact hn ⟨v, hv, htv⟩
      obtain ⟨v, hv, htv⟩ := hex
      have hgeq : g v.1 = g t := by
        apply le_antisymm (hmono htv.1.le)
        calc
          g t ≤ g v.2 := hmono htv.2.le
          _ = g v.1 := (hflat v hv).symm
      exact ⟨v.1, hendpoint v hv, hgeq.trans ht⟩
  have hfiber : ∀ s ∈ F, ∀ t ∈ F, g s = g t ↔ p s = p t := by
    intro s hs t ht
    constructor
    · exact hsep s t hs ht
    · intro hp
      rcases lt_trichotomy s t with hlt | rfl | hgt
      · obtain ⟨v, hv, hv1, hv2⟩ := hS.eq_off_interiors_of_maximal p hmax hlt hp hs ht
        simpa only [hv1, hv2] using hflat v hv
      · rfl
      · obtain ⟨v, hv, hv1, hv2⟩ := hS.eq_off_interiors_of_maximal p hmax hgt hp.symm ht hs
        simpa only [hv1, hv2] using (hflat v hv).symm
  exact exists_injective_path_of_compact_quotient p F hF h0 h1 g hg hg0 hg1 hsurj hfiber

/-- If a monotone map collapses exactly the closed intervals of a maximal
cancellation, its quotient is an injective subpath. -/
theorem exists_injective_path_of_exact_loop_collapse
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (S : Set (unitInterval × unitInterval)) (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S)
    (g : unitInterval → unitInterval) (hg : Continuous g) (hmono : Monotone g)
    (hg0 : g 0 = 0) (hg1 : g 1 = 1)
    (hflat : ∀ v ∈ S, g v.1 = g v.2)
    (honly : ∀ s t : unitInterval, s < t → g s = g t →
      ∃ v ∈ S, v.1 ≤ s ∧ t ≤ v.2) :
    ∃ q : Path x y, Function.Injective q ∧ range q ⊆ range p := by
  apply exists_injective_path_of_loop_collapse p S hS hmax g hg hmono hg0 hg1 hflat
  intro s t hs ht hgeq
  have hforward : ∀ a b : unitInterval, a < b → g a = g b →
      (∀ v ∈ S, a ∉ Ioo v.1 v.2) → (∀ v ∈ S, b ∉ Ioo v.1 v.2) → p a = p b := by
    intro a b hab hg' ha hb
    obtain ⟨v, hv, hva, hbv⟩ := honly a b hab hg'
    have ha' : a = v.1 := by
      by_contra hne
      have hlt : v.1 < a := lt_of_le_of_ne hva (Ne.symm hne)
      exact ha v hv ⟨hlt, lt_of_lt_of_le hab hbv⟩
    have hb' : b = v.2 := by
      by_contra hne
      have hlt : b < v.2 := lt_of_le_of_ne hbv hne
      exact hb v hv ⟨lt_of_le_of_lt hva hab, hlt⟩
    simpa only [ha', hb'] using (hS.1 v hv).2
  rcases lt_trichotomy s t with hlt | rfl | hgt
  · exact hforward s t hlt hgeq hs ht
  · rfl
  · exact (hforward t s hgt hgeq.symm ht hs).symm

end FiniteAvalanches.Electrical.StatementGeometry.ArcAccess
