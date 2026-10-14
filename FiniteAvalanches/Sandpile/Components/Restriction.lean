import FiniteAvalanches.Sandpile.Waves.SourceExtension
import FiniteAvalanches.Sandpile.Waves.Cycles

                                                                             
                                                                            
                                                                             
                                                                                       
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- A source component is contained in the wired box and contains the actual source. -/
abbrev ComponentShape {N : ℕ} (o : FiniteWired.Active N) :=
  {C : Finset Site2 // C ⊆ boxSites N ∧ FiniteWired.site o ∈ C}

/-- The actual largest source-minus-one forbidden core is a component shape. -/
def coreShape {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) : ComponentShape o :=
  ⟨core h, forbidden_core_subset _ _, source_mem_core h⟩

@[simp] theorem core_shape_val {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    (coreShape h).val = core h := rfl

theorem degree_union_of_disjoint {A B : Finset Site2} (h : Disjoint A B) (x : Site2) :
    degree (A ∪ B) x = degree A x + degree B x := by
  unfold degree
  rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
  exact h.mono Finset.inter_subset_right Finset.inter_subset_right

/-- Maximality of the forbidden core gives the exact nonnegative outer shift. -/
theorem height_ge_degree_core_outside {N : ℕ} {o : FiniteWired.Active N}
    (h : OffField N o) {x : Site2} (hx : x ∈ boxSites N) (hc : x ∉ core h) :
    (degree (core h) x : ℤ) ≤ wiredHeight (-1) h x := by
  by_contra hn
  have hf : forbidden (wiredHeight (-1) h) (insert x (core h)) := by
    refine ⟨Finset.insert_nonempty _ _, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with hxy | hy
    · subst y
      have hd : (degree (core h) x : ℤ) ≤ (degree (insert x (core h)) x : ℤ) := by
        exact_mod_cast degree_mono (Finset.subset_insert _ _) x
      omega
    · exact lt_of_lt_of_le ((core_forbidden h).2 y hy)
        (by exact_mod_cast degree_mono (Finset.subset_insert _ _) y)
  have hsub : insert x (core h) ⊆ boxSites N :=
    Finset.insert_subset hx (forbidden_core_subset _ _)
  exact hc (forbidden_subset_core hsub hf (Finset.mem_insert_self ..))

/-- The outer field is stable at the complementary induced graph's degree. -/
theorem shifted_core_height_stable {N : ℕ} {o : FiniteWired.Active N}
    (h : OffField N o) {x : Site2} (hx : x ∈ boxSites N) (hc : x ∉ core h) :
    0 ≤ wiredHeight (-1) h x - (degree (core h) x : ℤ) ∧
      wiredHeight (-1) h x - (degree (core h) x : ℤ) < (4 - degree (core h) x : ℕ) := by
  have hlo := height_ge_degree_core_outside h hx hc
  have hxo : x ≠ FiniteWired.site o := fun he => hc (he ▸ source_mem_core h)
  have hhi := wired_height_le_three h hx hxo
  rw [wired_height_off (-1) 4 h hxo] at hlo ⊢
  have hd := degree_le_four (core h) x
  omega

/-- A forbidden outer shifted set would enlarge the actual largest forbidden set. -/
theorem shifted_core_allowed {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    allowed (boxSites N \ core h)
      (fun x => wiredHeight (-1) h x - (degree (core h) x : ℤ)) := by
  intro A hA hf
  have hd : Disjoint (core h) A := Finset.disjoint_left.mpr (fun x hx hxA =>
    (Finset.mem_sdiff.mp (hA hxA)).2 hx)
  have hforb : forbidden (wiredHeight (-1) h) (core h ∪ A) := by
    refine ⟨(core_forbidden h).1.mono Finset.subset_union_left, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact lt_of_lt_of_le ((core_forbidden h).2 x hx)
        (by exact_mod_cast degree_mono Finset.subset_union_left x)
    · have hh := hf.2 x hx
      dsimp only at hh
      rw [degree_union_of_disjoint hd]
      push_cast
      omega
  have hsub : core h ∪ A ⊆ boxSites N := Finset.union_subset
    (forbidden_core_subset _ _) (hA.trans Finset.sdiff_subset)
  obtain ⟨x, hx⟩ := hf.1
  exact (Finset.mem_sdiff.mp (hA hx)).2
    (forbidden_subset_core hsub hforb (Finset.mem_union_right _ hx))

/-- The literal source core is characterized by the two restricted fields.
The inner field has induced degree in C; the outer field is shifted by e(v,C).
No burning law, product law, or recurrence equivalence is assumed. -/
theorem punctured_core_iff {N : ℕ} {o : FiniteWired.Active N}
    (h : OffField N o) (C : Finset Site2) (hC : C ⊆ boxSites N)
    (hoC : FiniteWired.site o ∈ C) :
    (punctured_allowed h ∧ core h = C) ↔
      (∀ x ∈ C, x ≠ FiniteWired.site o → wiredHeight (-1) h x < (degree C x : ℤ)) ∧
      allowed (C.erase (FiniteWired.site o)) (wiredHeight (-1) h) ∧
      (∀ x ∈ boxSites N \ C, (degree C x : ℤ) ≤ wiredHeight (-1) h x) ∧
      allowed (boxSites N \ C) (fun x => wiredHeight (-1) h x - (degree C x : ℤ)) := by
  constructor
  · rintro ⟨ha, rfl⟩
    refine ⟨fun x hx _ => (core_forbidden h).2 x hx, ?_, ?_, shifted_core_allowed h⟩
    · intro A hA
      exact ha A (hA.trans (by
        intro x hx
        obtain ⟨hxo, hxC⟩ := Finset.mem_erase.mp hx
        exact Finset.mem_erase.mpr ⟨hxo, forbidden_core_subset _ _ hxC⟩))
    · intro x hx
      obtain ⟨hxB, hxC⟩ := Finset.mem_sdiff.mp hx
      exact height_ge_degree_core_outside h hxB hxC
  · rintro ⟨hi, haC, _, haD⟩
    have hforbC : forbidden (wiredHeight (-1) h) C := by
      refine ⟨⟨FiniteWired.site o, hoC⟩, ?_⟩
      intro x hx
      by_cases hxo : x = FiniteWired.site o
      · subst x
        rw [wired_height_site, active_height_source]
        exact lt_of_lt_of_le (by norm_num : (-1 : ℤ) < 0) (Nat.cast_nonneg _)
      · exact hi x hx hxo
    have hsubset : ∀ A ⊆ boxSites N, forbidden (wiredHeight (-1) h) A → A ⊆ C := by
      intro A hA hf
      by_contra hn
      apply haD (A \ C) (by intro x hx; exact Finset.mem_sdiff.mpr ⟨hA (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩)
      refine ⟨Finset.sdiff_nonempty.mpr hn, ?_⟩
      intro x hx
      have hh := hf.2 x (Finset.mem_sdiff.mp hx).1
      have hd : (degree A x : ℤ) ≤ (degree (A \ C) x : ℤ) + (degree C x : ℤ) := by
        exact_mod_cast degree_le_sdiff_add A C x
      dsimp only
      omega
    refine ⟨?_, Finset.Subset.antisymm ?_ (forbidden_subset_core hC hforbC)⟩
    · intro A hA hf
      apply haC A
      · intro x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hA hx)).1,
          hsubset A (hA.trans (Finset.erase_subset _ _)) hf hx⟩
      · exact hf
    · intro x hx
      obtain ⟨_, A, hA, hf, hxA⟩ := Finset.mem_filter.mp hx
      exact hsubset A hA hf hxA

end
end FiniteAvalanches.Sandpile.Components
