import FiniteAvalanches.Sandpile.Waves.Inverse

/-! Source extensions are characterized by the largest forbidden set.
Here `FiniteWired.recurrent` is exactly no forbidden subconfiguration; its
identification with Markov recurrence remains a separate literature boundary. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem source_singleton_forbidden {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    forbidden (wiredHeight (-1) h) {FiniteWired.site o} := by
  refine ⟨Finset.singleton_nonempty _, ?_⟩
  intro x hx
  have he : x = FiniteWired.site o := Finset.mem_singleton.mp hx
  subst x
  rw [wired_height_site, active_height_source]
  have hn : 0 ≤ (degree {FiniteWired.site o} (FiniteWired.site o) : ℤ) := Nat.cast_nonneg _
  omega

theorem source_mem_core {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    FiniteWired.site o ∈ core h :=
  forbidden_subset_core (by simpa using site_mem_box o) (source_singleton_forbidden h)
    (Finset.mem_singleton_self _)

theorem core_forbidden {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    forbidden (wiredHeight (-1) h) (core h) :=
  forbidden_core ⟨{FiniteWired.site o}, by simpa using site_mem_box o, source_singleton_forbidden h⟩

theorem forbidden_of_height_le {h g : Site2 → ℤ} {A : Finset Site2}
    (he : ∀ x ∈ A, g x ≤ h x) (hf : forbidden h A) : forbidden g A :=
  ⟨hf.1, fun x hx => lt_of_le_of_lt (he x hx) (hf.2 x hx)⟩

theorem wired_height_mono {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o)
    {a b : ℤ} (hab : a ≤ b) : ∀ x, wiredHeight a h x ≤ wiredHeight b h x := by
  intro x
  unfold wiredHeight activeHeight
  split
  · split
    · exact hab
    · exact le_rfl
  · exact le_rfl

/-- Exact source-height interval, expressed first on the lattice image carrier. -/
theorem source_extension_allowed_iff {N : ℕ} {o : FiniteWired.Active N}
    {h : OffField N o} (ha : punctured_allowed h) (a : ℕ) :
    allowed (boxSites N) (wiredHeight a h) ↔ degree (core h) (FiniteWired.site o) ≤ a := by
  constructor
  · intro hh
    by_contra hn
    apply hh (core h) (forbidden_core_subset _ _)
    refine ⟨(core_forbidden h).1, ?_⟩
    intro x hx
    by_cases hxo : x = FiniteWired.site o
    · subst x
      rw [wired_height_site, active_height_source]
      omega
    · rw [wired_height_off a (-1) h hxo]
      exact (core_forbidden h).2 x hx
  · intro hdeg H hH hf
    have hf' : forbidden (wiredHeight (-1) h) H :=
      forbidden_of_height_le (fun x _ => wired_height_mono h (by omega) x) hf
    have hcore := forbidden_subset_core hH hf'
    by_cases ho : FiniteWired.site o ∈ H
    · have ht := hf.2 (FiniteWired.site o) ho
      rw [wired_height_site, active_height_source] at ht
      have hd : (degree H (FiniteWired.site o) : ℤ) ≤ (degree (core h) (FiniteWired.site o) : ℤ) := by
        exact_mod_cast degree_mono hcore (FiniteWired.site o)
      omega
    · apply ha H (fun x hx => Finset.mem_erase.mpr ⟨fun he => ho (he ▸ hx), hH hx⟩)
      exact hf'

/-- Source insertion on the whole literal finite height carrier. -/
def sourceExtension {N : ℕ} {o : FiniteWired.Active N} (a : Fin 4) (h : OffField N o) :
    FiniteWired.Heights N := fun x => if hx : x = o then a else h ⟨x, hx⟩

theorem source_extension_height {N : ℕ} {o : FiniteWired.Active N}
    (a : Fin 4) (h : OffField N o) (x : FiniteWired.Active N) :
    ((sourceExtension a h x).val : ℤ) = activeHeight a.val h x := by
  unfold sourceExtension activeHeight
  split <;> rfl

theorem forbidden_image_iff {N : ℕ} (η : FiniteWired.Heights N) (h : Site2 → ℤ)
    (hh : ∀ x, h (FiniteWired.site x) = (η x).val) (A : Finset (FiniteWired.Active N)) :
    forbidden h (A.image FiniteWired.site) ↔ FiniteWired.forbidden η A := by
  have hn : (A.image FiniteWired.site).Nonempty ↔ A.Nonempty := Finset.image_nonempty
  simp only [forbidden, FiniteWired.forbidden, hn]
  constructor
  · rintro ⟨hne, ht⟩
    refine ⟨hne, ?_⟩
    intro x hx
    have hf := ht (FiniteWired.site x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    rw [hh x] at hf
    exact_mod_cast hf
  · rintro ⟨hne, ht⟩
    refine ⟨hne, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [hh y]
    exact_mod_cast ht y hy

theorem recurrent_iff_allowed {N : ℕ} (η : FiniteWired.Heights N) (h : Site2 → ℤ)
    (hh : ∀ x, h (FiniteWired.site x) = (η x).val) :
    FiniteWired.recurrent η ↔ allowed (boxSites N) h := by
  constructor
  · intro hr A hA hf
    let B : Finset (FiniteWired.Active N) := Finset.univ.filter (fun x => FiniteWired.site x ∈ A)
    have he : B.image FiniteWired.site = A := by
      ext x
      simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx
        have hb : FiniteWired.inBox N x := (mem_box_sites N x).mp (hA hx)
        exact ⟨FiniteWired.activeOfSite N x hb, hx, rfl⟩
    apply hr B
    exact (forbidden_image_iff η h hh B).mp (he ▸ hf)
  · intro ha A hf
    apply ha (A.image FiniteWired.site)
    · intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact site_mem_box y
    · exact (forbidden_image_iff η h hh A).mpr hf

/-- The second assertion of `fv:inverse-waves` on the accepted wired height model. -/
theorem source_extension_recurrent_iff {N : ℕ} {o : FiniteWired.Active N}
    {h : OffField N o} (ha : punctured_allowed h) (a : Fin 4) :
    FiniteWired.recurrent (sourceExtension a h) ↔ degree (core h) (FiniteWired.site o) ≤ a.val := by
  rw [recurrent_iff_allowed (sourceExtension a h) (wiredHeight a.val h)
    (fun x => by rw [wired_height_site, source_extension_height])]
  exact source_extension_allowed_iff ha a.val

end
end FiniteAvalanches.Sandpile.Waves
