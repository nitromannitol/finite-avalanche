import FiniteAvalanches.Sandpile.Waves.Forbidden

/-! Literal finite-box fields with the source removed. Existence and legal-count
uniqueness are proved before choosing the wave odometer or defining its output.
The auxiliary lattice extension is zero only at the wired sink exterior. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

abbrev OffVertex (N : ℕ) (o : FiniteWired.Active N) := {x : FiniteWired.Active N // x ≠ o}
abbrev OffField (N : ℕ) (o : FiniteWired.Active N) := OffVertex N o → Fin 4

/-- The height on every active vertex, with the specified source height. -/
def activeHeight {N : ℕ} {o : FiniteWired.Active N} (a : ℤ) (h : OffField N o)
    (x : FiniteWired.Active N) : ℤ :=
  if hx : x = o then a else (h ⟨x, hx⟩).val

/-- Auxiliary extension for the literal wired Laplacian: the exterior is the sink. -/
def wiredHeight {N : ℕ} {o : FiniteWired.Active N} (a : ℤ) (h : OffField N o)
    (x : Site2) : ℤ :=
  if hx : FiniteWired.inBox N x then activeHeight a h (FiniteWired.activeOfSite N x hx) else 0

theorem active_height_source {N : ℕ} {o : FiniteWired.Active N}
    (a : ℤ) (h : OffField N o) : activeHeight a h o = a := by simp [activeHeight]

theorem active_height_off {N : ℕ} {o : FiniteWired.Active N}
    (a : ℤ) (h : OffField N o) (x : OffVertex N o) :
    activeHeight a h x.val = (h x).val := by simp [activeHeight, x.property]

theorem wired_height_site {N : ℕ} {o : FiniteWired.Active N}
    (a : ℤ) (h : OffField N o) (x : FiniteWired.Active N) :
    wiredHeight a h (FiniteWired.site x) = activeHeight a h x := by
  have hx : FiniteWired.inBox N (FiniteWired.site x) := fun i => (x i).property
  simp only [wiredHeight, dif_pos hx]
  congr 1

theorem site_mem_box {N : ℕ} (x : FiniteWired.Active N) : FiniteWired.site x ∈ boxSites N := by
  rw [mem_box_sites]
  exact fun i => (x i).property

theorem wired_height_off {N : ℕ} {o : FiniteWired.Active N}
    (a b : ℤ) (h : OffField N o) {x : Site2} (hx : x ≠ FiniteWired.site o) :
    wiredHeight a h x = wiredHeight b h x := by
  unfold wiredHeight
  split
  · rename_i hb
    have hne : FiniteWired.activeOfSite N x hb ≠ o := by
      intro he
      apply hx
      exact congrArg FiniteWired.site he
    simp only [activeHeight, dif_neg hne]
  · rfl

/-- Stable fields with no forbidden subset avoiding the held source. -/
def punctured_allowed {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) : Prop :=
  allowed ((boxSites N).erase (FiniteWired.site o)) (wiredHeight (-1) h)

abbrev Punctured (N : ℕ) (o : FiniteWired.Active N) := {h : OffField N o // punctured_allowed h}

/-- A legal source-first list that stabilizes every other active vertex. -/
def wave_realizes {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) (u : Counts) : Prop :=
  ∃ v : List Site2,
    (∀ x ∈ v, x ∈ boxSites N ∧ x ≠ FiniteWired.site o) ∧
    LegalList (wiredHeight 4 h) (FiniteWired.site o :: v) ∧
    (∀ x ∈ boxSites N, x ≠ FiniteWired.site o →
      0 ≤ heightAfter (wiredHeight 4 h) (FiniteWired.site o :: v) x ∧
      heightAfter (wiredHeight 4 h) (FiniteWired.site o :: v) x < 4) ∧
    listCounts (FiniteWired.site o :: v) = u

theorem wired_height_nonneg {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    ∀ x, 0 ≤ wiredHeight 4 h x := by
  intro x
  unfold wiredHeight activeHeight
  split
  · split
    · norm_num
    · exact Nat.cast_nonneg _
  · norm_num

theorem exists_unique_wave_counts {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    ∃! u : Counts, wave_realizes h u := by
  have hs : ∀ x ∈ boxSites N, x ≠ FiniteWired.site o → wiredHeight 4 h x ≤ 3 := by
    intro x hx hxo
    have hb : FiniteWired.inBox N x := (mem_box_sites N x).mp hx
    have hne : FiniteWired.activeOfSite N x hb ≠ o := by
      intro he
      exact hxo (congrArg FiniteWired.site he)
    simp only [wiredHeight, dif_pos hb, activeHeight, dif_neg hne]
    have hh := (h ⟨FiniteWired.activeOfSite N x hb, hne⟩).isLt
    omega
  obtain ⟨v, hv, hl, _, _, ht⟩ := exists_legal_wave (wiredHeight 4 h) N (boxSites N)
    (FiniteWired.site o) (fun _ hx => hx) (site_mem_box o)
    (by rw [wired_height_site, active_height_source]) (wired_height_nonneg h) hs
  refine ⟨listCounts (FiniteWired.site o :: v), ⟨v, hv, hl, ht, rfl⟩, ?_⟩
  intro u hu
  obtain ⟨v', hv', hl', ht', he'⟩ := hu
  rw [← he']
  exact wave_counts_unique hv' hv hl' hl (fun x hx hxo => (ht' x hx hxo).2)
    (fun x hx hxo => (ht x hx hxo).2)

/-- The unique finitely supported legal wave count, chosen only after uniqueness. -/
def waveCounts {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) : Counts :=
  (exists_unique_wave_counts h).choose

theorem wave_counts_realizes {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    wave_realizes h (waveCounts h) := (exists_unique_wave_counts h).choose_spec.1

theorem wave_counts_eq {N : ℕ} {o : FiniteWired.Active N} {h : OffField N o} {u : Counts}
    (hu : wave_realizes h u) : u = waveCounts h :=
  (exists_unique_wave_counts h).choose_spec.2 u hu

def waveHeight {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) (x : Site2) : ℤ :=
  wiredHeight 4 h x + lap (fun y => (waveCounts h y : ℤ)) x

theorem wave_height_stable {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o)
    (x : OffVertex N o) : 0 ≤ waveHeight h (FiniteWired.site x.val) ∧
      waveHeight h (FiniteWired.site x.val) < 4 := by
  obtain ⟨v, _, _, ht, he⟩ := wave_counts_realizes h
  have hn : FiniteWired.site x.val ≠ FiniteWired.site o := fun hh =>
    x.property (FiniteWired.site_injective N hh)
  have hh := ht (FiniteWired.site x.val) (site_mem_box x.val) hn
  simpa only [heightAfter, he, waveHeight] using hh

/-- The actual off-source stabilized field, defined on every off-source vertex. -/
def waveOutput {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) : OffField N o :=
  fun x => ⟨(waveHeight h (FiniteWired.site x.val)).toNat, by
    have ht := wave_height_stable h x
    omega⟩

theorem wave_output_height {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o)
    (x : OffVertex N o) : ((waveOutput h x).val : ℤ) = waveHeight h (FiniteWired.site x.val) :=
  Int.toNat_of_nonneg (wave_height_stable h x).1

theorem wave_output_allowed {N : ℕ} {o : FiniteWired.Active N} {h : OffField N o}
    (ha : punctured_allowed h) : punctured_allowed (waveOutput h) := by
  have ha' : allowed ((boxSites N).erase (FiniteWired.site o)) (wiredHeight 4 h) :=
    (allowed_congr (fun x hx => wired_height_off (-1) 4 h (Finset.mem_erase.mp hx).1)).mp ha
  obtain ⟨v, _, hl, _, he⟩ := wave_counts_realizes h
  have ht := allowed_legal_list ha' hl (wired_height_nonneg h)
  apply (allowed_congr (h := heightAfter (wiredHeight 4 h) (FiniteWired.site o :: v))
    (g := wiredHeight (-1) (waveOutput h)) ?_).mp ht
  intro x hx
  obtain ⟨hxo, hxB⟩ := Finset.mem_erase.mp hx
  have hb : FiniteWired.inBox N x := (mem_box_sites N x).mp hxB
  let y := FiniteWired.activeOfSite N x hb
  have hne : y ≠ o := fun hh => hxo (congrArg FiniteWired.site hh)
  have hy : FiniteWired.site y = x := rfl
  rw [← hy, wired_height_site, active_height_off (-1) (waveOutput h) ⟨y, hne⟩,
    wave_output_height]
  simp only [heightAfter, waveHeight, he]

/-- The source-four, source-once, source-held forward map on the literal state space. -/
def forward {N : ℕ} {o : FiniteWired.Active N} (h : Punctured N o) : Punctured N o :=
  ⟨waveOutput h.val, wave_output_allowed h.property⟩

theorem wired_height_le_three {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o)
    {x : Site2} (hx : x ∈ boxSites N) (hxo : x ≠ FiniteWired.site o) :
    wiredHeight 4 h x ≤ 3 := by
  have hb : FiniteWired.inBox N x := (mem_box_sites N x).mp hx
  have hne : FiniteWired.activeOfSite N x hb ≠ o := fun he => hxo (congrArg FiniteWired.site he)
  simp only [wiredHeight, dif_pos hb, activeHeight, dif_neg hne]
  have hh := (h ⟨FiniteWired.activeOfSite N x hb, hne⟩).isLt
  omega

theorem wave_counts_source {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    waveCounts h (FiniteWired.site o) = 1 := by
  obtain ⟨v, hv, _, _, he⟩ := wave_counts_realizes h
  have hn : FiniteWired.site o ∉ v := fun hx => (hv _ hx).2 rfl
  rw [← he]
  simp [listCounts_apply, List.count_eq_zero_of_not_mem hn]

theorem wave_counts_le_one {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    ∀ x, waveCounts h x ≤ 1 := by
  obtain ⟨v, hv, hl, _, he⟩ := wave_counts_realizes h
  rw [← he]
  apply count_le_one_of_legal_list (FiniteWired.site o) hl
  · intro x hx hxo
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hxo rfl).elim
    · exact wired_height_le_three h (hv x hx).1 hxo
  · rw [he, wave_counts_source]

theorem wave_counts_support_subset {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    (waveCounts h).support ⊆ boxSites N := by
  obtain ⟨v, hv, _, _, he⟩ := wave_counts_realizes h
  rw [← he, listCounts_support]
  intro x hx
  rcases List.mem_cons.mp (List.mem_toFinset.mp hx) with rfl | hx
  · exact site_mem_box o
  · exact (hv x hx).1

theorem wired_output_height {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o)
    {x : Site2} (hx : x ∈ boxSites N) (hxo : x ≠ FiniteWired.site o) :
    wiredHeight (-1) (waveOutput h) x = waveHeight h x := by
  have hb : FiniteWired.inBox N x := (mem_box_sites N x).mp hx
  let y := FiniteWired.activeOfSite N x hb
  have hn : y ≠ o := fun he => hxo (congrArg FiniteWired.site he)
  change wiredHeight (-1) (waveOutput h) (FiniteWired.site y) = waveHeight h (FiniteWired.site y)
  rw [wired_height_site, active_height_off (-1) (waveOutput h) ⟨y, hn⟩, wave_output_height]

end
end FiniteAvalanches.Sandpile.Waves
