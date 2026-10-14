import FiniteAvalanches.Paper.Current.RawPuncturedCarrier

/-! The literal largest union of FSCs and the actual origin-first wave. U is a
proved permutation and is characterized by legal punctured stabilization. -/
namespace FiniteAvalanches.Paper.RawPunctured
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

def W {N : ℕ} {o : FiniteWired.Active N} (η : State o) : Finset Site2 :=
  forbiddenCore (boxSites N) (extension (-1) η)

theorem W_eq_core {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    W η = core (toOld η).val := by rw [W, extension_eq_wired]; rfl

theorem W_characterization {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    W η ⊆ boxSites N ∧ forbidden (extension (-1) η) (W η) ∧
    (∀ B ⊆ boxSites N, forbidden (extension (-1) η) B → B ⊆ W η) ∧
    FiniteWired.site o ∈ W η := by
  rw [W_eq_core, extension_eq_wired]
  exact ⟨forbidden_core_subset _ _, core_forbidden _,
    fun _ hb hf => forbidden_subset_core hb hf, source_mem_core _⟩

theorem W_unique {N : ℕ} {o : FiniteWired.Active N} (η : State o) (B : Finset Site2)
    (hb : B ⊆ boxSites N) (hf : forbidden (extension (-1) η) B)
    (hmax : ∀ C ⊆ boxSites N, forbidden (extension (-1) η) C → C ⊆ B) : B = W η :=
  Finset.Subset.antisymm ((W_characterization η).2.2.1 B hb hf)
    (hmax _ (W_characterization η).1 (W_characterization η).2.1)

def U {N : ℕ} {o : FiniteWired.Active N} (η : State o) : State o :=
  (stateEquiv o).symm (forward (toOld η))

theorem to_old_U {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    toOld (U η) = forward (toOld η) := (stateEquiv o).apply_symm_apply _

def UEquiv {N : ℕ} (o : FiniteWired.Active N) : State o ≃ State o :=
  (stateEquiv o).trans (waveEquiv.trans (stateEquiv o).symm)

theorem U_equiv_value {N : ℕ} {o : FiniteWired.Active N} (η : State o) : UEquiv o η = U η := rfl

def seed {N : ℕ} {o : FiniteWired.Active N} (η : State o) : Site2 → ℤ :=
  fun x => extension 4 η x + lap (dirac (FiniteWired.site o)) x

/-- One grain for each original origin-incident direction copy landing in the domain. -/
theorem seed_value {N : ℕ} {o : FiniteWired.Active N} (η : State o) (x : volume o) :
    seed η x.val = η.val.val x + if FiniteWired.site o ∈ nbrFinset x.val then 1 else 0 := by
  rw [seed, extension_site, lap_dirac_off _ _ (Finset.mem_erase.mp x.property).1]

def stabilizes {N : ℕ} {o : FiniteWired.Active N} (η : State o)
    (ζ : RawInteger.Field (volume o)) : Prop :=
  ∃ v : List Site2, (∀ x ∈ v, x ∈ volume o) ∧ LegalList (seed η) v ∧
    ∀ x : volume o, heightAfter (seed η) v x.val = ζ x

theorem height_after_origin {N : ℕ} {o : FiniteWired.Active N} (η : State o)
    (v : List Site2) : heightAfter (extension 4 η) (FiniteWired.site o :: v) =
      heightAfter (seed η) v := by
  funext x
  simp only [heightAfter, list_counts_cons_int, lap_add, seed]
  omega

def waveRealizes {N : ℕ} {o : FiniteWired.Active N} (η : State o) (u : Counts) : Prop :=
  ∃ v : List Site2, (∀ x ∈ v, x ∈ volume o) ∧
    LegalList (extension 4 η) (FiniteWired.site o :: v) ∧
    (∀ x : volume o, 0 ≤ heightAfter (extension 4 η) (FiniteWired.site o :: v) x.val ∧
      heightAfter (extension 4 η) (FiniteWired.site o :: v) x.val < 4) ∧
    listCounts (FiniteWired.site o :: v) = u

theorem wave_realizes_iff {N : ℕ} {o : FiniteWired.Active N} (η : State o) (u : Counts) :
    waveRealizes η u ↔ wave_realizes (encode η) u := by
  rw [waveRealizes, extension_eq_wired]
  constructor
  · rintro ⟨v, hv, hl, hs, hc⟩
    exact ⟨v, fun x hx => ⟨(Finset.mem_erase.mp (hv x hx)).2,
      (Finset.mem_erase.mp (hv x hx)).1⟩, hl,
      fun x hx hxo => hs ⟨x, Finset.mem_erase.mpr ⟨hxo, hx⟩⟩, hc⟩
  · rintro ⟨v, hv, hl, hs, hc⟩
    exact ⟨v, fun x hx => Finset.mem_erase.mpr ⟨(hv x hx).2, (hv x hx).1⟩, hl,
      fun x => hs x.val (Finset.mem_erase.mp x.property).2 (Finset.mem_erase.mp x.property).1, hc⟩

def waveCounts {N : ℕ} {o : FiniteWired.Active N} (η : State o) : Counts :=
  Waves.waveCounts (encode η)

theorem wave_counts_characterization {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    waveRealizes η (waveCounts η) ∧ ∀ u, waveRealizes η u → u = waveCounts η :=
  ⟨(wave_realizes_iff η _).mpr (wave_counts_realizes _),
    fun _ hu => Waves.wave_counts_eq ((wave_realizes_iff η _).mp hu)⟩

theorem U_stabilizes {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    stabilizes η (U η).val.val := by
  obtain ⟨v, hv, hl, _, hc⟩ := (wave_counts_characterization η).1
  refine ⟨v, hv, ?_, ?_⟩
  · exact legal_list_of_cons hl
  · intro x
    rw [← height_after_origin]
    have hout := congrArg Subtype.val (to_old_U η)
    have he := wave_output_height (encode η) (volumeOff x)
    change ((Waves.waveOutput (encode η) (volumeOff x)).val : ℤ) =
      wiredHeight 4 (encode η) x.val + lap (fun y => (Waves.waveCounts (encode η) y : ℤ)) x.val at he
    have hval := encode_value (U η) (volumeOff x)
    rw [off_site_volume_off] at hval
    change encode (U η) = Waves.waveOutput (encode η) at hout
    rw [hout] at hval
    rw [← hval, he, heightAfter, hc, extension_eq_wired]
    rfl

/-- No stabilization certificate is a public assumption: the operation is the
unique upper-stable endpoint of the literal seeded legal word. -/
theorem U_characterization {N : ℕ} {o : FiniteWired.Active N} (η : State o)
    (ζ : RawInteger.StableState (volume o)) :
    stabilizes η ζ.val ↔ ζ = (U η).val := by
  constructor
  · rintro ⟨v, hv, hl, hz⟩
    obtain ⟨w, hw, hm, hu⟩ := U_stabilizes η
    have hc := legal_list_counts_unique_in hl hm hv hw
      (fun x hx => by rw [hz ⟨x, hx⟩]; exact ζ.property ⟨x, hx⟩)
      (fun x hx => by rw [hu ⟨x, hx⟩]; exact (U η).val.property ⟨x, hx⟩)
    apply Subtype.ext
    funext x
    rw [← hz x, ← hu x]
    unfold heightAfter
    rw [hc]
  · intro he
    rw [he]
    exact U_stabilizes η

/-- Incoming fv:inverse-waves, on the actual integer accessibility carrier. -/
theorem inverse_waves {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    ∀ x : Site2, waveCounts η x = if x ∈ W (U η) then 1 else 0 := by
  have h := (Waves.Source.paper_inverse_waves o (toOld η)).1
  rw [W_eq_core, to_old_U]
  exact h

end
end FiniteAvalanches.Paper.RawPunctured
