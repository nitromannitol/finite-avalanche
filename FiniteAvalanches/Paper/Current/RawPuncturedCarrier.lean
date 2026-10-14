import FiniteAvalanches.Sandpile.Recurrence.GammaLaw
import FiniteAvalanches.Paper.Providers.InverseWavesProvider

/-! Integer R_N^(o): upper stability and accessibility from EVERY integer input.
The source-minus-one extension and bounded encoding are characterized by values. -/
namespace FiniteAvalanches.Paper.RawPunctured
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

def volume {N : ℕ} (o : FiniteWired.Active N) : Finset Site2 :=
  (boxSites N).erase (FiniteWired.site o)
abbrev State {N : ℕ} (o : FiniteWired.Active N) := RawInteger.GammaRecurrentState (volume o)

def offSite {N : ℕ} {o : FiniteWired.Active N} (x : OffVertex N o) : volume o :=
  ⟨FiniteWired.site x.val, Finset.mem_erase.mpr
    ⟨fun h => x.property ((FiniteWired.site_injective N) h), site_mem_box x.val⟩⟩

def volumeOff {N : ℕ} {o : FiniteWired.Active N} (x : volume o) : OffVertex N o :=
  ⟨FiniteWired.activeOfSite N x.val ((mem_box_sites N x.val).mp (Finset.mem_erase.mp x.property).2),
    fun h => (Finset.mem_erase.mp x.property).1 (congrArg FiniteWired.site h)⟩

theorem off_site_volume_off {N : ℕ} {o : FiniteWired.Active N} (x : volume o) :
    offSite (volumeOff x) = x := Subtype.ext rfl

theorem volume_off_off_site {N : ℕ} {o : FiniteWired.Active N} (x : OffVertex N o) :
    volumeOff (offSite x) = x := by
  apply Subtype.ext
  apply FiniteWired.site_injective N
  rfl

def encode {N : ℕ} {o : FiniteWired.Active N} (η : State o) : OffField N o :=
  fun x => RawInteger.gammaSourceEmbedding (volume o) η (offSite x).val

theorem encode_value {N : ℕ} {o : FiniteWired.Active N} (η : State o) (x : OffVertex N o) :
    ((encode η x).val : ℤ) = η.val.val (offSite x) :=
  RawInteger.gamma_source_embedding_value η (offSite x)

theorem encode_unique {N : ℕ} {o : FiniteWired.Active N} (η : State o) (h : OffField N o)
    (hh : ∀ x, ((h x).val : ℤ) = η.val.val (offSite x)) : h = encode η := by
  funext x
  apply Fin.ext
  exact_mod_cast (hh x).trans (encode_value η x).symm

def extension {N : ℕ} {o : FiniteWired.Active N} (a : ℤ) (η : State o) (x : Site2) : ℤ :=
  if x = FiniteWired.site o then a else RawInteger.extend η.val.val x

theorem extension_source {N : ℕ} {o : FiniteWired.Active N} (a : ℤ) (η : State o) :
    extension a η (FiniteWired.site o) = a := by simp only [extension, ite_true]

theorem extension_site {N : ℕ} {o : FiniteWired.Active N} (a : ℤ) (η : State o)
    (x : volume o) : extension a η x.val = η.val.val x := by
  rw [extension, if_neg (Finset.mem_erase.mp x.property).1, RawInteger.extend_site]

theorem extension_eq_wired {N : ℕ} {o : FiniteWired.Active N} (a : ℤ) (η : State o) :
    extension a η = wiredHeight a (encode η) := by
  funext x
  by_cases hx : x = FiniteWired.site o
  · subst x
    rw [extension_source, wired_height_site, active_height_source]
  · by_cases hb : FiniteWired.inBox N x
    · let y : volume o := ⟨x, Finset.mem_erase.mpr ⟨hx, (mem_box_sites N x).mpr hb⟩⟩
      have he : extension a η x = η.val.val y := extension_site a η y
      rw [he]
      change η.val.val y = wiredHeight a (encode η) (FiniteWired.site (volumeOff y).val)
      rw [wired_height_site, active_height_off, encode_value, off_site_volume_off]
    · simp only [extension, if_neg hx, RawInteger.extend, wiredHeight, dif_neg hb]
      have hm : x ∉ volume o := fun hm => hb ((mem_box_sites N x).mp
        (Finset.mem_erase.mp hm).2)
      rw [dif_neg hm]

theorem encode_allowed {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    punctured_allowed (encode η) := by
  have h := (RawInteger.no_fsc_iff_allowed η.val.val).mp
    ((RawInteger.no_fsc_iff_accessible η.val.val).mpr η.property)
  apply (allowed_congr (V := volume o) (h := RawInteger.extend η.val.val) ?_).mp h
  intro x hx
  rw [← extension_eq_wired]
  simp only [extension, if_neg (Finset.mem_erase.mp hx).1]

def toOld {N : ℕ} {o : FiniteWired.Active N} (η : State o) : Punctured N o :=
  ⟨encode η, encode_allowed η⟩

def fromOld {N : ℕ} {o : FiniteWired.Active N} (h : Punctured N o) : State o :=
  ⟨⟨fun x => wiredHeight (-1) h.val x.val, fun x => by
      change wiredHeight (-1) h.val x.val < 4
      have hs := wired_height_le_three h.val (Finset.mem_erase.mp x.property).2
        (Finset.mem_erase.mp x.property).1
      rw [← wired_height_off (-1) 4 h.val (Finset.mem_erase.mp x.property).1] at hs
      omega⟩,
    (RawInteger.no_fsc_iff_accessible _).mp ((RawInteger.no_fsc_iff_allowed _).mpr
      ((allowed_congr (V := volume o) (h := wiredHeight (-1) h.val)
        (fun x hx => by simp only [RawInteger.extend, dif_pos hx])).mp h.property))⟩

theorem to_old_from_old {N : ℕ} {o : FiniteWired.Active N} (h : Punctured N o) :
    toOld (fromOld h) = h := by
  apply Subtype.ext
  symm
  apply encode_unique
  intro x
  change ((h.val x).val : ℤ) = wiredHeight (-1) h.val (FiniteWired.site x.val)
  rw [wired_height_site, active_height_off]

theorem from_old_to_old {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    fromOld (toOld η) = η := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change wiredHeight (-1) (encode η) x.val = η.val.val x
  rw [← extension_eq_wired, extension_site]

def stateEquiv {N : ℕ} (o : FiniteWired.Active N) : State o ≃ Punctured N o where
  toFun := toOld
  invFun := fromOld
  left_inv := from_old_to_old
  right_inv := to_old_from_old

theorem state_accessible {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    ∀ θ : RawInteger.Field (volume o), RawInteger.Reach θ η.val.val := η.property

theorem state_nonnegative {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    ∀ x, 0 ≤ η.val.val x :=
  RawInteger.no_fsc_nonnegative ((RawInteger.no_fsc_iff_accessible η.val.val).mpr η.property)

end
end FiniteAvalanches.Paper.RawPunctured
