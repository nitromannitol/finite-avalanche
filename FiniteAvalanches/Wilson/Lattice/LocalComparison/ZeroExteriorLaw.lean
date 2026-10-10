import FiniteAvalanches.Wilson.Lattice.LocalComparison.ColorSwapLaw
import FiniteAvalanches.Wilson.Lattice.FixedBoxColorLaw
import FiniteAvalanches.Electrical.Reference.Lattice
import FiniteAvalanches.Wilson.Lattice.ContactWindow

set_option autoImplicit false
namespace LocalZeroExterior
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Electrical.Plane.SourceLattice MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- The exact source roots: all exterior sites are zero, and the given P is one. -/
def domainRoots (D : Finset (Site 2)) (P : OneSet D) : RootPair where
  zero := (D : Set (Site 2))ᶜ
  one := P.val.image Subtype.val
  disjoint := Set.disjoint_left.mpr (by
    intro x h0 h1
    obtain ⟨y, _, he⟩ := Finset.mem_image.mp h1
    exact h0 (he ▸ y.property))
  zero_nonempty := D.exists_notMem
  one_nonempty := by
    obtain ⟨x, hx⟩ := P.property
    exact ⟨x.val, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

/-- The same full original-copy forest carrier, with its exterior/root colors complemented. -/
def field (R : RootPair) (N : ℕ) (F : FiniteForest (LocalColorSwap.roots R) N) : ColorField :=
  LocalColorSwap.colors (finiteForestField (LocalColorSwap.roots R) N F).2

theorem measurable_field (R : RootPair) (N : ℕ) : Measurable (field R N) :=
  measurable_of_finite _

theorem field_apply (R : RootPair) (N : ℕ)
    (F : FiniteForest (LocalColorSwap.roots R) N) (x : Site 2) :
    field R N F x = !(finiteColors (LocalColorSwap.roots R) N F (wiredSite N x)) := rfl

/-- Every site color is the actual component label of an original one root. -/
theorem field_true_iff (R : RootPair) (N : ℕ)
    (F : FiniteForest (LocalColorSwap.roots R) N) (x : Site 2) :
    field R N F x = true ↔ ∃ r ∈ wiredZero (LocalColorSwap.roots R) N,
      (WiredTrees.graph N).reaches F.val (wiredSite N x) r := by
  change (!decide (∃ r ∈ wiredOne (LocalColorSwap.roots R) N,
    (WiredTrees.graph N).reaches F.val (wiredSite N x) r)) = true ↔ _
  rw [LocalColorSwap.not_eq]
  simp only [Bool.not_true, decide_eq_false_iff_not]
  constructor
  · intro h
    obtain ⟨r, hr, hxr, _⟩ := F.property.2 (wiredSite N x)
    rcases hr with hz | ho
    · exact ⟨r, hz, hxr⟩
    · exact (h ⟨r, ho, hxr⟩).elim
  · rintro ⟨r, hz, hxr⟩ ⟨s, ho, hxs⟩
    obtain ⟨u, _, _, hu⟩ := F.property.2 (wiredSite N x)
    have he : r = s := (hu r (Or.inl hz) hxr).trans (hu s (Or.inr ho) hxs).symm
    exact Set.disjoint_left.mp (wired_roots_disjoint (LocalColorSwap.roots R) N)
      hz (he.symm ▸ ho)

theorem field_exterior (R : RootPair) (N : ℕ)
    (F : FiniteForest (LocalColorSwap.roots R) N) {x : Site 2}
    (hx : ¬FiniteWired.inBox N x) : field R N F x = false := by
  unfold field LocalColorSwap.colors
  rw [finiteForestField_outside _ _ _ hx]
  rfl

theorem field_one_root (R : RootPair) (N : ℕ)
    (F : FiniteForest (LocalColorSwap.roots R) N) {x : Site 2}
    (hx : x ∈ R.one) (hbox : FiniteWired.inBox N x) : field R N F x = true := by
  have hc := finiteColors_zero (LocalColorSwap.roots R) N F
    (v := some (FiniteWired.activeOfSite N x hbox)) hx
  rw [field_apply, wiredSite, dif_pos hbox, hc]
  rfl

theorem field_zero_root (R : RootPair) (N : ℕ)
    (F : FiniteForest (LocalColorSwap.roots R) N) {x : Site 2}
    (hx : x ∈ R.zero) : field R N F x = false := by
  by_cases hbox : FiniteWired.inBox N x
  · have hc := finiteColors_one (LocalColorSwap.roots R) N F
      (v := some (FiniteWired.activeOfSite N x hbox)) hx
    rw [field_apply, wiredSite, dif_pos hbox, hc]
    rfl
  · exact field_exterior R N F hbox

/-- Full color-law identification on the already proved one-exterior copied forest. -/
theorem one_exterior_color_law (R : RootPair) (N : ℕ)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) :
    (finiteUniformLaw R N).map (fun F => (finiteForestField R N F).2) = wilsonColorLaw R := by
  apply Translation.measure_eq_of_patterns
  intro W p
  let H : Set (W → Bool) := {s | ∀ d : W, s d = p d.val}
  have he : windowColorEvent W H = {σ : ColorField | ∀ d ∈ W, σ d = p d} := by
    ext σ
    exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d.val d.property⟩
  have hreal := WiredBoxCopies.fixed_box_window_real R N houtside W H
  have hprob : finiteForestLaw R N (Prod.snd ⁻¹' windowColorEvent W H) =
      wilsonColorLaw R (windowColorEvent W H) :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal
  rw [← he, Measure.map_apply (measurable_of_finite _)
    (isClopen_windowColorEvent W H).isClosed.measurableSet]
  rw [finiteForestLaw, Measure.map_apply (finiteForestField_measurable R N)
    ((isClopen_windowColorEvent W H).isClosed.measurableSet.preimage measurable_snd)] at hprob
  exact hprob

/-- An actual zero-exterior Wilson law equals the full copied-forest pushforward.
No finite-law identity or equivalence is a supplied premise. -/
theorem zero_exterior_color_law (R : RootPair) (N : ℕ)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero) :
    (finiteUniformLaw (LocalColorSwap.roots R) N).map (field R N) = wilsonColorLaw R := by
  calc
    _ = ((finiteUniformLaw (LocalColorSwap.roots R) N).map
        (fun F => (finiteForestField (LocalColorSwap.roots R) N F).2)).map LocalColorSwap.colors := by
      rw [Measure.map_map LocalColorSwap.measurable_colors (measurable_of_finite _)]
      rfl
    _ = (wilsonColorLaw (LocalColorSwap.roots R)).map LocalColorSwap.colors := by
      rw [one_exterior_color_law _ N houtside]
    _ = wilsonColorLaw R := by
      rw [LocalColorSwap.law_map, LocalColorSwap.roots_involutive]

theorem event_count (R : RootPair) (N : ℕ)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero)
    (S : Set ColorField) (hS : MeasurableSet S) :
    wilsonColorLaw R S =
      (Nat.card {F : FiniteForest (LocalColorSwap.roots R) N | field R N F ∈ S} : ℝ≥0∞) /
        finiteForestCount (LocalColorSwap.roots R) N := by
  rw [← zero_exterior_color_law R N houtside, Measure.map_apply (measurable_field R N) hS]
  exact uniformMeasure_apply _ _

/-- Actual local source contact event, with D-complement zero and P one.
The denominator is every original copied rooted forest in the wired box. -/
theorem local_contact_event_count (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (A : Set (Site 2)) (a : Site 2) (r : ℕ) (t : ℝ) :
    wilsonColorLaw (domainRoots D P) (localContactEvent A a r t) =
      (Nat.card {F : FiniteForest (LocalColorSwap.roots (domainRoots D P)) N |
        t ≤ (localContacts A a r (field (domainRoots D P) N F) : ℝ)} : ℝ≥0∞) /
        finiteForestCount (LocalColorSwap.roots (domainRoots D P)) N := by
  exact event_count (domainRoots D P) N (by
    intro x hx
    change x ∉ D
    exact fun hD => hx (hDbox x hD)) _
    (isClopen_localContactEvent A a r t).isClosed.measurableSet

end
end LocalZeroExterior
