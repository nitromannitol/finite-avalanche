import FiniteAvalanches.Wilson.Lattice.ForestEvents
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Unordered lattice contacts for arbitrary sets, with infinite counts retained.
Every original lattice edge is one coordinate. The finite incidence dictionary
is proved when the vertices of the counted set have color zero. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Trees.Lattice MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- The original unordered lattice edges with an endpoint in V and the other endpoint colored one. -/
def unorderedContactEdges (V : Set (Site 2)) (σ : ColorField) : Set LatticeEdge :=
  {e | ∃ x ∈ V, ∃ y : Site 2, σ y = true ∧ e.val = s(x, y)}

/-- The extended count of original unordered edges; infinitely many edges give infinity. -/
def unorderedContacts (V : Set (Site 2)) (σ : ColorField) : ℝ≥0∞ :=
  ∑' e : LatticeEdge, if e ∈ unorderedContactEdges V σ then 1 else 0

/-- The sum counts exactly the edge set, including its infinite cardinality. -/
theorem unorderedContacts_eq_encard (V : Set (Site 2)) (σ : ColorField) :
    unorderedContacts V σ = (unorderedContactEdges V σ).encard.toENNReal := by
  rw [unorderedContacts, ← ENNReal.tsum_set_one]
  exact (tsum_subtype (unorderedContactEdges V σ) (fun _ => (1 : ℝ≥0∞))).symm

/-- Membership of one unordered edge is a measurable color event. -/
theorem measurableSet_unorderedContactEdge (V : Set (Site 2)) (e : LatticeEdge) :
    MeasurableSet {σ : ColorField | e ∈ unorderedContactEdges V σ} := by
  have h : MeasurableSet (⋃ x ∈ V, ⋃ y : Site 2, ⋃ (_ : e.val = s(x, y)),
      {σ : ColorField | σ y = true}) :=
    MeasurableSet.iUnion (fun x => MeasurableSet.iUnion (fun _ =>
      MeasurableSet.iUnion (fun y => MeasurableSet.iUnion (fun _ =>
        (measurable_pi_apply y : Measurable (fun σ : ColorField => σ y))
          (measurableSet_singleton true)))))
  convert h using 1
  ext σ
  simp only [unorderedContactEdges, Set.mem_setOf_eq, Set.mem_iUnion]
  aesop

/-- Arbitrary vertex sets and infinite contact counts retain a measurable count. -/
theorem measurable_unorderedContacts (V : Set (Site 2)) : Measurable (unorderedContacts V) := by
  exact Measurable.tsum (fun e => Measurable.ite
    (measurableSet_unorderedContactEdge V e) measurable_const measurable_const)

/-- Enlarging the set of one-colored sites can only add original unordered contacts. -/
theorem unorderedContactEdges_mono (V : Set (Site 2)) {σ τ : ColorField}
    (h : ∀ x, σ x = true → τ x = true) :
    unorderedContactEdges V σ ⊆ unorderedContactEdges V τ := by
  rintro e ⟨x, hx, y, hy, he⟩
  exact ⟨x, hx, y, h y hy, he⟩

/-- Pointwise monotonicity includes the value infinity. -/
theorem unorderedContacts_mono (V : Set (Site 2)) {σ τ : ColorField}
    (h : ∀ x, σ x = true → τ x = true) :
    unorderedContacts V σ ≤ unorderedContacts V τ := by
  apply ENNReal.tsum_le_tsum
  intro e
  by_cases he : e ∈ unorderedContactEdges V σ
  · rw [if_pos he, if_pos (unorderedContactEdges_mono V h he)]
  · rw [if_neg he]
    exact bot_le

/-- One finite directed incidence, retaining both genuine neighboring endpoints. -/
abbrev ContactIncidence (K : Finset (Site 2)) (σ : ColorField) :=
  Σ x : K, {y : nbrFinset x.val // σ y.val = true}

private def contactIncidenceEdge (K : Finset (Site 2)) (σ : ColorField)
    (p : ContactIncidence K σ) : LatticeEdge :=
  ⟨s(p.1.val, p.2.val.val), (FiniteAvalanches.Sandpile.FiniteWired.mem_neighbors_iff _ _).mp p.2.val.property⟩

private theorem contactIncidenceEdge_injective (K : Finset (Site 2)) (σ : ColorField)
    (hK : ∀ x ∈ K, σ x = false) : Function.Injective (contactIncidenceEdge K σ) := by
  rintro ⟨⟨x, hx⟩, ⟨⟨y, hy⟩, hσy⟩⟩ ⟨⟨x', hx'⟩, ⟨⟨y', hy'⟩, hσy'⟩⟩ h
  have he := Sym2.eq_iff.mp (congrArg Subtype.val h)
  rcases he with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · change x = x' at hxx
    change y = y' at hyy
    subst x'
    subst y'
    rfl
  · change x = y' at hxy
    have hf : σ y' = false := hxy ▸ hK x hx
    rw [hσy'] at hf
    exact Bool.noConfusion hf

private theorem contactIncidenceEdge_range (K : Finset (Site 2)) (σ : ColorField) :
    Set.range (contactIncidenceEdge K σ) = unorderedContactEdges (K : Set (Site 2)) σ := by
  ext e
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1.val, p.1.property, p.2.val.val, p.2.property, rfl⟩
  · rintro ⟨x, hx, y, hy, he⟩
    have hxy : (lattice 2).Adj x y := by
      have h := e.property
      rw [he] at h
      exact h
    let p : ContactIncidence K σ :=
      ⟨⟨x, hx⟩, ⟨⟨y, (FiniteAvalanches.Sandpile.FiniteWired.mem_neighbors_iff _ _).mpr hxy⟩, hy⟩⟩
    exact ⟨p, Subtype.ext he.symm⟩

private theorem card_contactIncidence (K : Finset (Site 2)) (σ : ColorField) :
    Fintype.card (ContactIncidence K σ) = contacts K σ := by
  rw [Fintype.card_sigma]
  change (∑ x : K, Fintype.card {y : nbrFinset x.val // σ y.val = true}) = _
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [show (∑ x : K, ∑ a : nbrFinset x.val, if σ a.val = true then 1 else 0) =
      ∑ x ∈ K, ∑ a : nbrFinset x, if σ a.val = true then 1 else 0 from
    Finset.sum_coe_sort K (fun x => ∑ a : nbrFinset x, if σ a.val = true then 1 else 0)]
  unfold contacts
  apply Finset.sum_congr rfl
  intro x hx
  exact Finset.sum_coe_sort (nbrFinset x) (fun y => if σ y = true then 1 else 0)

/-- The actual finite incidence statistic equals the unordered edge count on zero-colored K.
This proves the dictionary directly; no division by two occurs. -/
theorem unorderedContacts_eq_contacts (K : Finset (Site 2)) (σ : ColorField)
    (hK : ∀ x ∈ K, σ x = false) :
    unorderedContacts (K : Set (Site 2)) σ = (contacts K σ : ℝ≥0∞) := by
  have hcard := (contactIncidenceEdge_injective K σ hK).encard_image Set.univ
  rw [Set.image_univ, Set.encard_univ] at hcard
  rw [unorderedContacts_eq_encard, ← contactIncidenceEdge_range, hcard,
    ENat.card_eq_coe_fintype_card, card_contactIncidence]
  rfl

end
end FiniteAvalanches.Wilson.Lattice
