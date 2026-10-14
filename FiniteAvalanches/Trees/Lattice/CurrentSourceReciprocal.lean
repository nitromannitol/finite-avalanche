import FiniteAvalanches.Sandpile.Source.RadiusConnector
import FiniteAvalanches.Trees.ReciprocalBounds
import Mathlib.Order.LiminfLimsup

/-! The finite source object is defined only when every mark belongs to the
volume. Its contact count retains the entire copied edge carrier and the
prescribed infinite sink branch. The older `finiteZN` is used only as an
auxiliary extension, with an ordinary equality bridge on every valid volume. -/
namespace TreeMeasurability11.CurrentDomain
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Sandpile.SourceCounting MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

def sourceContactCopies (N : ℕ) (S : Finset (Site 2)) (hS : S.Nonempty)
    (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree) : Finset (FiniteWired.Edge N) :=
  (WiredTrees.graph N).admissibleEdges
    ((WiredTrees.graph N).descendants t none ((WiredTrees.graph N).ancestorOf
      t none (finiteMarks N S) (finiteMarks_nonempty N S hS hN)))
    ((WiredTrees.graph N).span t (finiteMarks N S))

/-- Literal source count: each original interior or sink exit copy counts once. -/
def sourceContactCount (N : ℕ) (S : Finset (Site 2)) (hS : S.Nonempty)
    (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree) : ℝ≥0∞ :=
  if (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) ≠ none then
    (sourceContactCopies N S hS hN t).card
  else ⊤

/-- The real reciprocal of the fully extended source count. -/
def sourceFiniteReciprocal (N : ℕ) (S : Finset (Site 2)) (hS : S.Nonempty)
    (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree) : ℝ :=
  (sourceContactCount N S hS hN t)⁻¹.toReal

theorem source_mark_represented (N : ℕ) (S : Finset (Site 2))
    (hN : ∀ x ∈ S, FiniteWired.inBox N x) (x : Site 2) (hx : x ∈ S) :
    ∃ a : FiniteWired.Active N, some a ∈ finiteMarks N S ∧ FiniteWired.site a = x := by
  refine ⟨FiniteWired.activeOfSite N x (hN x hx), ?_, FiniteWired.site_activeOfSite _ _ _⟩
  exact ⟨FiniteWired.activeOfSite N x (hN x hx), hx, rfl⟩

theorem sourceContactCount_of_nonsink (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree)
    (hne : (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) ≠ none) :
    sourceContactCount N S hS hN t =
      ((sourceContactCopies N S hS hN t).card : ℝ≥0∞) := by
  rw [sourceContactCount, if_pos hne]

theorem sourceContactCount_of_sink (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree)
    (hsink : (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) = none) :
    sourceContactCount N S hS hN t = ⊤ := by
  simp only [sourceContactCount, hsink, ne_eq, not_true_eq_false, if_false]

theorem sourceContactCount_eq_top_iff (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree) :
    sourceContactCount N S hS hN t = ⊤ ↔
      (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
        (finiteMarks_nonempty N S hS hN) = none := by
  by_cases hne : (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) ≠ none
  · simp [sourceContactCount, hne]
  · simp [sourceContactCount, not_not.mp hne]

theorem sourceContactCount_ge_one (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree) :
    1 ≤ sourceContactCount N S hS hN t := by
  by_cases hne : (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) ≠ none
  · rw [sourceContactCount_of_nonsink N S hS hN t hne]
    have hc : 1 ≤ (sourceContactCopies N S hS hN t).card :=
      Finset.one_le_card.mpr ((WiredTrees.graph N).admissibleEdges_nonempty_of_ancestor_ne_root
        none (finiteMarks N S) (finiteMarks_nonempty N S hS hN) t hne)
    exact_mod_cast hc
  · simp only [sourceContactCount, hne, if_false, le_top]

/-- On the nonsink branch the counted region is exactly the actual ancestor past. -/
theorem sourceContactCopies_eq_past (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree)
    (hne : (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) ≠ none) :
    sourceContactCopies N S hS hN t =
      (WiredTrees.graph N).admissibleEdges
        ((WiredTrees.graph N).past t none ((WiredTrees.graph N).ancestorOf
          t none (finiteMarks N S) (finiteMarks_nonempty N S hS hN)) hne)
        ((WiredTrees.graph N).span t (finiteMarks N S)) := by
  rw [(WiredTrees.graph N).past_eq_descendants]
  rfl

/-- The two prescribed branches determine the count on the whole tree carrier. -/
theorem sourceContactCount_unique (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (f : (WiredTrees.graph N).SpanningTree → ℝ≥0∞)
    (hfinite : ∀ t, (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) ≠ none →
      f t = ((sourceContactCopies N S hS hN t).card : ℝ≥0∞))
    (hinfinite : ∀ t, (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) = none → f t = ⊤) :
    f = sourceContactCount N S hS hN := by
  funext t
  by_cases hne : (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) ≠ none
  · exact (hfinite t hne).trans (sourceContactCount_of_nonsink N S hS hN t hne).symm
  · exact (hinfinite t (not_not.mp hne)).trans
      (sourceContactCount_of_sink N S hS hN t (not_not.mp hne)).symm

theorem sourceFiniteReciprocal_eq_wired (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree) :
    sourceFiniteReciprocal N S hS hN t =
      WiredTrees.reciprocal N (finiteMarks N S) (finiteMarks_nonempty N S hS hN) t := by
  by_cases hne : (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) ≠ none
  · simp [sourceFiniteReciprocal, sourceContactCount, sourceContactCopies,
      WiredTrees.reciprocal, Multigraph.reciprocalWeight, hne]
  · simp [sourceFiniteReciprocal, sourceContactCount,
      WiredTrees.reciprocal, Multigraph.reciprocalWeight, hne]

theorem sourceFiniteReciprocal_eq_auxiliary (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree) :
    sourceFiniteReciprocal N S hS hN t = finiteZN N S hS t := by
  rw [sourceFiniteReciprocal_eq_wired, finiteZN, dif_pos hN]

theorem sourceFiniteReciprocal_bounds (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (WiredTrees.graph N).SpanningTree) :
    0 ≤ sourceFiniteReciprocal N S hS hN t ∧ sourceFiniteReciprocal N S hS hN t ≤ 1 := by
  rw [sourceFiniteReciprocal_eq_wired]
  exact (WiredTrees.graph N).reciprocalWeight_one_nonneg_le_one none
    (finiteMarks N S) (finiteMarks_nonempty N S hS hN) t

/-- In particular the actual endpoint N=r is included, with no lost marks. -/
theorem source_marks_endpoint (r : ℕ) (hr : 2 ≤ r)
    (t : (WiredTrees.graph r).SpanningTree) :
    sourceFiniteReciprocal r (sourceMarks r) (Finset.insert_nonempty _ _)
      (fun _ hx => sourceMarks_inBox hr le_rfl hx) t =
      finiteZN r (sourceMarks r) (Finset.insert_nonempty _ _) t :=
  sourceFiniteReciprocal_eq_auxiliary _ _ _ _ _

/-- Auxiliary extensions have no source meaning at invalid volumes. Agreement
on every valid volume nevertheless fixes their eventual actual expectations. -/
theorem eventual_mean_eq_of_valid_extensions (r : ℕ) (hr : 2 ≤ r)
    (f g : (N : ℕ) → (WiredTrees.graph N).SpanningTree → ℝ)
    (hf : ∀ N, ∀ hrN : r ≤ N, ∀ t,
      f N t = sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t)
    (hg : ∀ N, ∀ hrN : r ≤ N, ∀ t,
      g N t = sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t) :
    ∀ᶠ N in atTop, (∫ t, f N t ∂WiredTrees.law N) = (∫ t, g N t ∂WiredTrees.law N) := by
  filter_upwards [eventually_ge_atTop r] with N hrN
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => (hf N hrN t).trans (hg N hrN t).symm)

theorem limsup_mean_eq_of_valid_extensions (r : ℕ) (hr : 2 ≤ r)
    (f g : (N : ℕ) → (WiredTrees.graph N).SpanningTree → ℝ)
    (hf : ∀ N, ∀ hrN : r ≤ N, ∀ t,
      f N t = sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t)
    (hg : ∀ N, ∀ hrN : r ≤ N, ∀ t,
      g N t = sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t) :
    limsup (fun N => ∫ t, f N t ∂WiredTrees.law N) atTop =
      limsup (fun N => ∫ t, g N t ∂WiredTrees.law N) atTop :=
  limsup_congr (eventual_mean_eq_of_valid_extensions r hr f g hf hg)

/-- Real use of the historical auxiliary sequence, with its agreement proved
internally rather than included as a premise of this application. -/
theorem limsup_finiteZN_eq_valid_extension (r : ℕ) (hr : 2 ≤ r)
    (g : (N : ℕ) → (WiredTrees.graph N).SpanningTree → ℝ)
    (hg : ∀ N, ∀ hrN : r ≤ N, ∀ t,
      g N t = sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t) :
    limsup (fun N => ∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t
      ∂WiredTrees.law N) atTop =
      limsup (fun N => ∫ t, g N t ∂WiredTrees.law N) atTop := by
  apply limsup_mean_eq_of_valid_extensions r hr
  · intro N hrN t
    exact (sourceFiniteReciprocal_eq_auxiliary N (sourceMarks r)
      (Finset.insert_nonempty _ _) (fun _ hx => sourceMarks_inBox hr hrN hx) t).symm
  · exact hg

end
end TreeMeasurability11.CurrentDomain

#print axioms TreeMeasurability11.CurrentDomain.sourceContactCount_unique
#print axioms TreeMeasurability11.CurrentDomain.sourceContactCount_ge_one
#print axioms TreeMeasurability11.CurrentDomain.sourceContactCount_eq_top_iff
#print axioms TreeMeasurability11.CurrentDomain.sourceContactCopies_eq_past
#print axioms TreeMeasurability11.CurrentDomain.sourceFiniteReciprocal_eq_auxiliary
#print axioms TreeMeasurability11.CurrentDomain.sourceFiniteReciprocal_bounds
#print axioms TreeMeasurability11.CurrentDomain.source_marks_endpoint
#print axioms TreeMeasurability11.CurrentDomain.limsup_mean_eq_of_valid_extensions
#print axioms TreeMeasurability11.CurrentDomain.limsup_finiteZN_eq_valid_extension
