import FiniteAvalanches.Wilson.Lattice.WiredHistoryColors

/-! Copied edges determined by finite wired Wilson branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- An original copied edge with both endpoints in a set has the same
membership under arrow assignments agreeing at its nonroot endpoints. -/
theorem wiredArrowCopies_mem_iff_of_agree (R : RootPair) (B : ℕ)
    (a b : GoodArrows (wiredRoots R B).val (wiredHead B))
    (U : Set (FiniteWired.Vertex B)) (e : FiniteWired.Edge B)
    (hleft : (FiniteWired.endpoints e).1 ∈ U) (hright : (FiniteWired.endpoints e).2 ∈ U)
    (hagree : ∀ v ∈ U, v ∉ (wiredRoots R B).val → a.val v = b.val v) :
    e ∈ wiredArrowCopies R B a ↔ e ∈ wiredArrowCopies R B b := by
  have hforward : ∀ a b : GoodArrows (wiredRoots R B).val (wiredHead B),
      (∀ v ∈ U, v ∉ (wiredRoots R B).val → a.val v = b.val v) →
      e ∈ wiredArrowCopies R B a → e ∈ wiredArrowCopies R B b := by
    intro a b hab he
    obtain ⟨v, hv, hcopy⟩ := Finset.mem_image.mp he
    have hvroot : some v ∉ (wiredRoots R B).val := (Finset.mem_filter.mp hv).2
    have hvU : some v ∈ U := by
      have hends := wiredHead_direction_endpoints v (a.val (some v))
      rw [hcopy] at hends
      rcases hends with h | h
      · exact h.1 ▸ hleft
      · exact h.1 ▸ hright
    refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
    rw [← hab (some v) hvU hvroot]
    exact hcopy
  exact ⟨hforward a b hagree, hforward b a (fun v hv hr => (hagree v hv hr).symm)⟩

/-- Any two realizations of a root-ending history agree on an edge whose
endpoints are attached by that history. -/
theorem BranchHistory.Realizes.wiredEdge_mem_iff (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (n : ℕ) (h : BranchHistory n)
    (a b : GoodArrows (wiredRoots R B).val (wiredHead B)) (e : FiniteWired.Edge B)
    (hend : BranchHistory.EndsInRoots (wiredHead B) x (wiredRoots R B).val n h)
    (ha : BranchHistory.Realizes (wiredHead B) x a.val n h)
    (hb : BranchHistory.Realizes (wiredHead B) x b.val n h)
    (hleft : (FiniteWired.endpoints e).1 ∈ branchHistoryRoots (wiredHead B) x (wiredRoots R B).val n h)
    (hright : (FiniteWired.endpoints e).2 ∈ branchHistoryRoots (wiredHead B) x (wiredRoots R B).val n h) :
    e ∈ (wiredArrowForest R B a).val ↔ e ∈ (wiredArrowForest R B b).val := by
  apply wiredArrowCopies_mem_iff_of_agree R B a b _ e hleft hright
  intro v hv hvR
  exact BranchHistory.Realizes.eq_of_mem_roots (wiredHead B) x (wiredRoots R B).val n h
    a.val b.val hend ha hb hv hvR

/-- The copied-edge cylinder for queried endpoints is determined by the
root-ending Wilson branch history. -/
theorem wiredEdgeCylinder_determined_by_history (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (n : ℕ) (h : BranchHistory n)
    (E : Finset (FiniteWired.Edge B)) (p : FiniteWired.Edge B → Bool)
    (hE : ∀ e ∈ E, (∃ i < n, x i = (FiniteWired.endpoints e).1) ∧
      (∃ i < n, x i = (FiniteWired.endpoints e).2))
    (hend : BranchHistory.EndsInRoots (wiredHead B) x (wiredRoots R B).val n h)
    (a b : GoodArrows (wiredRoots R B).val (wiredHead B))
    (ha : BranchHistory.Realizes (wiredHead B) x a.val n h)
    (hb : BranchHistory.Realizes (wiredHead B) x b.val n h) :
    (∀ e ∈ E, decide (e ∈ (wiredArrowForest R B a).val) = p e) ↔
      (∀ e ∈ E, decide (e ∈ (wiredArrowForest R B b).val) = p e) := by
  have he (e : FiniteWired.Edge B) (he : e ∈ E) :
      decide (e ∈ (wiredArrowForest R B a).val) = decide (e ∈ (wiredArrowForest R B b).val) := by
    obtain ⟨⟨i, hi, hi'⟩, ⟨j, hj, hj'⟩⟩ := hE e he
    have hleft := hi' ▸ mem_branchHistoryRoots_of_query (wiredHead B) x (wiredRoots R B).val n h hi
    have hright := hj' ▸ mem_branchHistoryRoots_of_query (wiredHead B) x (wiredRoots R B).val n h hj
    apply decide_eq_decide.mpr
    exact BranchHistory.Realizes.wiredEdge_mem_iff R B x n h a b e hend ha hb hleft hright
  constructor <;> intro hc e he'
  · rw [← he e he']
    exact hc e he'
  · rw [he e he']
    exact hc e he'

/-- The joint event for specified copied-edge indicators and vertex colors. -/
def wiredJointCylinder (R : RootPair) (B : ℕ) (E : Finset (FiniteWired.Edge B))
    (D : Finset (FiniteWired.Vertex B)) (pe : FiniteWired.Edge B → Bool)
    (pc : FiniteWired.Vertex B → Bool) : Set (FiniteForest R B) :=
  {F | (∀ e ∈ E, decide (e ∈ F.val) = pe e) ∧ ∀ v ∈ D, finiteColors R B F v = pc v}

/-- The finite wired joint edge and color law is determined by the stopped
Wilson branches at all observed vertices and edge endpoints. -/
theorem wilsonRows_wiredJointCylinder_eq (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (E : Finset (FiniteWired.Edge B)) (D : Finset (FiniteWired.Vertex B))
    (pe : FiniteWired.Edge B → Bool) (pc : FiniteWired.Vertex B → Bool)
    (hE : ∀ e ∈ E, (∃ i < n, x i = (FiniteWired.endpoints e).1) ∧
      (∃ i < n, x i = (FiniteWired.endpoints e).2))
    (hD : ∀ v ∈ D, ∃ i < n, x i = v) :
    wilsonRows {rows | ∃ N,
      BranchHistory.HitsBefore N n
        (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n) ∧
      BranchHistory.WiredForestEvent R B x n (wiredJointCylinder R B E D pe pc)
        (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n)} =
      finiteUniformLaw R B (wiredJointCylinder R B E D pe pc) := by
  apply wilsonRows_wiredForest_eq_of_prefix_determines R B x k n
    (wiredJointCylinder R B E D pe pc)
  intro h hend a b ha hb
  change ((∀ e ∈ E, decide (e ∈ (wiredArrowForest R B a).val) = pe e) ∧
      ∀ v ∈ D, finiteColors R B (wiredArrowForest R B a) v = pc v) ↔
    ((∀ e ∈ E, decide (e ∈ (wiredArrowForest R B b).val) = pe e) ∧
      ∀ v ∈ D, finiteColors R B (wiredArrowForest R B b) v = pc v)
  exact and_congr (wiredEdgeCylinder_determined_by_history R B x n h E pe hE hend a b ha hb)
    (wiredColorCylinder_determined_by_history R B x n h D pc hD hend a b ha hb)

end
end FiniteAvalanches.Wilson.Lattice
