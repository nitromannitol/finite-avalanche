import FiniteAvalanches.Sandpile.SourceCounting.CountingGeometry

/-! The original source vertices, including the complete integer segment. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices
open LatticeProb FiniteAvalanches Sandpile
open scoped Classical
noncomputable section

/-- The actual original integer sites from 0 through (r,0), both endpoints included. -/
def sourceSegment (r : ℕ) : Finset (Site 2) := (Finset.range (r + 1)).image axisSite

/-- Exactly the marked source sites and the integer segment, not endpoint slots. -/
def sourceVertices (r : ℕ) : Finset (Site 2) := sourceMarks r ∪ sourceSegment r

theorem axisSite_eq_smul_unit (k : ℕ) : axisSite k = (k : ℤ) • unit (0 : Fin 2) := by
  funext i
  fin_cases i <;> simp [axisSite, unit]

theorem axisSite_injective : Function.Injective axisSite := by
  intro k l h
  have he := congrFun h 0
  simp only [axisSite, ite_true] at he
  exact_mod_cast he

theorem card_sourceSegment (r : ℕ) : (sourceSegment r).card = r + 1 := by
  rw [sourceSegment, Finset.card_image_of_injective _ axisSite_injective, Finset.card_range]

theorem axis_mem_segment {r k : ℕ} (hk : k ≤ r) : axisSite k ∈ sourceSegment r :=
  Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩

theorem sourceVertices_eq_three_insert_segment (r : ℕ) (hr : 2 ≤ r) :
    sourceVertices r = insert (-unit (0 : Fin 2))
      (insert (-unit (1 : Fin 2)) (insert (unit (1 : Fin 2)) (sourceSegment r))) := by
  have hzero : (0 : Site 2) ∈ sourceSegment r := axisSite_zero ▸ axis_mem_segment (Nat.zero_le r)
  have hplus : unit (0 : Fin 2) ∈ sourceSegment r := by
    have he : axisSite 1 = unit (0 : Fin 2) := by
      simpa only [axisSite_zero, zero_add] using axisSite_succ 0
    exact he ▸ axis_mem_segment (by omega : 1 ≤ r)
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (axis_mem_segment le_rfl)))
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hzero))
        · obtain ⟨i, hi | hi⟩ := (FiniteWired.mem_neighbors_iff 0 x).mp hx
          · have he : x = unit i := by simpa only [zero_add] using hi
            subst x
            fin_cases i
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (by simpa [unit] using hplus)))
            · simp [unit]
          · have he : x = -unit i := by
              have he := congrArg (fun z : Site 2 => z - unit i) hi
              simpa using he.symm
            subst x
            fin_cases i
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
  · intro hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | rfl | hx
    · apply Finset.mem_union_left
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact (FiniteWired.mem_neighbors_iff 0 _).mpr ⟨0, Or.inr (by simp)⟩
    · apply Finset.mem_union_left
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact (FiniteWired.mem_neighbors_iff 0 _).mpr ⟨1, Or.inr (by simp)⟩
    · apply Finset.mem_union_left
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact (FiniteWired.mem_neighbors_iff 0 _).mpr ⟨1, Or.inl (by simp)⟩
    · exact Finset.mem_union_right _ hx

theorem card_sourceVertices (r : ℕ) (hr : 2 ≤ r) : (sourceVertices r).card = r + 4 := by
  have hn0 : -unit (0 : Fin 2) ∉ sourceSegment r := by
    intro hx
    obtain ⟨k, _hk, he⟩ := Finset.mem_image.mp hx
    have he0 := congrFun he 0
    norm_num [axisSite, unit] at he0
    omega
  have hn1 : -unit (1 : Fin 2) ∉ sourceSegment r := by
    intro hx
    obtain ⟨k, _hk, he⟩ := Finset.mem_image.mp hx
    have he1 := congrFun he 1
    norm_num [axisSite, unit] at he1
  have hp1 : unit (1 : Fin 2) ∉ sourceSegment r := by
    intro hx
    obtain ⟨k, _hk, he⟩ := Finset.mem_image.mp hx
    have he1 := congrFun he 1
    norm_num [axisSite, unit] at he1
  have h01 : -unit (0 : Fin 2) ≠ -unit (1 : Fin 2) := by
    intro h
    have he := congrFun h 0
    norm_num [unit] at he
  have h02 : -unit (0 : Fin 2) ≠ unit (1 : Fin 2) := by
    intro h
    have he := congrFun h 0
    norm_num [unit] at he
  have h12 : -unit (1 : Fin 2) ≠ unit (1 : Fin 2) := by
    intro h
    have he := congrFun h 1
    norm_num [unit] at he
  rw [sourceVertices_eq_three_insert_segment r hr,
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert]; tauto :
      -unit (0 : Fin 2) ∉ insert (-unit (1 : Fin 2)) (insert (unit (1 : Fin 2)) (sourceSegment r))),
    Finset.card_insert_of_notMem (by simp only [Finset.mem_insert]; tauto :
      -unit (1 : Fin 2) ∉ insert (unit (1 : Fin 2)) (sourceSegment r)),
    Finset.card_insert_of_notMem hp1, card_sourceSegment]

theorem sourceVertices_inBox {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    {x : Site 2} (hx : x ∈ sourceVertices r) : FiniteWired.inBox N x := by
  rcases Finset.mem_union.mp hx with hx | hx
  · exact sourceMarks_inBox hr hrN hx
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact axisSite_inBox ((by have := Finset.mem_range.mp hk; omega : k ≤ r).trans hrN)

theorem sourceVertices_subset_box (r : ℕ) (hr : 2 ≤ r) : sourceVertices r ⊆ boxSites r :=
  fun _ hx => (mem_box_sites _ _).mpr (sourceVertices_inBox hr le_rfl hx)

/-- Both physical original endpoints lie in the same r+4 site family, even N=r. -/
theorem sourceEdges_endpoints_in_vertices {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    {f : FiniteWired.Edge N} (hf : f ∈ sourceEdges N r hrN) :
    ∃ x y : FiniteWired.Active N, FiniteWired.endpoints f = (some x, some y) ∧
      FiniteWired.site x ∈ sourceVertices r ∧ FiniteWired.site y ∈ sourceVertices r := by
  have h0 : (0 : Site 2) ∈ sourceVertices r :=
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hn {z : Site 2} (hz : z ∈ nbrFinset (0 : Site 2)) : z ∈ sourceVertices r :=
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
  rcases Finset.mem_union.mp hf with hf | hf
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨axisVertex N k.val (by omega), axisVertex N (k.val+1) (by omega), rfl,
      Finset.mem_union_right _ (axis_mem_segment (by omega)),
      Finset.mem_union_right _ (axis_mem_segment (by omega))⟩
  · simp only [otherSourceEdges, Finset.mem_insert, Finset.mem_singleton] at hf
    have hN : 1 ≤ N := by omega
    rcases hf with rfl | rfl | rfl
    · exact ⟨_, _, negative_endpoints hN 0, hn ((FiniteWired.mem_neighbors_iff 0 _).mpr
        ⟨0, Or.inr (by simp [FiniteWired.site_activeOfSite])⟩), h0⟩
    · exact ⟨_, _, negative_endpoints hN 1, hn ((FiniteWired.mem_neighbors_iff 0 _).mpr
        ⟨1, Or.inr (by simp [FiniteWired.site_activeOfSite])⟩), h0⟩
    · exact ⟨_, _, positive_endpoints hN 1, h0, hn ((FiniteWired.mem_neighbors_iff 0 _).mpr
        ⟨1, Or.inl (by simp [FiniteWired.site_activeOfSite])⟩)⟩

end
end FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceSegment
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceSegment

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceVertices
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceVertices

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.axisSite_eq_smul_unit
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.axisSite_eq_smul_unit

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.axisSite_injective
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.axisSite_injective

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.card_sourceSegment
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.card_sourceSegment

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.axis_mem_segment
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.axis_mem_segment

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceVertices_eq_three_insert_segment
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceVertices_eq_three_insert_segment

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.card_sourceVertices
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.card_sourceVertices

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceVertices_inBox
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceVertices_inBox

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceVertices_subset_box
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceVertices_subset_box

#print FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceEdges_endpoints_in_vertices
#print axioms FiniteAvalanches.Sandpile.SourceCounting.CurrentPastVertices.sourceEdges_endpoints_in_vertices
