import FiniteAvalanches.Model.WiredLaplacian
import FiniteAvalanches.Sandpile.Components.Supports

namespace FiniteAvalanches.Sandpile.SourceCounting
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

/-- The literal lattice site `(k,0)`. -/
def axisSite (k : ℕ) : Site2 := fun i => if i = 0 then (k : ℤ) else 0

theorem axisSite_zero : axisSite 0 = 0 := by
  funext i
  simp [axisSite]

theorem axisSite_succ (k : ℕ) : axisSite (k + 1) = axisSite k + unit 0 := by
  funext i
  fin_cases i <;> simp [axisSite, unit]

theorem axisSite_inBox {N k : ℕ} (hk : k ≤ N) : FiniteWired.inBox N (axisSite k) := by
  intro i
  fin_cases i <;> simp [axisSite]
  exact_mod_cast hk

def origin (N : ℕ) : FiniteWired.Active N :=
  FiniteWired.activeOfSite N 0 (by intro i; simp)

theorem site_origin (N : ℕ) : FiniteWired.site (origin N) = 0 := rfl

def axisVertex (N k : ℕ) (hk : k ≤ N) : FiniteWired.Active N :=
  FiniteWired.activeOfSite N (axisSite k) (axisSite_inBox hk)

theorem axisVertex_zero (N : ℕ) : axisVertex N 0 (Nat.zero_le N) = origin N := by
  apply FiniteWired.site_injective N
  exact axisSite_zero

/-- The marked set `N[0] ∪ {(r,0)}` on its literal lattice carrier. -/
def sourceMarks (r : ℕ) : Finset Site2 := insert (axisSite r) (insert 0 (nbrFinset 0))

theorem neighbor_inBox {N : ℕ} (hN : 1 ≤ N) {x : Site2}
    (hx : x ∈ nbrFinset (0 : Site2)) : FiniteWired.inBox N x := by
  obtain ⟨i, hi | hi⟩ := (FiniteWired.mem_neighbors_iff 0 x).mp hx
  · subst x
    intro j
    fin_cases i <;> fin_cases j <;> simp [unit] <;> omega
  · have he : x = -unit i := by
      have h := congrArg (fun z : Site2 => z - unit i) hi
      simpa using h.symm
    rw [he]
    intro j
    fin_cases i <;> fin_cases j <;> simp [unit] <;> omega

theorem sourceMarks_inBox {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    {x : Site2} (hx : x ∈ sourceMarks r) : FiniteWired.inBox N x := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact axisSite_inBox hrN
  · rcases Finset.mem_insert.mp hx with rfl | hx
    · intro i; simp
    · exact neighbor_inBox (by omega) hx

/-- The entire marked set on the active carrier, as a literal preimage. -/
def activeMarks (N r : ℕ) : Finset (FiniteWired.Active N) :=
  Finset.univ.filter fun x => FiniteWired.site x ∈ sourceMarks r

theorem markedSites_activeMarks {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    markedSites (activeMarks N r) = sourceMarks r := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hv).2
  · intro x hx
    exact Finset.mem_image.mpr ⟨FiniteWired.activeOfSite N x (sourceMarks_inBox hr hrN hx),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

theorem source_mem_activeMarks (N r : ℕ) : origin N ∈ activeMarks N r := by
  simp [activeMarks, sourceMarks, site_origin]

theorem marked_neighborhood {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    insert (FiniteWired.site (origin N)) (nbrFinset (FiniteWired.site (origin N))) ⊆
      markedSites (activeMarks N r) := by
  rw [site_origin, markedSites_activeMarks hr hrN]
  exact Finset.subset_insert _ _

/-- One original positive-coordinate edge copy from `(k,0)` to `(k+1,0)`. -/
def horizontalEdge (N r : ℕ) (hrN : r ≤ N) (k : Fin r) : FiniteWired.Edge N :=
  .inl ⟨(axisVertex N k.val (by omega), axisVertex N (k.val + 1) (by omega)),
    ⟨0, axisSite_succ k.val⟩⟩

def horizontalPath (N r : ℕ) (hrN : r ≤ N) : Finset (FiniteWired.Edge N) :=
  Finset.univ.image (horizontalEdge N r hrN)

/-- The three source edges outside the positive horizontal direction. -/
def otherSourceEdges (N : ℕ) : Finset (FiniteWired.Edge N) :=
  {FiniteWired.directionEdge (origin N) (0, false),
    FiniteWired.directionEdge (origin N) (1, false),
    FiniteWired.directionEdge (origin N) (1, true)}

/-- The fixed lattice graph from zero to the marks, retaining original edge copies. -/
def sourceEdges (N r : ℕ) (hrN : r ≤ N) : Finset (FiniteWired.Edge N) :=
  horizontalPath N r hrN ∪ otherSourceEdges N

theorem horizontalEdge_mem {N r : ℕ} (hrN : r ≤ N) (k : Fin r) :
    horizontalEdge N r hrN k ∈ sourceEdges N r hrN := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

theorem horizontal_reaches {N r : ℕ} (hrN : r ≤ N) (k : ℕ) (hk : k ≤ r) :
    (WiredTrees.graph N).reaches (sourceEdges N r hrN)
      (some (origin N)) (some (axisVertex N k (hk.trans hrN))) := by
  induction k with
  | zero => rw [axisVertex_zero]; exact .refl
  | succ k ih =>
    have hstep : (WiredTrees.graph N).adjacent (sourceEdges N r hrN)
        (some (axisVertex N k (by omega))) (some (axisVertex N (k+1) (hk.trans hrN))) :=
      ⟨horizontalEdge N r hrN ⟨k, by omega⟩, horizontalEdge_mem hrN _, Or.inl ⟨rfl, rfl⟩⟩
    exact (ih (by omega)).trans (Relation.ReflTransGen.single hstep)

theorem positive_source_edge_eq_horizontal {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    FiniteWired.directionEdge (origin N) (0, true) =
      horizontalEdge N r hrN ⟨0, by omega⟩ := by
  have hb : FiniteWired.inBox N (FiniteWired.site (origin N) + unit 0) := by
    rw [site_origin, ← axisSite_zero, ← axisSite_succ]
    exact axisSite_inBox (by omega)
  rw [FiniteWired.directionEdge, dif_pos hb]
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext
  · exact (axisVertex_zero N).symm
  · apply FiniteWired.site_injective N
    change FiniteWired.site (origin N) + unit 0 = axisSite (0 + 1)
    rw [axisSite_succ, axisSite_zero, site_origin]

theorem directionEdge_mem_sourceEdges {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    (d : FiniteWired.Direction) :
    FiniteWired.directionEdge (origin N) d ∈ sourceEdges N r hrN := by
  rcases d with ⟨i, b⟩
  fin_cases i <;> cases b
  · exact Finset.mem_union_right _ (by simp [otherSourceEdges])
  · change FiniteWired.directionEdge (origin N) (0, true) ∈ sourceEdges N r hrN
    rw [positive_source_edge_eq_horizontal hr hrN]
    exact horizontalEdge_mem hrN _
  · exact Finset.mem_union_right _ (by simp [otherSourceEdges])
  · exact Finset.mem_union_right _ (by simp [otherSourceEdges])

theorem neighbor_reaches {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    (y : FiniteWired.Active N) (hy : FiniteWired.site y ∈ nbrFinset (0 : Site2)) :
    (WiredTrees.graph N).reaches (sourceEdges N r hrN) (some (origin N)) (some y) := by
  obtain ⟨i, hi | hi⟩ := (FiniteWired.mem_neighbors_iff 0 (FiniteWired.site y)).mp hy
  · have hb : FiniteWired.inBox N (FiniteWired.site (origin N) + unit i) := by
      rw [site_origin, ← hi]
      exact fun j => (y j).property
    have he : FiniteWired.activeOfSite N (FiniteWired.site (origin N) + unit i) hb = y := by
      apply FiniteWired.site_injective N
      exact hi.symm
    apply Relation.ReflTransGen.single
    refine ⟨FiniteWired.directionEdge (origin N) (i, true),
      directionEdge_mem_sourceEdges hr hrN _, Or.inl ⟨?_, ?_⟩⟩
    · change (FiniteWired.endpoints _).1 = _
      rw [FiniteWired.directionEdge, dif_pos hb]
      rfl
    · change (FiniteWired.endpoints _).2 = _
      rw [FiniteWired.directionEdge, dif_pos hb]
      exact congrArg some he
  · have hs : FiniteWired.site (origin N) - unit i = FiniteWired.site y := by
      rw [site_origin, hi]
      abel
    have hb : FiniteWired.inBox N (FiniteWired.site (origin N) - unit i) := by
      rw [hs]
      exact fun j => (y j).property
    have he : FiniteWired.activeOfSite N (FiniteWired.site (origin N) - unit i) hb = y :=
      FiniteWired.site_injective N hs
    apply Relation.ReflTransGen.single
    refine ⟨FiniteWired.directionEdge (origin N) (i, false),
      directionEdge_mem_sourceEdges hr hrN _, Or.inr ⟨?_, ?_⟩⟩
    · change (FiniteWired.endpoints _).2 = _
      rw [FiniteWired.directionEdge, dif_pos hb]
      rfl
    · change (FiniteWired.endpoints _).1 = _
      rw [FiniteWired.directionEdge, dif_pos hb]
      exact congrArg some he

theorem sourceEdges_reaches_marks {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    (y : FiniteWired.Active N) (hy : y ∈ activeMarks N r) :
    (WiredTrees.graph N).reaches (sourceEdges N r hrN) (some (origin N)) (some y) := by
  have hm := (Finset.mem_filter.mp hy).2
  rcases Finset.mem_insert.mp hm with hm | hm
  · have he : y = axisVertex N r hrN := FiniteWired.site_injective N hm
    rw [he]
    exact horizontal_reaches hrN r le_rfl
  · rcases Finset.mem_insert.mp hm with hm | hm
    · have he : y = origin N := FiniteWired.site_injective N hm
      rw [he]
      exact .refl
    · exact neighbor_reaches hr hrN y hm

theorem card_sourceEdges_le {N r : ℕ} (hrN : r ≤ N) :
    (sourceEdges N r hrN).card ≤ r + 3 := by
  have hh : (horizontalPath N r hrN).card ≤ r := by
    simpa only [horizontalPath, Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_le (s := (Finset.univ : Finset (Fin r)))
        (f := horizontalEdge N r hrN)
  have ho : (otherSourceEdges N).card ≤ 3 := by
    have h1 := Finset.card_insert_le (FiniteWired.directionEdge (origin N) (0, false))
      ({FiniteWired.directionEdge (origin N) (1, false),
        FiniteWired.directionEdge (origin N) (1, true)} : Finset (FiniteWired.Edge N))
    have h2 := Finset.card_insert_le (FiniteWired.directionEdge (origin N) (1, false))
      ({FiniteWired.directionEdge (origin N) (1, true)} : Finset (FiniteWired.Edge N))
    simp only [Finset.card_singleton] at h2
    dsimp only [otherSourceEdges]
    omega
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hh ho)

theorem card_sourceEdges_le_three_mul {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    (sourceEdges N r hrN).card ≤ 3 * r := by
  have h := card_sourceEdges_le hrN
  omega

end
end FiniteAvalanches.Sandpile.SourceCounting
