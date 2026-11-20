import FiniteAvalanches.Wilson.Lattice.WiredObservationGeometry
import FiniteAvalanches.Wilson.Lattice.JointEventAgreement

/-! Joint ambient edge and color observations in finite wired Wilson laws. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Pull a finite ambient joint observation back to original wired forests. -/
def wiredObservationCylinder (R : RootPair) (B : ℕ) (E : Finset LatticeEdge)
    (D : Finset (Site 2)) (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) :
    Set (FiniteForest R B) :=
  {F | (∀ e ∈ E, finiteEdgeField R B F e = pe e) ∧
    ∀ z ∈ D, finiteColors R B F (wiredSite B z) = pc z}

/-- A wired observation depends only on its selected finite coordinates. -/
theorem wiredObservationCylinder_iff_of_agree (R : RootPair) (B : ℕ)
    (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) (F G : FiniteForest R B)
    (he : ∀ e ∈ E, finiteEdgeField R B F e = finiteEdgeField R B G e)
    (hd : ∀ z ∈ D, finiteColors R B F (wiredSite B z) = finiteColors R B G (wiredSite B z)) :
    F ∈ wiredObservationCylinder R B E D pe pc ↔ G ∈ wiredObservationCylinder R B E D pe pc := by
  change ((∀ e ∈ E, finiteEdgeField R B F e = pe e) ∧
      ∀ z ∈ D, finiteColors R B F (wiredSite B z) = pc z) ↔
    ((∀ e ∈ E, finiteEdgeField R B G e = pe e) ∧
      ∀ z ∈ D, finiteColors R B G (wiredSite B z) = pc z)
  constructor
  · intro h
    exact ⟨fun e he' => (he e he').symm.trans (h.1 e he'),
      fun z hz => (hd z hz).symm.trans (h.2 z hz)⟩
  · intro h
    exact ⟨fun e he' => (he e he').trans (h.1 e he'),
      fun z hz => (hd z hz).trans (h.2 z hz)⟩

/-- A queried interior copy has the same membership under any two
realizations of the same root-ending history. -/
theorem wiredObservation_copy_mem_iff (R : RootPair) (B : ℕ)
    (x : ℕ → Site 2) (n : ℕ) (h : BranchHistory n) (e : LatticeEdge)
    (i : FiniteWired.InteriorEdge B) (hi : interiorEdge i = e)
    (hq : ∀ z ∈ e.val, ∃ j < n, x j = z)
    (hend : BranchHistory.EndsInRoots (wiredHead B) (fun j => wiredSite B (x j))
      (wiredRoots R B).val n h)
    (a b : GoodArrows (wiredRoots R B).val (wiredHead B))
    (ha : BranchHistory.Realizes (wiredHead B) (fun j => wiredSite B (x j)) a.val n h)
    (hb : BranchHistory.Realizes (wiredHead B) (fun j => wiredSite B (x j)) b.val n h) :
    Sum.inl i ∈ (wiredArrowForest R B a).val ↔ Sum.inl i ∈ (wiredArrowForest R B b).val := by
  let bx := fun j => wiredSite B (x j)
  let roots := (wiredRoots R B).val
  have hm := interiorEdge_endpoint_mem i
  obtain ⟨j, hj, hj'⟩ := hq (FiniteWired.site i.val.1) (hi ▸ hm.1)
  obtain ⟨k, hk, hk'⟩ := hq (FiniteWired.site i.val.2) (hi ▸ hm.2)
  have hs (v : FiniteWired.Active B) : wiredSite B (FiniteWired.site v) = some v := by
    simpa only [wiredVertexSite] using wiredSite_wiredVertexSite B (some v)
  have hjroot : some i.val.1 ∈ branchHistoryRoots (wiredHead B) bx roots n h := by
    have ht := mem_branchHistoryRoots_of_query (wiredHead B) bx roots n h hj
    change wiredSite B (x j) ∈ _ at ht
    rw [hj', hs] at ht
    exact ht
  have hkroot : some i.val.2 ∈ branchHistoryRoots (wiredHead B) bx roots n h := by
    have ht := mem_branchHistoryRoots_of_query (wiredHead B) bx roots n h hk
    change wiredSite B (x k) ∈ _ at ht
    rw [hk', hs] at ht
    exact ht
  apply BranchHistory.Realizes.wiredEdge_mem_iff R B bx n h a b (Sum.inl i) hend ha hb
  · exact hjroot
  · exact hkroot

/-- The ambient indicator of a queried edge is fixed by the branch history. -/
theorem wiredObservation_edge_eq (R : RootPair) (B : ℕ)
    (x : ℕ → Site 2) (n : ℕ) (h : BranchHistory n) (e : LatticeEdge)
    (hq : ∀ z ∈ e.val, ∃ j < n, x j = z)
    (hend : BranchHistory.EndsInRoots (wiredHead B) (fun j => wiredSite B (x j))
      (wiredRoots R B).val n h)
    (a b : GoodArrows (wiredRoots R B).val (wiredHead B))
    (ha : BranchHistory.Realizes (wiredHead B) (fun j => wiredSite B (x j)) a.val n h)
    (hb : BranchHistory.Realizes (wiredHead B) (fun j => wiredSite B (x j)) b.val n h) :
    finiteEdgeField R B (wiredArrowForest R B a) e =
      finiteEdgeField R B (wiredArrowForest R B b) e := by
  apply Bool.eq_iff_iff.mpr
  simp only [finiteEdgeField, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hEq⟩
    exact ⟨i, (wiredObservation_copy_mem_iff R B x n h e i hEq hq hend a b ha hb).mp hi, hEq⟩
  · rintro ⟨i, hi, hEq⟩
    exact ⟨i, (wiredObservation_copy_mem_iff R B x n h e i hEq hq hend a b ha hb).mpr hi, hEq⟩

/-- The ambient color at a queried site is fixed by the branch history. -/
theorem wiredObservation_color_eq (R : RootPair) (B : ℕ)
    (x : ℕ → Site 2) (n : ℕ) (h : BranchHistory n) (z : Site 2)
    (hq : ∃ i < n, x i = z)
    (hend : BranchHistory.EndsInRoots (wiredHead B) (fun j => wiredSite B (x j))
      (wiredRoots R B).val n h)
    (a b : GoodArrows (wiredRoots R B).val (wiredHead B))
    (ha : BranchHistory.Realizes (wiredHead B) (fun j => wiredSite B (x j)) a.val n h)
    (hb : BranchHistory.Realizes (wiredHead B) (fun j => wiredSite B (x j)) b.val n h) :
    finiteColors R B (wiredArrowForest R B a) (wiredSite B z) =
      finiteColors R B (wiredArrowForest R B b) (wiredSite B z) := by
  obtain ⟨i, hi, hzi⟩ := hq
  apply BranchHistory.Realizes.wiredColor_eq R B (fun j => wiredSite B (x j)) n h a b hend ha hb
  rw [← hzi]
  exact mem_branchHistoryRoots_of_query (wiredHead B) (fun j => wiredSite B (x j))
    (wiredRoots R B).val n h hi

/-- A finite ambient joint cylinder is determined by a root-ending wired
history once all its observed sites and edge endpoints have been queried. -/
theorem wiredObservationCylinder_determined (R : RootPair) (B : ℕ)
    (x : ℕ → Site 2) (n : ℕ) (h : BranchHistory n) (E : Finset LatticeEdge)
    (D : Finset (Site 2)) (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hD : ∀ z ∈ D, ∃ i < n, x i = z)
    (hend : BranchHistory.EndsInRoots (wiredHead B) (fun i => wiredSite B (x i))
      (wiredRoots R B).val n h)
    (a b : GoodArrows (wiredRoots R B).val (wiredHead B))
    (ha : BranchHistory.Realizes (wiredHead B) (fun i => wiredSite B (x i)) a.val n h)
    (hb : BranchHistory.Realizes (wiredHead B) (fun i => wiredSite B (x i)) b.val n h) :
    (wiredArrowForest R B a ∈ wiredObservationCylinder R B E D pe pc ↔
      wiredArrowForest R B b ∈ wiredObservationCylinder R B E D pe pc) := by
  have he : ∀ e ∈ E, finiteEdgeField R B (wiredArrowForest R B a) e =
      finiteEdgeField R B (wiredArrowForest R B b) e :=
    fun e he => wiredObservation_edge_eq R B x n h e (hE e he) hend a b ha hb
  have hd : ∀ z ∈ D, finiteColors R B (wiredArrowForest R B a) (wiredSite B z) =
      finiteColors R B (wiredArrowForest R B b) (wiredSite B z) :=
    fun z hz => wiredObservation_color_eq R B x n h z (hD z hz) hend a b ha hb
  exact wiredObservationCylinder_iff_of_agree R B E D pe pc
    (wiredArrowForest R B a) (wiredArrowForest R B b) he hd

/-- The finite wired joint observation law is given by completed Wilson
branch histories of the queried endpoints. -/
theorem wilsonRows_wiredObservationCylinder_eq (R : RootPair) (B : ℕ)
    (x : ℕ → Site 2) (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hD : ∀ z ∈ D, ∃ i < n, x i = z) :
    wilsonRows {rows | ∃ N,
      BranchHistory.HitsBefore N n
        (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredRoots R B).val k N rows n) ∧
      BranchHistory.WiredForestEvent R B (fun i => wiredSite B (x i)) n
        (wiredObservationCylinder R B E D pe pc)
        (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredRoots R B).val k N rows n)} =
      finiteUniformLaw R B (wiredObservationCylinder R B E D pe pc) := by
  apply wilsonRows_wiredForest_eq_of_prefix_determines R B (fun i => wiredSite B (x i)) k n
    (wiredObservationCylinder R B E D pe pc)
  intro h hh a b ha hb
  exact wiredObservationCylinder_determined R B x n h E D pe pc hE hD hh a b ha hb

end
end FiniteAvalanches.Wilson.Lattice
