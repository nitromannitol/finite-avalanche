import FiniteAvalanches.Wilson.Lattice.WiredRowRealization

/-! Coupling finite wired observation events to lattice sampler events. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The row event realizing a prescribed finite wired observation. -/
def wiredObservationRowEvent (R : RootPair) (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) (E : Finset LatticeEdge)
    (D : Finset (Site 2)) (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) : Set (ℕ → WalkDriver) :=
  {rows | ∃ N,
    BranchHistory.HitsBefore N n
      (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredRoots R B).val k N rows n) ∧
    BranchHistory.WiredForestEvent R B (fun i => wiredSite B (x i)) n
      (wiredObservationCylinder R B E D pe pc)
      (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredRoots R B).val k N rows n)}

/-- Finite wired observation events are measurable in the independent rows. -/
theorem measurableSet_wiredObservationRowEvent (R : RootPair) (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) (E : Finset LatticeEdge)
    (D : Finset (Site 2)) (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) :
    MeasurableSet (wiredObservationRowEvent R B x k n E D pe pc) := by
  let bx := fun i => wiredSite B (x i)
  let P : ℕ → BranchHistory n → Prop := fun N h => BranchHistory.HitsBefore N n h ∧
    BranchHistory.WiredForestEvent R B bx n (wiredObservationCylinder R B E D pe pc) h
  have he : wiredObservationRowEvent R B x k n E D pe pc = ⋃ N : ℕ,
      {rows | P N (rowBranchHistory (wiredHead B) bx (wiredRoots R B).val k N rows n)} := by
    ext rows
    simp only [wiredObservationRowEvent, Set.mem_setOf_eq, Set.mem_iUnion, P, bx]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  exact measurableSet_of_countable_fibers
    (fun rows => rowBranchHistory (wiredHead B) bx (wiredRoots R B).val k N rows n)
    (fun a => measurableSet_rowBranchHistory_eq (wiredHead B) bx (wiredRoots R B).val k N n
      (fun i (rows : ℕ → WalkDriver) => rows i) (fun i => measurable_pi_apply i) a) (P N)

/-- The finite wired observation probability equals the corresponding row event. -/
theorem wilsonRows_wiredObservationRowEvent_eq (R : RootPair) (B : ℕ)
    (x : ℕ → Site 2) (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hD : ∀ z ∈ D, ∃ i < n, x i = z) :
    wilsonRows (wiredObservationRowEvent R B x k n E D pe pc) =
      finiteUniformLaw R B (wiredObservationCylinder R B E D pe pc) :=
  wilsonRows_wiredObservationCylinder_eq R B x k n E D pe pc hE hD

/-- A fixed successful sampler output determines membership in its query event. -/
theorem samplerEvent_iff_of_run (R : RootPair) (L : List (Site 2))
    (rows : ℕ → WalkDriver) (out : SamplerState)
    (hs : samplerRun (initialSampler R) L rows = some out)
    (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) :
    (rows ∈ samplerEvent R L E D pe pc ↔
      (∀ e ∈ E, decide (e.val ∈ out.edges) = pe e) ∧
        ∀ z ∈ D, out.colors z = some (pc z)) := by
  constructor
  · rintro ⟨out', hs', he, hd⟩
    have hout : out' = out := Option.some.inj (hs'.symm.trans hs)
    simpa only [hout] using And.intro he hd
  · intro h
    exact ⟨out, hs, h⟩

/-- Every successful confined lattice branch also hits within the horizon in
the coupled wired history. -/
theorem rowBranchHistory_wired_hits_of_confined (R : RootPair) (B N : ℕ)
    (x : ℕ → Site 2) (ka : Cursor (Site 2)) (kb : Cursor (FiniteWired.Vertex B))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (hN : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows (i + 1)).2.1 < N)
    (hbox : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j)) :
    ∀ i < n, (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i))
      (wiredRoots R B).val kb N rows (i + 1)).2.1 < N := by
  intro i hi
  have hn' : ∀ j < i + 1,
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows (j + 1)).2.1 < N :=
    fun j hj => hN j (lt_of_lt_of_le hj (Nat.succ_le_of_lt hi))
  have hb' : ∀ j < i + 1, ∀ q ≤
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows (j + 1)).2.1,
      FiniteWired.inBox B (position (x j) (rows j) q) :=
    fun j hj => hbox j (lt_of_lt_of_le hj (Nat.succ_le_of_lt hi))
  have he := (rowBranchHistory_wired_eq_of_confined B N x (wiredRoots R B).val
    (R.zero ∪ R.one) kb ka rows (i + 1) (wiredRoots_wiredSite_iff R B) hn' hb').1
  rw [he]
  exact hN i hi

/-- On confined rows, any realizable wired history gives the same joint event
as the lattice sampler. -/
theorem wiredObservationRowEvent_iff_samplerEvent_of_confined (R : RootPair) (B N : ℕ)
    (x : ℕ → Site 2) (ka : Cursor (Site 2)) (kb : Cursor (FiniteWired.Vertex B))
    (rows : ℕ → WalkDriver) (n : ℕ) (out : SamplerState)
    (hN : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows (i + 1)).2.1 < N)
    (hbox : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j))
    (hs : samplerRun (initialSampler R) ((List.range n).map x) rows = some out)
    (hreal : rows ∈ wiredRowRealizationEvent R B (fun i => wiredSite B (x i)) kb n)
    (E : Finset LatticeEdge) (D : Finset (Site 2)) (pe : LatticeEdge → Bool) (pc : Site 2 → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hD : ∀ z ∈ D, ∃ i < n, x i = z) :
    (rows ∈ wiredObservationRowEvent R B x kb n E D pe pc ↔
      rows ∈ samplerEvent R ((List.range n).map x) E D pe pc) := by
  let bx := fun i => wiredSite B (x i)
  let roots := (wiredRoots R B).val
  have hw := rowBranchHistory_wired_hits_of_confined R B N x ka kb rows n hN hbox
  have heq := (rowBranchHistory_wired_eq_of_confined B N x roots (R.zero ∪ R.one) kb ka rows n
    (wiredRoots_wiredSite_iff R B) hN hbox).1
  have hzbox (z : Site 2) (hq : ∃ i < n, x i = z) : FiniteWired.inBox B z := by
    obtain ⟨i, hi, hzi⟩ := hq
    have hz := hbox i hi 0 (Nat.zero_le _)
    simpa only [position_zero, hzi] using hz
  have hebox : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox B z :=
    fun e he z hz => hzbox z (hE e he z hz)
  have hdbox : ∀ z ∈ D, FiniteWired.inBox B z := fun z hz => hzbox z (hD z hz)
  have hcompare (a : GoodArrows roots (wiredHead B))
      (ha : BranchHistory.Realizes (wiredHead B) bx a.val n
        (rowBranchHistory (wiredHead B) bx roots kb N rows n)) :
      (wiredArrowForest R B a ∈ wiredObservationCylinder R B E D pe pc ↔
        rows ∈ samplerEvent R ((List.range n).map x) E D pe pc) := by
    rw [heq] at ha
    exact (samplerRun_jointEvent_iff_wiredObservation_of_confined R B N x ka kb rows n out
      hN hbox hs a ha E D pe pc hE hD hebox hdbox).trans
        (samplerEvent_iff_of_run R ((List.range n).map x) rows out hs E D pe pc).symm
  constructor
  · rintro ⟨M, hM, a, ha, hobs⟩
    have hM' := (rowBranchHistory_hitsBefore_iff (wiredHead B) bx roots kb M n rows).mp hM
    have hm := rowBranchHistory_eq_of_two_hits (wiredHead B) bx roots kb M N n rows hM' hw
    rw [hm] at ha
    exact (hcompare a ha).mp hobs
  · intro hsamp
    obtain ⟨M, hM, a, ha⟩ := hreal
    have hM' := (rowBranchHistory_hitsBefore_iff (wiredHead B) bx roots kb M n rows).mp hM
    have hm := rowBranchHistory_eq_of_two_hits (wiredHead B) bx roots kb M N n rows hM' hw
    rw [hm] at ha
    exact ⟨N, (rowBranchHistory_hitsBefore_iff (wiredHead B) bx roots kb N n rows).mpr hw,
      a, ha, (hcompare a ha).mpr hsamp⟩

end
end FiniteAvalanches.Wilson.Lattice
