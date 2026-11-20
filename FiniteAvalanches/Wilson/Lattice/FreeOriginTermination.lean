import FiniteAvalanches.Wilson.Lattice.FreeStoppedExploration
import FiniteAvalanches.Wilson.CyclePopping.RootDescent

/-! Termination of free-box cycle popping rooted at the origin. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance (N : ℕ) : DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- The coordinate distance from an active site to the origin. -/
def freeOriginRank {N : ℕ} (x : FiniteWired.Active N) : ℕ :=
  (|FiniteWired.site x 0| + |FiniteWired.site x 1|).toNat

/-- Every non-origin free-box vertex has an incident copy reducing its origin rank. -/
theorem freeOriginRank_exists_descent (N : ℕ) (x : FiniteWired.Active (N + 1))
    (hx : x ∉ ({wiredOrigin (N + 1)} : Set (FiniteWired.Active (N + 1)))) :
    ∃ e : IncidentCopy (freeBoxGraph (N + 1)) x,
      freeOriginRank (incidentCopyHead (freeBoxGraph (N + 1)) x e) < freeOriginRank x := by
  have hx0 : FiniteWired.site x ≠ 0 := by
    intro h
    apply hx
    simp only [Set.mem_singleton_iff]
    apply FiniteWired.site_injective (N + 1)
    change FiniteWired.site x = (0 : Site 2)
    exact h
  have hi : ∃ i : Fin 2, FiniteWired.site x i ≠ 0 := by
    by_contra h
    apply hx0
    funext i
    fin_cases i <;> simp_all
  obtain ⟨i, hi⟩ := hi
  obtain ⟨z, hzx, hdec, hother⟩ := FiniteAvalanches.Needle.exists_axis_step (FiniteWired.site x) i hi
  have hrad : FiniteAvalanches.Needle.radius (FiniteWired.site x) ≤ ((N + 1 : ℕ) : ℤ) := by
    apply (FiniteAvalanches.Needle.mem_box_iff _ (N + 1)).mp
    exact (FiniteWired.inBox_iff (N + 1) _).mp (fun j => (x j).property)
  have hzrad := FiniteAvalanches.Needle.radius_le_of_step (N + 1) (FiniteWired.site x) z i
    hrad hdec hother
  have hz : FiniteWired.inBox (N + 1) z :=
    (FiniteWired.inBox_iff (N + 1) z).mpr ((FiniteAvalanches.Needle.mem_box_iff z (N + 1)).mpr hzrad)
  let y := FiniteWired.activeOfSite (N + 1) z hz
  have hxy : (freeBoxGraph (N + 1)).adjacent Finset.univ x y :=
    (freeBoxGraph_adjacent_iff _ _ _).mpr hzx
  obtain ⟨e, _, he⟩ := hxy
  have hrank : freeOriginRank y < freeOriginRank x := by
    change (|z 0| + |z 1|).toNat <
      (|FiniteWired.site x 0| + |FiniteWired.site x 1|).toNat
    fin_cases i
    · have hsame := hother 1 (by decide)
      change |z 0| + 1 = |FiniteWired.site x 0| at hdec
      change z 1 = FiniteWired.site x 1 at hsame
      have hnonx := abs_nonneg (FiniteWired.site x 0)
      have hnonx' := abs_nonneg (FiniteWired.site x 1)
      have hnon := abs_nonneg (z 0)
      have hnon' := abs_nonneg (z 1)
      rw [hsame]
      have hpos : 0 < |FiniteWired.site x 0| + |FiniteWired.site x 1| := by omega
      rw [Int.toNat_lt_toNat hpos]
      omega
    · have hsame := hother 0 (by decide)
      change |z 1| + 1 = |FiniteWired.site x 1| at hdec
      change z 0 = FiniteWired.site x 0 at hsame
      have hnonx := abs_nonneg (FiniteWired.site x 0)
      have hnonx' := abs_nonneg (FiniteWired.site x 1)
      have hnon := abs_nonneg (z 0)
      have hnon' := abs_nonneg (z 1)
      rw [hsame]
      have hpos : 0 < |FiniteWired.site x 0| + |FiniteWired.site x 1| := by omega
      rw [Int.toNat_lt_toNat hpos]
      omega
  rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · refine ⟨⟨e, Or.inl hl⟩, ?_⟩
    dsimp only [incidentCopyHead]
    rw [if_pos hl, hr]
    exact hrank
  · refine ⟨⟨e, Or.inr hr⟩, ?_⟩
    have hn : (freeBoxGraph (N + 1)).left e ≠ x := by
      intro h
      exact (freeBoxGraph (N + 1)).loopless e (h.trans hr.symm)
    dsimp only [incidentCopyHead]
    rw [if_neg hn, hl]
    exact hrank

/-- An origin-rooted free box has a cycle-free assignment of incident copies. -/
theorem freeBox_goodOriginArrows_nonempty (N : ℕ) :
    Nonempty (GoodIncidentArrows (freeBoxGraph (N + 1)) {wiredOrigin (N + 1)}) :=
  exists_goodArrows_of_descent _ _ freeOriginRank (freeOriginRank_exists_descent N)

/-- Origin-rooted free-box cycle popping terminates almost surely. -/
theorem variableStackLaw_ae_freeOrigin_terminates (N : ℕ)
    (k : Cursor (FiniteWired.Active (N + 1))) :
    ∀ᵐ σ ∂variableStackLaw (IncidentCopy (freeBoxGraph (N + 1))),
      ∃ l, Relation.ReflTransGen
        (pop_step {wiredOrigin (N + 1)} (incidentCopyHead (freeBoxGraph (N + 1)))
          (fun v i => σ (v, i))) k l ∧
        terminal {wiredOrigin (N + 1)} (incidentCopyHead (freeBoxGraph (N + 1)))
          (fun v i => σ (v, i)) l := by
  obtain ⟨a⟩ := freeBox_goodOriginArrows_nonempty N
  exact variableStackLaw_ae_terminates _ _ _ _ a

/-- Every positive-radius free box has an original-copy spanning tree. -/
theorem freeBox_spanningTree_nonempty (N : ℕ) :
    Nonempty (freeBoxGraph (N + 1)).SpanningTree := by
  obtain ⟨a⟩ := freeBox_goodOriginArrows_nonempty N
  exact ⟨singletonRootedForestEquiv _ _ (incidentArrowForest _ _ a)⟩

end
end FiniteAvalanches.Wilson.Lattice
