import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths

namespace FiniteAvalanches.Sandpile.SourceCounting
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

theorem unit_inBox {N : ℕ} (hN : 1 ≤ N) (i : Fin 2) :
    FiniteWired.inBox N (unit i) := by
  apply neighbor_inBox hN
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and, zero_add]
  exact ⟨i, Finset.mem_insert_self _ _⟩

theorem neg_unit_inBox {N : ℕ} (hN : 1 ≤ N) (i : Fin 2) :
    FiniteWired.inBox N (-unit i) := by
  apply neighbor_inBox hN
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and, zero_sub]
  exact ⟨i, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

theorem positive_endpoints {N : ℕ} (hN : 1 ≤ N) (i : Fin 2) :
    FiniteWired.endpoints (FiniteWired.directionEdge (origin N) (i, true)) =
      (some (origin N), some (FiniteWired.activeOfSite N (unit i) (unit_inBox hN i))) := by
  rw [FiniteWired.directionEdge]
  simp only [site_origin, zero_add]
  rw [dif_pos (unit_inBox hN i)]
  simp only [FiniteWired.endpoints, Prod.mk.injEq, Option.some.injEq, true_and]
  apply FiniteWired.site_injective N
  change 0 + unit i = unit i
  exact zero_add _

theorem negative_endpoints {N : ℕ} (hN : 1 ≤ N) (i : Fin 2) :
    FiniteWired.endpoints (FiniteWired.directionEdge (origin N) (i, false)) =
      (some (FiniteWired.activeOfSite N (-unit i) (neg_unit_inBox hN i)), some (origin N)) := by
  rw [FiniteWired.directionEdge]
  simp only [site_origin, zero_sub]
  rw [dif_pos (neg_unit_inBox hN i)]
  simp only [FiniteWired.endpoints, Prod.mk.injEq, Option.some.injEq, and_true]
  apply FiniteWired.site_injective N
  change 0 - unit i = -unit i
  exact zero_sub _

theorem horizontalEdge_injective {N r : ℕ} (hrN : r ≤ N) :
    Function.Injective (horizontalEdge N r hrN) := by
  intro k l h
  have he := congrArg (fun f => (FiniteWired.endpoints f).1) h
  have he' := Option.some.inj he
  have hx := congrArg (fun x => FiniteWired.site x 0) he'
  change (k.val : ℤ) = (l.val : ℤ) at hx
  exact Fin.ext (by exact_mod_cast hx)

theorem card_horizontalPath {N r : ℕ} (hrN : r ≤ N) :
    (horizontalPath N r hrN).card = r := by
  rw [horizontalPath, Finset.card_image_of_injective _ (horizontalEdge_injective hrN),
    Finset.card_univ, Fintype.card_fin]

theorem card_otherSourceEdges {N : ℕ} (hN : 1 ≤ N) : (otherSourceEdges N).card = 3 := by
  have h01 : FiniteWired.directionEdge (origin N) (0, false) ≠
      FiniteWired.directionEdge (origin N) (1, false) := by
    intro h
    have he := congrArg (fun e => (FiniteWired.endpoints e).1) h
    rw [negative_endpoints hN 0, negative_endpoints hN 1] at he
    have hs := congrArg (fun x => FiniteWired.site x 0) (Option.some.inj he)
    norm_num [FiniteWired.site_activeOfSite, unit] at hs
  have h02 : FiniteWired.directionEdge (origin N) (0, false) ≠
      FiniteWired.directionEdge (origin N) (1, true) := by
    intro h
    have he := congrArg (fun e => (FiniteWired.endpoints e).1) h
    rw [negative_endpoints hN 0, positive_endpoints hN 1] at he
    have hs := congrArg (fun x => FiniteWired.site x 0) (Option.some.inj he)
    norm_num [FiniteWired.site_activeOfSite, site_origin, unit] at hs
  have h12 : FiniteWired.directionEdge (origin N) (1, false) ≠
      FiniteWired.directionEdge (origin N) (1, true) := by
    intro h
    have he := congrArg (fun e => (FiniteWired.endpoints e).1) h
    rw [negative_endpoints hN 1, positive_endpoints hN 1] at he
    have hs := congrArg (fun x => FiniteWired.site x 1) (Option.some.inj he)
    norm_num [FiniteWired.site_activeOfSite, site_origin, unit] at hs
  have hn0 : FiniteWired.directionEdge (origin N) (0, false) ∉
      ({FiniteWired.directionEdge (origin N) (1, false),
        FiniteWired.directionEdge (origin N) (1, true)} : Finset (FiniteWired.Edge N)) := by
    simp [h01, h02]
  have hn1 : FiniteWired.directionEdge (origin N) (1, false) ∉
      ({FiniteWired.directionEdge (origin N) (1, true)} : Finset (FiniteWired.Edge N)) := by
    simp [h12]
  rw [otherSourceEdges, Finset.card_insert_of_notMem hn0,
    Finset.card_insert_of_notMem hn1, Finset.card_singleton]

theorem horizontalPath_disjoint_otherSourceEdges {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    Disjoint (horizontalPath N r hrN) (otherSourceEdges N) := by
  apply Finset.disjoint_left.mpr
  intro f hh ho
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hh
  have hN : 1 ≤ N := by omega
  have hl : (FiniteWired.endpoints (horizontalEdge N r hrN k)).1 =
      some (axisVertex N k.val (by omega)) := rfl
  have ht : (FiniteWired.endpoints (horizontalEdge N r hrN k)).2 =
      some (axisVertex N (k.val+1) (by omega)) := rfl
  simp only [otherSourceEdges, Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with he | he | he
  · have hs := congrArg (fun e => (FiniteWired.endpoints e).1) he
    rw [hl, negative_endpoints hN 0] at hs
    have hx := congrArg (fun x => FiniteWired.site x 0) (Option.some.inj hs)
    simp only [FiniteWired.site_activeOfSite, axisVertex, axisSite, ite_true,
      Pi.neg_apply, unit, Pi.single_eq_same] at hx
    omega
  · have hs := congrArg (fun e => (FiniteWired.endpoints e).1) he
    rw [hl, negative_endpoints hN 1] at hs
    have hx := congrArg (fun x => FiniteWired.site x 1) (Option.some.inj hs)
    norm_num [FiniteWired.site_activeOfSite, axisVertex, axisSite, unit] at hx
  · have hs := congrArg (fun e => (FiniteWired.endpoints e).2) he
    rw [ht, positive_endpoints hN 1] at hs
    have hx := congrArg (fun x => FiniteWired.site x 1) (Option.some.inj hs)
    norm_num [FiniteWired.site_activeOfSite, axisVertex, axisSite, unit] at hx

theorem card_sourceEdges {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    (sourceEdges N r hrN).card = r + 3 := by
  rw [sourceEdges, Finset.card_union_of_disjoint (horizontalPath_disjoint_otherSourceEdges hr hrN),
    card_horizontalPath hrN, card_otherSourceEdges (by omega)]

theorem sourceEdges_endpoints_in_box {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    {f : FiniteWired.Edge N} (hf : f ∈ sourceEdges N r hrN) :
    ∃ x y : FiniteWired.Active N, FiniteWired.endpoints f = (some x, some y) ∧
      FiniteWired.site x ∈ boxSites r ∧ FiniteWired.site y ∈ boxSites r := by
  rcases Finset.mem_union.mp hf with hf | hf
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hf
    refine ⟨axisVertex N k.val (by omega), axisVertex N (k.val+1) (by omega), rfl, ?_, ?_⟩
    · exact (mem_box_sites r _).mpr (axisSite_inBox (by omega))
    · exact (mem_box_sites r _).mpr (axisSite_inBox (by omega))
  · simp only [otherSourceEdges, Finset.mem_insert, Finset.mem_singleton] at hf
    have hN : 1 ≤ N := by omega
    have h0 : FiniteWired.site (origin N) ∈ boxSites r := by
      rw [site_origin, mem_box_sites]
      intro i; simp
    rcases hf with rfl | rfl | rfl
    · exact ⟨_, _, negative_endpoints hN 0,
        (mem_box_sites r _).mpr (neg_unit_inBox (by omega) 0), h0⟩
    · exact ⟨_, _, negative_endpoints hN 1,
        (mem_box_sites r _).mpr (neg_unit_inBox (by omega) 1), h0⟩
    · exact ⟨_, _, positive_endpoints hN 1, h0,
        (mem_box_sites r _).mpr (unit_inBox (by omega) 1)⟩

/-- Every fixed source edge is an original interior copy, including when `N=r`. -/
theorem sourceEdges_no_exit {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    {f : FiniteWired.Edge N} (hf : f ∈ sourceEdges N r hrN) :
    ∃ e : FiniteWired.InteriorEdge N, f = Sum.inl e := by
  obtain ⟨x, y, he, _, _⟩ := sourceEdges_endpoints_in_box hr hrN hf
  cases f with
  | inl e => exact ⟨e, rfl⟩
  | inr e => have h := congrArg Prod.snd he; simp [FiniteWired.endpoints] at h

end
end FiniteAvalanches.Sandpile.SourceCounting
