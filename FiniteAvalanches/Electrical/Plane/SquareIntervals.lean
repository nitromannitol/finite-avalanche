import FiniteAvalanches.Electrical.Plane.SquareSlices

/-! Actual cut-path intervals imply disjoint original square interiors and complete interior-voltage slices. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- An original square interior meets the strict ascending stream interval of its actual cut copy. -/
theorem cut_square_open_stream {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (M t : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (e : CutCopy a b phi t) {z : ℝ × ℝ}
    (hz : z ∈ (incrementSquare R da db phi psi (e.val,false) (hp (.inl (e.val,false)))).openCarrier) :
    z.2 ∈ Set.Ioo (psi (cutA R da db phi t e)) (psi (cutB R da db phi t e)) := by
  rw [← Square.interior_carrier,incrementSquare_carrier,← cut_rectangle_eq_original R da db phi t psi e] at hz
  simp only [potentialRectangle,rectangle,interior_prod_eq,interior_Icc] at hz
  have hi := cut_stream_increasing R da db phi M t psi hp e
  change _ ∧ z.2 ∈ Set.Ioo (min (psi (cutB R da db phi t e)) (psi (cutA R da db phi t e)))
    (max (psi (cutB R da db phi t e)) (psi (cutA R da db phi t e))) at hz
  rw [min_eq_right hi.le,max_eq_left hi.le] at hz
  exact hz.2

/-- Every interior voltage slice is covered, including vertex-voltage levels and closed vertical endpoints. -/
theorem square_slice_cover {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hface : R.rightFace da = R.rightFace db)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (M : ℝ) (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0)
    (t u : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hu0 : 0 ≤ u) (huM : u ≤ M) :
    ∃ e : E, (t,u) ∈ (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).carrier := by
  have hneD : da ≠ db := by intro h; rw [h,hb] at ha; exact hne ha.symm
  have hneF := (arcFace_card_and_distinct R da db hneD hface).2.symm
  obtain ⟨p,_,_,hall,_⟩ := exists_cut_path R alpha beta hne da db ha hb phi hp0 hp1 M psi hp t ht0 ht1
  have hM := exterior_stream_values R da db phi psi M (hp (.inr false)) h0
  obtain ⟨e,_,he⟩ := p.closed_interval_cover psi hneF
    (fun e _ => cut_stream_increasing R da db phi M t psi hp e) u
    (by rw [h0]; exact hu0) (by rw [hM]; exact huM)
  exact ⟨e.val,(cut_square_slice R da db phi M t psi hp e u).mpr he⟩

/-- Distinct original copy IDs have disjoint open square interiors, without a supplied packing premise. -/
theorem square_open_disjoint {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (M : ℝ) (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset E))
      (fun e => (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).openCarrier) := by
  intro e _ f _ hef
  apply Set.disjoint_left.mpr
  intro z hze hzf
  have hpe : psi (arcLeftFace R da db (.inl (e,false)))-psi (arcRightFace R da db (.inl (e,false))) = current a b phi (e,false) := hp (.inl (e,false))
  have hpf : psi (arcLeftFace R da db (.inl (f,false)))-psi (arcRightFace R da db (.inl (f,false))) = current a b phi (f,false) := hp (.inl (f,false))
  have hze' : z ∈ (incrementSquare R da db phi psi (e,false) hpe).openCarrier := hze
  have hzf' : z ∈ (incrementSquare R da db phi psi (f,false) hpf).openCarrier := hzf
  have hx_e : min (phi (a e)) (phi (b e)) < z.1 ∧ z.1 < max (phi (a e)) (phi (b e)) := by
    rw [incrementSquare_openCarrier] at hze'
    exact hze'.1
  have hx_f : min (phi (a f)) (phi (b f)) < z.1 ∧ z.1 < max (phi (a f)) (phi (b f)) := by
    rw [incrementSquare_openCarrier] at hzf'
    exact hzf'.1
  have hv := voltage_range a b alpha beta hc phi hp0 hp1 hh
  have ht0 : 0 < z.1 := (le_min (hv (a e)).1 (hv (b e)).1).trans_lt hx_e.1
  have ht1 : z.1 < 1 := hx_e.2.trans_le (max_le (hv (a e)).2 (hv (b e)).2)
  let ce : CutCopy a b phi z.1 := ⟨e,mem_crossingEdges_of_voltage_interior a b phi z.1 e hx_e⟩
  let cf : CutCopy a b phi z.1 := ⟨f,mem_crossingEdges_of_voltage_interior a b phi z.1 f hx_f⟩
  obtain ⟨p,_,_,hall,_⟩ := exists_cut_path R alpha beta hne da db ha hb phi hp0 hp1 M psi hp z.1 ht0 ht1
  have he : ce ∈ p.edges := by
    apply List.mem_toFinset.mp
    rw [hall]
    exact Finset.mem_univ ce
  have hf : cf ∈ p.edges := by
    apply List.mem_toFinset.mp
    rw [hall]
    exact Finset.mem_univ cf
  have hcf : ce ≠ cf := fun h => hef (congrArg Subtype.val h)
  have hd := p.interval_disjoint psi
    (fun e _ => cut_stream_increasing R da db phi M z.1 psi hp e) ce he cf hf hcf
  exact Set.disjoint_left.mp hd
    (cut_square_open_stream R da db phi M z.1 psi hp ce hze)
    (cut_square_open_stream R da db phi M z.1 psi hp cf hzf)

end FiniteAvalanches.Electrical.Plane
