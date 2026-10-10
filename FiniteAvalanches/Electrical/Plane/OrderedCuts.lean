import FiniteAvalanches.Electrical.Plane.PathEnumeration

/-! Actual source-normalized cut paths with ordered original IDs, exact cardinality and total current. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical

/-- Every interior voltage threshold has an exhaustive simple actual dual path with total current M. -/
theorem exists_ordered_cut_path_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected)
    (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ psi : ArcFace R da db → ℝ,
      (∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi (energy a b phi) d) ∧
      psi (arcRightFace R da db (.inr false)) = 0 ∧
      psi (arcLeftFace R da db (.inr false)) = energy a b phi ∧
      ∃ p : ForwardPath (cutA R da db phi t) (cutB R da db phi t)
          (arcRightFace R da db (.inr false)) (arcLeftFace R da db (.inr false)),
        p.edges.Nodup ∧ p.vertices.Nodup ∧
        (p.edges.map Subtype.val).Nodup ∧
        (p.edges.map Subtype.val).toFinset = crossingEdges a b phi t ∧
        p.vertices.length = (crossingEdges a b phi t).card+1 ∧
        (p.edges.map (fun e => |phi (a e.val)-phi (b e.val)|)).sum = energy a b phi ∧
        ∀ e ∈ p.edges,
          psi (cutB R da db phi t e)-psi (cutA R da db phi t e) = |phi (a e.val)-phi (b e.val)| ∧
          0 < psi (cutB R da db phi t e)-psi (cutA R da db phi t e) := by
  obtain ⟨psi,⟨hj,h0,hM,_,hpaths⟩,_⟩ := existsUnique_stream_cut_paths_of_euler
    R alpha beta hne da db ha hb hc hface heuler phi hp0 hp1 hh
  obtain ⟨_,_,p,he,hv,hall,hinc⟩ := hpaths t ht0 ht1
  obtain ⟨hids,hidsall⟩ := cut_path_original_ids a b phi t p.edges he hall
  have hlength : p.vertices.length = (crossingEdges a b phi t).card+1 := by
    rw [p.vertices_length,← List.length_map (f := Subtype.val),← List.toFinset_card_of_nodup hids,hidsall]
  have htotal : (p.edges.map (fun e => |phi (a e.val)-phi (b e.val)|)).sum = energy a b phi := by
    have heq : p.edges.map (fun e => |phi (a e.val)-phi (b e.val)|) =
        p.edges.map (fun e => psi (cutB R da db phi t e)-psi (cutA R da db phi t e)) := by
      apply List.map_congr_left
      intro e he
      exact (hinc e he).symm
    rw [heq,p.sum_height_increments psi,hM,h0,sub_zero]
  exact ⟨psi,hj,h0,hM,p,he,hv,hids,hidsall,hlength,htotal,
    fun e he => ⟨hinc e he,sub_pos.mpr (cut_stream_increasing R da db phi (energy a b phi) t psi hj e)⟩⟩

end FiniteAvalanches.Electrical.Plane
