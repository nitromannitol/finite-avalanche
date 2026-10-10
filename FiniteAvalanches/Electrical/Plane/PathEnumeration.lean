import FiniteAvalanches.Electrical.Plane.CutPaths

/-! The ordered path exposes every actual original copy ID exactly once. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- Forgetting only subtype membership retains a once-only enumeration of original crossing IDs. -/
theorem cut_path_original_ids {V E : Type*} [Fintype E] (a b : E → V) (phi : V → ℝ) (t : ℝ)
    (l : List (CutCopy a b phi t)) (hn : l.Nodup) (hall : l.toFinset = Finset.univ) :
    (l.map Subtype.val).Nodup ∧ (l.map Subtype.val).toFinset = crossingEdges a b phi t := by
  constructor
  · exact hn.map Subtype.val_injective
  · have hm : (l.map Subtype.val).toFinset = l.toFinset.image Subtype.val := by
      ext e
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,List.mem_toFinset]
    rw [hm,hall,Finset.univ_eq_attach,Finset.attach_image_val]

/-- Ordered positive stream increments telescope to the exact end-to-start height difference. -/
theorem ForwardPath.sum_height_increments {V E : Type*} {a b : E → V}
    (H : V → ℝ) {x y : V} (p : ForwardPath a b x y) :
    (p.edges.map (fun e => H (b e)-H (a e))).sum = H y-H x := by
  induction p with
  | nil => simp only [ForwardPath.edges,List.map_nil,List.sum_nil,sub_self]
  | cons e p ih => simp only [ForwardPath.edges,List.map_cons,List.sum_cons,ih]; ring

end FiniteAvalanches.Electrical.Plane
