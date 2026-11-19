import FiniteAvalanches.Electrical.Geometry.BSST
import FiniteAvalanches.Support.Plane.LoopPaths

/-!
# Drawings from crossing paths

Ported from Lattice-Probability `LatticeProb/Topology/PlaneGraph/CrossingDrawing.lean` at commit `ba2b67f3`.

A family of separated paths to edge crossings determines a plane drawing,
including loops when the two incident vertices coincide.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

open Set

/-- Separated paths from vertices to crossings assemble into a drawing. -/
theorem exists_drawing_of_crossing_paths {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (point : V → ℝ × ℝ) (hpoint : Function.Injective point)
    (crossing : E → ℝ × ℝ)
    (p : ∀ e, Path (point (J.left e)) (crossing e))
    (q : ∀ e, Path (point (J.right e)) (crossing e))
    (hp : ∀ e, Function.Injective (p e)) (hq : ∀ e, Function.Injective (q e))
    (hloop : ∀ e, point (J.left e) = point (J.right e) →
      range (p e) ∩ range (q e) = {point (J.left e), crossing e})
    (hedge : ∀ e, point (J.left e) ≠ point (J.right e) →
      range (p e) ∩ range (q e) = {crossing e})
    (hpv : ∀ e t, t ≠ 0 → p e t ∉ range point)
    (hqv : ∀ e t, t ≠ 0 → q e t ∉ range point)
    (hinter : ∀ e f, e ≠ f →
      range ((p e).trans (q e).symm) ∩ range ((p f).trans (q f).symm) ⊆ range point) :
    ∃ D : Drawing J, D.point = point ∧
      ∀ e t, D.curve e t = ((p e).trans (q e).symm) t := by
  let D : Drawing J := {
    point := point
    point_injective := hpoint
    curve := fun e => (p e).trans (q e).symm
    continuous := fun e => ((p e).trans (q e).symm).continuous
    injective := fun e => (path_trans_symm_crossing (p e) (q e) (U := Set.univ) (V := Set.univ) (hp e) (hq e)
      (hloop e) (hedge e) (fun _ _ => trivial) (fun _ _ => trivial)).1
    start := fun e => ((p e).trans (q e).symm).source
    finish := fun e => ((p e).trans (q e).symm).target
    avoids := by
      intro e t ht0 ht1 v hv
      have ht := path_trans_symm_mem_vertices (p e) (q e) (hpv e) (hqv e) t
        ⟨v, hv.symm⟩
      rcases ht with h | h <;> linarith
    intersects := by
      intro e f hef s t h
      exact path_trans_symm_intersects_at_endpoints (p e) (q e) (p f) (q f)
        (hpv e) (hqv e) (hpv f) (hqv f) (hinter e f hef) s t h }
  exact ⟨D, rfl, fun _ _ => rfl⟩

/-- A drawing assembled from separated paths inherits their side and crossing data. -/
theorem exists_drawing_with_crossings {V W E : Type} [Fintype V] [Fintype W] [Fintype E]
    {J : CopiedGraph V E} (D : Drawing J) (J' : CopiedGraph W E)
    (point : W → ℝ × ℝ) (hpoint : Function.Injective point)
    (crossing : E → ℝ × ℝ)
    (p : ∀ e, Path (point (J'.left e)) (crossing e))
    (q : ∀ e, Path (point (J'.right e)) (crossing e))
    (hp : ∀ e, Function.Injective (p e)) (hq : ∀ e, Function.Injective (q e))
    (hloop : ∀ e, point (J'.left e) = point (J'.right e) →
      range (p e) ∩ range (q e) = {point (J'.left e), crossing e})
    (hedge : ∀ e, point (J'.left e) ≠ point (J'.right e) →
      range (p e) ∩ range (q e) = {crossing e})
    (hpv : ∀ e t, t ≠ 0 → p e t ∉ range point)
    (hqv : ∀ e t, t ≠ 0 → q e t ∉ range point)
    (hinter : ∀ e f, e ≠ f →
      range ((p e).trans (q e).symm) ∩ range ((p f).trans (q f).symm) ⊆ range point)
    (U V : E → Set (ℝ × ℝ))
    (hpU : ∀ e t, t ≠ 1 → p e t ∈ U e)
    (hqV : ∀ e t, t ≠ 1 → q e t ∈ V e)
    (hU : ∀ e, Disjoint (U e) (Source.drawingTrace D))
    (hV : ∀ e, Disjoint (V e) (Source.drawingTrace D))
    (hcross : ∀ e f s, D.curve f s = crossing e ↔ f = e ∧ s.val = 1 / 2)
    (chart : E → (ℝ × ℝ → ℝ × ℝ)) (r : E → ℝ)
    (hpchart : ∀ e s, 1 - 2 * r e < s.val →
      chart e (p e s) = (1 / 2, (s.val - 1) / 2))
    (hqchart : ∀ e s, 1 - 2 * r e < s.val →
      chart e (q e s) = (1 / 2, (1 - s.val) / 2)) :
    ∃ D' : Drawing J', D'.point = point ∧
      (∀ e t, (t.val < 1 / 2 → D'.curve e t ∈ U e) ∧
        (1 / 2 < t.val → D'.curve e t ∈ V e)) ∧
      (∀ e f s t, D.curve f s = D'.curve e t ↔
        f = e ∧ s.val = 1 / 2 ∧ t.val = 1 / 2) ∧
      (∀ e t, |t.val - 1 / 2| < r e →
        chart e (D'.curve e t) = (1 / 2, t.val - 1 / 2)) := by
  obtain ⟨D', hpoint', hcurve⟩ :=
    exists_drawing_of_crossing_paths J' point hpoint crossing p q hp hq hloop hedge hpv hqv hinter
  refine ⟨D', hpoint', ?_, ?_, ?_⟩
  · intro e t
    rw [hcurve]
    exact ⟨(path_trans_symm_mem_sides (p e) (q e) (hpU e) (hqV e)).1 t,
      (path_trans_symm_mem_sides (p e) (q e) (hpU e) (hqV e)).2.1 t⟩
  · intro e f s t
    rw [hcurve]
    have hmid := (path_trans_symm_mem_sides (p e) (q e) (hpU e) (hqV e)).2.2
    have hcross_trace : crossing e ∈ Source.drawingTrace D := by
      have h := (hcross e e ⟨1 / 2, by norm_num⟩).mpr ⟨rfl, rfl⟩
      exact Or.inr (mem_iUnion.mpr ⟨e, ⟨_, h⟩⟩)
    have ht := path_trans_symm_mem_trace_iff (p e) (q e) (hpU e) (hqV e)
      (hU e) (hV e) hcross_trace t
    constructor
    · intro h
      have htrace : (p e).trans (q e).symm t ∈ Source.drawingTrace D :=
        h ▸ Or.inr (mem_iUnion.mpr ⟨f, ⟨s, rfl⟩⟩)
      have ht' := ht.mp htrace
      have heq : t = ⟨1 / 2, by norm_num⟩ := Subtype.ext ht'
      have hf := (hcross e f s).mp (by simpa only [heq, hmid] using h)
      exact ⟨hf.1, hf.2, ht'⟩
    · rintro ⟨hfe, hs, ht'⟩
      have heq : t = ⟨1 / 2, by norm_num⟩ := Subtype.ext ht'
      simpa only [heq, hmid] using (hcross e f s).mpr ⟨hfe, hs⟩
  · intro e t ht
    rw [hcurve]
    exact path_trans_symm_chart (p e) (q e) (chart e) (hpchart e) (hqchart e) t ht

end FiniteAvalanches.Electrical.StatementGeometry
