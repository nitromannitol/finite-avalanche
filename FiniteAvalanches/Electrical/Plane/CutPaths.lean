import FiniteAvalanches.Electrical.Plane.PathExtraction
import FiniteAvalanches.Electrical.Plane.CutBoundary
import FiniteAvalanches.Electrical.Plane.Rectangle

/-! Actual ordered dual voltage-cut paths obtained from the constructed face stream. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- Positive oriented cut current equals the original copy's absolute voltage difference. -/
theorem cut_current_eq_abs {V E : Type*} [Fintype E] (a b : E → V) (phi : V → ℝ) (t : ℝ)
    (e : CutCopy a b phi t) : current a b phi (cutDart a b phi t e) = |phi (a e.val)-phi (b e.val)| := by
  have hp := cut_current_pos a b phi t e
  by_cases h : phi (a e.val) < t
  · simp only [cutDart,if_pos h] at hp ⊢
    change phi (b e.val)-phi (a e.val) = _
    change 0 < phi (b e.val)-phi (a e.val) at hp
    rw [abs_sub_comm]
    exact (abs_of_pos hp).symm
  · simp only [cutDart,if_neg h] at hp ⊢
    exact (abs_of_pos hp).symm

/-- One simple directed dual path exhausts every original crossing copy once. -/
theorem exists_cut_path {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (M : ℝ) (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ p : ForwardPath (cutA R da db phi t) (cutB R da db phi t)
        (arcRightFace R da db (.inr false)) (arcLeftFace R da db (.inr false)),
      p.edges.Nodup ∧ p.vertices.Nodup ∧ p.edges.toFinset = Finset.univ ∧
      ∀ e ∈ p.edges, psi (cutB R da db phi t e)-psi (cutA R da db phi t e) =
        |phi (a e.val)-phi (b e.val)| := by
  classical
  obtain ⟨p,he,hv,hall⟩ := exists_forwardPath_exhausting_unitBoundary
    (cutA R da db phi t) (cutB R da db phi t) Finset.univ psi
    (arcRightFace R da db (.inr false)) (arcLeftFace R da db (.inr false))
    (fun e _ => cut_stream_increasing R da db phi M t psi hp e)
    (by
      intro f
      have h := cut_unitBoundary R alpha beta hne da db ha hb phi hp0 hp1 t ht0 ht1 f
      split_ifs at h ⊢ <;> exact h)
  refine ⟨p,he,hv,?_,fun e _ => (cut_stream_increment R da db phi M t psi hp e).trans
    (cut_current_eq_abs a b phi t e)⟩
  ext z
  have hh := congrArg (fun S : Finset (CutCopy a b phi t) => z ∈ S) hall
  simpa only [List.mem_toFinset,Finset.mem_univ] using (iff_of_eq hh)

/-- The Euler stream existence theorem produces the stream before obtaining all actual cut paths. -/
theorem existsUnique_stream_cut_paths_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected)
    (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    ∃! psi : ArcFace R da db → ℝ,
      (∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi (energy a b phi) d) ∧
      psi (arcRightFace R da db (.inr false)) = 0 ∧
      psi (arcLeftFace R da db (.inr false)) = energy a b phi ∧
      (∀ f, 0 ≤ psi f ∧ psi f ≤ energy a b phi) ∧
      ∀ t : ℝ, 0 < t → t < 1 →
        ((supportGraph a b).induce {x | phi x < t}).Connected ∧
        ((supportGraph a b).induce {x | t < phi x}).Connected ∧
        ∃ p : ForwardPath (cutA R da db phi t) (cutB R da db phi t)
            (arcRightFace R da db (.inr false)) (arcLeftFace R da db (.inr false)),
          p.edges.Nodup ∧ p.vertices.Nodup ∧ p.edges.toFinset = Finset.univ ∧
          ∀ e ∈ p.edges, psi (cutB R da db phi t e)-psi (cutA R da db phi t e) =
            |phi (a e.val)-phi (b e.val)| := by
  obtain ⟨psi,hpsi,hu⟩ := existsUnique_normalized_stream_of_euler
    R alpha beta hne da db ha hb hc hface heuler phi hp0 hp1 hh
  refine ⟨psi,⟨hpsi.1,hpsi.2,?_,?_,?_⟩,?_⟩
  · exact exterior_stream_values R da db phi psi (energy a b phi) (hpsi.1 (.inr false)) hpsi.2
  · exact stream_range R alpha beta hne da db ha hb hc phi (energy a b phi)
      (energy_nonneg a b phi) psi hpsi.1 hpsi.2
  · intro t ht0 ht1
    obtain ⟨hl,hh'⟩ := (voltage_range_and_levels a b alpha beta hc phi hp0 hp1 hh).2 t ht0 ht1
    exact ⟨hl,hh',exists_cut_path R alpha beta hne da db ha hb phi hp0 hp1
      (energy a b phi) psi hpsi.1 t ht0 ht1⟩
  · intro chi hchi
    exact hu chi ⟨hchi.1,hchi.2.1⟩

end FiniteAvalanches.Electrical.Plane
