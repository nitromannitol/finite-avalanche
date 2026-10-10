import FiniteAvalanches.Needle.ConnectedSetApplication

set_option autoImplicit false
namespace Needle107Path
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open scoped Classical

lemma staircase_progress (h : ℕ) (b : ℤ) (hb0 : 0 ≤ b) (hb : b ≤ 2*h)
    (s t : Fin (h+(b-h).toNat+1)) (hst : s.val ≤ t.val) :
    radius (staircase h b hb0 hb t) ≤ radius (staircase h b hb0 hb s) ∧
    (t.val : ℤ)-s.val ≤
      2*(radius (staircase h b hb0 hb s)-radius (staircase h b hb0 hb t))+1 := by
  obtain ⟨hs0, _, hs1, _, _⟩ := staircase_coordinates h b hb0 hb s
  obtain ⟨ht0, _, ht1, _, _⟩ := staircase_coordinates h b hb0 hb t
  have hsi := s.isLt
  have hti := t.isLt
  simp only [radius, abs_of_nonneg (by omega : 0 ≤ staircase h b hb0 hb s 0),
    abs_of_nonneg (by omega : 0 ≤ staircase h b hb0 hb t 0),
    abs_of_nonneg hs1, abs_of_nonneg ht1]
  dsimp only [staircase, Matrix.cons_val_zero, Matrix.cons_val_one] at *
  omega

lemma staircase_span (h : ℕ) (b : ℤ) (hb0 : 0 ≤ b) (hb : b ≤ 2*h)
    (s t : Fin (h+(b-h).toNat+1)) :
    |(s.val : ℤ)-t.val| ≤
      2*|radius (staircase h b hb0 hb s)-radius (staircase h b hb0 hb t)|+1 := by
  rcases le_total s.val t.val with hst | hts
  · obtain ⟨hr, hn⟩ := staircase_progress h b hb0 hb s t hst
    rw [abs_of_nonpos (by omega : (s.val : ℤ)-t.val ≤ 0), abs_of_nonneg (by omega)]
    omega
  · obtain ⟨hr, hn⟩ := staircase_progress h b hb0 hb t s hts
    rw [abs_of_nonneg (by omega : 0 ≤ (s.val : ℤ)-t.val), abs_of_nonpos (by omega)]
    omega

/-- The source staircase with the quantitative span retained in its ordinary constructor. -/
theorem exists_quantitative_path (h : ℕ) (z : Point) (hz : radius z = 2*h) :
    ∃ (L : ℕ) (p : InBoxVertices h L),
      p.val ⟨0, by omega⟩ ∈ box 2 h ∧ p.val ⟨L, by omega⟩ = z ∧
      (∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩) (p.val ⟨t.val+1, by omega⟩)) ∧
      (∀ s t, |(s.val : ℤ)-t.val| ≤ 2*|radius (p.val s)-radius (p.val t)|+1) := by
  obtain ⟨σ, ε, b, hε, hb0, hb, he⟩ := boundary_normalization h z hz
  let L := h+(b-h).toNat
  let rev (t : Fin (L+1)) : Fin (L+1) := ⟨L-t.val, by omega⟩
  let q (t : Fin (L+1)) : Point := symmetry σ ε hε (staircase h b hb0 hb (rev t))
  have hq : ∀ t, q t ∈ box 2 (2*h) := by
    intro t
    have hc := (staircase_radial h b hb0 hb (rev t)).1
    rw [mem_box_iff]
    simpa only [q, symmetry_radius σ ε hε, Nat.cast_mul, Nat.cast_ofNat] using hc
  let p : InBoxVertices h L := ⟨q, hq⟩
  refine ⟨L, p, ?_, ?_, ?_, ?_⟩
  · rw [mem_box_iff]
    change radius (symmetry σ ε hε (staircase h b hb0 hb ⟨L, by omega⟩)) ≤ h
    rw [symmetry_radius σ ε hε]
    exact (mem_box_iff _ _).mp (staircase_end_mem_box h b hb0 hb)
  · change symmetry σ ε hε (staircase h b hb0 hb ⟨L-L, by omega⟩) = z
    simpa only [Nat.sub_self, staircase_start] using he
  · intro t
    apply symmetry_adj σ ε hε
    have ht := staircase_adj h b hb0 hb (L-(t.val+1)) (by have := t.isLt; dsimp [L]; omega)
    convert ht.symm using 1
    · congr 1; apply Fin.ext; dsimp only [rev]; omega
  · intro s t
    have hh := staircase_span h b hb0 hb (rev s) (rev t)
    change |(s.val : ℤ)-t.val| ≤
      2*|radius (symmetry σ ε hε (staircase h b hb0 hb (rev s)))-
        radius (symmetry σ ε hε (staircase h b hb0 hb (rev t)))|+1
    rw [symmetry_radius σ ε hε, symmetry_radius σ ε hε]
    have hab : |((rev s).val : ℤ)-(rev t).val| = |(s.val : ℤ)-t.val| := by
      dsimp only [rev]
      rw [abs_eq_max_neg, abs_eq_max_neg]
      omega
    exact hab ▸ hh

lemma path_linf_le_span (L : ℕ) (p : Fin (L+1) → Point)
    (hstep : ∀ t : Fin L, (lattice 2).Adj (p ⟨t.val, by omega⟩) (p ⟨t.val+1, by omega⟩))
    (s t : Fin (L+1)) : linf (p s) (p t) ≤ |(s.val : ℤ)-t.val| := by
  have forward : ∀ n : ℕ, ∀ a : ℕ, ∀ ha : a < L+1, ∀ hn : a+n < L+1,
      linf (p ⟨a, ha⟩) (p ⟨a+n, hn⟩) ≤ n := by
    intro n
    induction n with
    | zero => intro a ha hn; simp [linf, radius]
    | succ n ih =>
      intro a ha hn
      have hh := linf_triangle (p ⟨a, ha⟩) (p ⟨a+n, by omega⟩) (p ⟨a+(n+1), hn⟩)
      have hs := radius_sub_neighbor (hstep ⟨a+n, by omega⟩)
      have he : p ⟨a+n+1, by omega⟩ = p ⟨a+(n+1), hn⟩ := by congr 1
      rw [he] at hs
      dsimp only [linf] at hh
      rw [hs] at hh
      have hih := ih a ha (by omega)
      dsimp only [linf] at hih
      change radius (p ⟨a, ha⟩-p ⟨a+(n+1), hn⟩) ≤ (n+1 : ℕ)
      push_cast
      omega
  rcases le_total s.val t.val with hst | hts
  · have hh := forward (t.val-s.val) s.val s.isLt (by omega)
    have he : s.val+(t.val-s.val) = t.val := by omega
    simp only [he] at hh
    change linf (p s) (p t) ≤ (t.val-s.val : ℕ) at hh
    rw [abs_of_nonpos (by omega : (s.val : ℤ)-t.val ≤ 0)]
    omega
  · have hh := forward (s.val-t.val) t.val t.isLt (by omega)
    have he : t.val+(s.val-t.val) = s.val := by omega
    simp only [he] at hh
    rw [linf_comm] at hh
    change linf (p s) (p t) ≤ (s.val-t.val : ℕ) at hh
    rw [abs_of_nonneg (by omega : 0 ≤ (s.val : ℤ)-t.val)]
    omega

end Needle107Path
