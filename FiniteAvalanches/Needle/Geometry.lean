import FiniteAvalanches.Model.FiniteWired
import FiniteAvalanches.Model.WiredTreeExistence
import FiniteAvalanches.Electrical.Dirichlet
import LatticeProb.Graph.Zd
import Mathlib.NumberTheory.Harmonic.Bounds

namespace FiniteAvalanches.Needle
open LatticeProb
open scoped BigOperators Classical

abbrev Point := Site 2

def radius (x : Point) : ℤ := max |x 0| |x 1|

def linf (x y : Point) : ℤ := radius (x - y)

theorem radius_nonneg (x : Point) : 0 ≤ radius x :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem radius_le_iff (x : Point) (r : ℤ) :
    radius x ≤ r ↔ ∀ i, |x i| ≤ r := by
  simp [radius, Fin.forall_fin_two]

theorem mem_box_iff (x : Point) (r : ℕ) :
    x ∈ box 2 r ↔ radius x ≤ r := (radius_le_iff x r).symm

theorem radius_sub_le (x y : Point) : radius (x - y) ≤ radius x + radius y := by
  apply (radius_le_iff _ _).mpr
  intro i
  have hx := (radius_le_iff x (radius x)).mp le_rfl i
  have hy := (radius_le_iff y (radius y)).mp le_rfl i
  exact (abs_sub _ _).trans (add_le_add hx hy)

theorem radius_le_radius_add (x y : Point) : radius x ≤ radius (x - y) + radius y := by
  have h := radius_sub_le (x - y) (-y)
  simpa only [sub_neg_eq_add, sub_add_cancel, radius, Pi.neg_apply, abs_neg] using h

/-- The reversed left/down staircase, followed by the horizontal segment. -/
def staircase (h : ℕ) (b : ℤ) (_hb0 : 0 ≤ b) (_hb : b ≤ 2*h) (t : Fin (h + (b - h).toNat + 1)) : Point :=
  ![(2 * h : ℤ) - ((t.val : ℤ) - min (t.val / 2) (b - h).toNat),
    b - min (t.val / 2) (b - h).toNat]

theorem staircase_coordinates (h : ℕ) (b : ℤ)
    (hb0 : 0 ≤ b) (hb : b ≤ 2 * h) (t : Fin (h + (b - h).toNat + 1)) :
    (h : ℤ) ≤ staircase h b hb0 hb t 0 ∧ staircase h b hb0 hb t 0 ≤ 2 * h ∧
    0 ≤ staircase h b hb0 hb t 1 ∧ staircase h b hb0 hb t 1 ≤ 2 * h ∧
    staircase h b hb0 hb t 1 ≤ staircase h b hb0 hb t 0 + 1 := by
  have ht := t.isLt
  dsimp [staircase]
  omega

theorem staircase_radial (h : ℕ) (b : ℤ)
    (hb0 : 0 ≤ b) (hb : b ≤ 2 * h) (t : Fin (h + (b - h).toNat + 1)) :
    radius (staircase h b hb0 hb t) ≤ 2 * h ∧
    linf ![2 * h, b] (staircase h b hb0 hb t) ≤ 2 * h - radius (staircase h b hb0 hb t) + 1 := by
  obtain ⟨hx0, hx1, hy0, hy1, _⟩ := staircase_coordinates h b hb0 hb t
  have ht := t.isLt
  simp only [radius, linf, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    abs_of_nonneg (show 0 ≤ staircase h b hb0 hb t 0 by omega),
    abs_of_nonneg hy0]
  dsimp [staircase] at *
  simp only [abs_eq_max_neg]
  omega

theorem staircase_start (h : ℕ) (b : ℤ) (hb0 : 0 ≤ b) (hb : b ≤ 2*h) :
    staircase h b hb0 hb ⟨0, by omega⟩ = ![(2 * h : ℤ), b] := by
  simp [staircase]

theorem staircase_end_mem_box (h : ℕ) (b : ℤ)
    (hb0 : 0 ≤ b) (hb : b ≤ 2 * h) :
    staircase h b hb0 hb ⟨h + (b - h).toNat, by omega⟩ ∈ box 2 h := by
  rw [mem_box_iff, radius_le_iff]
  intro i
  fin_cases i <;> dsimp [staircase] <;> rw [abs_le] <;> omega

theorem staircase_adj (h : ℕ) (b : ℤ) (hb0 : 0 ≤ b) (hb : b ≤ 2*h) (t : ℕ)
    (ht : t < h + (b - h).toNat) :
    (lattice 2).Adj (staircase h b hb0 hb ⟨t, by omega⟩)
      (staircase h b hb0 hb ⟨t + 1, by omega⟩) := by
  have hstep : min ((t+1)/2) (b-h).toNat = min (t/2) (b-h).toNat ∨
      min ((t+1)/2) (b-h).toNat = min (t/2) (b-h).toNat + 1 := by omega
  rcases hstep with hs | hs
  · refine ⟨0, Or.inr ?_⟩
    funext i
    fin_cases i <;> simp [staircase, unit] <;> omega
  · refine ⟨1, Or.inr ?_⟩
    funext i
    fin_cases i <;> simp [staircase, unit] <;> omega

theorem staircase_injective (h : ℕ) (b : ℤ) (hb0 : 0 ≤ b) (hb : b ≤ 2*h) : Function.Injective (staircase h b hb0 hb) := by
  intro t s he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  apply Fin.ext
  dsimp [staircase] at h0 h1
  omega


/-- Signed permutations are precisely square-lattice coordinate symmetries. -/
def symmetry (σ : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℤ)
    (_hε : ∀ i, ε i = 1 ∨ ε i = -1) (x : Point) : Point :=
  fun i => ε i * x (σ i)

theorem symmetry_radius (σ : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (x : Point) :
    radius (symmetry σ ε hε x) = radius x := by
  have hcoord (i : Fin 2) : |symmetry σ ε hε x i| = |x (σ i)| := by
    rcases hε i with hi | hi <;> simp [symmetry, hi]
  apply le_antisymm
  · apply (radius_le_iff _ _).mpr
    intro i
    rw [hcoord]
    exact (radius_le_iff x _).mp le_rfl (σ i)
  · apply (radius_le_iff _ _).mpr
    intro i
    have ht := (radius_le_iff (symmetry σ ε hε x) _).mp le_rfl (σ.symm i)
    simpa only [hcoord, σ.apply_symm_apply] using ht

theorem symmetry_linf (σ : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (x y : Point) :
    linf (symmetry σ ε hε x) (symmetry σ ε hε y) = linf x y := by
  have he : symmetry σ ε hε x - symmetry σ ε hε y = symmetry σ ε hε (x - y) := by
    funext i; simp [symmetry, mul_sub]
  rw [linf, he, symmetry_radius σ ε hε]
  rfl

theorem symmetry_injective (σ : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) : Function.Injective (symmetry σ ε hε) := by
  intro x y h
  funext i
  have hi := congrFun h (σ.symm i)
  rcases hε (σ.symm i) with hs | hs <;> simpa [symmetry, hs] using hi

theorem symmetry_adj (σ : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) {x y : Point}
    (h : (lattice 2).Adj x y) : (lattice 2).Adj (symmetry σ ε hε x) (symmetry σ ε hε y) := by
  have pos {x y : Point} (i : Fin 2) (hy : y = x + unit i) :
      (lattice 2).Adj (symmetry σ ε hε x) (symmetry σ ε hε y) := by
    rcases hε (σ.symm i) with hs | hs
    · refine ⟨σ.symm i, Or.inl ?_⟩
      subst y
      funext j
      by_cases hj : j = σ.symm i
      · subst j; simp [symmetry, unit, hs]
      · have hji : σ j ≠ i := fun hh => hj (σ.injective (by simpa using hh))
        simp [symmetry, unit, hj, hji]
    · refine ⟨σ.symm i, Or.inr ?_⟩
      subst y
      funext j
      by_cases hj : j = σ.symm i
      · subst j; simp [symmetry, unit, hs]
      · have hji : σ j ≠ i := fun hh => hj (σ.injective (by simpa using hh))
        simp [symmetry, unit, hj, hji]
  rcases h with ⟨i, hi | hi⟩
  · exact pos i hi
  · exact (pos i hi).symm

theorem boundary_normalization (h : ℕ) (z : Point) (hz : radius z = 2 * h) :
    ∃ (σ : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℤ) (b : ℤ),
      ∃ hε : (∀ i, ε i = 1 ∨ ε i = -1), 0 ≤ b ∧ b ≤ 2 * h ∧
        symmetry σ ε hε ![(2 * h : ℤ), b] = z := by
  let ε : Fin 2 → ℤ := fun i => if z i < 0 then -1 else 1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i; dsimp [ε]; split <;> simp
  have hsign (i : Fin 2) : ε i * |z i| = z i := by
    dsimp [ε]
    split
    · rename_i hi; rw [abs_of_neg hi]; ring
    · rename_i hi; rw [abs_of_nonneg (le_of_not_gt hi), one_mul]
  have hb := (radius_le_iff z (2 * h)).mp hz.le
  rcases max_eq_iff.mp hz with ⟨hz0, _⟩ | ⟨hz1, _⟩
  · refine ⟨Equiv.refl _, ε, |z 1|, hε, abs_nonneg _, hb 1, ?_⟩
    funext i
    fin_cases i
    · simpa [symmetry, ← hz0] using hsign 0
    · simpa [symmetry] using hsign 1
  · refine ⟨Equiv.swap 0 1, ε, |z 0|, hε, abs_nonneg _, hb 0, ?_⟩
    funext i
    fin_cases i
    · simpa [symmetry] using hsign 0
    · simpa [symmetry, ← hz1] using hsign 1

/-- Every boundary point has a simple nearest-neighbor needle, with radial depth control. -/
theorem exists_radial_path (h : ℕ) (z : Point) (hz : radius z = 2 * h) :
    ∃ (L : ℕ) (p : Fin (L+1) → Point),
      Function.Injective p ∧ p ⟨0, by omega⟩ ∈ box 2 h ∧
      p ⟨L, by omega⟩ = z ∧
      (∀ t : Fin L, (lattice 2).Adj (p ⟨t.val, by omega⟩) (p ⟨t.val+1, by omega⟩)) ∧
      (∀ t, p t ∈ box 2 (2*h) ∧ linf z (p t) ≤ 2*h - radius (p t) + 1) := by
  obtain ⟨σ, ε, b, hε, hb0, hb, he⟩ := boundary_normalization h z hz
  let L := h + (b-h).toNat
  let rev (t : Fin (L+1)) : Fin (L+1) := ⟨L-t.val, by omega⟩
  let p (t : Fin (L+1)) : Point := symmetry σ ε hε (staircase h b hb0 hb (rev t))
  have hr : Function.Injective rev := by intro t s hs; apply Fin.ext; have := congrArg Fin.val hs; dsimp [rev] at this; omega
  refine ⟨L, p, (symmetry_injective σ ε hε).comp ((staircase_injective h b hb0 hb).comp hr), ?_, ?_, ?_, ?_⟩
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
    · congr 1; apply Fin.ext; dsimp [rev]; omega
  · intro t
    obtain ⟨hc, hd⟩ := staircase_radial h b hb0 hb (rev t)
    constructor
    · rw [mem_box_iff]
      simpa only [p, symmetry_radius σ ε hε, Nat.cast_mul, Nat.cast_ofNat] using hc
    · rw [← he]
      simpa only [p, symmetry_radius σ ε hε, symmetry_linf σ ε hε] using hd


/-- Four sides of a square, restricted to a coordinate window. -/
noncomputable def sideWindow (R : ℤ) (z : Point) (r : ℕ) : Finset Point :=
  ((Finset.Icc (-(r : ℤ)) r).image (fun v => ![R, z 1 + v])) ∪
  ((Finset.Icc (-(r : ℤ)) r).image (fun v => ![-R, z 1 + v])) ∪
  ((Finset.Icc (-(r : ℤ)) r).image (fun v => ![z 0 + v, R])) ∪
  ((Finset.Icc (-(r : ℤ)) r).image (fun v => ![z 0 + v, -R]))

theorem mem_sideWindow {R : ℤ} {z x : Point} {r : ℕ}
    (hx : radius x = R) (hz : linf x z ≤ r) : x ∈ sideWindow R z r := by
  have h0 := (radius_le_iff (x-z) (r:ℤ)).mp hz 0
  have h1 := (radius_le_iff (x-z) (r:ℤ)).mp hz 1
  have hp0 : x 0-z 0 ∈ Finset.Icc (-(r:ℤ)) r := Finset.mem_Icc.mpr (abs_le.mp h0)
  have hp1 : x 1-z 1 ∈ Finset.Icc (-(r:ℤ)) r := Finset.mem_Icc.mpr (abs_le.mp h1)
  have ext0 : ![x 0, x 1] = x := by funext i; fin_cases i <;> rfl
  have hside : x 0 = R ∨ x 0 = -R ∨ x 1 = R ∨ x 1 = -R := by
    dsimp [radius] at hx
    simp only [abs_eq_max_neg] at hx
    omega
  simp only [sideWindow, Finset.mem_union, Finset.mem_image]
  rcases hside with hx0 | hx0 | hx1 | hx1
  · exact Or.inl (Or.inl (Or.inl ⟨x 1-z 1, hp1, by simpa [hx0] using ext0⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨x 1-z 1, hp1, by simpa [hx0] using ext0⟩))
  · exact Or.inl (Or.inr ⟨x 0-z 0, hp0, by simpa [hx1] using ext0⟩)
  · exact Or.inr ⟨x 0-z 0, hp0, by simpa [hx1] using ext0⟩

theorem card_sideWindow (R : ℤ) (z : Point) (r : ℕ) :
    (sideWindow R z r).card ≤ 4 * (2*r+1) := by
  have hc : (Finset.Icc (-(r:ℤ)) r).card = 2*r+1 := by
    rw [Int.card_Icc]; omega
  unfold sideWindow
  calc
    _ ≤ (((Finset.Icc (-(r:ℤ)) r).image (fun v => ![R, z 1+v])).card +
      ((Finset.Icc (-(r:ℤ)) r).image (fun v => ![-R, z 1+v])).card) +
      ((Finset.Icc (-(r:ℤ)) r).image (fun v => ![z 0+v, R])).card +
      ((Finset.Icc (-(r:ℤ)) r).image (fun v => ![z 0+v, -R])).card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _)
    _ ≤ (2*r+1) + (2*r+1) + (2*r+1) + (2*r+1) := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        ((Finset.card_image_le).trans hc.le) ((Finset.card_image_le).trans hc.le))
        ((Finset.card_image_le).trans hc.le)) ((Finset.card_image_le).trans hc.le)
    _ = _ := by omega

theorem card_circuit_window (S : Finset Point) (R : ℤ) (z : Point) (r : ℕ)
    (hS : ∀ x ∈ S, radius x = R ∧ linf x z ≤ r) :
    S.card ≤ 4*(2*r+1) :=
  (Finset.card_le_card (fun x hx => mem_sideWindow (hS x hx).1 (hS x hx).2)).trans
    (card_sideWindow R z r)


/-- A finite nonempty target has the literal lattice graph distance. -/
noncomputable def targetDistance (S : Finset Point) (hS : S.Nonempty) (x : Point) : ℕ :=
  S.inf' hS (fun p => (lattice 2).dist x p)

theorem targetDistance_le (S : Finset Point) (hS : S.Nonempty) (x p : Point)
    (hp : p ∈ S) : targetDistance S hS x ≤ (lattice 2).dist x p :=
  Finset.inf'_le _ hp

theorem targetDistance_attained (S : Finset Point) (hS : S.Nonempty) (x : Point) :
    ∃ p ∈ S, targetDistance S hS x = (lattice 2).dist x p :=
  Finset.exists_mem_eq_inf' hS _

theorem targetDistance_zero_iff (S : Finset Point) (hS : S.Nonempty) (x : Point) :
    targetDistance S hS x = 0 ↔ x ∈ S := by
  constructor
  · intro hz
    obtain ⟨p, hp, he⟩ := targetDistance_attained S hS x
    have hx : x = p := (LatticeProb.Graph.Zd.latticeConnected 2).dist_eq_zero_iff.mp (he.symm.trans hz)
    simpa only [hx] using hp
  · intro hx
    exact Nat.eq_zero_of_le_zero (by simpa using targetDistance_le S hS x x hx)

theorem targetDistance_neighbor (S : Finset Point) (hS : S.Nonempty) {x y : Point}
    (hxy : (lattice 2).Adj x y) :
    targetDistance S hS x ≤ targetDistance S hS y + 1 := by
  obtain ⟨p, hp, he⟩ := targetDistance_attained S hS y
  have ht := (LatticeProb.Graph.Zd.latticeConnected 2).dist_triangle (u:=x) (v:=y) (w:=p)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxy, ← he] at ht
  exact (targetDistance_le S hS x p hp).trans (by omega)

theorem radius_sub_neighbor {x y : Point} (hxy : (lattice 2).Adj x y) :
    radius (x-y) = 1 := by
  rcases hxy with ⟨i, hi | hi⟩ <;> rw [hi]
  · have he : x - (x+unit i) = -unit i := by abel
    rw [he]
    fin_cases i <;> norm_num [radius, unit, Pi.single_apply]
  · have he : y + unit i - y = unit i := by abel
    rw [he]
    fin_cases i <;> norm_num [radius, unit, Pi.single_apply]

theorem linf_le_walk_length {x y : Point} (p : (lattice 2).Walk x y) :
    linf x y ≤ p.length := by
  induction p with
  | nil => simp [linf, radius]
  | @cons x y z hxy q ih =>
    have ht : radius (x-z) ≤ radius (x-y) + radius (y-z) := by
      have := radius_sub_le (x-y) (z-y)
      simpa only [sub_sub_sub_cancel_right, radius, Pi.sub_apply, abs_sub_comm] using this
    rw [radius_sub_neighbor hxy] at ht
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    dsimp [linf] at ih ⊢
    omega

theorem linf_le_dist (x y : Point) : linf x y ≤ (lattice 2).dist x y := by
  obtain ⟨p, hp⟩ := (LatticeProb.Graph.Zd.latticeConnected 2).exists_walk_length_eq_dist x y
  simpa only [hp] using linf_le_walk_length p

theorem radius_le_dist_add (x y : Point) : radius x ≤ (lattice 2).dist x y + radius y :=
  (radius_le_radius_add x y).trans (by have hh := linf_le_dist x y; dsimp [linf] at hh; omega)

/-- Positive distance to the exterior at an active vertex. -/
def depth (N : ℕ) (x : FiniteAvalanches.Sandpile.FiniteWired.Active N) : ℕ :=
  N+1 - (radius (FiniteAvalanches.Sandpile.FiniteWired.site x)).toNat

theorem depth_cast (N : ℕ) (x : FiniteAvalanches.Sandpile.FiniteWired.Active N) :
    (depth N x : ℤ) = N+1-radius (FiniteAvalanches.Sandpile.FiniteWired.site x) := by
  have hr : radius (FiniteAvalanches.Sandpile.FiniteWired.site x) ≤ N := by
    apply (radius_le_iff _ _).mpr
    intro i; exact abs_le.mpr (x i).property
  have hn := radius_nonneg (FiniteAvalanches.Sandpile.FiniteWired.site x)
  unfold depth
  omega

theorem depth_pos (N : ℕ) (x : FiniteAvalanches.Sandpile.FiniteWired.Active N) :
    0 < depth N x := by
  have hc := depth_cast N x
  have hr : radius (FiniteAvalanches.Sandpile.FiniteWired.site x) ≤ N := by
    apply (radius_le_iff _ _).mpr
    intro i; exact abs_le.mpr (x i).property
  omega

theorem depth_le (N : ℕ) (x : FiniteAvalanches.Sandpile.FiniteWired.Active N) :
    depth N x ≤ N+1 := by
  have hc := depth_cast N x
  have hn := radius_nonneg (FiniteAvalanches.Sandpile.FiniteWired.site x)
  omega

theorem depth_neighbor (N : ℕ) (x y : FiniteAvalanches.Sandpile.FiniteWired.Active N)
    (hxy : (lattice 2).Adj (FiniteAvalanches.Sandpile.FiniteWired.site x)
      (FiniteAvalanches.Sandpile.FiniteWired.site y)) : depth N x ≤ depth N y + 1 := by
  have hx := depth_cast N x
  have hy := depth_cast N y
  have hr := radius_le_radius_add (FiniteAvalanches.Sandpile.FiniteWired.site y)
    (FiniteAvalanches.Sandpile.FiniteWired.site x)
  rw [radius_sub_neighbor hxy.symm] at hr
  omega


open FiniteAvalanches.Sandpile.FiniteWired

noncomputable def boxPoints (h : ℕ) : Finset Point := Finset.univ.image (@site h)

theorem mem_boxPoints (h : ℕ) (x : Point) : x ∈ boxPoints h ↔ x ∈ box 2 h := by
  simp only [boxPoints, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, rfl⟩
    exact (inBox_iff h _).mp (fun i => (y i).property)
  · intro hx
    exact ⟨activeOfSite h x ((inBox_iff h x).mpr hx), rfl⟩

/-- The literal union of the central square and all vertices of the path. -/
noncomputable def target (h L : ℕ) (p : Fin (L+1) → Point) : Finset Point :=
  boxPoints h ∪ Finset.univ.image p

theorem target_nonempty (h L : ℕ) (p : Fin (L+1) → Point) : (target h L p).Nonempty := by
  refine ⟨p ⟨0, by omega⟩, Finset.mem_union_right _ ?_⟩
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem linf_comm (x y : Point) : linf x y = linf y x := by
  simp only [linf, radius, Pi.sub_apply, abs_sub_comm]

theorem linf_triangle (x y z : Point) : linf x z ≤ linf x y + linf y z := by
  have h := radius_sub_le (x-y) (z-y)
  simpa only [linf, sub_sub_sub_cancel_right, radius, Pi.sub_apply, abs_sub_comm] using h

/-- Small-depth points close to the needle are in a small boundary window. -/
theorem near_target_window (h L s : ℕ) (p : Fin (L+1) → Point) (z x : Point)
    (hs : 2*s+1 < h) (hx : radius x = 2*h+1-s)
    (hn : targetDistance (target h L p) (target_nonempty h L p) x ≤ s+2)
    (hp : ∀ t, linf z (p t) ≤ 2*h-radius (p t)+1) :
    linf x z ≤ 3*s+4 := by
  obtain ⟨q, hq, hd⟩ := targetDistance_attained (target h L p) (target_nonempty h L p) x
  have hdist : (lattice 2).dist x q ≤ s+2 := by omega
  have hr := radius_le_dist_add x q
  have hclose := linf_le_dist x q
  rcases Finset.mem_union.mp hq with hb | hpath
  · have hqbox : radius q ≤ h := (mem_box_iff q h).mp ((mem_boxPoints h q).mp hb)
    omega
  · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hpath
    have hrad := hp t
    have htri := linf_triangle x (p t) z
    rw [linf_comm (p t) z] at htri
    omega

/-- Active vertices of one depth whose graph distance to the target is at most `s+2`. -/
noncomputable def nearLayer (h L s : ℕ) (p : Fin (L+1) → Point) : Finset (Active (2*h)) :=
  Finset.univ.filter (fun x => depth (2*h) x = s ∧
    targetDistance (target h L p) (target_nonempty h L p) (site x) ≤ s+2)

theorem card_nearLayer (h L s : ℕ) (p : Fin (L+1) → Point) (z : Point)
    (hs : 1 ≤ s) (hsh : s ≤ 2*h+1)
    (hp : ∀ t, linf z (p t) ≤ 2*h-radius (p t)+1) :
    (nearLayer h L s p).card ≤ 60*s := by
  let S := (nearLayer h L s p).image site
  have hc : S.card = (nearLayer h L s p).card :=
    Finset.card_image_of_injective _ (site_injective _)
  have hrad (x : Point) (hx : x ∈ S) : radius x = 2*h+1-s := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hd := (Finset.mem_filter.mp hy).2.1
    have he := depth_cast (2*h) y
    push_cast at he
    omega
  by_cases hsmall : h ≤ 2*s+1
  · have hrnonneg : 0 ≤ (2*h+1-s : ℤ) := by omega
    have hrnat : ((2*h+1-s : ℤ).toNat : ℤ) = 2*h+1-s := Int.toNat_of_nonneg hrnonneg
    have hwindow : ∀ x ∈ S, radius x = (2*h+1-s : ℤ) ∧
        linf x 0 ≤ (2*h+1-s : ℤ).toNat := by
      intro x hx
      refine ⟨hrad x hx, ?_⟩
      simpa only [linf, sub_zero, hrad x hx, hrnat] using (le_refl (2*h+1-s : ℤ))
    have hb := card_circuit_window S (2*h+1-s : ℤ) 0 (2*h+1-s : ℤ).toNat hwindow
    rw [hc] at hb
    omega
  · have hwindow : ∀ x ∈ S, radius x = (2*h+1-s : ℤ) ∧ linf x z ≤ 3*s+4 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hyn := (Finset.mem_filter.mp hy).2.2
      have hyr := hrad (site y) (Finset.mem_image_of_mem _ hy)
      exact ⟨hyr, near_target_window h L s p z (site y) (by omega) hyr hyn hp⟩
    have hb := card_circuit_window S (2*h+1-s : ℤ) z (3*s+4) (by
      intro x hx; obtain ⟨hr, hw⟩ := hwindow x hx
      exact ⟨hr, by exact_mod_cast hw⟩)
    rw [hc] at hb
    omega


end FiniteAvalanches.Needle
