import FiniteAvalanches.Walk.Beurling.LastExit
import FiniteAvalanches.Walk.Beurling.DiskGreenLower
import FiniteAvalanches.Walk.Beurling.DenseSum

/-!
# Hitting a dense set in a disk

For a dense set in the plane, a walk started inside the disk of radius `3n/4` has a
uniformly positive probability of hitting the part of the set between radii `n/4` and
`n/2` before leaving the disk of radius `n` (Lawler and Limic, 2004, Lemma 7).
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

private theorem green_symm (r : ℝ) (x y : Site 2) : green r x y = green r y x := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (diskFinset r)
  rw [green, green, Network.killedGreenReal_symm (Graph.Zd.latticeConnected 2) _ hq x y]

private theorem green_nonneg (r : ℝ) (x y : Site 2) : 0 ≤ green r x y := by
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset (diskFinset r)
  exact mul_nonneg (by norm_num)
    (Network.killedGreenReal_nonneg (Graph.Zd.latticeConnected 2) (diskFinset r) hq x y)

private theorem prob_nonneg (E : Set (ℕ → Dir 2)) : 0 ≤ prob E := ENNReal.toReal_nonneg

private theorem prob_hit_self (r : ℝ) (B : Finset (Site 2)) (x : Site 2)
    (hx : x ∈ B) (hr : euclidNorm x < r) : prob (hitsBefore B r x) = 1 := by
  have h : hitsBefore B r x = Set.univ := by
    ext ω
    simp only [Set.mem_univ, iff_true]
    refine ⟨0, ?_, ?_⟩
    · simpa [walkPos] using hx
    · intro s hs
      have : s = 0 := by omega
      subst s
      simpa [walkPos] using hr
  rw [h, prob, measure_univ, ENNReal.toReal_one]

private theorem card_le_mul_sum_escape (r : ℝ) (B : Finset (Site 2)) (K : ℝ)
    (hB : ∀ x ∈ B, euclidNorm x < r)
    (hK : ∀ x ∈ B, (∑ y ∈ B, green r y x) ≤ K) :
    (B.card : ℝ) ≤ K * ∑ x ∈ B, prob (exitsBefore r B x) := by
  classical
  calc
    (B.card : ℝ) = ∑ y ∈ B, ∑ x ∈ B, green r y x * prob (exitsBefore r B x) := by
      symm
      calc
        (∑ y ∈ B, ∑ x ∈ B, green r y x * prob (exitsBefore r B x)) =
            ∑ y ∈ B, prob (hitsBefore B r y) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact (hitsBefore_eq_sum_green_mul r B hB y).symm
        _ = ∑ _ ∈ B, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact prob_hit_self r B y hy (hB y hy)
        _ = (B.card : ℝ) := by simp
    _ = ∑ x ∈ B, (∑ y ∈ B, green r y x) * prob (exitsBefore r B x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ B, K * prob (exitsBefore r B x) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_right (hK x hx) (prob_nonneg _)
    _ = K * ∑ x ∈ B, prob (exitsBefore r B x) := by rw [Finset.mul_sum]

private theorem card_mul_le_hit (r : ℝ) (B : Finset (Site 2)) (z : Site 2) (a K : ℝ)
    (ha : 0 ≤ a) (hK : 0 ≤ K) (hB : ∀ x ∈ B, euclidNorm x < r)
    (hupper : ∀ x ∈ B, (∑ y ∈ B, green r y x) ≤ K)
    (hlower : ∀ x ∈ B, a ≤ green r z x) :
    a * B.card ≤ K * prob (hitsBefore B r z) := by
  have hcard := card_le_mul_sum_escape r B K hB hupper
  have hhit : a * (∑ x ∈ B, prob (exitsBefore r B x)) ≤ prob (hitsBefore B r z) := by
    rw [hitsBefore_eq_sum_green_mul r B hB z, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_right (hlower x hx) (prob_nonneg _)
  calc
    a * B.card ≤ a * (K * ∑ x ∈ B, prob (exitsBefore r B x)) :=
      mul_le_mul_of_nonneg_left hcard ha
    _ = K * (a * ∑ x ∈ B, prob (exitsBefore r B x)) := by ring
    _ ≤ K * prob (hitsBefore B r z) := mul_le_mul_of_nonneg_left hhit hK

/-- **Lawler and Limic (2004), Lemma 7.** A dense set is hit with uniformly positive
probability in the annulus before the walk exits the larger disk. -/
theorem hit_shellPart_lower : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Set (Site 2), IsDense A → ∀ z : Site 2,
      euclidNorm z < 3 * n / 4 → c ≤ prob (hitsBefore (shellPart A (n / 4) (n / 2)) n z) := by
  classical
  obtain ⟨a, ha, N₀, haGreen⟩ := green_lower (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨C₀, hC₀⟩ := sum_green_minimal_le
  let C := max C₀ 1
  have hC : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨a / (8 * C), by positivity, max N₀ 16, ?_⟩
  intro n hn A hA z hz
  have hn₀ : N₀ ≤ n := le_of_max_le_left hn
  have hn16 : 16 ≤ n := le_of_max_le_right hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨w, hwA, hw⟩ := hA.exists_minimal
  have hinj : Function.Injective w := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h := (hw j).1
      rw [← hij] at h
      have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      linarith [(hw i).2]
    · have h := (hw i).1
      rw [hij] at h
      have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      linarith [(hw j).2]
  let I : Finset ℕ := Finset.Ico ((n + 3) / 4) (n / 2)
  let B : Finset (Site 2) := I.image w
  have hI : I ⊆ Finset.range n := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    exact Finset.mem_range.mpr (by omega)
  have hloc : ∀ x ∈ B, x ∈ shellPart A (n / 4) (n / 2) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hj' := Finset.mem_Ico.mp hj
    have hl : n ≤ 4 * j := by omega
    have hr : 2 * (j + 1) ≤ n := by omega
    have hl' : (n : ℝ) ≤ 4 * (j : ℝ) := by exact_mod_cast hl
    have hr' : (2 : ℝ) * ((j : ℝ) + 1) ≤ n := by exact_mod_cast hr
    exact ⟨hwA j, by linarith [(hw j).1], by linarith [(hw j).2]⟩
  have hB : ∀ x ∈ B, euclidNorm x < (n : ℝ) := by
    intro x hx
    have h := (hloc x hx).2.2
    linarith
  have hcardnat : n ≤ 8 * B.card := by
    have hi : n ≤ 8 * I.card := by
      dsimp [I]
      rw [Nat.card_Ico]
      omega
    simpa [B, Finset.card_image_of_injective I hinj] using hi
  have hcard : (n : ℝ) ≤ 8 * (B.card : ℝ) := by exact_mod_cast hcardnat
  have hupper : ∀ x ∈ B, (∑ y ∈ B, green n y x) ≤ C * n := by
    intro x hx
    have hsum : (∑ j ∈ I, green n x (w j)) ≤ ∑ j ∈ Finset.range n, green n x (w j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hI (fun j _ _ => green_nonneg _ _ _)
    have hsum' := hC₀ n (by omega) w hw x (hB x hx)
    calc
      (∑ y ∈ B, green n y x) = ∑ j ∈ I, green n x (w j) := by
        change (∑ y ∈ I.image w, green n y x) = _
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro j hj
          exact green_symm _ _ _
        · intro i hi j hj h
          exact hinj h
      _ ≤ ∑ j ∈ Finset.range n, green n x (w j) := hsum
      _ ≤ C₀ * n := hsum'
      _ ≤ C * n := mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hnpos)
  have hlower : ∀ x ∈ B, a ≤ green n z x := by
    intro x hx
    apply haGreen n hn₀ z x (by linarith)
    have h := (hloc x hx).2.2
    linarith
  have hkey := card_mul_le_hit n B z a (C * n) ha.le (mul_nonneg hC.le hnpos.le)
    hB hupper hlower
  have hmono : prob (hitsBefore B n z) ≤
      prob (hitsBefore (shellPart A (n / 4) (n / 2)) n z) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    rintro ω ⟨t, ht, hs⟩
    exact ⟨t, hloc _ ht, hs⟩
  have hfinal : a / (8 * C) ≤ prob (hitsBefore B n z) := by
    have h8C : 0 < 8 * C := by positivity
    apply (div_le_iff₀ h8C).2
    have hscaled := mul_le_mul_of_nonneg_left hcard ha.le
    have hh : a * (n : ℝ) ≤ (8 * C * prob (hitsBefore B n z)) * n := by
      nlinarith [hscaled, hkey]
    have hh' := le_of_mul_le_mul_right hh hnpos
    nlinarith [hh']
  exact hfinal.trans hmono

end FiniteAvalanches.Walk.Beurling
