import FiniteAvalanches.Support.Plane.OuterRedrawing.OneSide

/-!
# All edge ends at interior path vertices lie on one side

For a selection of edges containing a stretch of a straight boundary path, with
no loop at an interior vertex of the stretch and with every interior vertex
non-separating for the endpoints of the selected edges, the other selected edges
leave all interior vertices of the stretch on one common side of the line.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric Bornology
open FiniteAvalanches.Electrical.Source (drawingTrace)
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
variable {D : Drawing J} {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

/-- An arc leaving an interior path vertex upwards blocks an upper collar at it. -/
theorem blocked_upper {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U) {a : ℕ} (ha0 : 0 < a) (ham : a < m)
    (A : Finset E) (hA : ∀ e ∈ A, J.left e ≠ path ⟨a, by omega⟩ ∧ J.right e ≠ path ⟨a, by omega⟩)
    {e : E} (he : e ∉ range copies) {w : V} (hwa : w ≠ path ⟨a, by omega⟩)
    (hends : (J.left e = path ⟨a, by omega⟩ ∧ J.right e = w) ∨
      (J.right e = path ⟨a, by omega⟩ ∧ J.left e = w))
    (hreach : ∃ x ∈ range path, J.reaches A w x)
    (γ₀ : Path (D.point (path ⟨a, by omega⟩)) (D.point w)) (hγ₀inj : Function.Injective γ₀)
    (hγ₀range : range γ₀ = range (D.curve e))
    (hup : ∃ τ₀ > 0, ∀ s : unitInterval, 0 < (s : ℝ) → (s : ℝ) < τ₀ → 0 < (γ₀ s).2) :
    ¬ upperCollar D copies ⟨a, ham⟩ ⊆ U ∨ ¬ upperCollar D copies ⟨a - 1, by omega⟩ ⊆ U := by
  obtain ⟨c, hca, β, hβ, hβtrace, hβseg, hβγ⟩ :=
    exists_arc_to_path_vertex h A hA he hwa hends hreach γ₀ hγ₀inj hγ₀range
  obtain ⟨τ₀, hτ₀, hτup⟩ := hup
  obtain ⟨τ, hτ, hτβ⟩ := hβγ τ₀ hτ₀
  have hβup : ∃ τ > 0, ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < τ → 0 < (β t).2 := by
    refine ⟨τ, hτ, fun t ht0 htτ => ?_⟩
    obtain ⟨s, hs0, hsτ, hst⟩ := hτβ t ht0 htτ
    rw [hst]
    exact hτup s hs0 hsτ
  have hcne : (c : ℕ) ≠ a := fun hc => hca (Fin.ext hc)
  rcases lt_or_gt_of_ne hcne with hlt | hgt
  · exact Or.inr (h.not_upperCollar_of_up_left hU hfront ha0 ham hlt β hβ hβtrace hβseg hβup)
  · exact Or.inl (h.not_upperCollar_of_up_right hU hfront ha0 ham hgt β hβ hβtrace hβseg hβup)

/-- An arc leaving an interior path vertex downwards blocks a lower collar at it. -/
theorem blocked_lower {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U) {a : ℕ} (ha0 : 0 < a) (ham : a < m)
    (A : Finset E) (hA : ∀ e ∈ A, J.left e ≠ path ⟨a, by omega⟩ ∧ J.right e ≠ path ⟨a, by omega⟩)
    {e : E} (he : e ∉ range copies) {w : V} (hwa : w ≠ path ⟨a, by omega⟩)
    (hends : (J.left e = path ⟨a, by omega⟩ ∧ J.right e = w) ∨
      (J.right e = path ⟨a, by omega⟩ ∧ J.left e = w))
    (hreach : ∃ x ∈ range path, J.reaches A w x)
    (γ₀ : Path (D.point (path ⟨a, by omega⟩)) (D.point w)) (hγ₀inj : Function.Injective γ₀)
    (hγ₀range : range γ₀ = range (D.curve e))
    (hdown : ∃ τ₀ > 0, ∀ s : unitInterval, 0 < (s : ℝ) → (s : ℝ) < τ₀ → (γ₀ s).2 < 0) :
    ¬ lowerCollar D copies ⟨a, ham⟩ ⊆ U ∨ ¬ lowerCollar D copies ⟨a - 1, by omega⟩ ⊆ U := by
  obtain ⟨c, hca, β, hβ, hβtrace, hβseg, hβγ⟩ :=
    exists_arc_to_path_vertex h A hA he hwa hends hreach γ₀ hγ₀inj hγ₀range
  obtain ⟨τ₀, hτ₀, hτdown⟩ := hdown
  obtain ⟨τ, hτ, hτβ⟩ := hβγ τ₀ hτ₀
  have hβdown : ∃ τ > 0, ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < τ → (β t).2 < 0 := by
    refine ⟨τ, hτ, fun t ht0 htτ => ?_⟩
    obtain ⟨s, hs0, hsτ, hst⟩ := hτβ t ht0 htτ
    rw [hst]
    exact hτdown s hs0 hsτ
  have hcne : (c : ℕ) ≠ a := fun hc => hca (Fin.ext hc)
  rcases lt_or_gt_of_ne hcne with hlt | hgt
  · exact Or.inr (h.not_lowerCollar_of_down_left hU hfront ha0 ham hlt β hβ hβtrace hβseg hβdown)
  · exact Or.inl (h.not_lowerCollar_of_down_right hU hfront ha0 ham hgt β hβ hβtrace hβseg hβdown)

end StraightPath

/-- Between an index without property `P` and an index without property `Q`,
where every index has one of the properties, the properties switch at a
consecutive pair. -/
theorem exists_switch {P Q : ℕ → Prop} {p q : ℕ} (hPQ : ∀ i, p ≤ i → i < q → P i ∨ Q i)
    {i j : ℕ} (hi : p ≤ i ∧ i < q) (hj : p ≤ j ∧ j < q) (hPi : ¬ P i) (hQj : ¬ Q j) :
    ∃ k, p < k ∧ k < q ∧ ((P (k - 1) ∧ Q k) ∨ (Q (k - 1) ∧ P k)) := by
  have hij : i ≠ j := by
    rintro rfl
    rcases hPQ i hi.1 hi.2 with h1 | h1
    · exact hPi h1
    · exact hQj h1
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · -- from `¬ P i` up to `¬ Q j`
    have hex : ∃ l, i < l ∧ ¬ Q l := ⟨j, hlt, hQj⟩
    let l := Nat.find hex
    have hl : i < l ∧ ¬ Q l := Nat.find_spec hex
    have hlj : l ≤ j := Nat.find_min' hex ⟨hlt, hQj⟩
    refine ⟨l, by omega, by omega, Or.inr ⟨?_, ?_⟩⟩
    · rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt hl.1) with heq | hlt'
      · rw [← heq]
        exact (hPQ i hi.1 hi.2).resolve_left hPi
      · by_contra hQ
        exact Nat.find_min hex (show l - 1 < l by omega) ⟨hlt', hQ⟩
    · exact (hPQ l (by omega) (by omega)).resolve_right hl.2
  · have hex : ∃ l, j < l ∧ ¬ P l := ⟨i, hgt, hPi⟩
    let l := Nat.find hex
    have hl : j < l ∧ ¬ P l := Nat.find_spec hex
    have hli : l ≤ i := Nat.find_min' hex ⟨hgt, hPi⟩
    refine ⟨l, by omega, by omega, Or.inl ⟨?_, ?_⟩⟩
    · rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt hl.1) with heq | hlt'
      · rw [← heq]
        exact (hPQ j hj.1 hj.2).resolve_right hQj
      · by_contra hP
        exact Nat.find_min hex (show l - 1 < l by omega) ⟨hlt', hP⟩
    · exact (hPQ l (by omega) (by omega)).resolve_left hl.2

/-- All selected off-path edges leave the interior vertices of the stretch from above. -/
def EndsAbove (D : Drawing J) (path : Fin (m + 1) → V) (copies : Fin m → E) (T : Finset E)
    (p q : ℕ) : Prop :=
  ∀ e ∈ T, e ∉ range copies → ∀ a : ℕ, p < a → a < q → ∀ ham : a < m,
    (J.left e = path ⟨a, by omega⟩ → StartsAbove D e) ∧
      (J.right e = path ⟨a, by omega⟩ → FinishesAbove D e)

/-- All selected off-path edges leave the interior vertices of the stretch from below. -/
def EndsBelow (D : Drawing J) (path : Fin (m + 1) → V) (copies : Fin m → E) (T : Finset E)
    (p q : ℕ) : Prop :=
  ∀ e ∈ T, e ∉ range copies → ∀ a : ℕ, p < a → a < q → ∀ ham : a < m,
    (J.left e = path ⟨a, by omega⟩ → StartsBelow D e) ∧
      (J.right e = path ⟨a, by omega⟩ → FinishesBelow D e)

/-- The curve of an edge as a path between its endpoints. -/
def edgePath (D : Drawing J) (e : E) : Path (D.point (J.left e)) (D.point (J.right e)) where
  toFun := D.curve e
  continuous_toFun := D.continuous e
  source' := D.start e
  target' := D.finish e

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

/-- An end above an interior vertex blocks an upper collar next to it. -/
theorem blocked_upper_of_end {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U) (T : Finset E) {a : ℕ} (ha0 : 0 < a)
    (ham : a < m) {e : E} (he : e ∉ range copies)
    (hnoloop : ¬ (J.left e = path ⟨a, by omega⟩ ∧ J.right e = path ⟨a, by omega⟩))
    (hconn : ∀ x, (x = J.left e ∨ x = J.right e) → x ≠ path ⟨a, by omega⟩ →
      J.reaches (avoiding J T (path ⟨a, by omega⟩)) x (path ⟨a - 1, by omega⟩))
    (hend : (J.left e = path ⟨a, by omega⟩ ∧ StartsAbove D e) ∨
      (J.right e = path ⟨a, by omega⟩ ∧ FinishesAbove D e)) :
    ¬ upperCollar D copies ⟨a, ham⟩ ⊆ U ∨ ¬ upperCollar D copies ⟨a - 1, by omega⟩ ⊆ U := by
  have hA : ∀ e' ∈ avoiding J T (path ⟨a, by omega⟩),
      J.left e' ≠ path ⟨a, by omega⟩ ∧ J.right e' ≠ path ⟨a, by omega⟩ := by
    intro e' he'
    rw [avoiding, Finset.mem_filter] at he'
    exact he'.2
  rcases hend with ⟨hl, τ, hτ, hup⟩ | ⟨hr, τ, hτ, hup⟩
  · have hwa : J.right e ≠ path ⟨a, by omega⟩ := fun hr => hnoloop ⟨hl, hr⟩
    let γ₀ : Path (D.point (path ⟨a, by omega⟩)) (D.point (J.right e)) :=
      (edgePath D e).cast (by rw [hl]) rfl
    refine h.blocked_upper hU hfront ha0 ham _ hA he hwa (Or.inl ⟨hl, rfl⟩)
      ⟨_, ⟨_, rfl⟩, hconn _ (Or.inr rfl) hwa⟩ γ₀
      (D.nonloop_curve_injective e (by rw [hl]; exact Ne.symm hwa)) rfl ⟨τ, hτ, ?_⟩
    intro s hs0 hsτ
    exact hup s hs0 hsτ
  · have hwa : J.left e ≠ path ⟨a, by omega⟩ := fun hl => hnoloop ⟨hl, hr⟩
    let γ₀ : Path (D.point (path ⟨a, by omega⟩)) (D.point (J.left e)) :=
      ((edgePath D e).symm).cast (by rw [hr]) rfl
    have hinj : Function.Injective γ₀ := by
      intro s t hst
      have := D.nonloop_curve_injective e (by rw [hr]; exact hwa) hst
      exact unitInterval.symm_involutive.injective this
    have hrange : range γ₀ = range (D.curve e) := by
      change range (edgePath D e).symm = _
      rw [Path.symm_range]
      rfl
    refine h.blocked_upper hU hfront ha0 ham _ hA he hwa (Or.inr ⟨hr, rfl⟩)
      ⟨_, ⟨_, rfl⟩, hconn _ (Or.inl rfl) hwa⟩ γ₀ hinj hrange ⟨τ, hτ, ?_⟩
    intro s hs0 hsτ
    change 0 < (D.curve e (unitInterval.symm s)).2
    exact hup _ (by simp only [unitInterval.coe_symm_eq]; linarith)
      (by simp only [unitInterval.coe_symm_eq]; linarith)

/-- An end below an interior vertex blocks a lower collar next to it. -/
theorem blocked_lower_of_end {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U) (T : Finset E) {a : ℕ} (ha0 : 0 < a)
    (ham : a < m) {e : E} (he : e ∉ range copies)
    (hnoloop : ¬ (J.left e = path ⟨a, by omega⟩ ∧ J.right e = path ⟨a, by omega⟩))
    (hconn : ∀ x, (x = J.left e ∨ x = J.right e) → x ≠ path ⟨a, by omega⟩ →
      J.reaches (avoiding J T (path ⟨a, by omega⟩)) x (path ⟨a - 1, by omega⟩))
    (hend : (J.left e = path ⟨a, by omega⟩ ∧ StartsBelow D e) ∨
      (J.right e = path ⟨a, by omega⟩ ∧ FinishesBelow D e)) :
    ¬ lowerCollar D copies ⟨a, ham⟩ ⊆ U ∨ ¬ lowerCollar D copies ⟨a - 1, by omega⟩ ⊆ U := by
  have hA : ∀ e' ∈ avoiding J T (path ⟨a, by omega⟩),
      J.left e' ≠ path ⟨a, by omega⟩ ∧ J.right e' ≠ path ⟨a, by omega⟩ := by
    intro e' he'
    rw [avoiding, Finset.mem_filter] at he'
    exact he'.2
  rcases hend with ⟨hl, τ, hτ, hdown⟩ | ⟨hr, τ, hτ, hdown⟩
  · have hwa : J.right e ≠ path ⟨a, by omega⟩ := fun hr => hnoloop ⟨hl, hr⟩
    let γ₀ : Path (D.point (path ⟨a, by omega⟩)) (D.point (J.right e)) :=
      (edgePath D e).cast (by rw [hl]) rfl
    refine h.blocked_lower hU hfront ha0 ham _ hA he hwa (Or.inl ⟨hl, rfl⟩)
      ⟨_, ⟨_, rfl⟩, hconn _ (Or.inr rfl) hwa⟩ γ₀
      (D.nonloop_curve_injective e (by rw [hl]; exact Ne.symm hwa)) rfl ⟨τ, hτ, ?_⟩
    intro s hs0 hsτ
    exact hdown s hs0 hsτ
  · have hwa : J.left e ≠ path ⟨a, by omega⟩ := fun hl => hnoloop ⟨hl, hr⟩
    let γ₀ : Path (D.point (path ⟨a, by omega⟩)) (D.point (J.left e)) :=
      ((edgePath D e).symm).cast (by rw [hr]) rfl
    have hinj : Function.Injective γ₀ := by
      intro s t hst
      have := D.nonloop_curve_injective e (by rw [hr]; exact hwa) hst
      exact unitInterval.symm_involutive.injective this
    have hrange : range γ₀ = range (D.curve e) := by
      change range (edgePath D e).symm = _
      rw [Path.symm_range]
      rfl
    refine h.blocked_lower hU hfront ha0 ham _ hA he hwa (Or.inr ⟨hr, rfl⟩)
      ⟨_, ⟨_, rfl⟩, hconn _ (Or.inl rfl) hwa⟩ γ₀ hinj hrange ⟨τ, hτ, ?_⟩
    intro s hs0 hsτ
    change (D.curve e (unitInterval.symm s)).2 < 0
    exact hdown _ (by simp only [unitInterval.coe_symm_eq]; linarith)
      (by simp only [unitInterval.coe_symm_eq]; linarith)

/-- The selected off-path edges leave all interior vertices of the stretch on one
common side, unless some interior vertex carries a loop or separates. -/
theorem ends_one_side {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U) (T : Finset E) {p q : ℕ}
    (hqm : q ≤ m) (hcop : ∀ i : Fin m, p ≤ (i : ℕ) → (i : ℕ) < q → copies i ∈ T)
    (hnoloop : ∀ a : ℕ, p < a → ∀ haq : a < q, ∀ e ∈ T,
      ¬ (J.left e = path ⟨a, by omega⟩ ∧ J.right e = path ⟨a, by omega⟩))
    (hconn : ∀ a : ℕ, ∀ hpa : p < a, ∀ haq : a < q, ∀ e ∈ T, ∀ x, (x = J.left e ∨ x = J.right e) →
      x ≠ path ⟨a, by omega⟩ →
        J.reaches (avoiding J T (path ⟨a, by omega⟩)) x (path ⟨a - 1, by omega⟩)) :
    EndsAbove D path copies T p q ∨ EndsBelow D path copies T p q := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hnA, hnB⟩ := hcon
  simp only [EndsAbove, EndsBelow, not_forall, not_and_or] at hnA hnB
  -- an end above, from the failure of `EndsBelow`
  obtain ⟨e₁, he₁T, he₁, a₁, hpa₁, ha₁q, ham₁, hend₁⟩ := hnB
  obtain ⟨e₂, he₂T, he₂, a₂, hpa₂, ha₂q, ham₂, hend₂⟩ := hnA
  have ha₁0 : 0 < a₁ := by omega
  have ha₂0 : 0 < a₂ := by omega
  have hup₁ : (J.left e₁ = path ⟨a₁, by omega⟩ ∧ StartsAbove D e₁) ∨
      (J.right e₁ = path ⟨a₁, by omega⟩ ∧ FinishesAbove D e₁) := by
    rcases hend₁ with ⟨hl, hnot⟩ | ⟨hr, hnot⟩
    · exact Or.inl ⟨hl, (starts_above_or_below h he₁ ha₁0 ham₁ hl).resolve_right hnot⟩
    · exact Or.inr ⟨hr, (finishes_above_or_below h he₁ ha₁0 ham₁ hr).resolve_right hnot⟩
  have hdown₂ : (J.left e₂ = path ⟨a₂, by omega⟩ ∧ StartsBelow D e₂) ∨
      (J.right e₂ = path ⟨a₂, by omega⟩ ∧ FinishesBelow D e₂) := by
    rcases hend₂ with ⟨hl, hnot⟩ | ⟨hr, hnot⟩
    · exact Or.inl ⟨hl, (starts_above_or_below h he₂ ha₂0 ham₂ hl).resolve_left hnot⟩
    · exact Or.inr ⟨hr, (finishes_above_or_below h he₂ ha₂0 ham₂ hr).resolve_left hnot⟩
  have hb₁ := h.blocked_upper_of_end hU hfront T ha₁0 ham₁ he₁ (hnoloop a₁ hpa₁ ha₁q e₁ he₁T)
    (hconn a₁ hpa₁ ha₁q e₁ he₁T) hup₁
  have hb₂ := h.blocked_lower_of_end hU hfront T ha₂0 ham₂ he₂ (hnoloop a₂ hpa₂ ha₂q e₂ he₂T)
    (hconn a₂ hpa₂ ha₂q e₂ he₂T) hdown₂
  let P : ℕ → Prop := fun i => ∀ hi : i < m, upperCollar D copies ⟨i, hi⟩ ⊆ U
  let Q : ℕ → Prop := fun i => ∀ hi : i < m, lowerCollar D copies ⟨i, hi⟩ ⊆ U
  have hPQ : ∀ i, p ≤ i → i < q → P i ∨ Q i := by
    intro i _ hiq
    rcases h.upper_or_lower_of_closure hU ⟨i, by omega⟩ (hfront _) with h1 | h1
    · exact Or.inl fun _ => h1
    · exact Or.inr fun _ => h1
  have hi : ∃ i, (p ≤ i ∧ i < q) ∧ ¬ P i := by
    rcases hb₁ with h1 | h1
    · exact ⟨a₁, ⟨by omega, ha₁q⟩, fun hP => h1 (hP ham₁)⟩
    · exact ⟨a₁ - 1, ⟨by omega, by omega⟩, fun hP => h1 (hP (by omega))⟩
  have hj : ∃ j, (p ≤ j ∧ j < q) ∧ ¬ Q j := by
    rcases hb₂ with h1 | h1
    · exact ⟨a₂, ⟨by omega, ha₂q⟩, fun hQ => h1 (hQ ham₂)⟩
    · exact ⟨a₂ - 1, ⟨by omega, by omega⟩, fun hQ => h1 (hQ (by omega))⟩
  obtain ⟨i, hi, hPi⟩ := hi
  obtain ⟨j, hj, hQj⟩ := hj
  obtain ⟨k, hpk, hkq, hsw⟩ := exists_switch hPQ hi hj hPi hQj
  have hk0 : 0 < k := by omega
  have hkm : k < m := by omega
  have hA : ∀ e ∈ avoiding J T (path ⟨k, by omega⟩),
      J.left e ≠ path ⟨k, by omega⟩ ∧ J.right e ≠ path ⟨k, by omega⟩ := by
    intro e he
    rw [avoiding, Finset.mem_filter] at he
    exact he.2
  have hsides : (upperCollar D copies ⟨k - 1, by omega⟩ ⊆ U ∧
        lowerCollar D copies ⟨k, hkm⟩ ⊆ U) ∨
      (lowerCollar D copies ⟨k - 1, by omega⟩ ⊆ U ∧ upperCollar D copies ⟨k, hkm⟩ ⊆ U) := by
    rcases hsw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1 _, h2 _⟩
    · exact Or.inr ⟨h1 _, h2 _⟩
  apply h.not_reaches_of_opposite_collars hU hk0 hkm _ hA hsides
  have hcopk : copies ⟨k, hkm⟩ ∈ T := hcop _ (by simp only; omega) hkq
  have hsucc : (⟨k, hkm⟩ : Fin m).succ = (⟨k + 1, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
  have hend : path ⟨k + 1, by omega⟩ = J.left (copies ⟨k, hkm⟩) ∨
      path ⟨k + 1, by omega⟩ = J.right (copies ⟨k, hkm⟩) := by
    rcases h.ends ⟨k, hkm⟩ with ⟨_, hr⟩ | ⟨_, hl⟩
    · exact Or.inr (by rw [hr, hsucc])
    · exact Or.inl (by rw [hl, hsucc])
  have hne : path ⟨k + 1, by omega⟩ ≠ path ⟨k, by omega⟩ := by
    intro he
    have := congrArg Fin.val (h.injective he)
    simp only at this
    omega
  exact hconn k hpk hkq _ hcopk _ hend hne

end StraightPath

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
