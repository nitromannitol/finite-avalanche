import FiniteAvalanches.Wilson.Lattice.WiredBranchHorizon

/-! Horizon stability for independently driven Wilson branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- If all row-driven branches hit before `N`, increasing the horizon leaves
their complete ordered history unchanged. -/
theorem rowBranchHistory_eq_of_hits (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N M n : ℕ) (rows : ℕ → WalkDriver)
    (hNM : N ≤ M)
    (h : ∀ i < n, (rowBranchHistory head x R k N rows (i + 1)).2.1 < N) :
    rowBranchHistory head x R k M rows n = rowBranchHistory head x R k N rows n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpast : ∀ i < n, (rowBranchHistory head x R k N rows (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hs := ih hpast
    let a := rowBranchHistory head x R k N rows n
    let S := branchHistoryRoots head x R n a
    let c := branchHistoryCursor head x k n a
    have hhit : boundedWordHit head S (x n) c N (rows n) < N := h n (Nat.lt_succ_self n)
    have htime := boundedWordHit_eq_of_hit head S (x n) c N M (rows n) hNM hhit
    change (rowBranchHistory head x R k M rows n,
      stoppedDirectionHistory (boundedWordHit head
        (branchHistoryRoots head x R n (rowBranchHistory head x R k M rows n)) (x n)
        (branchHistoryCursor head x k n (rowBranchHistory head x R k M rows n)) M) (rows n)) =
      (a, stoppedDirectionHistory (boundedWordHit head S (x n) c N) (rows n))
    rw [hs]
    change (a, stoppedDirectionHistory (boundedWordHit head S (x n) c M) (rows n)) =
      (a, stoppedDirectionHistory (boundedWordHit head S (x n) c N) (rows n))
    congr 1
    change (⟨boundedWordHit head S (x n) c M (rows n), fun i => rows n i.val⟩ : DirectionHistory) =
      ⟨boundedWordHit head S (x n) c N (rows n), fun i => rows n i.val⟩
    exact congrArg (fun t : ℕ => (⟨t, fun i : Fin t => rows n i.val⟩ : DirectionHistory)) htime

/-- Every branch in a finite history ends strictly before the given horizon. -/
def BranchHistory.HitsBefore (N : ℕ) : (n : ℕ) → BranchHistory n → Prop
  | 0, _ => True
  | n + 1, h => BranchHistory.HitsBefore N n h.1 ∧ h.2.1 < N

/-- A history successful before one horizon is successful before any larger one. -/
theorem BranchHistory.HitsBefore.mono {N M n : ℕ} {h : BranchHistory n}
    (hnm : N ≤ M) (hh : BranchHistory.HitsBefore N n h) : BranchHistory.HitsBefore M n h := by
  induction n with
  | zero => trivial
  | succ n ih =>
    exact ⟨ih hh.1, lt_of_lt_of_le hh.2 hnm⟩

/-- The recursive successful-history predicate is equivalent to checking each
successive branch in a compatible family of finite histories. -/
theorem branchHistory_hitsBefore_iff (N : ℕ) (H : (n : ℕ) → BranchHistory n)
    (hprefix : ∀ n, (H (n + 1)).1 = H n) (n : ℕ) :
    BranchHistory.HitsBefore N n (H n) ↔ ∀ i < n, (H (i + 1)).2.1 < N := by
  induction n with
  | zero => simp only [BranchHistory.HitsBefore, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true]
  | succ n ih =>
    change BranchHistory.HitsBefore N n (H (n + 1)).1 ∧ (H (n + 1)).2.1 < N ↔ _
    rw [hprefix n, ih]
    constructor
    · rintro ⟨hp, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hp i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

/-- A bounded stack history is successful exactly when all its branches hit. -/
theorem boundedBranchHistory_hitsBefore_iff (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N n : ℕ)
    (σ : V × ℕ → FiniteWired.Direction) :
    BranchHistory.HitsBefore N n (boundedBranchHistory head x R k N σ n) ↔
      ∀ i < n, (boundedBranchHistory head x R k N σ (i + 1)).2.1 < N :=
  branchHistory_hitsBefore_iff N (boundedBranchHistory head x R k N σ) (fun _ => rfl) n

/-- A bounded row history is successful exactly when all its branches hit. -/
theorem rowBranchHistory_hitsBefore_iff (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (k : Cursor V) (N n : ℕ) (rows : ℕ → WalkDriver) :
    BranchHistory.HitsBefore N n (rowBranchHistory head x R k N rows n) ↔
      ∀ i < n, (rowBranchHistory head x R k N rows (i + 1)).2.1 < N :=
  branchHistory_hitsBefore_iff N (rowBranchHistory head x R k N rows) (fun _ => rfl) n

/-- A predicate on a countable-valued function is measurable when all of its
fibers are measurable. -/
theorem measurableSet_of_countable_fibers {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (f : Ω → α) (hf : ∀ a, MeasurableSet {ω | f ω = a}) (P : α → Prop) :
    MeasurableSet {ω | P (f ω)} := by
  have he : {ω | P (f ω)} = ⋃ a : {a : α // P a}, {ω | f ω = a.val} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨⟨f ω, h⟩, rfl⟩
    · rintro ⟨a, ha⟩
      rw [ha]
      exact a.property
  rw [he]
  exact MeasurableSet.iUnion (fun a => hf a.val)

/-- Independently driven wired Wilson branches also admit a finite common
horizon almost surely. -/
theorem wilsonRows_wired_ae_finite_branch_horizon (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ N,
      ∀ i < n, (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows (i + 1)).2.1 < N := by
  let V := FiniteWired.Vertex B
  let E : ℕ → Set (V × ℕ → FiniteWired.Direction) := fun N =>
    {σ | BranchHistory.HitsBefore N n
      (boundedBranchHistory (wiredHead B) x (wiredRoots R B).val k N σ n)}
  let F : ℕ → Set (ℕ → WalkDriver) := fun N =>
    {rows | BranchHistory.HitsBefore N n
      (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n)}
  have hE : ∀ N, MeasurableSet (E N) := fun N => measurableSet_of_countable_fibers
    (fun σ => boundedBranchHistory (wiredHead B) x (wiredRoots R B).val k N σ n)
    (measurableSet_boundedBranchHistory_eq (wiredHead B) x (wiredRoots R B).val k N n)
    (BranchHistory.HitsBefore N n)
  have hF : ∀ N, MeasurableSet (F N) := fun N => measurableSet_of_countable_fibers
    (fun rows => rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n)
    (fun a => measurableSet_rowBranchHistory_eq (wiredHead B) x (wiredRoots R B).val k N n
      (fun i (rows : ℕ → WalkDriver) => rows i) (fun i => measurable_pi_apply i) a)
    (BranchHistory.HitsBefore N n)
  have hmE : Monotone E := by
    intro N M hNM σ hσ
    have hhit := (boundedBranchHistory_hitsBefore_iff (wiredHead B) x (wiredRoots R B).val k N n σ).mp hσ
    change BranchHistory.HitsBefore M n
      (boundedBranchHistory (wiredHead B) x (wiredRoots R B).val k M σ n)
    rw [boundedBranchHistory_eq_of_hits (wiredHead B) x (wiredRoots R B).val k N M n σ hNM hhit]
    exact BranchHistory.HitsBefore.mono hNM hσ
  have hmF : Monotone F := by
    intro N M hNM rows hrows
    have hhit := (rowBranchHistory_hitsBefore_iff (wiredHead B) x (wiredRoots R B).val k N n rows).mp hrows
    change BranchHistory.HitsBefore M n
      (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k M rows n)
    rw [rowBranchHistory_eq_of_hits (wiredHead B) x (wiredRoots R B).val k N M n rows hNM hhit]
    exact BranchHistory.HitsBefore.mono hNM hrows
  have hmass : ∀ N, directionStackLaw V (E N) = wilsonRows (F N) := fun N =>
    directionStackLaw_branchHistory_event_eq_wilsonRows (wiredHead B) x (wiredRoots R B).val k N n
      (BranchHistory.HitsBefore N n)
  have hae : ∀ᵐ σ ∂directionStackLaw V, σ ∈ ⋃ N, E N := by
    filter_upwards [wiredStack_ae_finite_branch_horizon R B x k n] with σ hσ
    obtain ⟨N, hN⟩ := hσ
    exact Set.mem_iUnion.mpr ⟨N,
      (boundedBranchHistory_hitsBefore_iff (wiredHead B) x (wiredRoots R B).val k N n σ).mpr hN⟩
  have hone : directionStackLaw V (⋃ N, E N) = 1 :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hE)).mp hae
  have hrow : wilsonRows (⋃ N, F N) = 1 := by
    calc
      wilsonRows (⋃ N, F N) = ⨆ N, wilsonRows (F N) := hmF.measure_iUnion
      _ = ⨆ N, directionStackLaw V (E N) := iSup_congr fun N => (hmass N).symm
      _ = directionStackLaw V (⋃ N, E N) := hmE.measure_iUnion.symm
      _ = 1 := hone
  have hrowae : ∀ᵐ rows ∂wilsonRows, rows ∈ ⋃ N, F N :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hF)).mpr hrow
  filter_upwards [hrowae] with rows hrows
  obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hrows
  exact ⟨N, (rowBranchHistory_hitsBefore_iff (wiredHead B) x (wiredRoots R B).val k N n rows).mp hN⟩

/-- Removing the horizon preserves equality in law for every event of a
completed finite branch history. -/
theorem directionStackLaw_completedBranchHistory_eq_wilsonRows [Fintype V]
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R : Set V)
    (k : Cursor V) (n : ℕ) (P : BranchHistory n → Prop) :
    directionStackLaw V {σ | ∃ N,
      BranchHistory.HitsBefore N n (boundedBranchHistory head x R k N σ n) ∧
        P (boundedBranchHistory head x R k N σ n)} =
    wilsonRows {rows | ∃ N,
      BranchHistory.HitsBefore N n (rowBranchHistory head x R k N rows n) ∧
        P (rowBranchHistory head x R k N rows n)} := by
  let E : ℕ → Set (V × ℕ → FiniteWired.Direction) := fun N =>
    {σ | BranchHistory.HitsBefore N n (boundedBranchHistory head x R k N σ n) ∧
      P (boundedBranchHistory head x R k N σ n)}
  let F : ℕ → Set (ℕ → WalkDriver) := fun N =>
    {rows | BranchHistory.HitsBefore N n (rowBranchHistory head x R k N rows n) ∧
      P (rowBranchHistory head x R k N rows n)}
  have hmE : Monotone E := by
    intro N M hNM σ ⟨hgood, hp⟩
    have hhit := (boundedBranchHistory_hitsBefore_iff head x R k N n σ).mp hgood
    have he := boundedBranchHistory_eq_of_hits head x R k N M n σ hNM hhit
    change BranchHistory.HitsBefore M n (boundedBranchHistory head x R k M σ n) ∧
      P (boundedBranchHistory head x R k M σ n)
    rw [he]
    exact ⟨BranchHistory.HitsBefore.mono hNM hgood, hp⟩
  have hmF : Monotone F := by
    intro N M hNM rows ⟨hgood, hp⟩
    have hhit := (rowBranchHistory_hitsBefore_iff head x R k N n rows).mp hgood
    have he := rowBranchHistory_eq_of_hits head x R k N M n rows hNM hhit
    change BranchHistory.HitsBefore M n (rowBranchHistory head x R k M rows n) ∧
      P (rowBranchHistory head x R k M rows n)
    rw [he]
    exact ⟨BranchHistory.HitsBefore.mono hNM hgood, hp⟩
  have hmass : ∀ N, directionStackLaw V (E N) = wilsonRows (F N) := fun N =>
    directionStackLaw_branchHistory_event_eq_wilsonRows head x R k N n
      (fun a => BranchHistory.HitsBefore N n a ∧ P a)
  have he : {σ | ∃ N,
      BranchHistory.HitsBefore N n (boundedBranchHistory head x R k N σ n) ∧
        P (boundedBranchHistory head x R k N σ n)} = ⋃ N, E N := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
  have hf : {rows | ∃ N,
      BranchHistory.HitsBefore N n (rowBranchHistory head x R k N rows n) ∧
        P (rowBranchHistory head x R k N rows n)} = ⋃ N, F N := by
    ext rows
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, F]
  rw [he, hf]
  calc
    directionStackLaw V (⋃ N, E N) = ⨆ N, directionStackLaw V (E N) := hmE.measure_iUnion
    _ = ⨆ N, wilsonRows (F N) := iSup_congr hmass
    _ = wilsonRows (⋃ N, F N) := hmF.measure_iUnion.symm

end
end FiniteAvalanches.Wilson.Lattice
