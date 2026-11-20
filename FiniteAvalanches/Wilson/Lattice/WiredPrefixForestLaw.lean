import FiniteAvalanches.Wilson.Lattice.RowWiredForestLaw
import FiniteAvalanches.Wilson.Lattice.HistorySelected

/-! Forest events determined by finite prefixes of wired Wilson exploration. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A forest event is determined by the selected nonroot directions on a
specified vertex set. -/
def WiredForestDeterminedBy (R : RootPair) (B : ℕ)
    (S : Set (FiniteForest R B)) (U : Set (FiniteWired.Vertex B)) : Prop :=
  ∀ a b : GoodArrows (wiredRoots R B).val (wiredHead B),
    (∀ v ∈ U, v ∉ (wiredRoots R B).val → a.val v = b.val v) →
      (wiredArrowForest R B a ∈ S ↔ wiredArrowForest R B b ∈ S)

/-- A terminal output realizes every retained branch of a successful finite
prefix, even when the prefix does not cover the whole graph. -/
theorem wiredTerminal_realizes_branchHistory (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (k t : Cursor (FiniteWired.Vertex B))
    (N n : ℕ) (σ : FiniteWired.Vertex B × ℕ → FiniteWired.Direction)
    (hrun : Relation.ReflTransGen
      (pop_step (wiredRoots R B).val (wiredHead B) (fun v i => σ (v, i))) k t)
    (ht : terminal (wiredRoots R B).val (wiredHead B) (fun v i => σ (v, i)) t)
    (h : ∀ i < n, (boundedBranchHistory (wiredHead B) x (wiredRoots R B).val k N σ (i + 1)).2.1 < N) :
    BranchHistory.Realizes (wiredHead B) x (fun v => σ (v, t v)) n
      (boundedBranchHistory (wiredHead B) x (wiredRoots R B).val k N σ n) := by
  let a := boundedBranchHistory (wiredHead B) x (wiredRoots R B).val k N σ n
  let U := branchHistoryRoots (wiredHead B) x (wiredRoots R B).val n a
  let j := branchHistoryErasedCursor (wiredHead B) x k n a
  have hexact := (stackExplore_eq_historyErasedCursor (wiredHead B) x (wiredRoots R B).val k N n σ h).1
  obtain ⟨U', j', hexplore, _, _, _, hcontinue, _⟩ :=
    stackExplore_of_terminal (wiredRoots R B).val (wiredHead B) (fun v i => σ (v, i))
      k t hrun ht ((List.range n).map x)
  rw [hexplore, Option.some.injEq, Prod.mk.injEq] at hexact
  have heU : U' = U := hexact.1
  have hej : j' = j := hexact.2
  have hc : ∀ v ∈ U, j v = t v := by
    intro v hv
    rw [← heU] at hv
    rw [← hej]
    exact (pop_run_root_cursor U' (wiredHead B) (fun v i => σ (v, i)) hcontinue hv).symm
  have hs : BranchHistory.Selected (wiredHead B) x σ j n a :=
    branchHistory_selected_of_hits (wiredHead B) x (wiredRoots R B).val k N n σ h
  have hs' := BranchHistory.Selected.congr (wiredHead B) x (wiredRoots R B).val σ j t n a hs hc
  exact BranchHistory.Selected.top (wiredHead B) x σ n a t hs'

/-- Any finite wired exploration determines the law of every forest event
whose membership is fixed by its retained nonroot directions. -/
theorem wilsonRows_wiredForest_eq_of_prefix_determines (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (S : Set (FiniteForest R B))
    (hdet : ∀ a : BranchHistory n,
      BranchHistory.EndsInRoots (wiredHead B) x (wiredRoots R B).val n a →
      WiredForestDeterminedBy R B S
        (branchHistoryRoots (wiredHead B) x (wiredRoots R B).val n a)) :
    wilsonRows {rows | ∃ N,
      BranchHistory.HitsBefore N n
        (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n) ∧
      BranchHistory.WiredForestEvent R B x n S
        (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n)} =
      finiteUniformLaw R B S := by
  let V := FiniteWired.Vertex B
  let roots := (wiredRoots R B).val
  let head := wiredHead B
  let P := BranchHistory.WiredForestEvent R B x n S
  let E : Set (V × ℕ → FiniteWired.Direction) := {σ | ∃ N,
    BranchHistory.HitsBefore N n (boundedBranchHistory head x roots k N σ n) ∧
      P (boundedBranchHistory head x roots k N σ n)}
  let F : Set (V × ℕ → FiniteWired.Direction) := {σ |
    ∃ a : GoodArrows roots head, wiredArrowForest R B a ∈ S ∧
      σ ∈ terminalOutputEvent roots head k (fun v i σ => σ (v, i)) a}
  have hae : ∀ᵐ σ ∂directionStackLaw V, σ ∈ E ↔ σ ∈ F := by
    filter_upwards [wiredStack_ae_terminates R B k] with σ hterm
    obtain ⟨t, hrun, ht⟩ := hterm
    let z : GoodArrows roots head := ⟨fun v => σ (v, t v), ht⟩
    constructor
    · rintro ⟨N, hN, a, ha, hS⟩
      have hh := (boundedBranchHistory_hitsBefore_iff head x roots k N n σ).mp hN
      let b := boundedBranchHistory head x roots k N σ n
      have hb : BranchHistory.Realizes head x z.val n b :=
        wiredTerminal_realizes_branchHistory R B x k t N n σ hrun ht hh
      have hend := branchHistory_endsInRoots_of_hits head x roots k N n σ hh
      have heq : ∀ v ∈ branchHistoryRoots head x roots n b, v ∉ roots → a.val v = z.val v := by
        intro v hv hvR
        exact BranchHistory.Realizes.eq_of_mem_roots head x roots n b a.val z.val hend ha hb hv hvR
      have hzS : wiredArrowForest R B z ∈ S := (hdet b hend a z heq).mp hS
      exact ⟨z, hzS, t, hrun, fun _ => rfl⟩
    · rintro ⟨a, hS, u, hrun', htop⟩
      have htu : terminal roots head (fun v i => σ (v, i)) u :=
        terminal_of_top_eq roots head (fun v i => σ (v, i)) u a.val a.property htop
      have hut : u = t := terminal_cursor_eq roots head (fun v i => σ (v, i)) hrun' hrun htu ht
      have haz : a = z := by
        apply Subtype.ext
        funext v
        exact (htop v).symm.trans (congrArg (fun q => σ (v, q v)) hut)
      have hzS : wiredArrowForest R B z ∈ S := by simpa only [haz] using hS
      obtain ⟨U, j, hexplore, _⟩ := stackExplore_of_terminal roots head
        (fun v i => σ (v, i)) k t hrun ht ((List.range n).map x)
      obtain ⟨N, hh⟩ := exists_horizon_of_stackExplore head x roots k n σ U j hexplore
      refine ⟨N, (boundedBranchHistory_hitsBefore_iff head x roots k N n σ).mpr hh, ?_⟩
      exact ⟨z, wiredTerminal_realizes_branchHistory R B x k t N n σ hrun ht hh, hzS⟩
  calc
    wilsonRows {rows | ∃ N, BranchHistory.HitsBefore N n
        (rowBranchHistory head x roots k N rows n) ∧
      P (rowBranchHistory head x roots k N rows n)} = directionStackLaw V E :=
      (directionStackLaw_completedBranchHistory_eq_wilsonRows head x roots k n P).symm
    _ = directionStackLaw V F := measure_congr (hae.mono fun _ h => propext h)
    _ = finiteUniformLaw R B S := directionStackLaw_forestEvent_eq R B k S

end
end FiniteAvalanches.Wilson.Lattice
