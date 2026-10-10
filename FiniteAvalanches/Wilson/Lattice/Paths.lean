import FiniteAvalanches.Trees.Lattice.Space

/-! Literal finite walks (including zero edges) and genuinely infinite walks/rays.
No finite list represents an infinite path or a failed stopping time. -/
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb

structure FiniteWalk where
  length : ℕ
  vertex : Fin (length + 1) → Site 2
  adjacent : ∀ i : Fin length, (lattice 2).Adj (vertex i.castSucc) (vertex i.succ)

structure InfiniteWalk where
  vertex : ℕ → Site 2
  adjacent : ∀ n, (lattice 2).Adj (vertex n) (vertex (n + 1))

structure SimpleRay extends InfiniteWalk where
  injective : Function.Injective vertex

def FiniteWalk.start (p : FiniteWalk) : Site 2 := p.vertex 0
def FiniteWalk.finish (p : FiniteWalk) : Site 2 := p.vertex ⟨p.length, Nat.lt_succ_self _⟩
def FiniteWalk.vertices (p : FiniteWalk) : Set (Site 2) := Set.range p.vertex

def zeroWalk (x : Site 2) : FiniteWalk :=
  ⟨0, fun _ => x, fun i => Fin.elim0 i⟩

theorem zeroWalk_length (x : Site 2) : (zeroWalk x).length = 0 := rfl
theorem zeroWalk_vertices (x : Site 2) : (zeroWalk x).vertices = {x} := by
  ext y
  simp [FiniteWalk.vertices, zeroWalk]

/-- A stopped trace retains its complete finite word, or its genuinely infinite word. -/
inductive StoppedTrace (B : Set (Site 2)) (x : Site 2) where
  | hit (walk : FiniteWalk) (start : walk.start = x) (finish : walk.finish ∈ B)
      (first : ∀ i : Fin walk.length, walk.vertex i.castSucc ∉ B)
  | escape (walk : InfiniteWalk) (start : walk.vertex 0 = x)
      (avoids : ∀ n, walk.vertex n ∉ B)

def SimpleRay.vertices (γ : SimpleRay) : Set (Site 2) := Set.range γ.vertex
def SimpleRay.tailVertices (γ : SimpleRay) : Set (Site 2) :=
  Set.range (fun n => γ.vertex (n + 1))

theorem SimpleRay.vertices_infinite (γ : SimpleRay) : γ.vertices.Infinite :=
  Set.infinite_range_of_injective γ.injective

theorem SimpleRay.tail_nonempty (γ : SimpleRay) : γ.tailVertices.Nonempty :=
  ⟨γ.vertex 1, ⟨0, rfl⟩⟩

theorem SimpleRay.start_not_mem_tail (γ : SimpleRay) : γ.vertex 0 ∉ γ.tailVertices := by
  rintro ⟨n, hn⟩
  have he := γ.injective hn
  omega

end FiniteAvalanches.Wilson.Lattice
