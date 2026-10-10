import FiniteAvalanches.Electrical.Plane.Incidence
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith

/-! Directed paths naming original copied edges, with literal ordered edge and vertex lists. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- A forward path uses a named copy from its a endpoint to its b endpoint at every step. -/
inductive ForwardPath {V E : Type*} (a b : E → V) : V → V → Type _
  | nil (x : V) : ForwardPath a b x x
  | cons {y : V} (e : E) (p : ForwardPath a b (b e) y) : ForwardPath a b (a e) y

def ForwardPath.edges {V E : Type*} {a b : E → V} : {x y : V} → ForwardPath a b x y → List E
  | _,_,.nil _ => []
  | _,_,.cons e p => e :: p.edges

def ForwardPath.vertices {V E : Type*} {a b : E → V} : {x y : V} → ForwardPath a b x y → List V
  | _,_,.nil x => [x]
  | _,_,.cons e p => a e :: p.vertices

theorem ForwardPath.vertices_length {V E : Type*} {a b : E → V} {x y : V} (p : ForwardPath a b x y) :
    p.vertices.length = p.edges.length+1 := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [vertices,edges,List.length_cons,ih]

/-- Increasing heights bound every actual visited vertex below by the start height. -/
theorem ForwardPath.vertex_height {V E : Type*} {a b : E → V} (H : V → ℝ)
    {x y : V} (p : ForwardPath a b x y)
    (hi : ∀ e ∈ p.edges, H (a e) < H (b e)) :
    ∀ z ∈ p.vertices, H x ≤ H z := by
  induction p with
  | nil x =>
    intro z hz
    have hz : z = x := List.mem_singleton.mp hz
    rw [hz]
  | cons e p ih =>
    have he := hi e (List.mem_cons_self)
    have hp := ih (fun z hz => hi z (List.mem_cons_of_mem _ hz))
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_rfl
    · exact he.le.trans (hp z hz)

/-- Every named copy's tail lies at or above the actual path start. -/
theorem ForwardPath.edge_height {V E : Type*} {a b : E → V} (H : V → ℝ)
    {x y : V} (p : ForwardPath a b x y)
    (hi : ∀ e ∈ p.edges, H (a e) < H (b e)) :
    ∀ e ∈ p.edges, H x ≤ H (a e) := by
  induction p with
  | nil => intro e he; exact (List.not_mem_nil he).elim
  | cons e p ih =>
    have he := hi e (List.mem_cons_self)
    have hp := ih (fun z hz => hi z (List.mem_cons_of_mem _ hz))
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_rfl
    · exact he.le.trans (hp z hz)

/-- A strictly increasing actual path visits no vertex twice. -/
theorem ForwardPath.vertices_nodup {V E : Type*} {a b : E → V} (H : V → ℝ)
    {x y : V} (p : ForwardPath a b x y)
    (hi : ∀ e ∈ p.edges, H (a e) < H (b e)) : p.vertices.Nodup := by
  induction p with
  | nil => exact List.nodup_singleton _
  | cons e p ih =>
    have he := hi e (List.mem_cons_self)
    have hp : ∀ z ∈ p.edges, H (a z) < H (b z) := fun z hz => hi z (List.mem_cons_of_mem _ hz)
    apply List.nodup_cons.mpr
    exact ⟨fun hm => (not_le_of_gt he) (p.vertex_height H hp _ hm),ih hp⟩

/-- Strict height increase also prevents repeating a parallel-copy ID. -/
theorem ForwardPath.edges_nodup {V E : Type*} {a b : E → V} (H : V → ℝ)
    {x y : V} (p : ForwardPath a b x y)
    (hi : ∀ e ∈ p.edges, H (a e) < H (b e)) : p.edges.Nodup := by
  induction p with
  | nil => exact List.nodup_nil
  | cons e p ih =>
    have he := hi e (List.mem_cons_self)
    have hp : ∀ z ∈ p.edges, H (a z) < H (b z) := fun z hz => hi z (List.mem_cons_of_mem _ hz)
    apply List.nodup_cons.mpr
    exact ⟨fun hm => (not_le_of_gt he) (p.edge_height H hp e hm),ih hp⟩

/-- Unit divergence telescopes along the ordered named copies. -/
theorem ForwardPath.sum_incidence {V E : Type*} {a b : E → V} {x y : V}
    (p : ForwardPath a b x y) (z : V) :
    (p.edges.map (fun e => (if a e = z then (1 : ℝ) else 0)-(if b e = z then 1 else 0))).sum =
      (if x = z then 1 else 0)-(if y = z then 1 else 0) := by
  induction p with
  | nil => simp only [edges,List.map_nil,List.sum_nil,sub_self]
  | cons e p ih => simp only [edges,List.map_cons,List.sum_cons,ih]; ring

end FiniteAvalanches.Electrical.Plane
