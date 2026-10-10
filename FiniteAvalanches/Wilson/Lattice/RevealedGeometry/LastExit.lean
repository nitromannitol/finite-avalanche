import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.CofiniteComponent
import FiniteAvalanches.Needle.Geometry

set_option autoImplicit false
namespace JointLastExit
open LatticeProb FiniteAvalanches
open scoped Classical
noncomputable section

/-- Decompose a finite walk at its final visit to a prescribed set. -/
theorem last_exit {V : Type*} (G : SimpleGraph V) (B : Set V) {a b : V}
    (p : G.Walk a b) (hi : ∃ x ∈ p.support, x ∈ B) (hb : b ∉ B) :
    ∃ (w z : V) (q₀ : G.Walk a w) (e : G.Adj w z) (q₁ : G.Walk z b),
      p = q₀.append (.cons e q₁) ∧ w ∈ B ∧ ∀ x ∈ q₁.support, x ∉ B := by
  induction p with
  | nil =>
    obtain ⟨x,hx,hxB⟩ := hi
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    subst x
    exact (hb hxB).elim
  | @cons a c b e p ih =>
    by_cases ht : ∃ x ∈ p.support, x ∈ B
    · obtain ⟨w,z,q₀,ez,q₁,he,hw,hq⟩ := ih ht hb
      refine ⟨w,z,.cons e q₀,ez,q₁,?_,hw,hq⟩
      simp only [SimpleGraph.Walk.cons_append, ← he]
    · have ha : a ∈ B := by
        obtain ⟨x,hx,hxB⟩ := hi
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hxB
        · exact (ht ⟨x,hx,hxB⟩).elim
      exact ⟨a,c,.nil,e,p,rfl,ha,fun x hx hxB => ht ⟨x,hx,hxB⟩⟩

theorem boundary_of_exit (n : ℕ) (w z : Site 2) (hw : w ∈ box 2 n)
    (hz : z ∉ box 2 n) (h : (lattice 2).Adj w z) :
    Needle.radius w = n := by
  have hwle := (Needle.mem_box_iff w n).mp hw
  have hzgt : (n : ℤ) < Needle.radius z := by
    exact lt_of_not_ge (fun he => hz ((Needle.mem_box_iff z n).mpr he))
  have ht := Needle.radius_le_radius_add z w
  have he := Needle.radius_sub_neighbor h.symm
  rw [he] at ht
  omega

end
end JointLastExit
