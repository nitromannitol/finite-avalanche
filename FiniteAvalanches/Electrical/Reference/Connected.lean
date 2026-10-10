import FiniteAvalanches.Electrical.Reference.Lattice
import FiniteAvalanches.Trees.ForestProjection.Uniform
import FiniteAvalanches.Electrical.Dirichlet

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.Repair8
open LatticeProb
open scoped Classical BigOperators
noncomputable section

/-- A copy with both original endpoints in D cannot be the marked boundary copy. -/
theorem internal_ne_marked (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (e : OriginalCopy)
    (ha : originalA e ∈ D) (hb : originalB e ∈ D) : e ≠ marked.val := by
  intro he
  subst e
  rcases marked.property with h | h
  · exact ((project_eq_alpha_iff D P _).mp h.1) ha
  · exact ((project_eq_alpha_iff D P _).mp h.2) hb

/-- An original interior edge yields a walk after contraction, including collapsed loops. -/
theorem internal_copy_reaches (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (e : OriginalCopy)
    (ha : originalA e ∈ D) (hb : originalB e ∈ D) :
    (StatementTypes.graph D P marked).reaches Finset.univ
      (project D P (originalA e)) (project D P (originalB e)) := by
  by_cases heq : project D P (originalA e) = project D P (originalB e)
  · rw [heq]
    exact .refl
  · let c : Copy D P marked := ⟨e, (mem_retainedCopies D P marked e).mpr
        ⟨Or.inl ha, heq, internal_ne_marked D P marked e ha hb⟩⟩
    exact .single ⟨c, Finset.mem_univ c, Or.inl ⟨rfl, rfl⟩⟩

/-- Both orientations of a physical lattice edge transport to actual copied walks. -/
theorem internal_adj_reaches (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (x y : Site 2) (hx : x ∈ D) (hy : y ∈ D)
    (hxy : (lattice 2).Adj x y) :
    (StatementTypes.graph D P marked).reaches Finset.univ (project D P x) (project D P y) := by
  change ∃ i : Fin 2, y = x + unit i ∨ x = y + unit i at hxy
  obtain ⟨i, h | h⟩ := hxy
  · subst y
    exact internal_copy_reaches D P marked (x, i) hx hy
  · subst x
    exact (StatementTypes.graph D P marked).reaches_symm
      (internal_copy_reaches D P marked (y, i) hy hx)

/-- Connectedness of D gives complete actual copied walks between all its images. -/
theorem internal_reaches (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (x y : D) :
    (StatementTypes.graph D P marked).reaches Finset.univ
      (project D P x.val) (project D P y.val) := by
  have hr := (SimpleGraph.reachable_iff_reflTransGen x y).mp (hD x y)
  induction hr with
  | refl => exact .refl
  | @tail u v _ huv ih =>
    exact ih.trans (internal_adj_reaches D P marked u.val v.val u.property v.property huv)

/-- Every D image reaches the actual one terminal without using the marked copy. -/
theorem internal_reaches_beta (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (x : D) :
    (StatementTypes.graph D P marked).reaches Finset.univ (project D P x.val) (beta D P) := by
  obtain ⟨p, hp⟩ := P.property
  have hb : project D P p.val = beta D P :=
    (project_eq_beta_iff D P _).mpr (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  simpa only [hb] using internal_reaches D P hD marked x p

/-- A perpendicular outward boundary copy survives deletion of the marked original ID. -/
theorem alpha_reaches_beta (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    (StatementTypes.graph D P marked).reaches Finset.univ (alpha D P) (beta D P) := by
  let j : Fin 2 := if marked.val.2 = 0 then 1 else 0
  have hj : j ≠ marked.val.2 := by
    have hi : marked.val.2 = 0 ∨ marked.val.2 = 1 := by omega
    rcases hi with hi | hi <;> simp [j, hi]
  obtain ⟨p, _⟩ := P.property
  obtain ⟨x, hx, hmax⟩ := D.exists_max_image (fun x => x j) ⟨p.val, p.property⟩
  have hout : x + unit j ∉ D := by
    intro hy
    have hle := hmax (x + unit j) hy
    simp only [Pi.add_apply, unit, Pi.single_eq_same] at hle
    omega
  have houter : project D P (x + unit j) = alpha D P :=
    (project_eq_alpha_iff D P _).mpr hout
  have hfree : project D P x ≠ alpha D P := by
    intro h
    exact ((project_eq_alpha_iff D P _).mp h) hx
  have hmarked : (x, j) ≠ marked.val := by
    intro h
    exact hj (congrArg Prod.snd h)
  let c : Copy D P marked := ⟨(x, j), (mem_retainedCopies D P marked _).mpr
    ⟨Or.inl hx, by change project D P x ≠ project D P (x + unit j); rwa [houter], hmarked⟩⟩
  have hedge : (StatementTypes.graph D P marked).reaches Finset.univ
      (project D P x) (alpha D P) :=
    .single ⟨c, Finset.mem_univ c, Or.inl ⟨rfl, houter⟩⟩
  exact ((StatementTypes.graph D P marked).reaches_symm hedge).trans
    (internal_reaches_beta D P hD marked ⟨x, hx⟩)

/-- Every actual terminal/free vertex reaches beta after deletion of one original copy. -/
theorem reaches_beta (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (x : Vertex D P) :
    (StatementTypes.graph D P marked).reaches Finset.univ x (beta D P) := by
  cases x with
  | inl v => cases v with
    | false => exact alpha_reaches_beta D P hD marked
    | true => exact .refl
  | inr v => simpa only [project_free] using internal_reaches_beta D P hD marked v.val

/-- Full global copied connectivity, not a supplied reachability premise. -/
theorem graph_reaches (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (x y : Vertex D P) :
    (StatementTypes.graph D P marked).reaches Finset.univ x y :=
  (reaches_beta D P hD marked x).trans
    ((StatementTypes.graph D P marked).reaches_symm (reaches_beta D P hD marked y))

/-- The positive-Laplacian supporting graph is genuinely connected. -/
theorem graph_connected (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    (supportGraph (copyA D P marked) (copyB D P marked)).Connected := by
  haveI : Nonempty (Vertex D P) := ⟨alpha D P⟩
  exact ⟨(StatementTypes.graph D P marked).supportGraph_preconnected_of_reaches
    (graph_reaches D P hD marked)⟩

/-- The exact original two-rooted-forest carrier is inhabited on every admitted D. -/
theorem forest_nonempty (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    Nonempty ((StatementTypes.graph D P marked).RootedForest
      ({alpha D P, beta D P} : Set (Vertex D P))) :=
  (StatementTypes.graph D P marked).nonempty_rootedForest _
    ⟨alpha D P, by simp⟩ (graph_reaches D P hD marked)

/-- The denominator is the positive FULL original two-rooted-forest count. -/
theorem forest_card_pos (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    0 < Fintype.card ((StatementTypes.graph D P marked).RootedForest
      ({alpha D P, beta D P} : Set (Vertex D P))) := by
  haveI := forest_nonempty D P hD marked
  exact Fintype.card_pos

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.Repair8
