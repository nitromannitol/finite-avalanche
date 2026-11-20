import FiniteAvalanches.Support.Plane.BondDualMinimality
import FiniteAvalanches.Support.Plane.CopiedSimplePath

/-!
# A plane bond as an indexed dual cycle

A dual walk around a marked bond copy contains the whole remaining bond. A
simple path extracted from that walk therefore traverses every remaining bond
copy exactly once, retaining its original identity and either orientation.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
/-- An ordered vertex-simple copied path has distinct edge IDs. -/
theorem CopiedGraph.copies_injective_of_vertices_injective (J : CopiedGraph V E)
    (m : ℕ) (vertices : Fin (m + 1) → V) (hvertices : Function.Injective vertices)
    (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = vertices i.castSucc ∧
        J.right (copies i) = vertices i.succ) ∨
      (J.right (copies i) = vertices i.castSucc ∧ J.left (copies i) = vertices i.succ)) :
    Function.Injective copies := by
  intro i j h
  have hi := hends i
  rw [h] at hi
  rcases hi with ⟨ai, bi⟩ | ⟨bi, ai⟩ <;> rcases hends j with ⟨aj, bj⟩ | ⟨bj, aj⟩
  · exact Fin.castSucc_injective m (hvertices (ai.symm.trans aj))
  · have ha := congrArg Fin.val (hvertices (ai.symm.trans aj))
    have hb := congrArg Fin.val (hvertices (bi.symm.trans bj))
    simp only [Fin.val_castSucc, Fin.val_succ] at ha hb
    omega
  · have ha := congrArg Fin.val (hvertices (bi.symm.trans bj))
    have hb := congrArg Fin.val (hvertices (ai.symm.trans aj))
    simp only [Fin.val_castSucc, Fin.val_succ] at ha hb
    omega
  · exact Fin.castSucc_injective m (hvertices (bi.symm.trans bj))

/-- A bond, cut at a marked crossing, is a vertex-simple dual path through all
other crossing copies. -/
theorem exists_indexed_dual_bond_cycle {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) (A : Finset V)
    (hA : ∀ x y : V, x ∈ A → y ∈ A →
      J.reaches (Finset.univ.filter fun e => J.left e ∈ A ∧ J.right e ∈ A) x y)
    (hAc : ∀ x y : V, x ∉ A → y ∉ A →
      J.reaches (Finset.univ.filter fun e => J.left e ∉ A ∧ J.right e ∉ A) x y)
    (marked : E) (hmarked : J.Crosses A marked) :
    ∃ m : ℕ, ∃ vertices : Fin (m + 1) → Face D,
      Function.Injective vertices ∧
      ∃ copies : Fin m ≃ {e : E // e ≠ marked ∧ J.Crosses A e},
        m + 1 = (Finset.univ.filter fun e : E => J.Crosses A e).card ∧
        (∀ i : Fin m,
          (negativeChartFace D (copies i).val (charts (copies i).val) = vertices i.castSucc ∧
            positiveChartFace D (copies i).val (charts (copies i).val) = vertices i.succ) ∨
          (positiveChartFace D (copies i).val (charts (copies i).val) = vertices i.castSucc ∧
            negativeChartFace D (copies i).val (charts (copies i).val) = vertices i.succ)) ∧
        negativeChartFace D marked (charts marked) = vertices 0 ∧
        positiveChartFace D marked (charts marked) = vertices (Fin.last m) := by
  classical
  let K : CopiedGraph (Face D) E := ⟨fun e => negativeChartFace D e (charts e),
    fun e => positiveChartFace D e (charts e)⟩
  let cut : Finset E := Finset.univ.filter fun e => J.Crosses A e
  let S : Finset E := cut.erase marked
  have hwalk : K.reaches S (K.left marked) (K.right marked) :=
    dual_reaches_other_cut_edges D charts A marked hmarked
  obtain ⟨m, vertices, copies, hver, hfirst, hlast, hmem, hends⟩ :=
    K.exists_simple_ordered_path S hwalk
  let T : Finset E := Finset.univ.image copies
  have hcopies : ∀ i, copies i ≠ marked ∧ J.Crosses A (copies i) := by
    intro i
    have hi := Finset.mem_erase.mp (hmem i)
    exact ⟨hi.1, (Finset.mem_filter.mp hi.2).2⟩
  have hTS : T ⊆ S := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact hmem i
  have hTm : marked ∉ T := fun h => (Finset.notMem_erase marked cut) (hTS h)
  have hTcut : ∀ e ∈ T, J.Crosses A e := by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp (hTS he)).2).2
  have hpath : K.reaches T (K.left marked) (K.right marked) := by
    have hp := K.reaches_of_ordered_copies m vertices copies
      (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) hends
    simpa only [hfirst, hlast] using hp
  have hall := dual_path_contains_all_bond_edges D charts A hA hAc marked hmarked T hTm hTcut hpath
  let c : Fin m → {e : E // e ≠ marked ∧ J.Crosses A e} := fun i => ⟨copies i, hcopies i⟩
  have hc_inj : Function.Injective c := by
    intro i j hij
    apply K.copies_injective_of_vertices_injective m vertices hver copies hends
    exact congrArg Subtype.val hij
  have hc_surj : Function.Surjective c := by
    rintro ⟨e, hem, he⟩
    have heT := hall e hem he
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp heT
    exact ⟨i, Subtype.ext hi⟩
  let equiv := Equiv.ofBijective c ⟨hc_inj, hc_surj⟩
  have hcard : m = (cut.erase marked).card := by
    have heq := Fintype.card_congr equiv
    have hs : Fintype.card {e : E // e ≠ marked ∧ J.Crosses A e} =
        (cut.erase marked).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, cut]
    simpa only [Fintype.card_fin, hs] using heq
  have hmcut : marked ∈ cut := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmarked⟩
  refine ⟨m, vertices, hver, equiv, ?_, ?_, hfirst.symm, hlast.symm⟩
  · exact hcard ▸ Finset.card_erase_add_one hmcut
  · exact hends

end FiniteAvalanches.Electrical.StatementGeometry
