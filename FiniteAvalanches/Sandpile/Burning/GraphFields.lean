module

public import FiniteAvalanches.Sandpile.Burning.GraphDegrees
public import FiniteAvalanches.Sandpile.Burning.FieldTransport

@[expose] public section

/-! Compose the actual two-phase restriction/reconstruction with original-copy
vertex and degree transports. Both target fields live on the literal graphs,
with their own degrees and all nonsink vertices. No recurrence is defined here. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

def insideHeightsGraphEquiv (B A : Finset (SourceVertex s)) (hBA : B ⊆ A) :
    InnerField G (Finset.univ.erase s) B A ≃ SourceHeights (sourceHeldGraph G s B A hBA) none :=
  reindexHeights (heldVertexEquiv s A)
    (fun x => if x.val ∈ B then degree G x.val.val else activeDegree G (Finset.univ.erase s) A x.val)
    (fun y => degree (sourceHeldGraph G s B A hBA) y.val) (inside_graph_degree G s B A hBA)

def outsideHeightsGraphEquiv (A : Finset (SourceVertex s)) :
    OuterField G (Finset.univ.erase s) A ≃ SourceHeights (complementGraph G s A) (complementSink s A) :=
  reindexHeights (outsideVertexEquiv s A)
    (fun x => degree G x.val.val - activeDegree G (Finset.univ.erase s) A x.val)
    (fun y => degree (complementGraph G s A) y.val) (outside_graph_degree G s A)

theorem inside_allowed_graph_iff (B A : Finset (SourceVertex s)) (hBA : B ⊆ A)
    (a : InnerField G (Finset.univ.erase s) B A) :
    InnerAllowed G (Finset.univ.erase s) B A a ↔
      noForbidden (sourceHeldGraph G s B A hBA) (Finset.univ.erase none)
        (insideHeightsGraphEquiv G s B A hBA a) := by
  have hr := restricted_allowed_iff (fun x : SourceVertex s => x ∈ A)
    (fun x => (a x).val) (activeDegree G (Finset.univ.erase s))
  have ht := indexed_allowed_iff (heldVertexEquiv s A) _
    (fun y => degree (sourceHeldGraph G s B A hBA) y.val) (inside_graph_degree G s B A hBA)
    (fun H x => activeDegree G (Finset.univ.erase s) (H.image Subtype.val) x.val)
    (activeDegree (sourceHeldGraph G s B A hBA) (Finset.univ.erase none))
    (inside_graph_active_degree G s B A hBA) a
  exact hr.trans ht

theorem outside_allowed_graph_iff (A : Finset (SourceVertex s))
    (d : OuterField G (Finset.univ.erase s) A) :
    OuterAllowed G (Finset.univ.erase s) A d ↔
      noForbidden (complementGraph G s A) (Finset.univ.erase (complementSink s A))
        (outsideHeightsGraphEquiv G s A d) := by
  have hr := restricted_allowed_iff (fun x : SourceVertex s => x ∉ A)
    (fun x => (d x).val) (activeDegree G (Finset.univ.erase s))
  have ho : OuterAllowed G (Finset.univ.erase s) A d ↔
      ∀ T : Finset (OutsideVertex s A), ¬(T.Nonempty ∧ ∀ x ∈ T,
        (d x).val < activeDegree G (Finset.univ.erase s) (T.image Subtype.val) x.val) := by
    rw [← hr]
    constructor
    · intro hn H hp
      exact hn H (fun x hx => Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hp x hx⟩)
    · intro hn H hHD
      exact hn H (fun x hx => (Finset.mem_sdiff.mp (hHD hx)).2)
  have ht := indexed_allowed_iff (outsideVertexEquiv s A) _
    (fun y => degree (complementGraph G s A) y.val) (outside_graph_degree G s A)
    (fun H x => activeDegree G (Finset.univ.erase s) (H.image Subtype.val) x.val)
    (activeDegree (complementGraph G s A) (Finset.univ.erase (complementSink s A)))
    (outside_graph_active_degree G s A) d
  exact ho.trans ht

def insideAllowedGraphEquiv (B A : Finset (SourceVertex s)) (hBA : B ⊆ A) :
    {a : InnerField G (Finset.univ.erase s) B A // InnerAllowed G (Finset.univ.erase s) B A a} ≃
      {h : SourceHeights (sourceHeldGraph G s B A hBA) none //
        noForbidden (sourceHeldGraph G s B A hBA) (Finset.univ.erase none) h} :=
  Equiv.subtypeEquiv (insideHeightsGraphEquiv G s B A hBA) (inside_allowed_graph_iff G s B A hBA)

def outsideAllowedGraphEquiv (A : Finset (SourceVertex s)) :
    {d : OuterField G (Finset.univ.erase s) A // OuterAllowed G (Finset.univ.erase s) A d} ≃
      {h : SourceHeights (complementGraph G s A) (complementSink s A) //
        noForbidden (complementGraph G s A) (Finset.univ.erase (complementSink s A)) h} :=
  Equiv.subtypeEquiv (outsideHeightsGraphEquiv G s A) (outside_allowed_graph_iff G s A)

/-- Actual graph-indexed two-phase field equivalence, complement first and held graph second. -/
def heldGraphFieldEquiv (B A : Finset (SourceVertex s)) (hBA : B ⊆ A) :
    {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h ∧
      heldBurning G (Finset.univ.erase s) h B = A} ≃
      ({d : SourceHeights (complementGraph G s A) (complementSink s A) //
          noForbidden (complementGraph G s A) (Finset.univ.erase (complementSink s A)) d} ×
        {a : SourceHeights (sourceHeldGraph G s B A hBA) none //
          noForbidden (sourceHeldGraph G s B A hBA) (Finset.univ.erase none) a}) :=
  (sourceHeldFieldEquiv G s B A hBA).trans
    ((Equiv.prodCongr (insideAllowedGraphEquiv G s B A hBA) (outsideAllowedGraphEquiv G s A)).trans
      (Equiv.prodComm _ _))

end
end FiniteAvalanches.Sandpile.Burning
