import FiniteAvalanches.Sandpile.Components.SubsetDegrees
import FiniteAvalanches.Sandpile.Components.Fields

/-! The typed lattice allowed fields are precisely canonical noForbidden fields
on the actual induced copied graphs. No connectivity or tree-count input occurs. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves ComponentTransport
open scoped Classical
noncomputable section

abbrev InnerSourceHeights {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  Burning.SourceHeights (inducedGraph (insideSupport C)) (innerRoot C)
abbrev OuterSourceHeights {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  Burning.SourceHeights (inducedGraph (outsideSupport C)) (outerRoot C)

def innerSourceHeightsEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    InnerField o C ≃ InnerSourceHeights C :=
  reindexHeights (innerSourceVertexEquiv C) (fun x => degree C.val x.val)
    (fun v => Burning.degree (inducedGraph (insideSupport C)) v.val) (inner_source_degree C)

def outerSourceHeightsEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    OuterField C ≃ OuterSourceHeights C :=
  reindexHeights (outerSourceVertexEquiv C) (fun x => 4 - degree C.val x.val)
    (fun v => Burning.degree (inducedGraph (outsideSupport C)) v.val) (outer_source_degree C)

theorem inner_allowed_source_iff {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (r : InnerField o C) :
    allowedOn (C.val.erase (FiniteWired.site o)) (fun x => (r x).val) ↔
      Burning.noForbidden (inducedGraph (insideSupport C))
        (Finset.univ.erase (innerRoot C)) (innerSourceHeightsEquiv C r) := by
  have hr := restricted_allowed_iff (fun x : Site2 => x ∈ C.val.erase (FiniteWired.site o))
    (fun x => (r x).val) degree
  have ht := indexed_allowed_iff (innerSourceVertexEquiv C)
    (fun x => degree C.val x.val)
    (fun v => Burning.degree (inducedGraph (insideSupport C)) v.val) (inner_source_degree C)
    (fun S x => degree (S.image Subtype.val) x.val)
    (Burning.activeDegree (inducedGraph (insideSupport C)) (Finset.univ.erase (innerRoot C)))
    (inner_subset_degree C) r
  exact hr.trans ht

theorem outer_allowed_source_iff {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (r : OuterField C) :
    allowedOn (boxSites N \ C.val) (fun x => (r x).val) ↔
      Burning.noForbidden (inducedGraph (outsideSupport C))
        (Finset.univ.erase (outerRoot C)) (outerSourceHeightsEquiv C r) := by
  have hr := restricted_allowed_iff (fun x : Site2 => x ∈ boxSites N \ C.val)
    (fun x => (r x).val) degree
  have ht := indexed_allowed_iff (outerSourceVertexEquiv C)
    (fun x => 4 - degree C.val x.val)
    (fun v => Burning.degree (inducedGraph (outsideSupport C)) v.val) (outer_source_degree C)
    (fun S x => degree (S.image Subtype.val) x.val)
    (Burning.activeDegree (inducedGraph (outsideSupport C)) (Finset.univ.erase (outerRoot C)))
    (outer_subset_degree C) r
  exact hr.trans ht

abbrev InnerGraphAllowed {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  {h : InnerSourceHeights C // Burning.noForbidden (inducedGraph (insideSupport C))
    (Finset.univ.erase (innerRoot C)) h}
abbrev OuterGraphAllowed {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  {h : OuterSourceHeights C // Burning.noForbidden (inducedGraph (outsideSupport C))
    (Finset.univ.erase (outerRoot C)) h}

def innerAllowedSourceEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    InnerAllowed o C ≃ InnerGraphAllowed C :=
  Equiv.subtypeEquiv (innerSourceHeightsEquiv C) (inner_allowed_source_iff C)

def outerAllowedSourceEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    OuterAllowed C ≃ OuterGraphAllowed C :=
  Equiv.subtypeEquiv (outerSourceHeightsEquiv C) (outer_allowed_source_iff C)

/-- The complete core fiber equals the complement-first actual graph product. -/
def coreGraphFieldEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    CoreField o C.val ≃ OuterGraphAllowed C × InnerGraphAllowed C :=
  (componentFieldEquiv (C := C)).trans
    ((Equiv.prodCongr (innerAllowedSourceEquiv C) (outerAllowedSourceEquiv C)).trans
      (Equiv.prodComm _ _))

end
end FiniteAvalanches.Sandpile.Components
