module

public import DirectedCycles.ActualCycleExpansion
public import DirectedCycles.TemplateRetainedTails
public import DirectedCycles.FibreSpanning

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- Coordinates selected by the actual auxiliary cycle in one layer,
viewed in B. When C=B these are exactly the manuscript's layer coordinates. -/
def auxiliaryLayerCoordinates {G : Type*} [Group G] (a : G) (D : ℕ)
    (data : List (ℕ × G)) (hne : data ≠ [])
    (Q : Cycle (cyclicAuxiliaryGraph a D data hne))
    (z : ZMod (slotBaseline (cyclicLiftSlots a D data)).length) : Set (elementCommutators a) :=
  {b | ∃ e, (Q.vertex e).2 = z ∧ (Q.vertex e).1.val = b.val}

/-- A spanning set of actual auxiliary coordinates in a fixed-run layer
supplies the whole corresponding B-fibre in the span of expanded a-edge tails. -/
theorem actual_fixed_fibre_mem {G : Type*} [Group G] [Finite G]
    (a : G) (D : ℕ) (data : List (ℕ × G)) (hne : data ≠ [])
    (hC : cyclicAuxiliaryGroup a D data hne ≤ elementCommutators a)
    (hr : Function.Injective (fun i : Fin data.length =>
      QuotientGroup.mk' (elementClosure a) (cycleLabelPrefixes data i.castSucc)))
    (hl : ∀ i : Fin data.length, (data[i.val]).1 < orderOf (QuotientGroup.mk' (elementCommutators a) a))
    (Q : Cycle (cyclicAuxiliaryGraph a D data hne))
    (R : Digraph G) (L : Cycle R)
    (hV : let E := cyclicAuxiliary_expansionTemplate a D data hne hC hr hl Q
      List.ofFn L.vertex = (List.ofFn (fun e => List.ofFn (E.point e))).flatten)
    (hA : L.ClosedUnderGenerator a)
    (W : AddSubgroup (TruncatedGroupRing G D))
    (hW : ∀ x ∈ L.generatorTails a, truncatedElement G D x ∈ W)
    (i : Fin data.length) (k : ℕ) (hk : k < (data[i.val]).1)
    (hspan : SpansTruncation D (auxiliaryLayerCoordinates a D data hne Q
      (retainedLayerEquiv a D data hne ⟨i,⟨k,by omega⟩⟩))) :
    ∀ b : elementCommutators a, truncatedElement G D (b.val*runReference a D data i*a^k) ∈ W := by
  let E := cyclicAuxiliary_expansionTemplate a D data hne hC hr hl Q
  let p : RetainedPosition data := ⟨i,⟨k,by omega⟩⟩
  let g := runReference a D data i*a^k
  let φ : TruncatedGroupRing (elementCommutators a) D →+ TruncatedGroupRing G D :=
    (AddMonoidHom.mulRight (truncatedElement G D g)).comp
      (truncatedMap (elementCommutators a).subtype D).toAddMonoidHom
  have hφ : ∀ b : elementCommutators a,
      φ (truncatedElement (elementCommutators a) D b) = truncatedElement G D (b.val*g) := by
    intro b
    change truncatedMap (elementCommutators a).subtype D (truncatedElement (elementCommutators a) D b) *
      truncatedElement G D g = _
    rw [truncatedMap_element,← map_mul]
    rfl
  have hsel : ∀ b ∈ auxiliaryLayerCoordinates a D data hne Q (retainedLayerEquiv a D data hne p),
      φ (truncatedElement (elementCommutators a) D b) ∈ W := by
    rintro b ⟨e,hz,hb⟩
    have hp : (retainedLayerEquiv a D data hne).symm (Q.vertex e).2 = p := by
      rw [hz,Equiv.symm_apply_apply]
    have hfixed : E.level e < (data[(E.position e).val]).1 := by
      change ((retainedLayerEquiv a D data hne).symm (Q.vertex e).2).2.val <
        (data[((retainedLayerEquiv a D data hne).symm (Q.vertex e).2).1.val]).1
      have hnum : ((retainedLayerEquiv a D data hne).symm (Q.vertex e).2).2.val = k :=
        congrArg (fun t : RetainedPosition data => t.2.val) hp
      have hlen : (data[((retainedLayerEquiv a D data hne).symm (Q.vertex e).2).1.val]).1 = (data[i.val]).1 :=
        congrArg (fun t : RetainedPosition data => (data[t.1.val]).1) hp
      omega
    have hpoint : E.vertex e = b.val*g := by
      change normalizedRealization (slotBaseline (cyclicLiftSlots a D data))
        ((Q.vertex e).1.val,(Q.vertex e).2) = b.val*g
      simp only [normalizedRealization,hb,hz,retainedLayerEquiv_val,cyclicLiftSlots_baseline]
      rw [cyclicBaseline_prefix_retained]
    have ht := E.fixed_vertex_is_tail L hV hA e hfixed
    rw [hpoint] at ht
    rw [hφ]
    exact hW _ ht
  intro b
  have hm := spansTruncation_map_mem D _ hspan φ W hsel (truncatedElement (elementCommutators a) D b)
  rw [hφ] at hm
  simpa only [g,mul_assoc] using hm

end DirectedCycles
