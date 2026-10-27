module

public import DirectedCycles.TotallyDisconnectedGoodModel
public import DirectedCycles.RelativeInternalSubgroups
public import DirectedCycles.InternalFiniteCoverTransfer

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- A totally disconnected good model of a bounded internal set yields
actual finite component subgroups and uniformly bounded coset covers. -/
theorem finite_subgroup_covers_of_totallyDisconnected_model {ι : Type*}
    (u : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Finset (G i)) (H : Subgroup (GroupUltraproduct (u : Filter ι) G))
    (hAH : ultraSet (u : Filter ι) G (fun i => (A i : Set (G i))) ⊆ H)
    (T : Set H) (hT : T = H.subtype ⁻¹' ultraSet (u : Filter ι) G (fun i => (A i : Set (G i))))
    (M : InternalLocallyCompactGroupModel H T (IsInternalFiniteIn u G H))
    [@TotallyDisconnectedSpace M.carrier M.topology] :
    ∃ (B : ∀ i, Subgroup (G i)) (E : ∀ i, Finset (G i)) (k : ℕ),
      (∀ i, (E i).card ≤ k) ∧ ∀ᶠ i in (u : Filter ι),
        (B i : Set (G i)) ⊆ (A i : Set (G i)) ∧
        (A i : Set (G i)) ⊆ (E i : Set (G i))*(B i : Set (G i)) := by
  classical
  obtain ⟨N,hN,hNA,F,hcover⟩ := internal_subgroup_of_totallyDisconnected_model M
  obtain ⟨B,hB,hBA⟩ := relative_internal_subgroup_components u G H N A hAH hN (by simpa only [hT] using hNA)
  let F' := F.image H.subtype
  have hcov : ultraSet (u : Filter ι) G (fun i => (A i : Set (G i))) ⊆
      (F' : Set _)*ultraSet (u : Filter ι) G (fun i => (B i : Set (G i))) := by
    intro x hx
    let y : H := ⟨x,hAH hx⟩
    have hyT : y ∈ T := by rw [hT]; exact hx
    obtain ⟨f,hf,n,hn,he⟩ := hcover hyT
    refine ⟨f.val,Finset.mem_image.mpr ⟨f,hf,rfl⟩,n.val,?_,?_⟩
    · change n.val ∈ ultraSubgroup (u : Filter ι) G B
      rw [hB]
      exact Subgroup.mem_map.mpr ⟨n,hn,rfl⟩
    · exact congrArg Subtype.val he
  obtain ⟨E,hE,hcovE⟩ := finite_cover_components u G _ _ F' hcov
  exact ⟨B,E,F'.card,hE,hBA.and hcovE⟩
end DirectedCycles
