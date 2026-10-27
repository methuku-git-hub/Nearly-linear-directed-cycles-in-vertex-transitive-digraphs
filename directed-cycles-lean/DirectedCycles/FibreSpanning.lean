module

public import DirectedCycles.TruncatedDescent

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The manuscript's additive determining property in the actual quotient. -/
def SpansTruncation {G : Type*} [Group G] (D : ℕ) (E : Set G) : Prop :=
  AddSubgroup.closure (truncatedElement G D '' E) = ⊤

/-- A generating subset can be tested through any additive map. -/
theorem spansTruncation_map_mem {G V : Type*} [Group G] [AddCommGroup V]
    (D : ℕ) (E : Set G) (hE : SpansTruncation D E)
    (φ : TruncatedGroupRing G D →+ V) (W : AddSubgroup V)
    (h : ∀ g ∈ E, φ (truncatedElement G D g) ∈ W) :
    ∀ x : TruncatedGroupRing G D, φ x ∈ W := by
  have hle : AddSubgroup.closure (truncatedElement G D '' E) ≤ W.comap φ := by
    apply (W.comap φ).closure_le.mpr
    rintro x ⟨g,hg,rfl⟩
    exact h g hg
  rw [hE] at hle
  exact fun x => hle (AddSubgroup.mem_top x)

/-- Spanning in each fibre supplies its full coset span in the ambient ring. -/
theorem full_fibre_mem_of_spanning {G : Type*} [Group G] (K : Subgroup G)
    (D : ℕ) (E : Set G) (W : AddSubgroup (TruncatedGroupRing G D))
    (hE : ∀ e ∈ E, truncatedElement G D e ∈ W)
    (g : G) (hspan : SpansTruncation D {k : K | k.val*g ∈ E}) :
    ∀ k : K, truncatedElement G D (k.val*g) ∈ W := by
  let φ : TruncatedGroupRing K D →+ TruncatedGroupRing G D :=
    (AddMonoidHom.mulRight (truncatedElement G D g)).comp (truncatedMap K.subtype D).toAddMonoidHom
  have hφ : ∀ k : K, φ (truncatedElement K D k) = truncatedElement G D (k.val*g) := by
    intro k
    change truncatedMap K.subtype D (truncatedElement K D k) * truncatedElement G D g = _
    rw [truncatedMap_element,map_mul]
    rfl
  have hh : ∀ k ∈ {k : K | k.val*g ∈ E}, φ (truncatedElement K D k) ∈ W := by
    intro k hk
    rw [hφ]
    exact hE (k.val*g) hk
  intro k
  rw [← hφ]
  exact spansTruncation_map_mem D _ hspan φ W hh (truncatedElement K D k)

/-- Manuscript Lemma 5.6: quotient spanning and spanning inside every coset
that meets E imply spanning in the whole group. -/
theorem spanning_through_fibres {G : Type*} [Group G] (K : Subgroup G) [K.Normal]
    (D : ℕ) (E : Set G)
    (hquot : SpansTruncation D ((QuotientGroup.mk' K) '' E))
    (hfibres : ∀ g ∈ E, SpansTruncation D {k : K | k.val*g ∈ E}) :
    SpansTruncation D E := by
  let W := AddSubgroup.closure (truncatedElement G D '' E)
  have hE : ∀ g ∈ E, truncatedElement G D g ∈ W := fun g hg =>
    AddSubgroup.subset_closure ⟨g,hg,rfl⟩
  have hfull : ∀ g ∈ E, ∀ k : K, truncatedElement G D (k.val*g) ∈ W := by
    intro g hg
    exact full_fibre_mem_of_spanning K D E W hE g (hfibres g hg)
  apply truncated_spanning_descent (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) D W
  · intro k hk x hx
    have hkK : k ∈ K := by simpa only [QuotientGroup.ker_mk'] using hk
    let L := AddMonoidHom.mulLeft (truncatedElement G D k)
    have hle : W ≤ W.comap L := by
      apply (W.comap L).closure_le.mpr
      rintro y ⟨g,hg,rfl⟩
      change truncatedElement G D k * truncatedElement G D g ∈ W
      rw [← map_mul]
      exact hfull g hg ⟨k,hkK⟩
    exact hle hx
  · apply top_le_iff.mp
    have hle : AddSubgroup.closure (truncatedElement (G ⧸ K) D '' ((QuotientGroup.mk' K) '' E)) ≤
        W.map (truncatedMap (QuotientGroup.mk' K) D).toAddMonoidHom := by
      apply (W.map (truncatedMap (QuotientGroup.mk' K) D).toAddMonoidHom).closure_le.mpr
      rintro y ⟨q,⟨g,hg,rfl⟩,rfl⟩
      exact ⟨truncatedElement G D g,hE g hg,truncatedMap_element _ D g⟩
    rw [hquot] at hle
    exact hle

end DirectedCycles
