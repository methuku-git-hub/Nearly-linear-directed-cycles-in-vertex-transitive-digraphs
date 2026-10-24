import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A compact set inside an open set has one symmetric identity
neighbourhood whose left and right multiplication both remain in that set. -/
theorem compact_two_sided_window (K O : Set G) (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧
      (∀ x ∈ W, x⁻¹ ∈ W) ∧ W*K*W ⊆ O := by
  have hm : IsOpen ((fun p : G × G => p.1*p.2) ⁻¹' O) := hO.preimage continuous_mul
  obtain ⟨A,B,hA,hB,h1A,hKB,hAB⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({1} : Set G)) hK hm (by
      rintro ⟨a,b⟩ ⟨ha,hb⟩
      have ha' : a = 1 := ha
      change a*b ∈ O
      simpa only [ha',one_mul] using hKO hb)
  obtain ⟨C,D,_hC,hD,hKC,h1D,hCD⟩ := generalized_tube_lemma hK
    (isCompact_singleton : IsCompact ({1} : Set G)) (hB.preimage continuous_mul) (by
      rintro ⟨a,b⟩ ⟨ha,hb⟩
      have hb' : b = 1 := hb
      change a*b ∈ B
      simpa only [hb',mul_one] using hKB ha)
  let W := (A ∩ D) ∩ (A ∩ D)⁻¹
  have hW : IsOpen W := (hA.inter hD).inter (hA.inter hD).inv
  have hW1 : (1 : G) ∈ W := by
    have h1 : (1 : G) ∈ A ∩ D := ⟨h1A (Set.mem_singleton _),h1D (Set.mem_singleton _)⟩
    exact ⟨h1,by simpa using h1⟩
  refine ⟨W,hW,hW1,?_,?_⟩
  · intro x hx
    exact ⟨hx.2,by simpa using hx.1⟩
  · rintro x ⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩
    have hbc : b*c ∈ B := hCD (show (b,c) ∈ C ×ˢ D from ⟨hKC hb,hc.1.2⟩)
    have habc : a*(b*c) ∈ O := hAB (show (a,b*c) ∈ A ×ˢ B from ⟨ha.1.1,hbc⟩)
    simpa only [mul_assoc] using habc
end DirectedCycles
