import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Continuity of multiplication gives a common open identity window
whose prescribed finite word power lies in the target neighbourhood. -/
theorem open_identity_word_window {U : Set G} (hU : IsOpen U) (hU1 : (1 : G) ∈ U) (n : ℕ) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ W^n ⊆ U := by
  induction n generalizing U with
  | zero => exact ⟨Set.univ,isOpen_univ,Set.mem_univ _,by simpa using hU1⟩
  | succ n ih =>
      obtain ⟨V,hV,hV1,hVV⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds hU1)
      obtain ⟨W,hW,hW1,hWn⟩ := ih hV hV1
      refine ⟨W ∩ V,hW.inter hV,⟨hW1,hV1⟩,?_⟩
      rw [pow_succ]
      exact (Set.mul_subset_mul
        ((Set.pow_subset_pow_left Set.inter_subset_left).trans hWn) Set.inter_subset_right).trans hVV

/-- Conjugation is uniformly small on a compact set of conjugators. -/
theorem compact_conjugation_window {K U : Set G} (hK : IsCompact K)
    (hU : IsOpen U) (hU1 : (1 : G) ∈ U) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ V⁻¹ = V ∧
      ∀ v ∈ V, ∀ y ∈ K, y⁻¹*v*y ∈ U := by
  have ho : IsOpen ((fun p : G × G => p.2⁻¹*p.1*p.2) ⁻¹' U) :=
    hU.preimage (by fun_prop)
  obtain ⟨A,B,hA,_hB,h1A,hKB,hAB⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({1} : Set G)) hK ho (by
      rintro ⟨a,b⟩ ⟨ha,_hb⟩
      have ha' : a = 1 := ha
      change b⁻¹*a*b ∈ U
      simpa only [ha',mul_one,inv_mul_cancel] using hU1)
  refine ⟨A ∩ A⁻¹,hA.inter hA.inv,?_,?_,?_⟩
  · have h := h1A (Set.mem_singleton 1)
    exact ⟨h,by simpa using h⟩
  · ext z
    change (z⁻¹ ∈ A ∧ (z⁻¹)⁻¹ ∈ A) ↔ (z ∈ A ∧ z⁻¹ ∈ A)
    simp only [inv_inv,and_comm]
  · intro v hv y hy
    exact hAB (show (v,y) ∈ A ×ˢ B from ⟨hv.1,hKB hy⟩)

/-- Combining uniform conjugation with multiplication produces the
actual second generator set used by the Haar finite-trapping argument. -/
theorem compact_conjugate_word_window {K U : Set G} (hK : IsCompact K)
    (hU : IsOpen U) (hU1 : (1 : G) ∈ U) (hK1 : (1 : G) ∈ K) (M : ℕ) :
    ∃ V P : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ V⁻¹ = V ∧
      (1 : G) ∈ P ∧ P⁻¹ = P ∧ P^M ⊆ U ∧
        ∀ v ∈ V, ∀ y ∈ K, y⁻¹*v*y ∈ P := by
  obtain ⟨W,hW,hW1,hWM⟩ := open_identity_word_window hU hU1 M
  obtain ⟨V,hV,hV1,hVi,hconj⟩ := compact_conjugation_window hK hW hW1
  let P : Set G := {z | ∃ v ∈ V, ∃ y ∈ K, z = y⁻¹*v*y}
  have hPW : P ⊆ W := by
    rintro z ⟨v,hv,y,hy,rfl⟩
    exact hconj v hv y hy
  have hPclosed : ∀ z ∈ P, z⁻¹ ∈ P := by
    rintro z ⟨v,hv,y,hy,rfl⟩
    refine ⟨v⁻¹,?_,y,hy,?_⟩
    · simpa only [hVi] using Set.inv_mem_inv.mpr hv
    · simp only [mul_inv_rev,inv_inv,mul_assoc]
  have hPi : P⁻¹ = P := by
    ext z
    change z⁻¹ ∈ P ↔ z ∈ P
    exact ⟨fun hz => by simpa only [inv_inv] using hPclosed z⁻¹ hz,hPclosed z⟩
  exact ⟨V,P,hV,hV1,hVi,⟨1,hV1,1,hK1,by simp⟩,hPi,
    (Set.pow_subset_pow_left hPW).trans hWM,fun v hv y hy => ⟨v,hv,y,hy,rfl⟩⟩
end DirectedCycles
