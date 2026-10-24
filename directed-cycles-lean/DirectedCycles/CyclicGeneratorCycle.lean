import DirectedCycles.BaselineHamiltonian
import DirectedCycles.NilpotentCycleBounds

set_option autoImplicit false
namespace DirectedCycles

/-- An available generator of a nontrivial cyclic group yields its full
generator cycle, including integral spanning at every truncation depth. -/
theorem cyclic_generator_cycle {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (S : Set G) (a : G) (ha : a ∈ S) (hgen : Subgroup.zpowers a = ⊤) :
    ∃ C : Cycle (CayleyDigraph S), C.length = Nat.card G ∧
      ∀ D : ℕ, SpansTruncation D (Set.range C.vertex) := by
  have hword : LayerWord (fun _ : ZMod 1 => S) 0 [a] := by
    simp only [LayerWord,ha,true_and]
  obtain ⟨C,hC,hfull⟩ := generating_baseline_hamiltonian
    (fun _ : ZMod 1 => S) [a] rfl hword (by simpa using hgen)
  let e : G × ZMod 1 ≃ G := Equiv.prodUnique _ _
  have hmap : ∀ x y, CyclicLayerDigraph (fun _ : ZMod 1 => S) x y →
      CayleyDigraph S (e x) (e y) := by
    rintro x y ⟨_,s,hs,he⟩
    exact ⟨s,hs,he⟩
  let L := C.map e.toEmbedding hmap
  refine ⟨L,by simpa only [L,Cycle.map,one_mul] using hC,?_⟩
  intro D
  have hsur : Set.range L.vertex = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ C.layerCoordinates 0 := by rw [hfull]; trivial
    obtain ⟨i,hi⟩ := hx
    exact ⟨i,congrArg e hi⟩
  rw [hsur]
  exact spansTruncation_univ D

end DirectedCycles
