module

public import DirectedCycles.LocalMinimalEscape
public import DirectedCycles.LocalPowerExtension
public import DirectedCycles.LocalProductCompression

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- When binary products of A exist, the first failed PowerIn has an actual
value outside A. Thus domain failure does not masquerade as a first exit. -/
theorem first_exit_product {A : Set G} {u : G} {N : ℕ} (hN : 0 < N) (hu : u ∈ A)
    (hdom : L.AllProductsDefined A 2)
    (hbad : ¬ L.PowerIn A u N) (hprev : ∀ n < N, L.PowerIn A u n) :
    ∃ z, L.Product (List.replicate N u) z ∧ z ∉ A ∧ z ∈ L.wordPower A 2 := by
  have hp : ∀ n ≤ N-1, L.PowerIn A u n := fun n hn => hprev n (by omega)
  let p := L.powerSegmentOfPowerIn hp
  have hb : ∀ x ∈ A, ∀ y ∈ A, L.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hdom [x,y] (by simp) (by aesop)
    exact ⟨z,(Product.pair_iff L x y z).1 hz⟩
  obtain ⟨z,hz⟩ := p.extend_product L (fun n hn => L.powerSegmentOfPowerIn_mem hp hn) hu hb
  have heN : N-1+1 = N := by omega
  rw [heN] at hz
  refine ⟨z,hz,fun hzA => hbad ⟨z,hzA,hz⟩,?_⟩
  have hsplit : List.replicate N u = List.replicate (N-1) u ++ List.replicate 1 u := by
    rw [← List.replicate_add,heN]
  obtain ⟨a,b,ha,hb',hab⟩ := hz.split_allow_empty L hsplit
  have hae : a = p.power (N-1) := ha.unique L (p.product (N-1) le_rfl)
  have hbe : b = u := (Product.singleton_iff L).1 hb'
  refine ⟨[a,b],rfl,?_,(Product.pair_iff L a b z).2 hab⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · rw [hae]
    exact L.powerSegmentOfPowerIn_mem hp le_rfl
  · exact hbe.symm ▸ hu

/-- The complete first-exit segment is constructed from positive escape,
including its endpoint and all earlier membership certificates. -/
theorem exists_first_exit_segment {A : Set G} (hA : L.one ∈ A) {u : G} (hu : u ∈ A)
    (hdom : L.AllProductsDefined A 2) (hupos : 0 < L.escapeNorm A u) :
    ∃ N : ℕ, 0 < N ∧ ∃ p : L.PowerSegment u N,
      p.power N ∉ A ∧ (∀ n < N, p.power n ∈ A) ∧
      p.power N ∈ L.wordPower A 2 ∧ L.escapeNorm A u = 1/(N : ℝ) := by
  classical
  obtain ⟨N,hN,hbad,hprev,hnorm⟩ := L.exists_first_escape hA hupos
  obtain ⟨z,hz,hzout,hz2⟩ := L.first_exit_product hN hu hdom hbad hprev
  have hex : ∀ n ≤ N, ∃ x, L.Product (List.replicate n u) x := by
    intro n hn
    by_cases he : n = N
    · subst n; exact ⟨z,hz⟩
    · obtain ⟨x,_,hx⟩ := hprev n (by omega)
      exact ⟨x,hx⟩
  let p : L.PowerSegment u N := {
    power n := if hn : n ≤ N then Classical.choose (hex n hn) else L.one
    product := by intro n hn; simp only [dite_eq_left hn]; exact Classical.choose_spec (hex n hn) }
  have hpz : p.power N = z := (p.product N le_rfl).unique L hz
  refine ⟨N,hN,p,hpz ▸ hzout,?_,hpz ▸ hz2,hnorm⟩
  intro n hn
  obtain ⟨x,hx,hpx⟩ := hprev n hn
  exact ((p.product n hn.le).unique L hpx).symm ▸ hx
end LocalGroupAlgebra
end DirectedCycles
