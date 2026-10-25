module

public import DirectedCycles.LocalChainBump
public import DirectedCycles.LocalWordPowerMonotonicity
public import DirectedCycles.LocalTripleProducts

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- The local word-ball bump is built from actual neighbourhood-chain
membership. The long Q-domain and the three-letter A-domain supply every
translation witness, including inverse translations at the support boundary. -/
theorem exists_wordBall_bump (hd : L.DivisionClosed) (hr : L.Reversible)
    (A Q : Set G) (hQ1 : L.one ∈ Q) (hQi : ∀ q ∈ Q, L.inv q ∈ Q)
    (N : ℕ) (hN : 0 < N) (hQdom : L.AllProductsDefined Q N)
    (hQA : L.wordPower Q N ⊆ A) (hAdom : L.AllProductsDefined A 3) :
    ∃ ψ : G → ℝ, (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      (∀ x ∈ A, ψ x = 1) ∧ (∀ x, x ∉ L.wordPower A 2 → ψ x = 0) ∧
      (∀ q ∈ Q, ∀ x, |L.derivative q ψ x| ≤ 1/(N : ℝ)) := by
  let E := fun i => L.setMul (L.wordPower Q i) A
  have hpowA : ∀ i ≤ N, L.wordPower Q i ⊆ A :=
    L.wordPower_subset_of_maximum hQ1 hQdom hQA
  have hQsub : Q ⊆ A := by
    simpa only [L.wordPower_one] using hpowA 1 (by omega)
  have hone : ∀ i : ℕ, L.one ∈ L.wordPower Q i := by
    intro i
    refine ⟨List.replicate i L.one,List.length_replicate,?_,L.product_replicate_one i⟩
    intro x hx
    exact (List.mem_replicate.mp hx).2.symm ▸ hQ1
  apply L.exists_chain_bump hd (hd.cancellative L hr) Q A (L.wordPower A 2) E N hN hQi
  · intro i _ x hx
    exact ⟨L.one,hone i,x,hx,L.one_mul x⟩
  · intro i hi x hx
    obtain ⟨p,hp,a,ha,hm⟩ := hx
    rw [show 2 = 1+1 by rfl,L.wordPower_add hAdom (by omega),L.wordPower_one]
    exact ⟨p,hpowA i (by omega) hp,a,ha,hm⟩
  · intro q hq i hi x hx
    obtain ⟨p,hp,a,ha,hpa⟩ := hx
    have hqA := hQsub hq
    have hpA := hpowA i (by omega) hp
    obtain ⟨r,hr'⟩ := hAdom [q,p] (by simp) (by aesop)
    have hqp : L.mulRel q p r := (Product.pair_iff L _ _ _).1 hr'
    have hrQ : r ∈ L.wordPower Q (i+1) := by
      rw [show i+1 = 1+i by omega,L.wordPower_add hQdom (by omega : 1+i ≤ N),L.wordPower_one]
      exact ⟨q,hq,p,hp,hqp⟩
    obtain ⟨y,hry,hqy⟩ := hAdom.triple L hqA hpA ha hqp hpa
    exact ⟨y,⟨r,hrQ,a,ha,hry⟩,hqy⟩
end LocalGroupAlgebra
end DirectedCycles
