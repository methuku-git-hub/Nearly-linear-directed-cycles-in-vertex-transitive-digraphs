module

public import DirectedCycles.LocalSignedPowers
public import DirectedCycles.LocalSignedProgression

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

theorem PowerSegment.mem_signedProgression_iff_signedPower {u : G} {N : ℕ}
    (p : L.PowerSegment u N) (x : G) :
    x ∈ p.signedProgression L ↔ ∃ k : ℤ, k.natAbs ≤ N ∧ p.signedPower k = x := by
  constructor
  · intro hx
    obtain ⟨i,rfl⟩ := (p.mem_signedProgression L x).1 hx
    cases i with
    | inl i =>
      refine ⟨(i.val : ℤ),by simpa using (show i.val ≤ N by omega),?_⟩
      exact p.signedPower_nat i.val
    | inr i =>
      refine ⟨-((i.val+1 : ℕ) : ℤ),?_,p.signedPower_neg_nat (i.val+1)⟩
      rw [Int.natAbs_neg,Int.natAbs_natCast]
      omega
  · rintro ⟨k,hk,rfl⟩
    rcases Int.eq_nat_or_neg k with ⟨n,rfl | rfl⟩
    · rw [p.signedPower_nat]
      have hn : n ≤ N := by simpa only [Int.natAbs_natCast] using hk
      exact (p.mem_signedProgression L _).2 ⟨Sum.inl ⟨n,by omega⟩,rfl⟩
    · rw [p.signedPower_neg_nat]
      have hn : n ≤ N := by simpa only [Int.natAbs_neg,Int.natAbs_natCast] using hk
      apply p.inv_mem_signedProgression L
      exact (p.mem_signedProgression L _).2 ⟨Sum.inl ⟨n,by omega⟩,rfl⟩
end LocalGroupAlgebra
end DirectedCycles
