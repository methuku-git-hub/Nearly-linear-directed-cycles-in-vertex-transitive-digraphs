import DirectedCycles.LocalSignedProgressionInterval
import DirectedCycles.LocalShortProgressionModel

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- The finite signed progression from the prefix is exactly the signed set
used to identify the model curve image. -/
theorem PowerSegment.prefix_signedProgression_eq {u : G} {N M : ℕ}
    (p : L.PowerSegment u M) (q : L.PowerSegment u (N-1)) (hN : 0 < N)
    (hmatch : ∀ n ≤ N-1, q.power n = p.power n) :
    (q.signedProgression L : Set G) = p.shortSignedSet N := by
  have hpower : ∀ k : ℤ, k.natAbs < N → q.signedPower k = p.signedPower k := by
    intro k hk
    dsimp only [PowerSegment.signedPower]
    rw [hmatch k.natAbs (by omega)]
  ext x
  change x ∈ q.signedProgression L ↔ ∃ k : ℤ, k.natAbs < N ∧ p.signedPower k = x
  rw [q.mem_signedProgression_iff_signedPower L]
  constructor
  · rintro ⟨k,hk,he⟩
    have hk' : k.natAbs < N := by omega
    exact ⟨k,hk',(hpower k hk').symm.trans he⟩
  · rintro ⟨k,hk,he⟩
    exact ⟨k,by omega,(hpower k hk).trans he⟩
end LocalGroupAlgebra
end DirectedCycles
