module

public import DirectedCycles.LocalPowerSegment
public import DirectedCycles.LocalProductCompression

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Powers of a power-segment value are obtained by compressing the actual
long word into equal blocks. -/
theorem PowerSegment.product_power {u : G} {N : ℕ} (p : L.PowerSegment u N)
    {m k : ℕ} (hm : m ≤ N) (hmk : k*m ≤ N) :
    L.Product (List.replicate k (p.power m)) (p.power (k*m)) := by
  have hb : List.Forall₂ L.Product (List.replicate k (List.replicate m u)) (List.replicate k (p.power m)) := by
    induction k with
    | zero => exact List.Forall₂.nil
    | succ k ih =>
      simp only [List.replicate_succ]
      exact List.Forall₂.cons (p.product m hm) (ih (by nlinarith))
  have hp : L.Product (List.replicate k (List.replicate m u)).flatten (p.power (k*m)) := by
    simpa only [List.flatten_replicate_replicate] using p.product (k*m) hmk
  exact hp.compress L hb
end LocalGroupAlgebra
end DirectedCycles
