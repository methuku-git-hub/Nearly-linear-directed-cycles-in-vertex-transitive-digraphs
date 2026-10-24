import DirectedCycles.LocalEscapeNorm
import DirectedCycles.LocalWordPowers

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A finite segment of powers, with every bracketing certified up to N.
Values beyond N are deliberately unconstrained and are never used as powers. -/
structure PowerSegment (g : G) (N : ℕ) where
  power : ℕ → G
  product : ∀ n ≤ N, L.Product (List.replicate n g) (power n)

namespace PowerSegment
variable {L} {g : G} {N : ℕ} (p : L.PowerSegment g N)

theorem zero : p.power 0 = L.one := (Product.nil_iff L).1 (p.product 0 (by omega))

theorem one (hN : 1 ≤ N) : p.power 1 = g := (Product.singleton_iff L).1 (p.product 1 hN)

theorem add {n m : ℕ} (hnm : n+m ≤ N) :
    L.mulRel (p.power n) (p.power m) (p.power (n+m)) := by
  obtain ⟨x,y,hx,hy,hm⟩ := (p.product (n+m) hnm).split_allow_empty L (List.replicate_add n m g)
  have hex : x = p.power n := hx.unique L (p.product n (by omega))
  have hey : y = p.power m := hy.unique L (p.product m (by omega))
  simpa only [hex,hey] using hm
end PowerSegment

/-- Escape data supplies a genuine bounded power segment, without extending
it to an unjustified global sequence of powers. -/
noncomputable def powerSegmentOfPowerIn {A : Set G} {g : G} {N : ℕ}
    (h : ∀ n ≤ N, L.PowerIn A g n) : L.PowerSegment g N where
  power n := if hn : n ≤ N then Classical.choose (h n hn) else L.one
  product n hn := by
    rw [dite_eq_left hn]
    exact (Classical.choose_spec (h n hn)).2

theorem powerSegmentOfPowerIn_mem {A : Set G} {g : G} {N : ℕ}
    (h : ∀ n ≤ N, L.PowerIn A g n) {n : ℕ} (hn : n ≤ N) :
    (L.powerSegmentOfPowerIn h).power n ∈ A := by
  dsimp only [powerSegmentOfPowerIn]
  rw [dite_eq_left hn]
  exact (Classical.choose_spec (h n hn)).1
end LocalGroupAlgebra
end DirectedCycles
