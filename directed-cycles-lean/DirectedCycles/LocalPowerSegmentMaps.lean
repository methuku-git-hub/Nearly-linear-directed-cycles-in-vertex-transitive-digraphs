import DirectedCycles.LocalPowerSegment
import DirectedCycles.LocalGroupHom
import DirectedCycles.LocalUltraproductProducts

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G H : Type*} {L : LocalGroupAlgebra G} [Group H]

theorem PowerSegment.map_power {u : G} {N : ℕ} (p : L.PowerSegment u N)
    (π : LocalGroupHom L (ofGroup H)) {n : ℕ} (hn : n ≤ N) :
    π.toFun (p.power n) = (π.toFun u)^n := by
  have hh := (ofGroup_product_iff H _ _).1 ((p.product n hn).map π)
  simpa only [List.map_replicate,List.prod_replicate] using hh
end LocalGroupAlgebra

variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (u : ∀ i, G i) (M : ι → ℕ) (p : ∀ i, (L i).PowerSegment (u i) (M i))

/-- Every fixed standard power in the ultraproduct is an actual component
power whenever the segment lengths eventually contain that index. -/
theorem localUltraSegment_product (n : ℕ) (hn : ∀ᶠ i in F, n ≤ M i) :
    (localUltraAlgebra F G L).Product (List.replicate n (localUltraMk F G u))
      (localUltraMk F G (fun i => (p i).power n)) := by
  have hh := (localUltraProduct_mk_iff F G L (List.replicate n u) (fun i => (p i).power n)).2
    (hn.mono fun i hi => by simpa only [List.map_replicate] using (p i).product n hi)
  simpa only [List.map_replicate] using hh

theorem map_localUltraSegment {H : Type*} [Group H]
    (π : LocalGroupHom (localUltraAlgebra F G L) (LocalGroupAlgebra.ofGroup H))
    (n : ℕ) (hn : ∀ᶠ i in F, n ≤ M i) :
    π.toFun (localUltraMk F G (fun i => (p i).power n)) = (π.toFun (localUltraMk F G u))^n := by
  have hh := (LocalGroupAlgebra.ofGroup_product_iff H _ _).1
    ((localUltraSegment_product F G L u M p n hn).map π)
  simpa only [List.map_replicate,List.prod_replicate] using hh
end DirectedCycles
