import DirectedCycles.LocalCommutingProducts
import DirectedCycles.LocalPowerSegmentDouble
import DirectedCycles.LocalCommutingPowers

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Two finite power segments, at scales one and m, have the expected
addition table on their rectangular product grid. Carries are proved using
actual segment products and local associativity. -/
theorem power_grid_add {u : G} {m K : ℕ} (p : L.PowerSegment u m)
    (q : L.PowerSegment (p.power m) K) (hm : 1 ≤ m) {A : Set G} (hA : L.one ∈ A)
    (hpA : ∀ n ≤ m, p.power n ∈ A) (hqA : ∀ n ≤ K, q.power n ∈ A)
    (hdom : L.AllProductsDefined A 4) (F : ℕ → ℕ → G)
    (hF : ∀ i ≤ K, ∀ r ≤ m, L.mulRel (q.power i) (p.power r) (F i r)) :
    (∀ i j r s, i+j ≤ K → r+s < m →
      L.mulRel (F i r) (F j s) (F (i+j) (r+s))) ∧
    (∀ i j r s, i+j+1 ≤ K → r < m → s < m → m ≤ r+s →
      L.mulRel (F i r) (F j s) (F (i+j+1) (r+s-m))) := by
  obtain ⟨d,hd,_⟩ := p.exists_double L hm hA hpA hdom
  have hcomm : ∀ r ≤ m, ∀ j ≤ K, L.Commute (p.power r) (q.power j) := by
    intro r hr j hj
    have hrm := d.add (n := r) (m := m) (by omega)
    have hmr := d.add (n := m) (m := r) (by omega)
    rw [hd r hr,hd m le_rfl] at hrm hmr
    rw [Nat.add_comm m r] at hmr
    have hbase : L.Commute (p.power r) (p.power m) := ⟨d.power (r+m),hrm,hmr⟩
    exact q.commute L (hdom.mono L (Set.Subset.refl _) (by omega : 3 ≤ 4))
      (hpA m le_rfl) (hpA r hr) hbase hqA j hj
  constructor
  · intro i j r s hij hrs
    obtain ⟨z,hz,hz'⟩ := L.commuting_products hdom (hqA i (by omega)) (hpA r (by omega))
      (hqA j (by omega)) (hpA s (by omega)) (hcomm r (by omega) j (by omega))
      (hF i (by omega) r (by omega)) (hF j (by omega) s (by omega)) (q.add hij) (p.add (by omega))
    have he : z = F (i+j) (r+s) := L.unique hz' (hF (i+j) hij (r+s) (by omega))
    exact he ▸ hz
  · intro i j r s hij hr hs hrs
    have hps := d.add (n := r) (m := s) (by omega)
    rw [hd r hr.le,hd s hs.le] at hps
    obtain ⟨z,hz,hz'⟩ := L.commuting_products hdom (hqA i (by omega)) (hpA r hr.le)
      (hqA j (by omega)) (hpA s hs.le) (hcomm r hr.le j (by omega))
      (hF i (by omega) r hr.le) (hF j (by omega) s hs.le) (q.add (by omega)) hps
    have hcarry : L.mulRel (p.power m) (p.power (r+s-m)) (d.power (r+s)) := by
      have hh := d.add (n := m) (m := r+s-m) (by omega)
      rw [hd m le_rfl,hd (r+s-m) (by omega),show m+(r+s-m)=r+s by omega] at hh
      exact hh
    have hstep : L.mulRel (q.power (i+j)) (p.power m) (q.power (i+j+1)) := by
      simpa only [q.one (by omega)] using q.add (n := i+j) (m := 1) hij
    have he : F (i+j+1) (r+s-m) = z :=
      L.assoc hstep hcarry (hF (i+j+1) hij (r+s-m) (by omega)) hz'
    exact he.symm ▸ hz
end LocalGroupAlgebra
end DirectedCycles
