import DirectedCycles.LocalSignedPowers
import DirectedCycles.LocalCommutingPowers
import DirectedCycles.LocalGroupHom

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Only the initial segment through the chosen signed index is needed to
propagate commutation. No later power is presumed to remain in A. -/
theorem PowerSegment.commute_signedPower (hd : L.DivisionClosed) {A : Set G}
    (hi : ∀ y ∈ A, L.inv y ∈ A) (hdom : L.AllProductsDefined A 3)
    {u x : G} (hu : u ∈ A) (hx : x ∈ A) (hxu : L.Commute x u)
    {N : ℕ} (p : L.PowerSegment u N) (k : ℤ) (hk : k.natAbs ≤ N)
    (hmem : ∀ n ≤ k.natAbs, p.power n ∈ A) : L.Commute x (p.signedPower k) := by
  let q : L.PowerSegment u k.natAbs := ⟨p.power,fun n hn => p.product n (hn.trans hk)⟩
  have hc : L.Commute x (p.power k.natAbs) := q.commute L hdom hu hx hxu hmem _ le_rfl
  dsimp only [PowerSegment.signedPower]
  split_ifs
  · exact hc
  · exact Commute.inv_right L hd hdom hx (hmem _ le_rfl) (hi _ (hmem _ le_rfl)) hc

theorem Commute.map {H : Type*} [Group H] (π : LocalGroupHom L (ofGroup H))
    {x y : G} (h : L.Commute x y) : _root_.Commute (π.toFun x) (π.toFun y) := by
  obtain ⟨z,hxy,hyx⟩ := h
  exact (π.map_mul hxy).trans (π.map_mul hyx).symm
end LocalGroupAlgebra

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Actual local commutation transfers with both multiplication domains. -/
theorem localUltraCommute_mk (a b : ∀ i, G i)
    (h : ∀ᶠ i in (U : Filter ι), (L i).Commute (a i) (b i)) :
    (localUltraAlgebra (U : Filter ι) G L).Commute (localUltraMk (U : Filter ι) G a)
      (localUltraMk (U : Filter ι) G b) := by
  classical
  let c : ∀ i, G i := fun i => if hi : (L i).Commute (a i) (b i) then Classical.choose hi else (L i).one
  have hc : ∀ᶠ i in (U : Filter ι), (L i).mulRel (a i) (b i) (c i) ∧ (L i).mulRel (b i) (a i) (c i) := by
    filter_upwards [h] with i hi
    dsimp only [c]
    rw [dite_eq_left hi]
    exact Classical.choose_spec hi
  exact ⟨localUltraMk (U : Filter ι) G c,
    (localUltraMulRel_mk_iff _ G L a b c).2 (hc.mono fun _ hi => hi.1),
    (localUltraMulRel_mk_iff _ G L b a c).2 (hc.mono fun _ hi => hi.2)⟩
end DirectedCycles
