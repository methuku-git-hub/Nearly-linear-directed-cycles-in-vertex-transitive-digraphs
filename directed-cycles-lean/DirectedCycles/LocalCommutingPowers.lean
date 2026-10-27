module

public import DirectedCycles.LocalMinimalEscape
public import DirectedCycles.LocalSignedProgression
public import DirectedCycles.LocalPowerSegment
public import DirectedCycles.LocalTripleProducts
public import DirectedCycles.LocalDivision

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Local commutation is symmetric, including its domain witnesses. -/
theorem Commute.symm {x y : G} (h : L.Commute x y) : L.Commute y x := by
  obtain ⟨z,hxy,hyx⟩ := h
  exact ⟨z,hyx,hxy⟩

/-- Commutation propagates along a genuine finite power segment. All three
associativity comparisons are supplied by the actual three-letter domain. -/
theorem PowerSegment.commute {A : Set G}
    (hdom : L.AllProductsDefined A 3) {u x : G} (hu : u ∈ A) (hx : x ∈ A)
    (hxu : L.Commute x u) {N : ℕ} (p : L.PowerSegment u N)
    (hmem : ∀ n ≤ N, p.power n ∈ A) :
    ∀ n ≤ N, L.Commute x (p.power n) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [p.zero]
    exact ⟨x,L.mul_one x,L.one_mul x⟩
  | succ n ih =>
    intro hn
    obtain ⟨z,hxz,hzx⟩ := ih (by omega)
    obtain ⟨v,hxu',hux⟩ := hxu
    have hpu : L.mulRel (p.power n) u (p.power (n+1)) := by
      simpa only [p.one (by omega)] using p.add (n := n) (m := 1) hn
    obtain ⟨a,hzu,hxpu⟩ := hdom.triple L hx (hmem n (by omega)) hu hxz hpu
    obtain ⟨b,hzu',hpnv⟩ := hdom.triple L (hmem n (by omega)) hx hu hzx hxu'
    obtain ⟨c,hpux,hpnv'⟩ := hdom.triple L (hmem n (by omega)) hu hx hpu hux
    have hab : a = b := L.unique hzu hzu'
    have hbc : b = c := L.unique hpnv hpnv'
    exact ⟨a,hxpu,(hab.trans hbc).symm ▸ hpux⟩

/-- Commutation with an inverse is obtained by actual division and a
three-letter associativity comparison, so no inverse-product domain is assumed. -/
theorem Commute.inv_right (hd : L.DivisionClosed) {A : Set G}
    (hdom : L.AllProductsDefined A 3) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) (hyi : L.inv y ∈ A)
    (hxy : L.Commute x y) : L.Commute x (L.inv y) := by
  obtain ⟨z,hxz,hyz⟩ := hxy
  obtain ⟨v,hv⟩ := hdom [L.inv y,x] (by simp) (by aesop)
  have hix : L.mulRel (L.inv y) x v := (Product.pair_iff L _ _ _).1 hv
  obtain ⟨w,hwy,hiyz⟩ := hdom.triple L hyi hx hy hix hxz
  have he : w = x := L.inverse_cancel_left hyz hiyz
  have hvy : L.mulRel v y x := he ▸ hwy
  have hxiy : L.mulRel x (L.inv y) v := hd.right hvy
  exact ⟨v,hxiy,hix⟩
/-- Every signed power commutes locally once its generator commutes and
all relevant three-letter domains are available. -/
theorem PowerSegment.commute_signedProgression (hd : L.DivisionClosed) {A : Set G}
    (hi : ∀ y ∈ A, L.inv y ∈ A) (hdom : L.AllProductsDefined A 3)
    {u x : G} (hu : u ∈ A) (hx : x ∈ A) (hxu : L.Commute x u)
    {N : ℕ} (p : L.PowerSegment u N) (hmem : ∀ n ≤ N, p.power n ∈ A) :
    ∀ y ∈ p.signedProgression L, L.Commute x y := by
  intro y hy
  obtain ⟨i,rfl⟩ := (p.mem_signedProgression L y).1 hy
  cases i with
  | inl i => exact p.commute L hdom hu hx hxu hmem i.val (by omega)
  | inr i =>
    exact Commute.inv_right L hd hdom hx (hmem (i.val+1) (by omega))
      (hi _ (hmem (i.val+1) (by omega))) (p.commute L hdom hu hx hxu hmem (i.val+1) (by omega))
end LocalGroupAlgebra
end DirectedCycles
