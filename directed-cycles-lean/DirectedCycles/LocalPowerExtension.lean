module

public import DirectedCycles.LocalPowerSegment
public import DirectedCycles.LocalProductSplits

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A bounded power segment inside a set with ambient binary products extends
by one genuinely all-bracketings product. Its new value need not stay in the
set. The proof compares every split by defined local associativity. -/
theorem PowerSegment.extend_product {g : G} {N : ℕ} {B : Set G}
    (p : L.PowerSegment g N) (hp : ∀ n ≤ N, p.power n ∈ B) (hg : g ∈ B)
    (hB : ∀ x ∈ B, ∀ y ∈ B, L.Defined x y) :
    ∃ z, L.Product (List.replicate (N+1) g) z := by
  by_cases hN : N = 0
  · subst N
    exact ⟨g,Product.singleton g⟩
  obtain ⟨z,hz⟩ := hB g hg (p.power N) (hp N le_rfl)
  refine ⟨z,(L.product_iff_finite_splits (by simp; omega)).2 ?_⟩
  intro k hk hk'
  simp only [List.length_replicate] at hk'
  have hkN : k.val ≤ N := by omega
  let m := N+1-k.val
  have hmN : m ≤ N := by dsimp [m]; omega
  have hs : (k.val-1)+m = N := by dsimp [m]; omega
  have hab : L.mulRel g (p.power (k.val-1)) (p.power k.val) := by
    have hh := p.add (n := 1) (m := k.val-1) (by omega)
    rw [p.one (by omega),show 1+(k.val-1)=k.val by omega] at hh
    exact hh
  have hbc : L.mulRel (p.power (k.val-1)) (p.power m) (p.power N) := by
    simpa only [hs] using p.add (n := k.val-1) (m := m) (by omega)
  obtain ⟨v,hv⟩ := hB (p.power k.val) (hp k.val hkN) (p.power m) (hp m hmN)
  have he : v = z := L.assoc hab hbc hv hz
  refine ⟨p.power k.val,p.power m,?_,?_,he ▸ hv⟩
  · simpa only [List.take_replicate,Nat.min_eq_left (show k.val ≤ N+1 by omega)] using p.product k.val hkN
  · simpa only [List.drop_replicate,m] using p.product m hmN
end LocalGroupAlgebra
end DirectedCycles
