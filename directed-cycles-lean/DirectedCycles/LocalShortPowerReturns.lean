module

public import DirectedCycles.LocalPowerMultiples
public import DirectedCycles.LocalPowerSegmentCompression
public import DirectedCycles.LocalWordPowerIteration

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A first exiting power cannot have a later short-segment endpoint with
all prescribed powers back in A. The two-scale power grid supplies every
power needed by trapping, inside A^4. -/
theorem no_short_segment_return {A : Set G} (hA : L.one ∈ A)
    (hdom : L.AllProductsDefined A 8) (C : ℕ) (hC : 1 ≤ C)
    (htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn (L.wordPower A 4) x j) → x ∈ A)
    {u : G} {m N : ℕ} (p : L.PowerSegment u m) (hN : 0 < N) (hNm : N ≤ m)
    (hp : ∀ n ≤ m, p.power n ∈ L.wordPower A 2) (hexit : p.power N ∉ A)
    (hreturn : ∀ j ≤ C, L.PowerIn A (p.power m) j) : False := by
  let q := L.powerSegmentOfPowerIn hreturn
  have hA2 : L.one ∈ L.wordPower A 2 :=
    ⟨[L.one,L.one],rfl,by simp only [List.mem_cons,List.not_mem_nil,or_false]; aesop,
      (Product.pair_iff L _ _ _).2 (L.one_mul L.one)⟩
  have hsub : A ⊆ L.wordPower A 2 := by
    intro x hx
    apply L.wordPower_subset_wordPower hA hdom (by omega : 1 ≤ 2) (by omega)
    simpa only [L.wordPower_one] using hx
  obtain ⟨s,hsp,_,hsA⟩ := p.exists_multiples L q (by omega) hC hA2 hp
    (fun j hj => hsub (L.powerSegmentOfPowerIn_mem hreturn hj))
    (hdom.wordPower L (by omega : 2*4 ≤ 8))
  apply hexit
  apply htrap
  intro j _ hj
  have hNC : N ≤ m*C := by nlinarith
  have hjN : j*N ≤ m*C := by nlinarith
  have hprod := s.product_power L hNC hjN
  rw [hsp N hNm] at hprod
  exact ⟨s.power (j*N),L.wordPower_wordPower_subset hdom 2 2 (by omega) (hsA (j*N) hjN),hprod⟩
end LocalGroupAlgebra
end DirectedCycles
