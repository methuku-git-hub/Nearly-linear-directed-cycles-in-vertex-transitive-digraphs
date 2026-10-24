import DirectedCycles.LocalShortPowerReturns
import DirectedCycles.LocalSignedProgressionProducts

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- The proper signed progression is closed under local multiplication when
the result lies in a region with sufficiently many powers in A. The proof
constructs the candidate longer power segment and rules out a short return. -/
theorem PowerSegment.signedProgression_mul_mem (hd : L.DivisionClosed) (hr : L.Reversible)
    {A : Set G} (hA : L.one ∈ A) (hi : ∀ x ∈ A, L.inv x ∈ A)
    (hdom : L.AllProductsDefined A 8) (C : ℕ) (hC : 1 ≤ C)
    (htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn (L.wordPower A 4) x j) → x ∈ A)
    {u : G} {N : ℕ} (p : L.PowerSegment u N) (hN : 1 ≤ N)
    (hmem : ∀ n ≤ N, p.power n ∈ A)
    (hexit : ∀ z, L.Product (List.replicate (N+1) u) z → z ∉ A)
    {x y z : G} (hx : x ∈ p.signedProgression L) (hy : y ∈ p.signedProgression L)
    (hm : L.mulRel x y z) (hreturn : ∀ j ≤ C, L.PowerIn A z j) :
    z ∈ p.signedProgression L := by
  obtain ⟨d,hdp,hdA⟩ := p.exists_double L hN hA hmem
    (hdom.mono L (Set.Subset.refl _) (by omega : 4 ≤ 8))
  obtain ⟨t,ht,he⟩ := p.signed_product_in_double L hd hr d hdp hx hy hm
  have hsmall : t ≤ N := by
    by_contra h
    have hNt : N+1 ≤ t := by omega
    let s : L.PowerSegment u t := ⟨d.power,fun n hn => d.product n (by omega)⟩
    apply L.no_short_segment_return hA hdom C hC htrap s (N := N+1) (by omega) hNt
      (fun n hn => hdA n (by omega)) (hexit _ (d.product (N+1) (by omega)))
    intro j hj
    rcases he with he | he
    · simpa only [he] using hreturn j hj
    · exact (L.powerIn_inv_iff hr hi (d.power t) j).1 (by simpa only [he] using hreturn j hj)
  rcases he with he | he
  · rw [he,hdp t hsmall]
    exact p.power_mem_signedProgression L hsmall
  · rw [he,hdp t hsmall]
    exact p.inv_power_mem_signedProgression L hsmall
end LocalGroupAlgebra
end DirectedCycles
