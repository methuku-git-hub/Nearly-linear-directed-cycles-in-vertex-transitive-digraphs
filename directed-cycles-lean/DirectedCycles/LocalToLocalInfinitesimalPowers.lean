module

public import DirectedCycles.LocalSignedPowerProducts
public import DirectedCycles.LocalPowerSegmentMaps
public import DirectedCycles.LocalPowerSequence
public import DirectedCycles.LocalInternalSetLogic
public import DirectedCycles.InfinitesimalScaledPowers

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- A signed exponent negligible relative to the first exit is killed by an
NSS model. Each standard power is constructed inside the component segment,
then mapped to the target; no global source powers are used. -/
theorem local_to_local_map_infinitesimal_signed_power {H : Type*} (Q : LocalGroupAlgebra H)
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N M : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i)) (k : ι → ℤ)
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i ∧ N i ≤ M i)
    (hi : ∀ᶠ i in (U : Filter ι), ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι), |(k i : ℝ)/(N i : ℝ)| < ε)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H) (hNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V) :
    π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (k i))) = Q.one := by
  let a := π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (k i)))
  let f : ℕ → H := fun n => π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (k i*(n : ℤ))))
  have hall : ∀ n : ℕ, Q.Product (List.replicate n a) (f n) ∧ f n ∈ V := by
    intro n
    have hbound : ∀ᶠ i in (U : Filter ι), (k i*(n : ℤ)).natAbs < N i ∧ (k i).natAbs*n ≤ M i := by
      filter_upwards [hN,hsmall (1/((n : ℝ)+1)) (by positivity)] with i hNi hsi
      have hh := natAbs_mul_lt_of_ratio (k i) (N i) n hNi.1 hsi
      refine ⟨hh,?_⟩
      simp only [Int.natAbs_mul,Int.natAbs_natCast] at hh
      omega
    have hp : (localUltraAlgebra (U : Filter ι) G L).Product
        (List.replicate n (localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (k i))))
        (localUltraMk (U : Filter ι) G (fun i => (p i).signedPower (k i*(n : ℤ)))) := by
      have hh := (localUltraProduct_mk_iff (U : Filter ι) G L
        (List.replicate n (fun i => (p i).signedPower (k i)))
        (fun i => (p i).signedPower (k i*(n : ℤ)))).2
        (hbound.mono fun i hi => by
          simpa only [List.map_replicate] using (p i).signedPower_product (hd i) (hr i) (k i) n hi.2)
      simpa only [List.map_replicate] using hh
    refine ⟨by simpa only [a,f,List.map_replicate] using hp.map π,?_⟩
    apply himage
    apply (localUltraMk_mem_iff (U : Filter ι) G A _).2
    filter_upwards [hbound,hi,hprev] with i hbi hii hpi
    dsimp only [LocalGroupAlgebra.PowerSegment.signedPower]
    split_ifs
    · exact hpi _ hbi.1
    · exact hii _ (hpi _ hbi.1)
  let q : Q.PowerSequence a := ⟨f,fun n => (hall n).1⟩
  exact hNSS a q (fun n => (hall n).2)
end DirectedCycles
