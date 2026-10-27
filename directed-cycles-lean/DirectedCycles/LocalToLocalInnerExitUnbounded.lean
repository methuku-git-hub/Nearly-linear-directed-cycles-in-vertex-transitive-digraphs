module

public import DirectedCycles.LocalToLocalInfinitesimalGenerator
public import DirectedCycles.LocalZeroEscapeSubgroup

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Unbounded outer first-exit times force unbounded inner first-exit times
whenever the inner set contains the model kernel. Fixed powers map to the
identity, and all their actual finite domains are supplied by the outer segment. -/
theorem local_to_local_inner_first_exit_unbounded {H : Type*} (Q : LocalGroupAlgebra H)
    (A B : ∀ i, Set (G i)) (u : ∀ i, G i) (N M K J : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (M i))
    (q : ∀ i, (L i).PowerSegment (u i) (J i))
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hM : ∀ᶠ i in (U : Filter ι), N i ≤ M i)
    (hJ : ∀ᶠ i in (U : Filter ι), K i ≤ J i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (p i).power n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (q i).power (K i) ∉ B i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H) (hNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    (hkernel : ∀ z, π.toFun z = Q.one → z ∈ localUltraSet (U : Filter ι) G B) :
    ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < K i := by
  have hkill := local_to_local_model_kills_generator U G L Q A u N M p hN hM hprev π V hNSS himage
  have hpB : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), (p i).power n ∈ B i := by
    intro n
    have hn : ∀ᶠ i in (U : Filter ι), n ≤ M i := by
      filter_upwards [hN n,hM] with i hni hmi
      omega
    have hpmap : Q.Product (List.replicate n Q.one)
        (π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).power n))) := by
      simpa only [List.map_replicate,hkill] using
        (localUltraSegment_product (U : Filter ι) G L u M p n hn).map π
    have he := hpmap.unique Q (Q.product_replicate_one n)
    exact (localUltraMk_mem_iff (U : Filter ι) G B _).1 (hkernel _ he)
  intro n
  have hall : ∀ᶠ i in (U : Filter ι), ∀ j : Fin (n+1), (p i).power j.val ∈ B i :=
    Filter.eventually_all.mpr (fun j => hpB j.val)
  filter_upwards [hall,hN n,hM,hJ,hexit] with i halli hni hmi hji hei
  by_contra hh
  have hki : K i ≤ n := le_of_not_gt hh
  have he := ((p i).product (K i) (by omega)).unique (L i) ((q i).product (K i) hji)
  exact hei (he ▸ halli ⟨K i,by omega⟩)
end DirectedCycles
