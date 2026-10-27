module

public import DirectedCycles.LocalCentralComponentNeighbourhood
public import DirectedCycles.LocalToLocalCentralModelNeighbourhood

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
local notation "Du" => ultraproduct U G L P D

variable {H : Type*} {M : LocalGroupAlgebra H} {Q : Set H} (T : M.CentralQuotientData Q)
    (hM : M.DivisionClosed)

include hM in
/-- The same finite projected sets inherit small and thick neighbourhoods
under the actual component quotient model. -/
theorem localComponentModel_neighbourhood
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) M)
    (hPQ : ∀ p ∈ localUltraSet (U : Filter ι) G P, π.toFun p ∈ Q)
    (hDW : ∀ x ∈ (Du).small, π.toFun x ∈ T.small)
    (hQP : Q ⊆ π.toFun '' localUltraSet (U : Filter ι) G P)
    (hPi : ∀ i, ∀ p ∈ P i, (L i).inv p ∈ P i)
    (A B : ∀ i, Finset (G i))
    (hPA : ∀ i, P i ⊆ A i) (hDA : ∀ i, (D i).small ⊆ A i)
    (hAi : ∀ i, ∀ x ∈ A i, (L i).inv x ∈ A i)
    (hdom : ∀ i, (L i).AllProductsDefined (A i : Set (G i)) 2)
    (hBD : ∀ i, (B i : Set (G i)) ⊆ (D i).small) (V : Set H)
    (hsmall : ∀ x, π.toFun x ∈ V → x ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))
    (hthick : ∀ v ∈ V, ∃ x, π.toFun x = v) :
    let Ψ := ((Du).localModelQuotientHom T π hPQ hDW).comp (quotientUltraHom U G L P D hd hr)
    let Vq := T.project '' {v : T.small | v.val ∈ V}
    Ψ.toFun ⁻¹' Vq ⊆ localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
      (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)) ∧
    Vq ⊆ Ψ.toFun '' localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
      (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)) := by
  intro Ψ Vq
  have hAi' := localUltraWindow_inv_mem (U : Filter ι) G L (fun i => (A i : Set (G i))) hAi
  have hPi' := localUltraWindow_inv_mem (U : Filter ι) G L P hPi
  have hPA' := (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) P _).2 (Filter.Eventually.of_forall hPA)
  have hDA' := (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) (fun i => (D i).small) _).2
    (Filter.Eventually.of_forall hDA)
  have hBD' := (localUltraSet_subset_iff_eventually U G (fun i => (L i).one) _ (fun i => (D i).small)).2
    (Filter.Eventually.of_forall hBD)
  have hdom' := (localUltra_allProductsDefined_iff U G L (fun i => (A i : Set (G i))) 2).2
    (Filter.Eventually.of_forall hdom)
  have hbinary : ∀ x ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      ∀ y ∈ localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))),
      (localUltraAlgebra (U : Filter ι) G L).Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hdom' [x,y] (by simp) (by aesop)
    exact ⟨z,(Product.pair_iff _ x y z).1 hz⟩
  have h := (Du).localModelQuotientHom_neighbourhood T
    (localUltraAlgebra_divisionClosed (U : Filter ι) G L hd) hM π hPQ hDW hQP hPi'
    (localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i))))
    (localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))
    hPA' hDA' hAi' hbinary hBD' V hsmall hthick
  have he := quotientUltraEquiv_finiteImage U G L P D B
  constructor
  · intro y hy
    have hm := @h.1 (quotientUltraEquiv U G L P D y) hy
    rw [← he] at hm
    obtain ⟨z,hz,heq⟩ := hm
    have hz' : z = y := (quotientUltraEquiv U G L P D).injective heq
    exact hz' ▸ hz
  · intro v hv
    obtain ⟨y,hy,hπy⟩ := h.2 hv
    rw [← he] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact ⟨z,hz,hπy⟩
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
