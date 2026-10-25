module

public import DirectedCycles.LocalGeneratorCommutatorRestriction
public import DirectedCycles.LocalGeneratorCommutatorIdentity

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {G : Type*} {L : LocalGroupAlgebra G} {P : Set G} (D : L.CentralQuotientData P)

/-- The central quotient commutator step holds in the ambient local group
once the actual signed-word budget is large enough to construct every
restricted intermediate product. -/
theorem ambient_generatorCommutators_central_step (hr : L.Reversible)
    {r : ℕ} (g : Fin r → D.small) (N : Fin r → ℕ)
    (hwords : L.SignedWordsIn (fun i => (g i).val) N D.small)
    (c : ℕ) (hbudget : ∀ i, 4^(c+2) ≤ N i)
    (hcentral : ∀ p ∈ P, ∀ i, L.Commute p (g i).val)
    (hquot : ∀ x, D.algebra.GeneratorCommutators (Set.range (fun i => D.project (g i))) c x →
      x = D.algebra.one) :
    ∀ x, L.GeneratorCommutators (Set.range (fun i => (g i).val)) (c+1) x → x = L.one := by
  intro x hx
  obtain ⟨y,hy,hym⟩ := L.generatorCommutators_restrict hr D.small D.one_mem D.inv_mem g N hwords
    (c+1) hbudget (c+1) le_rfl x hx
  have he := D.generatorCommutators_central_step hr (Set.range g)
    (fun p hp y hy => by obtain ⟨i,rfl⟩ := hy; exact hcentral p hp i) c
    (fun z hz => by
      apply hquot z
      simpa only [← Set.range_comp'] using hz) y hym
  have hev := congrArg (fun t : D.small => t.val) he
  exact hy.symm.trans hev

/-- Quotient nilpotence of the prefix also controls an appended generator
whose actual image is the identity. -/
theorem quotient_prefix_commutators_vanish (hr : L.Reversible)
    {r : ℕ} (v : Fin (r+1) → D.small) (g : Fin r → D.Carrier)
    (hprefix : ∀ i, D.project (v i.castSucc) = g i)
    (hlast : D.project (v (Fin.last r)) = D.algebra.one)
    (c : ℕ) (hc : ∀ x, D.algebra.GeneratorCommutators (Set.range g) c x → x = D.algebra.one) :
    ∀ x, D.algebra.GeneratorCommutators (Set.range (fun i => D.project (v i))) c x →
      x = D.algebra.one := by
  have hsub : Set.range (fun i => D.project (v i)) ⊆ insert D.algebra.one (Set.range g) := by
    rintro _ ⟨i,rfl⟩
    induction i using Fin.lastCases with
    | last => exact Or.inl hlast
    | cast i => exact Or.inr ⟨i,(hprefix i).symm⟩
  intro x hx
  exact D.algebra.generatorCommutators_vanish_insert_one (D.algebra_reversible hr) c hc x (hx.mono D.algebra hsub)
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
