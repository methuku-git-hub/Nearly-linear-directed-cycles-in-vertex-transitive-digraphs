import DirectedCycles.GlobalProgressionFromLocalLaws

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- Local word, properness and ambient commutator data in a genuine finite
group produce the exact global coset-nilprogression carrier and density
required downstream. The kernel is the actual trivial subgroup. -/
theorem global_progression_of_local_data {G : Type*} [Group G] [Finite G]
    {r c : ℕ} (g : Fin r → G) (N : Fin r → ℕ) (hN : ∀ i, 1 ≤ N i)
    (A : Set G) (hw : (LocalGroupAlgebra.ofGroup G).SignedWordsIn g N A)
    (hproper : Function.Injective ((LocalGroupAlgebra.ofGroup G).orderedGrid hw))
    (hvanish : ∀ x, (LocalGroupAlgebra.ofGroup G).GeneratorCommutators (Set.range g) c x → x = 1)
    (a J : ℕ) (hdensity : a ≤ J * ∏ i, (2*N i+1)) :
    ∃ P : CosetNilprogression G r c, P.carrier ⊆ A ∧ a ≤ J*Nat.card P.carrier := by
  classical
  let L := LocalGroupAlgebra.ofGroup G
  let P := nilprogressionOfAmbientCommutators g N hN hvanish
  have hcarrier : P.carrier = L.wordProgression g N :=
    nilprogressionOfAmbientCommutators_carrier g N hN hvanish
  have hsub : P.carrier ⊆ A := by
    rw [hcarrier]
    rintro x ⟨w,hw',hp⟩
    obtain ⟨y,hy,hpy⟩ := hw w hw'
    exact (hp.unique L hpy).symm ▸ hy
  let f : SignedCoordinates N → P.carrier := fun k =>
    ⟨(L.orderedGrid hw k).val,hcarrier.symm ▸ L.orderedGrid_mem_progression hw k⟩
  have hf : Function.Injective f := by
    intro k l he
    apply hproper
    apply Subtype.ext
    exact congrArg (fun t : P.carrier => t.val) he
  have hcard : (∏ i, (2*N i+1)) ≤ Nat.card P.carrier := by
    have hh := Nat.card_le_card_of_injective f hf
    simpa only [Nat.card_eq_fintype_card,signedCoordinates_card] using hh
  exact ⟨P,hsub,hdensity.trans (Nat.mul_le_mul_left J hcard)⟩
end DirectedCycles
