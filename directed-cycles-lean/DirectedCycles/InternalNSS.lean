import DirectedCycles.UltraproductSubgroups
import DirectedCycles.InternalSetLogic

set_option autoImplicit false
open Filter
namespace DirectedCycles

/-- NSS means absence of nontrivial internal subgroups, not absence of arbitrary
external subgroups of the ultraproduct. -/
def InternalNSS {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Set (G i)) : Prop :=
  ∀ H : ∀ i, Subgroup (G i),
    (ultraSubgroup f G H : Set (GroupUltraproduct f G)) ⊆ ultraSet f G A →
      ultraSubgroup f G H = ⊥

/-- The exact internal NSS conclusion from componentwise cyclic NSS. -/
theorem internal_nss_of_components {ι : Type*} (u : Ultrafilter ι) (G : ι → Type*)
    [∀ i, Group (G i)] (A : ∀ i, Set (G i))
    (hA : ∀ᶠ i in (u : Filter ι), ∀ g : G i, (∀ n : ℕ, g^n ∈ A i) → g = 1) :
    InternalNSS (u : Filter ι) G A := by
  intro H hH
  have hsub : ∀ᶠ i in (u : Filter ι), (H i : Set (G i)) ⊆ A i :=
    (ultraSet_subset_iff_eventually u G (fun i => (H i : Set (G i))) A).1 hH
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y,rfl⟩ := ultraMk_surjective (u : Filter ι) G x
  have hy := (mem_ultraSubgroup_iff (u : Filter ι) G H y).1 hx
  have he : ∀ᶠ i in (u : Filter ι), y i = 1 := by
    filter_upwards [hA,hsub,hy] with i hAi hHi hyi
    exact hAi (y i) (fun n => hHi ((H i).pow_mem hyi n))
  have hq : ultraMk (u : Filter ι) G y = ultraMk (u : Filter ι) G 1 :=
    (ultraMk_eq_iff _ G y 1).2 he
  simpa using hq
end DirectedCycles
