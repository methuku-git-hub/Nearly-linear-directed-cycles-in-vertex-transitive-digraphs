module

public import DirectedCycles.CosetNilprogression
public import DirectedCycles.LeftGeneratorCommutators

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- The final global coset-nilprogression record can be constructed from
left-associated generator laws alone. All binary commutator laws in the
record are derived through the global nilpotency-class bound. -/
def cosetNilprogressionOfLeftCommutators {G : Type*} [Group G] {r c : ℕ}
    (U H : Subgroup G) (hHU : H ≤ U) (hNormal : (H.subgroupOf U).Normal)
    (g : Fin r → U) (N : Fin r → ℕ) (hN : ∀ i, 1 ≤ N i)
    (hgen : Subgroup.closure ((H.subgroupOf U : Set U) ∪ Set.range g) = ⊤)
    (hleft : letI := hNormal
      ∀ i : Fin r, ∀ l : List (Fin r), l.length = c →
        leftGeneratorCommutator (fun j => QuotientGroup.mk' (H.subgroupOf U) (g j)) i l = 1) :
    CosetNilprogression G r c := by
  letI := hNormal
  let q := QuotientGroup.mk' (H.subgroupOf U)
  have hqgen : Subgroup.closure (Set.range (fun j => q (g j))) = ⊤ := by
    have h := image_generators_mod_kernel q (QuotientGroup.mk'_surjective _)
      (H.subgroupOf U) (by rw [QuotientGroup.ker_mk']) (Set.range g) hgen
    simpa only [← Set.range_comp'] using h
  refine ⟨U,H,hHU,hNormal,g,N,hN,hgen,?_⟩
  obtain ⟨hNil,hclass⟩ := nilpotent_of_left_generator_commutators (fun j => q (g j)) hqgen c hleft
  let := hNil
  exact fun w hw => w.eval_eq_one_of_class_lt (fun j => q (g j)) c hclass (by omega)
end DirectedCycles
