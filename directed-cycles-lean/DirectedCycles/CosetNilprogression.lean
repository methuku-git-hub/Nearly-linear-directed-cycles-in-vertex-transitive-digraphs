import DirectedCycles.GeneratorCommutatorNilpotence
import DirectedCycles.AbelianShortGeneration
import Mathlib.Data.List.Count

set_option autoImplicit false
open scoped Pointwise commutatorElement
namespace DirectedCycles

/-- Evaluate a signed word in a generating tuple. -/
def signedWordValue {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) (w : List (Fin r × Bool)) : G :=
  (w.map (fun a => if a.2 then g a.1 else (g a.1)⁻¹)).prod

/-- A global coset nilprogression is described by genuine subgroups,
a generating tuple modulo its finite subgroup, and actual commutator
identities. Nilpotence of the generated quotient is proved below. -/
structure CosetNilprogression (G : Type*) [Group G] (r c : ℕ) where
  U : Subgroup G
  H : Subgroup G
  hHU : H ≤ U
  normal : (H.subgroupOf U).Normal
  generators : Fin r → U
  lengths : Fin r → ℕ
  lengths_pos : ∀ i, 1 ≤ lengths i
  generates : Subgroup.closure ((H.subgroupOf U : Set U) ∪ Set.range generators) = ⊤
  commutators : letI := normal
    ∀ w : CommutatorWord (Fin r), w.weight = c+1 →
      w.eval (fun i => QuotientGroup.mk' (H.subgroupOf U) (generators i)) = 1

namespace CosetNilprogression
variable {G : Type*} [Group G] {r c : ℕ}

instance normalSubgroup (P : CosetNilprogression G r c) : (P.H.subgroupOf P.U).Normal := P.normal

noncomputable def generatorSet (P : CosetNilprogression G r c) : Finset G := by
  classical
  exact Finset.univ.image (fun i => (P.generators i).val)

def carrier (P : CosetNilprogression G r c) : Set G :=
  {z | ∃ h : P.H, ∃ w : List (Fin r × Bool),
    (∀ i, w.countP (fun a => a.1 = i) ≤ P.lengths i) ∧
    h.val * signedWordValue (fun i => (P.generators i).val) w = z}

theorem subgroup_subset_carrier (P : CosetNilprogression G r c) : (P.H : Set G) ⊆ P.carrier := by
  intro h hh
  exact ⟨⟨h,hh⟩,[],by simp,by simp [signedWordValue]⟩

theorem generator_mem_carrier (P : CosetNilprogression G r c) (i : Fin r) :
    (P.generators i).val ∈ P.carrier := by
  refine ⟨1,[(i,true)],?_,?_⟩
  · intro j
    by_cases hij : i = j
    · subst j; simpa using P.lengths_pos i
    · simp [hij]
  · simp [signedWordValue]

theorem generatorSet_subset_carrier (P : CosetNilprogression G r c) :
    (P.generatorSet : Set G) ⊆ P.carrier := by
  classical
  intro g hg
  obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hg
  exact P.generator_mem_carrier i

theorem generatorSet_card_le (P : CosetNilprogression G r c) : P.generatorSet.card ≤ r := by
  classical
  exact (Finset.card_image_le).trans (by simp)

theorem signedWordValue_mem {K : Subgroup G} (g : Fin r → G)
    (hg : ∀ i, g i ∈ K) (w : List (Fin r × Bool)) : signedWordValue g w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons a w ih =>
    change (if a.2 then g a.1 else (g a.1)⁻¹)*signedWordValue g w ∈ K
    apply K.mul_mem _ ih
    split
    · exact hg a.1
    · exact K.inv_mem (hg a.1)

theorem carrier_subset_U (P : CosetNilprogression G r c) : P.carrier ⊆ P.U := by
  rintro z ⟨h,w,_hw,rfl⟩
  exact P.U.mul_mem (P.hHU h.property) (signedWordValue_mem _ (fun i => (P.generators i).property) w)

theorem carrier_subset_generated (P : CosetNilprogression G r c) :
    P.carrier ⊆ Subgroup.closure ((P.H : Set G) ∪ (P.generatorSet : Set G)) := by
  classical
  rintro z ⟨h,w,_hw,rfl⟩
  let N := Subgroup.closure ((P.H : Set G) ∪ (P.generatorSet : Set G))
  apply N.mul_mem (Subgroup.subset_closure (Or.inl h.property))
  apply signedWordValue_mem
  intro i
  exact Subgroup.subset_closure (Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))

theorem quotient_generator_closure (P : CosetNilprogression G r c) :
    Subgroup.closure (Set.range (fun i => QuotientGroup.mk' (P.H.subgroupOf P.U) (P.generators i))) = ⊤ := by
  let q := QuotientGroup.mk' (P.H.subgroupOf P.U)
  have h := image_generators_mod_kernel q (QuotientGroup.mk'_surjective _)
    (P.H.subgroupOf P.U) (by rw [QuotientGroup.ker_mk']) (Set.range P.generators) P.generates
  simpa only [← Set.range_comp'] using h

theorem quotient_nilpotent (P : CosetNilprogression G r c) :
    ∃ _hNil : Group.IsNilpotent (P.U ⧸ P.H.subgroupOf P.U),
      Group.nilpotencyClass (P.U ⧸ P.H.subgroupOf P.U) ≤ c :=
  nilpotent_of_generator_commutator_words _ P.quotient_generator_closure c P.commutators

theorem quotient_rank_le [Finite G] (P : CosetNilprogression G r c) :
    Group.rank (P.U ⧸ P.H.subgroupOf P.U) ≤ r := by
  classical
  let q := QuotientGroup.mk' (P.H.subgroupOf P.U)
  let F := Finset.univ.image (fun i => q (P.generators i))
  have hF : Subgroup.closure (F : Set (P.U ⧸ P.H.subgroupOf P.U)) = ⊤ := by
    simpa only [F,Finset.coe_image,Finset.coe_univ,Set.image_univ] using P.quotient_generator_closure
  exact (Group.rank_le hF).trans ((Finset.card_image_le).trans (by simp))

end CosetNilprogression
end DirectedCycles
