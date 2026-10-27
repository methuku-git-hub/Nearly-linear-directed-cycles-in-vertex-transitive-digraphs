module

public import DirectedCycles.AugmentationPowerSpan
public import DirectedCycles.CocycleExtension

@[expose] public section

set_option autoImplicit false
open scoped MonoidAlgebra
namespace DirectedCycles

@[simp] theorem cocycle_extension_one {G A : Type*} [Group G] [AddCommGroup A]
    {T : G →* Module.End ℤ A} {f : G → A} (hf : IsAdditiveCocycle T f) :
    groupRingAdditiveExtension f 1 = 0 := by
  rw [← map_one (MonoidAlgebra.of ℤ G),groupRingAdditiveExtension_of,cocycle_one hf]

theorem augmentation_groupDifferenceWord {G : Type*} [Group G]
    (gs : List G) (hne : gs ≠ []) : augmentation G (groupDifferenceWord gs) = 0 := by
  cases gs with
  | nil => exact (hne rfl).elim
  | cons g gs =>
    change augmentation G ((MonoidAlgebra.of ℤ G g - 1) * groupDifferenceWord gs) = 0
    rw [map_mul,map_sub,augmentation_of,map_one,sub_self,zero_mul]

/-- The exact ordered cocycle-difference identity in the integral group ring. -/
theorem cocycle_extension_difference_word {G A : Type*} [Group G] [AddCommGroup A]
    {T : G →* Module.End ℤ A} {f : G → A} (hf : IsAdditiveCocycle T f)
    (gs : List G) (g : G) :
    groupRingAdditiveExtension f (groupDifferenceWord (gs++[g])) =
      (gs.map (fun x => T x-1)).prod (f g) := by
  induction gs with
  | nil =>
    simp only [List.nil_append,groupDifferenceWord,List.map_singleton,List.prod_singleton,
      map_sub,groupRingAdditiveExtension_of,cocycle_extension_one hf,sub_zero,
      List.map_nil,List.prod_nil,Module.End.one_apply]
  | cons h gs ih =>
    change groupRingAdditiveExtension f
      ((MonoidAlgebra.of ℤ G h-1)*groupDifferenceWord (gs++[g])) = _
    rw [cocycle_extension_difference hf h _
      (augmentation_groupDifferenceWord _ (by simp)),ih]
    rfl

/-- Nilpotent iterated action differences force the cocycle extension to
vanish on the actual augmentation-ideal power. -/
theorem cocycle_extension_kills_power {G A : Type*} [Group G] [AddCommGroup A]
    {T : G →* Module.End ℤ A} {f : G → A} (hf : IsAdditiveCocycle T f)
    (n : ℕ) (hnil : ∀ gs : List G, gs.length = n → ∀ g : G,
      (gs.map (fun x => T x-1)).prod (f g) = 0) :
    ∀ x ∈ augmentationIdeal G ^ (n+1), groupRingAdditiveExtension f x = 0 := by
  have hle : (augmentationIdeal G ^ (n+1)).toAddSubgroup ≤
      (groupRingAdditiveExtension f).ker := by
    rw [augmentation_power_generated]
    apply (groupRingAdditiveExtension f).ker.closure_le.mpr
    rintro x ⟨gs,hlen,rfl⟩
    rcases List.eq_nil_or_concat' gs with rfl | ⟨ts,g,rfl⟩
    · simp at hlen
    · change groupRingAdditiveExtension f (groupDifferenceWord (ts++[g])) = 0
      rw [cocycle_extension_difference_word hf]
      exact hnil ts (by simpa using hlen) g
  exact fun x hx => hle hx

/-- The descended additive map from the truncated group ring is constructed
from its universal quotient property. -/
noncomputable def truncatedCocycleMap {G A : Type*} [Group G] [AddCommGroup A]
    {T : G →* Module.End ℤ A} {f : G → A} (hf : IsAdditiveCocycle T f)
    (n : ℕ) (hnil : ∀ gs : List G, gs.length = n → ∀ g : G,
      (gs.map (fun x => T x-1)).prod (f g) = 0) : TruncatedGroupRing G (n+1) →+ A :=
  QuotientAddGroup.lift (augmentationIdeal G ^ (n+1)).toAddSubgroup
    (groupRingAdditiveExtension f) (cocycle_extension_kills_power hf n hnil)

@[simp] theorem truncatedCocycleMap_element {G A : Type*} [Group G] [AddCommGroup A]
    {T : G →* Module.End ℤ A} {f : G → A} (hf : IsAdditiveCocycle T f)
    (n : ℕ) (hnil : ∀ gs : List G, gs.length = n → ∀ g : G,
      (gs.map (fun x => T x-1)).prod (f g) = 0) (g : G) :
    truncatedCocycleMap hf n hnil (truncatedElement G (n+1) g) = f g :=
  groupRingAdditiveExtension_of f g

theorem truncatedCocycleMap_surjective {G A : Type*} [Group G] [AddCommGroup A]
    {T : G →* Module.End ℤ A} {f : G → A} (hf : IsAdditiveCocycle T f)
    (n : ℕ) (hnil : ∀ gs : List G, gs.length = n → ∀ g : G,
      (gs.map (fun x => T x-1)).prod (f g) = 0)
    (hgen : AddSubgroup.closure (Set.range f) = ⊤) :
    Function.Surjective (truncatedCocycleMap hf n hnil) := by
  apply AddMonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply (truncatedCocycleMap hf n hnil).range.closure_le.mpr
  rintro x ⟨g,rfl⟩
  exact ⟨truncatedElement G (n+1) g,truncatedCocycleMap_element hf n hnil g⟩

end DirectedCycles
