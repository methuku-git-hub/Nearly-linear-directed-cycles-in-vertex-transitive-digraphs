import DirectedCycles.FiniteCosetNilprogressionInput

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- A single bound controls rank, class and inverse density. -/
def HasCosetNilprogressionModel {G : Type*} [Group G] (A : Set G) (n : ℕ) : Prop :=
  ∃ r c : ℕ, ∃ P : CosetNilprogression G r c,
    r ≤ n ∧ c ≤ n ∧ P.carrier ⊆ A^4 ∧ Nat.card A ≤ n*Nat.card P.carrier

theorem HasCosetNilprogressionModel.mono {G : Type*} [Group G] {A : Set G} {n m : ℕ}
    (h : HasCosetNilprogressionModel A n) (hnm : n ≤ m) : HasCosetNilprogressionModel A m := by
  obtain ⟨r,c,P,hr,hc,hPA,hd⟩ := h
  exact ⟨r,c,P,hr.trans hnm,hc.trans hnm,hPA,hd.trans (Nat.mul_le_mul_right _ hnm)⟩

def trivialCosetNilprogression (G : Type*) [Group G] : CosetNilprogression G 0 0 where
  U := ⊥
  H := ⊥
  hHU := le_rfl
  normal := inferInstance
  generators := Fin.elim0
  lengths := Fin.elim0
  lengths_pos := fun i => Fin.elim0 i
  generates := by simp [Subgroup.subgroupOf_self]
  commutators := by
    have hempty : ∀ w : CommutatorWord (Fin 0), False := by
      intro w
      induction w with
      | var i => exact Fin.elim0 i
      | bracket a b ha _hb => exact ha
    intro w _hw
    exact (hempty w).elim

theorem trivialCosetNilprogression_carrier (G : Type*) [Group G] :
    (trivialCosetNilprogression G).carrier = {1} := by
  ext g
  constructor
  · intro hg
    exact (trivialCosetNilprogression G).carrier_subset_U hg
  · intro hg
    apply (trivialCosetNilprogression G).subgroup_subset_carrier
    exact hg

theorem hasCosetModel_of_card_le {G : Type*} [Group G] (A : Set G) (h1 : 1 ∈ A)
    (n : ℕ) (hcard : Nat.card A ≤ n) : HasCosetNilprogressionModel A n := by
  refine ⟨0,0,trivialCosetNilprogression G,Nat.zero_le _,Nat.zero_le _,?_,?_⟩
  · rw [trivialCosetNilprogression_carrier]
    exact Set.singleton_subset_iff.mpr (Set.one_mem_pow h1)
  · simpa only [trivialCosetNilprogression_carrier,Nat.card_coe_set_eq,Set.ncard_singleton,mul_one] using hcard

theorem finite_coset_input_iff_uniform_bound : FiniteCosetNilprogressionTheorem ↔
    ∀ K : ℝ, 1 ≤ K → ∃ n : ℕ, 1 ≤ n ∧
      ∀ (G : Type) [Group G] [Finite G] (A : Set G),
        IsApproximateSubgroup K A → HasCosetNilprogressionModel A n := by
  constructor
  · intro h K hK
    obtain ⟨r,c,M,_hM,hmodel⟩ := h K hK
    refine ⟨r+c+M+1,by omega,?_⟩
    intro G _ _ A hA
    obtain ⟨r',c',P,hr,hc,hPA,hd⟩ := hmodel G A hA
    exact ⟨r',c',P,by omega,by omega,hPA,hd.trans (Nat.mul_le_mul_right _ (by omega))⟩
  · intro h K hK
    obtain ⟨n,hn,hmodel⟩ := h K hK
    exact ⟨n,n,n,hn,hmodel⟩

end DirectedCycles
