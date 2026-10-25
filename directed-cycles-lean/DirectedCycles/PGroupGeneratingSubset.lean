module

public import DirectedCycles.PrimeCharacterQuotients
public import DirectedCycles.ReturnLabelGeneration
public import Mathlib.GroupTheory.PGroup

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
universe u

/-- A generating set of a finite p-group contains a generating subset
whose size is at most its prime-character dimension. -/
theorem pgroup_generating_subset {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p G)
    (S : Set G) (hS : Subgroup.closure S = ⊤) :
    ∃ T : Finset G, (T : Set G) ⊆ S ∧
      T.card ≤ primeCharacterDimension G p ∧ Subgroup.closure (T : Set G) = ⊤ := by
  classical
  suffices hh : ∀ d : ℕ, ∀ (B : Type u) [Group B] [Finite B], IsPGroup p B →
      primeCharacterDimension B p ≤ d → ∀ S : Set B, Subgroup.closure S = ⊤ →
      ∃ T : Finset B, (T : Set B) ⊆ S ∧ T.card ≤ d ∧
        Subgroup.closure (T : Set B) = ⊤ by
    exact hh _ G hP le_rfl S hS
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro B _ _ hP hd S hS
    let : Group.IsNilpotent B := hP.isNilpotent
    rcases subsingleton_or_nontrivial B with htr | htr
    · let : Subsingleton B := htr
      refine ⟨∅,by simp,by simp,?_⟩
      exact Subsingleton.elim _ _
    · let : Nontrivial B := htr
      have hpdiv : p ∣ Nat.card B := hP.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne'
      obtain ⟨f,hf⟩ := nilpotent_prime_character p hpdiv
      obtain ⟨a,ha,hfa⟩ := nonzero_primeCharacter_on_generator S hS f hf
      let Q := B ⧸ elementClosure a
      let π : B →* Q := QuotientGroup.mk' (elementClosure a)
      have hdrop : primeCharacterDimension Q p + 1 = primeCharacterDimension B p :=
        primeCharacterDimension_normalClosure_drop p a f hfa
      have hlt : primeCharacterDimension Q p < d := by omega
      have hπgen : Subgroup.closure (π '' S) = ⊤ := by
        rw [← MonoidHom.map_closure,hS,Subgroup.map_top]
        exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
      obtain ⟨T,hT,hcard,hgen⟩ := ih _ hlt Q (hP.to_quotient _) le_rfl (π '' S) hπgen
      have hlift : ∀ q : T, ∃ x : B, x ∈ S ∧ π x = q.val := by
        intro q
        exact hT q.property
      choose t ht hπt using hlift
      let U : Finset B := Finset.univ.image t
      have hU : (U : Set B) ⊆ S := by
        intro x hx
        obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hx
        exact ht q
      have himage : π '' (U : Set B) = (T : Set Q) := by
        ext q
        constructor
        · rintro ⟨x,hx,rfl⟩
          obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
          rw [hπt y]
          exact y.property
        · intro hq
          exact ⟨t ⟨q,hq⟩,Finset.mem_image.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,rfl⟩,hπt _⟩
      refine ⟨insert a U,?_,?_,?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ha
        · exact hU hx
      · have hucard : U.card ≤ T.card := (Finset.card_image_le).trans_eq (Fintype.card_coe T)
        have hi := Finset.card_insert_le a U
        omega
      · simp only [Finset.coe_insert]
        apply nilpotent_generation_from_element_quotient a (U : Set B)
        rw [himage]
        exact hgen

/-- In particular the subset has size at most the minimum number of generators. -/
theorem pgroup_generating_subset_rank {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p G)
    (S : Set G) (hS : Subgroup.closure S = ⊤) :
    ∃ T : Finset G, (T : Set G) ⊆ S ∧ T.card ≤ Group.rank G ∧
      Subgroup.closure (T : Set G) = ⊤ := by
  obtain ⟨T,hT,hcard,hgen⟩ := pgroup_generating_subset p hP S hS
  exact ⟨T,hT,hcard.trans (primeCharacterDimension_le_rank p),hgen⟩

end DirectedCycles
