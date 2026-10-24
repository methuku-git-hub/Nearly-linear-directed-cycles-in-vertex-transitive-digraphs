import DirectedCycles.GlobalGoodLocallyCompactModel
import DirectedCycles.InternalSetLogic

set_option autoImplicit false
open scoped Pointwise Topology
namespace DirectedCycles

/-- Symmetric finite representatives of the original good-model sandwich,
inside the actual fourth powers and containing the identity at every index. -/
theorem global_good_model_symmetric_sandwich (u : Ultrafilter ℕ)
    (G : ℕ → Type*) [∀ i, Group (G i)] [∀ i, DecidableEq (G i)]
    (A : ∀ i, Finset (G i)) (hA1 : ∀ i, (1 : G i) ∈ A i)
    (M : let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
      let H := Subgroup.closure B
      InternalLocallyCompactGroupModel H (H.subtype ⁻¹' (B^4)) (IsInternalFiniteIn u G H))
    (F O : Set M.carrier) (hF : IsCompact F) (hO : IsOpen O)
    (hFO : F ⊆ O) (hOU : O ⊆ M.neighbourhood)
    (hF1 : (1 : M.carrier) ∈ F) (hFi : ∀ x ∈ F, x⁻¹ ∈ F) :
    ∃ D : ∀ i, Finset (G i),
      (∀ i, (1 : G i) ∈ D i ∧ (∀ x ∈ D i, x⁻¹ ∈ D i) ∧ D i ⊆ (A i)^4) ∧
      M.map ⁻¹' F ⊆ (Subgroup.closure (ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i))))).subtype ⁻¹'
        ultraSet (u : Filter ℕ) G (fun i => (D i : Set (G i))) ∧
      (Subgroup.closure (ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i))))).subtype ⁻¹'
        ultraSet (u : Filter ℕ) G (fun i => (D i : Set (G i))) ⊆ M.map ⁻¹' O := by
  classical
  obtain ⟨E,hEA,hFE,hEO⟩ := global_good_model_component_sandwich u G A M F O hF hO hFO hOU
  let D : ∀ i, Finset (G i) := fun i => insert 1 (E i ∩ (E i)⁻¹)
  have hDi : ∀ i, (1 : G i) ∈ D i ∧ (∀ x ∈ D i, x⁻¹ ∈ D i) ∧ D i ⊆ (A i)^4 := by
    intro i
    refine ⟨Finset.mem_insert_self _ _,?_,?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp only [inv_one]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        rcases Finset.mem_inter.mp hx with ⟨hx,hxi⟩
        exact Finset.mem_inter.mpr ⟨Finset.mem_inv'.mp hxi,by simpa only [Finset.mem_inv',inv_inv] using hx⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.one_mem_pow (hA1 i)
      · exact hEA i (Finset.mem_inter.mp hx).1
  refine ⟨D,hDi,?_,?_⟩
  · intro x hx
    have hxe := hFE hx
    have hxie := hFE (show M.map (x⁻¹) ∈ F from by rw [map_inv]; exact hFi _ hx)
    obtain ⟨a,ha⟩ := ultraMk_surjective (u : Filter ℕ) G x.val
    have hea : ∀ᶠ i in (u : Filter ℕ), a i ∈ E i :=
      (ultraMk_mem_ultraSet_iff _ G _ a).1 (ha.symm ▸ hxe)
    have heia : ∀ᶠ i in (u : Filter ℕ), (a i)⁻¹ ∈ E i := by
      apply (ultraMk_mem_ultraSet_iff _ G _ _).1
      change (ultraMk (u : Filter ℕ) G) (a⁻¹) ∈ _
      rw [map_inv,ha]
      exact hxie
    change x.val ∈ ultraSet (u : Filter ℕ) G (fun i => (D i : Set (G i)))
    rw [show x.val = ultraMk (u : Filter ℕ) G a from ha.symm]
    apply (ultraMk_mem_ultraSet_iff _ G _ a).2
    filter_upwards [hea,heia] with i hi hii
    exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hi,Finset.mem_inv'.mpr hii⟩)
  · intro x hx
    change x.val ∈ ultraSet (u : Filter ℕ) G (fun i => (D i : Set (G i))) at hx
    obtain ⟨a,ha⟩ := ultraMk_surjective (u : Filter ℕ) G x.val
    have hda := (ultraMk_mem_ultraSet_iff (u : Filter ℕ) G _ a).1 (ha.symm ▸ hx)
    have hcases : (∀ᶠ i in (u : Filter ℕ), a i = 1) ∨ (∀ᶠ i in (u : Filter ℕ), a i ∈ E i) := by
      apply Ultrafilter.eventually_or.mp
      exact hda.mono fun i hi => (Finset.mem_insert.mp hi).imp_right (fun h => (Finset.mem_inter.mp h).1)
    rcases hcases with hone | he
    · have hx1 : x = 1 := by
        apply Subtype.ext
        change x.val = 1
        rw [← ha,← map_one (ultraMk (u : Filter ℕ) G)]
        exact (ultraMk_eq_iff _ G _ _).2 hone
      change M.map x ∈ O
      rw [hx1,map_one]
      exact hFO hF1
    · apply hEO
      change x.val ∈ ultraSet (u : Filter ℕ) G (fun i => (E i : Set (G i)))
      rw [← ha]
      exact (ultraMk_mem_ultraSet_iff _ G _ a).2 he
end DirectedCycles
