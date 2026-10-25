module

public import DirectedCycles.InternalCountableSaturation
public import DirectedCycles.InternalSetLogic

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

theorem ultraSet_singleton {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (a : ∀ i, G i) : ultraSet f G (fun i => {a i}) = {ultraMk f G a} := by
  ext z
  obtain ⟨x,rfl⟩ := ultraMk_surjective f G z
  rw [ultraMk_mem_ultraSet_iff,Set.mem_singleton_iff,ultraMk_eq_iff]
  rfl

theorem ultraSet_leftTranslate {ι : Type*} (f : Filter ι)
    (G : ι → Type*) [∀ i, Group (G i)] (a : ∀ i, G i) (A : ∀ i, Set (G i)) :
    ultraSet f G (fun i => (fun x => a i*x) '' A i) =
      (fun x => ultraMk f G a*x) '' ultraSet f G A := by
  have he : ∀ i, (fun x => a i*x) '' A i = {a i}*A i := fun i => Set.singleton_mul.symm
  simp_rw [he]
  rw [ultraSet_mul,ultraSet_singleton,Set.singleton_mul]

/-- Countable intersections of internal translates remain valid after
restricting to a subgroup which contains the internal set being covered. -/
theorem internal_subgroup_translate_saturation (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ Filter.atTop) (G : ℕ → Type*) [∀ i, Group (G i)]
    (H : Subgroup (GroupUltraproduct (u : Filter ℕ) G))
    (T : ∀ i, Set (G i)) (R : ℕ → ∀ i, Set (G i))
    (hTH : ultraSet (u : Filter ℕ) G T ⊆ H)
    (c : ℕ → H)
    (hfinite : ∀ N, ∃ z : H, z.val ∈ ultraSet (u : Filter ℕ) G T ∧
      ∀ n ≤ N, z ∈ (fun y : H => c n*y) '' (H.subtype ⁻¹' ultraSet (u : Filter ℕ) G (R n))) :
    ∃ z : H, z.val ∈ ultraSet (u : Filter ℕ) G T ∧
      ∀ n, z ∈ (fun y : H => c n*y) '' (H.subtype ⁻¹' ultraSet (u : Filter ℕ) G (R n)) := by
  classical
  choose a ha using fun n => ultraMk_surjective (u : Filter ℕ) G (c n).val
  let B := fun n i => T i ∩ (fun x => a n i*x) '' R n i
  have he : ∀ n, ultraSet (u : Filter ℕ) G (B n) =
      ultraSet (u : Filter ℕ) G T ∩ (fun x => (c n).val*x) '' ultraSet (u : Filter ℕ) G (R n) := by
    intro n
    rw [ultraSet_inter,ultraSet_leftTranslate,ha n]
  have hs : ∀ N, ∃ z : GroupUltraproduct (u : Filter ℕ) G,
      ∀ n ≤ N, z ∈ ultraSet (u : Filter ℕ) G (B n) := by
    intro N
    obtain ⟨z,hz,hzn⟩ := hfinite N
    refine ⟨z.val,?_⟩
    intro n hn
    rw [he]
    obtain ⟨y,hy,hcy⟩ := hzn n hn
    exact ⟨hz,⟨y.val,hy,congrArg Subtype.val hcy⟩⟩
  obtain ⟨z,hz⟩ := internal_countable_saturation (u : Filter ℕ) hu G B hs
  have hzT : z ∈ ultraSet (u : Filter ℕ) G T := by
    have hh := hz 0
    rw [he] at hh
    exact hh.1
  refine ⟨⟨z,hTH hzT⟩,hzT,?_⟩
  intro n
  have hzn := hz n
  rw [he] at hzn
  obtain ⟨y,hy,hcy⟩ := hzn.2
  have hyH : y ∈ H := by
    have heq : y = (c n).val⁻¹*z := by rw [← hcy]; simp
    rw [heq]
    exact H.mul_mem (H.inv_mem (c n).property) (hTH hzT)
  exact ⟨⟨y,hyH⟩,hy,Subtype.ext hcy⟩

end DirectedCycles
