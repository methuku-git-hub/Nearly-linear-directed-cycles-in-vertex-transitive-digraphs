module

public import DirectedCycles.GroupUltraproduct

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise
namespace DirectedCycles

/-- Internal products are actual set products in the quotient group. -/
theorem ultraSet_mul {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A B : ∀ i, Set (G i)) :
    ultraSet f G (fun i => A i * B i) = ultraSet f G A * ultraSet f G B := by
  classical
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hchoose : ∀ i, ∃ a b : G i, x i ∈ A i*B i → a ∈ A i ∧ b ∈ B i ∧ a*b = x i := by
      intro i
      by_cases hi : x i ∈ A i*B i
      · obtain ⟨a,ha,b,hb,he⟩ := hi
        exact ⟨a,b,fun _ => ⟨ha,hb,he⟩⟩
      · exact ⟨1,1,fun h => (hi h).elim⟩
    choose a b hab using hchoose
    have ha : ∀ᶠ i in f, a i ∈ A i := hx.mono (fun i hi => (hab i hi).1)
    have hb : ∀ᶠ i in f, b i ∈ B i := hx.mono (fun i hi => (hab i hi).2.1)
    have he : ultraMk f G (a*b) = ultraMk f G x :=
      (ultraMk_eq_iff f G _ _).mpr (hx.mono (fun i hi => (hab i hi).2.2))
    exact ⟨ultraMk f G a,⟨a,ha,rfl⟩,ultraMk f G b,⟨b,hb,rfl⟩,(map_mul _ _ _).symm.trans he⟩
  · rintro ⟨a,⟨x,hx,rfl⟩,b,⟨y,hy,rfl⟩,rfl⟩
    change ultraMk f G x * ultraMk f G y ∈ ultraSet f G (fun i => A i*B i)
    rw [← map_mul]
    apply (ultraMk_mem_ultraSet_iff f G _ _).mpr
    filter_upwards [hx,hy] with i hi hj
    exact Set.mul_mem_mul hi hj

theorem ultraSet_inv {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Set (G i)) :
    ultraSet f G (fun i => (A i)⁻¹) = (ultraSet f G A)⁻¹ := by
  ext z
  obtain ⟨x,rfl⟩ := ultraMk_surjective f G z
  rw [ultraMk_mem_ultraSet_iff,Set.mem_inv,← map_inv,ultraMk_mem_ultraSet_iff]
  rfl

theorem ultraSet_one {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)] :
    ultraSet f G (fun i => (1 : Set (G i))) = 1 := by
  ext z
  obtain ⟨x,rfl⟩ := ultraMk_surjective f G z
  rw [ultraMk_mem_ultraSet_iff]
  change (∀ᶠ i in f, x i = 1) ↔ ultraMk f G x = 1
  rw [← map_one (ultraMk f G),ultraMk_eq_iff]
  rfl

theorem ultraSet_pow {ι : Type*} (f : Filter ι) (G : ι → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Set (G i)) (n : ℕ) :
    ultraSet f G (fun i => A i^n) = ultraSet f G A ^ n := by
  induction n with
  | zero => simp only [pow_zero,ultraSet_one]
  | succ n ih => simp only [pow_succ,ultraSet_mul,ih]

/-- A finite family of internal alternatives has one fixed alternative
on an ultrafilter-large set. This is the finite-disjunction transfer step. -/
theorem ultraSet_finite_range {ι J : Type*} [Finite J] (u : Ultrafilter ι)
    (G : ι → Type*) [∀ i, Group (G i)] (a : J → ∀ i, G i) :
    ultraSet (u : Filter ι) G (fun i => Set.range (fun j => a j i)) =
      Set.range (fun j => ultraMk (u : Filter ι) G (a j)) := by
  ext z
  obtain ⟨x,rfl⟩ := ultraMk_surjective (u : Filter ι) G z
  rw [ultraMk_mem_ultraSet_iff]
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := (Ultrafilter.eventually_exists_iff).mp hx
    exact ⟨j,(ultraMk_eq_iff (u : Filter ι) G _ _).mpr hj⟩
  · rintro ⟨j,hj⟩
    have he := (ultraMk_eq_iff (u : Filter ι) G _ _).mp hj
    exact he.mono (fun i hi => ⟨j,hi⟩)

end DirectedCycles
