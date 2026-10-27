module

public import DirectedCycles.ScaledUltraproductPowers
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- In a connected topological group, commuting with an identity neighbourhood
forces commuting with every element. -/
theorem commute_of_commutes_neighbourhood {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [PreconnectedSpace H] (g : H) {W : Set H} (hW : W ∈ 𝓝 (1 : H))
    (hcomm : ∀ x ∈ W, Commute g x) (x : H) : Commute g x := by
  let C : Subgroup H := {
    carrier := {x | Commute g x}
    one_mem' := Commute.one_right g
    mul_mem' := fun ha hb => ha.mul_right hb
    inv_mem' := fun ha => ha.inv_right }
  have hCnhds : (C : Set H) ∈ 𝓝 (1 : H) := Filter.mem_of_superset hW hcomm
  have hCo : IsOpen (C : Set H) := C.isOpen_of_mem_nhds hCnhds
  have hCc : IsClosed (C : Set H) := C.isClosed_of_isOpen hCo
  have he : (C : Set H) = Set.univ := (show IsClopen (C : Set H) from ⟨hCc,hCo⟩).eq_univ ⟨1,C.one_mem⟩
  change x ∈ (C : Set H)
  rw [he]
  exact Set.mem_univ x

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

theorem ultra_variable_zpow_commutes (u v : ∀ i, G i) (k : ι → ℤ)
    (hcomm : ∀ᶠ i in (U : Filter ι), Commute (u i) (v i)) :
    Commute (ultraMk (U : Filter ι) G (fun i => (u i)^(k i))) (ultraMk (U : Filter ι) G v) := by
  change _*_ = _*_
  rw [← map_mul,← map_mul]
  apply (ultraMk_eq_iff _ G _ _).2
  filter_upwards [hcomm] with i hi
  exact (hi.zpow_left (k i)).eq

/-- The actual scaled curve is central whenever the component generator
centralizes an internal set whose model image contains an identity
neighbourhood. This uses the formula for the curve, not an arbitrary
one-parameter subgroup. -/
theorem scaled_curve_central {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [PreconnectedSpace H]
    (u : ∀ i, G i) (N : ι → ℕ) (C : ∀ i, Set (G i))
    (S : Subgroup (GroupUltraproduct (U : Filter ι) G)) (π : S →* H)
    (φ : ℝ → H)
    (hφ : ∀ t : ℝ, ∃ h : scaledUltraPower U G u N t ∈ S, φ t = π ⟨scaledUltraPower U G u N t,h⟩)
    (hcomm : ∀ᶠ i in (U : Filter ι), ∀ v ∈ C i, Commute (u i) v)
    (W : Set H) (hW : W ∈ 𝓝 (1 : H))
    (hthick : ∀ x ∈ W, ∃ v : S, v.val ∈ ultraSet (U : Filter ι) G C ∧ π v = x) :
    ∀ t : ℝ, ∀ x : H, Commute (φ t) x := by
  intro t x
  apply commute_of_commutes_neighbourhood (φ t) hW _ x
  intro y hy
  obtain ⟨v,hv,hvy⟩ := hthick y hy
  obtain ⟨w,hw⟩ := ultraMk_surjective (U : Filter ι) G v.val
  have hwC : ∀ᶠ i in (U : Filter ι), w i ∈ C i :=
    (ultraMk_mem_ultraSet_iff _ G C w).1 (hw.symm ▸ hv)
  have hcw : ∀ᶠ i in (U : Filter ι), Commute (u i) (w i) := by
    filter_upwards [hcomm,hwC] with i hi hwi
    exact hi (w i) hwi
  have hcm := ultra_variable_zpow_commutes U G u w (fun i => Int.floor (t*(N i : ℝ))) hcw
  rw [hw] at hcm
  obtain ⟨ht,hft⟩ := hφ t
  have he : (⟨scaledUltraPower U G u N t,ht⟩ : S)*v = v*⟨scaledUltraPower U G u N t,ht⟩ :=
    Subtype.ext hcm.eq
  change φ t*y = y*φ t
  rw [hft,← hvy]
  simpa only [map_mul] using congrArg π he
end DirectedCycles
