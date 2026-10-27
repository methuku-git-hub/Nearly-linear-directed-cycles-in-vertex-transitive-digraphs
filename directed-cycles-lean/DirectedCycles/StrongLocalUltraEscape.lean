module

public import DirectedCycles.StrongLocalEscapeEstimates
public import DirectedCycles.StrongLocalWordEscape
public import DirectedCycles.LocalWordEscapeTransfer
public import DirectedCycles.LocalEscapeEstimateTransfer
public import DirectedCycles.LocalWordPowerTransfer

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (A : ∀ i, Finset (G i)) {K : ℕ}
local notation "M" => localUltraAlgebra (U : Filter ι) G L
local notation "B" => localUltraSet (U : Filter ι) G (fun i => (A i : Set (G i)))

theorem localUltra_inv_mk (a : ∀ i, G i) :
    (M).inv (localUltraMk (U : Filter ι) G a) =
      localUltraMk (U : Filter ι) G (fun i => (L i).inv (a i)) := rfl

/-- The analytic product premise in the actual local-ultraproduct transfer
is discharged by the proved finite strong local theorem. -/
theorem strong_localUltra_product [∀ i, Fintype (G i)]
    (hd : ∀ᶠ i in (U : Filter ι), (L i).DivisionClosed)
    (hr : ∀ᶠ i in (U : Filter ι), (L i).Reversible)
    (hA : ∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (A i))
    {l : List (LocalUltraproduct (U : Filter ι) G)} {x : LocalUltraproduct (U : Filter ι) G}
    (hp : (M).Product l x) :
    (M).escapeNorm B x ≤
      (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))*(l.map ((M).escapeNorm B)).sum := by
  obtain ⟨v,rfl⟩ := exists_localUltra_list_representatives (U : Filter ι) G l
  obtain ⟨a,rfl⟩ := Quotient.exists_rep x
  have hA1 := hA.mono (fun _ hi => hi.approximate.one_mem)
  have hprod := hd.and (hr.and hA)
  simpa only [List.map_map,Function.comp_def] using localUltra_escapeNorm_product_le U G L
    (fun i => (A i : Set (G i))) hA1 (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))
    (hprod.mono fun i hi l x hp => strong_local_approximate_product (L i) hi.1 hi.2.1 hi.2.2 hp) v a hp

/-- Conjugation estimates pass to the genuine local ultraproduct through
actual product and word-power transfer and convergence of escape norms. -/
theorem strong_localUltra_conjugate
    (hr : ∀ᶠ i in (U : Filter ι), (L i).Reversible)
    (hA : ∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (A i))
    {y g c : LocalUltraproduct (U : Filter ι) G} (hy : y ∈ (M).wordPower B 10)
    (hp : (M).Product [(M).inv y,g,y] c) : (M).escapeNorm B c ≤ 1000*(M).escapeNorm B g := by
  obtain ⟨y,rfl⟩ := Quotient.exists_rep y
  obtain ⟨g,rfl⟩ := Quotient.exists_rep g
  obtain ⟨c,rfl⟩ := Quotient.exists_rep c
  have hA1 := hA.mono (fun _ hi => hi.approximate.one_mem)
  have hy' := (localUltra_wordPower_mk_iff (U : Filter ι) G L _ y 10).1 hy
  have hp' : ∀ᶠ i in (U : Filter ι), (L i).Product [(L i).inv (y i),g i,y i] (c i) := by
    have ht := (localUltraProduct_mk_iff (U : Filter ι) G L [fun i => (L i).inv (y i),g,y] c).1
      (by simpa only [List.map_cons,List.map_nil,localUltra_inv_mk] using hp)
    simpa only [List.map_cons,List.map_nil] using ht
  apply le_of_tendsto_of_tendsto (localUltra_escapeNorm_tendsto G L U _ c hA1)
    ((localUltra_escapeNorm_tendsto G L U _ g hA1).const_mul 1000)
  filter_upwards [hr,hA,hy',hp'] with i hri hAi hyi hpi
  exact strong_local_approximate_conjugate (L i) hri hAi hyi hpi

/-- The local ultraproduct commutator estimate has no unproved finite-stage
analytic premise. In particular, zero escape is preserved by commutation. -/
theorem strong_localUltra_commutator [∀ i, Fintype (G i)]
    (hd : ∀ᶠ i in (U : Filter ι), (L i).DivisionClosed)
    (hr : ∀ᶠ i in (U : Filter ι), (L i).Reversible)
    (hA : ∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (A i))
    {g h k : LocalUltraproduct (U : Filter ι) G}
    (hg : g ∈ (M).wordPower B 10) (hh : h ∈ (M).wordPower B 10)
    (hp : (M).Product [(M).inv g,(M).inv h,g,h] k) :
    let P := 8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ)
    (M).escapeNorm B k ≤ (2*(1000 : ℝ)^2*(K : ℝ)^11*P^2)*(M).escapeNorm B g*(M).escapeNorm B h := by
  dsimp only
  obtain ⟨g,rfl⟩ := Quotient.exists_rep g
  obtain ⟨h,rfl⟩ := Quotient.exists_rep h
  obtain ⟨k,rfl⟩ := Quotient.exists_rep k
  have hA1 := hA.mono (fun _ hi => hi.approximate.one_mem)
  have hg' := (localUltra_wordPower_mk_iff (U : Filter ι) G L _ g 10).1 hg
  have hh' := (localUltra_wordPower_mk_iff (U : Filter ι) G L _ h 10).1 hh
  have hp' : ∀ᶠ i in (U : Filter ι), (L i).Product [(L i).inv (g i),(L i).inv (h i),g i,h i] (k i) := by
    have ht := (localUltraProduct_mk_iff (U : Filter ι) G L
      [fun i => (L i).inv (g i),fun i => (L i).inv (h i),g,h] k).1
      (by simpa only [List.map_cons,List.map_nil,localUltra_inv_mk] using hp)
    simpa only [List.map_cons,List.map_nil] using ht
  apply le_of_tendsto_of_tendsto (localUltra_escapeNorm_tendsto G L U _ k hA1)
    (((localUltra_escapeNorm_tendsto G L U _ g hA1).const_mul _).mul
      (localUltra_escapeNorm_tendsto G L U _ h hA1))
  filter_upwards [hd,hr,hA,hg',hh',hp'] with i hdi hri hAi hgi hhi hpi
  exact strong_local_approximate_commutator (L i) hdi hri hAi hgi hhi hpi
/-- The ultraproduct product estimate also includes undefined products,
using the proved convergence of word escape with that convention. -/
theorem strong_localUltra_wordEscape [∀ i, Fintype (G i)]
    (hd : ∀ᶠ i in (U : Filter ι), (L i).DivisionClosed)
    (hr : ∀ᶠ i in (U : Filter ι), (L i).Reversible)
    (hA : ∀ᶠ i in (U : Filter ι), IsStrongLocalFiniteApproximateGroup (L i) K (A i))
    (l : List (LocalUltraproduct (U : Filter ι) G)) :
    (M).wordEscape B l ≤
      (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))*(l.map ((M).escapeNorm B)).sum := by
  obtain ⟨v,rfl⟩ := exists_localUltra_list_representatives (U : Filter ι) G l
  have hA1 := hA.mono (fun _ hi => hi.approximate.one_mem)
  have hleft := localUltra_wordEscape_tendsto U G L (fun i => (A i : Set (G i))) hA1 v
  have hright := (localUltra_escapeNorm_sum_tendsto U G L (fun i => (A i : Set (G i))) hA1 v).const_mul
    (8*(1000 : ℝ)*(K : ℝ)*((1000000*K^3 : ℕ) : ℝ))
  simp only [List.map_map,Function.comp_def]
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hd,hr,hA] with i hdi hri hAi
  simpa only [List.map_map,Function.comp_def] using
    strong_local_wordEscape_le (L i) hdi hri hAi (v.map (fun a => a i))
end DirectedCycles
