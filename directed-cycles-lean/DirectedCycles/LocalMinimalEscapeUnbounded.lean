import DirectedCycles.LocalUltraproductEscape
import DirectedCycles.LocalInternalSetLogic

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Arbitrarily long nonidentity local power segments force the first escape
indices of least-escape elements to be unbounded. All finite powers transfer
with their actual multiplication domains. -/
theorem local_minimal_first_escape_unbounded (A : ∀ i, Set (G i))
    (u : ∀ i, G i) (N : ι → ℕ)
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i)
    (hnorm : ∀ᶠ i in (U : Filter ι), (L i).escapeNorm (A i) (u i) = 1/(N i : ℝ))
    (hmin : ∀ᶠ i in (U : Filter ι), ∀ v ∈ A i, v ≠ (L i).one →
      (L i).escapeNorm (A i) (u i) ≤ (L i).escapeNorm (A i) v)
    (hsegments : ∀ M : ℕ, ∃ z : LocalUltraproduct (U : Filter ι) G,
      z ≠ (localUltraAlgebra (U : Filter ι) G L).one ∧
        ∀ n ≤ M, (localUltraAlgebra (U : Filter ι) G L).PowerIn (localUltraSet (U : Filter ι) G A) z n) :
    ∀ M : ℕ, ∀ᶠ i in (U : Filter ι), M < N i := by
  intro M
  obtain ⟨z,hz,hp⟩ := hsegments (M+1)
  obtain ⟨v,rfl⟩ := Quotient.exists_rep z
  have hvne : ∀ᶠ i in (U : Filter ι), v i ≠ (L i).one :=
    Ultrafilter.eventually_not.mpr (fun he => hz ((localUltraMk_eq_iff _ G v (fun i => (L i).one)).2 he))
  have hj : ∀ j : Fin (M+2), ∀ᶠ i in (U : Filter ι), (L i).PowerIn (A i) (v i) j.val := by
    intro j
    exact (localUltraPowerIn_mk_iff _ G L A v j.val).1 (hp j.val (by omega))
  have hall := Filter.eventually_all.mpr hj
  filter_upwards [hN,hnorm,hmin,hvne,hall] with i hNi hni hmi hvni halli
  have hvA : v i ∈ A i := ((L i).powerIn_one (A i) (v i)).1 (halli ⟨1,by omega⟩)
  have he := (hmi (v i) hvA hvni).trans
    ((L i).escapeNorm_le_of_powers (n := M+1) (fun j hj => halli ⟨j,by omega⟩))
  rw [hni] at he
  have hNr : 0 < (N i : ℝ) := by exact_mod_cast hNi
  have hnum := (div_le_div_iff₀ hNr (by positivity : 0 < ((M+1 : ℕ) : ℝ)+1)).1 he
  have hnum' : (M : ℝ)+2 ≤ (N i : ℝ) := by
    simp only [one_mul,Nat.cast_add,Nat.cast_one] at hnum
    linarith
  have hbound : M+2 ≤ N i := by exact_mod_cast hnum'
  omega
end DirectedCycles
