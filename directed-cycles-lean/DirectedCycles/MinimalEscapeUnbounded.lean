module

public import DirectedCycles.UltraproductInternalSets
public import DirectedCycles.EscapeNorm

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) [∀ i, Group (G i)]

/-- Arbitrarily long nontrivial power segments force the component first-exit
times of least-positive-escape elements to be unbounded. -/
theorem minimal_first_escape_unbounded (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (hA : ∀ᶠ i in (U : Filter ι), (1 : G i) ∈ A i)
    (hprev : ∀ᶠ i in (U : Filter ι), ∀ n < N i, (u i)^n ∈ A i)
    (hexit : ∀ᶠ i in (U : Filter ι), (u i)^(N i) ∉ A i)
    (hmin : ∀ᶠ i in (U : Filter ι), ∀ v ∈ A i, v ≠ 1 → escapeNorm (A i) (u i) ≤ escapeNorm (A i) v)
    (hsegments : ∀ M : ℕ, ∃ z : GroupUltraproduct (U : Filter ι) G,
      z ≠ 1 ∧ ∀ n ≤ M, z^n ∈ ultraSet (U : Filter ι) G A) :
    ∀ M : ℕ, ∀ᶠ i in (U : Filter ι), M < N i := by
  intro M
  obtain ⟨z,hz,hp⟩ := hsegments (M+1)
  obtain ⟨v,rfl⟩ := ultraMk_surjective (U : Filter ι) G z
  have hz' : ultraMk (U : Filter ι) G v ≠ ultraMk (U : Filter ι) G 1 := by simpa using hz
  have hvne : ∀ᶠ i in (U : Filter ι), v i ≠ 1 :=
    Ultrafilter.eventually_not.mpr (fun he => hz' ((ultraMk_eq_iff _ G v 1).2 he))
  have hj : ∀ j : Fin (M+2), ∀ᶠ i in (U : Filter ι), (v i)^j.val ∈ A i := by
    intro j
    have h := hp j.val (by omega)
    rw [← map_pow] at h
    exact (ultraMk_mem_ultraSet_iff _ G A _).1 h
  have hall : ∀ᶠ i in (U : Filter ι), ∀ j : Fin (M+2), (v i)^j.val ∈ A i := Filter.eventually_all.mpr hj
  filter_upwards [hA,hprev,hexit,hmin,hvne,hall] with i hAi hpi hei hmi hvni halli
  have hNi : 0 < N i := by
    by_contra h
    have he : N i = 0 := by omega
    exact hei (by simpa [he] using hAi)
  have hvA : v i ∈ A i := by simpa using halli ⟨1,by omega⟩
  have hnorm := hmi (v i) hvA hvni
  have hupper := escapeNorm_le_of_powers (n := M+1)
    (fun j hj => halli ⟨j,by omega⟩)
  rw [escapeNorm_eq_inv_of_first_exit hAi hei hpi] at hnorm
  have he := hnorm.trans hupper
  have hNr : 0 < (N i : ℝ) := by exact_mod_cast hNi
  have hnum := (div_le_div_iff₀ hNr (by positivity : 0 < ((M+1 : ℕ) : ℝ)+1)).1 he
  have hnum' : (M : ℝ)+2 ≤ (N i : ℝ) := by
    simp only [one_mul,Nat.cast_add,Nat.cast_one] at hnum
    linarith
  have hbound : M+2 ≤ N i := by exact_mod_cast hnum'
  omega
end DirectedCycles
