module

public import DirectedCycles.LocalUltraproductProducts
public import DirectedCycles.LocalUltraproductDomain
public import DirectedCycles.LocalEscapeNorm
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- A fixed local power lies in an internal set precisely when the component
all-bracketings power lies in the component set eventually. -/
theorem localUltraPowerIn_mk_iff (A : ∀ i, Set (G i)) (a : ∀ i, G i) (n : ℕ) :
    (localUltraAlgebra F G L).PowerIn (localUltraSet F G A) (localUltraMk F G a) n ↔
      ∀ᶠ i in F, (L i).PowerIn (A i) (a i) n := by
  classical
  constructor
  · rintro ⟨x,hx,hp⟩
    obtain ⟨b,rfl⟩ := Quotient.exists_rep x
    have hb := (localUltraMk_mem_iff F G A b).1 hx
    have hprod : ∀ᶠ i in F, (L i).Product (List.replicate n (a i)) (b i) := by
      simpa only [List.map_replicate] using
        (localUltraProduct_mk_iff F G L (List.replicate n a) b).1 (by simpa using hp)
    filter_upwards [hb,hprod] with i hbi hpi
    exact ⟨b i,hbi,hpi⟩
  · intro h
    let b : ∀ i, G i := fun i => if hi : (L i).PowerIn (A i) (a i) n
      then Classical.choose hi else (L i).one
    have hb : ∀ᶠ i in F, b i ∈ A i ∧ (L i).Product (List.replicate n (a i)) (b i) := by
      filter_upwards [h] with i hi
      dsimp only [b]
      rw [dite_eq_left hi]
      exact Classical.choose_spec hi
    refine ⟨localUltraMk F G b,(localUltraMk_mem_iff F G A b).2 (hb.mono fun _ hi => hi.1),?_⟩
    have hprod := (localUltraProduct_mk_iff F G L (List.replicate n a) b).2 (by
      simpa only [List.map_replicate] using hb.mono (fun _ hi => hi.2))
    simpa only [List.map_replicate] using hprod

namespace LocalGroupAlgebra
variable {J : Type*} (M : LocalGroupAlgebra J)

theorem escapeNorm_eq_inv_of_first_exit {A : Set J} (hA : M.one ∈ A) {g : J} {N : ℕ}
    (hbad : ¬ M.PowerIn A g N) (hprev : ∀ n < N, M.PowerIn A g n) :
    M.escapeNorm A g = 1/(N : ℝ) := by
  have hN : 0 < N := by
    by_contra h
    have he : N = 0 := by omega
    subst N
    exact hbad ((M.powerIn_zero A g).2 hA)
  apply le_antisymm _ (M.inv_le_escapeNorm_of_not_powerIn hA hbad)
  have hh := M.escapeNorm_le_of_powers (n := N-1) (fun n hn => hprev n (by omega))
  have he : ((N-1 : ℕ) : ℝ)+1 = N := by exact_mod_cast (Nat.sub_add_cancel hN)
  simpa only [he] using hh
end LocalGroupAlgebra

variable (U : Ultrafilter ι)

/-- The actual local escape norm is the ultralimit of the actual finite-stage
escape norms. Zero limit is not confused with eventual exact zero. -/
theorem localUltra_escapeNorm_tendsto (A : ∀ i, Set (G i)) (a : ∀ i, G i)
    (hA : ∀ᶠ i in (U : Filter ι), (L i).one ∈ A i) :
    Filter.Tendsto (fun i => (L i).escapeNorm (A i) (a i)) (U : Filter ι)
      (𝓝 ((localUltraAlgebra (U : Filter ι) G L).escapeNorm
        (localUltraSet (U : Filter ι) G A) (localUltraMk (U : Filter ι) G a))) := by
  classical
  let M := localUltraAlgebra (U : Filter ι) G L
  let B := localUltraSet (U : Filter ι) G A
  let z := localUltraMk (U : Filter ι) G a
  have hB : M.one ∈ B := (localUltraMk_mem_iff _ G A (fun i => (L i).one)).2 hA
  by_cases hall : ∀ n : ℕ, M.PowerIn B z n
  · have hz : M.escapeNorm B z = 0 := (M.escapeNorm_eq_zero_iff hB z).2 hall
    change Filter.Tendsto _ _ (𝓝 (M.escapeNorm B z))
    rw [hz]
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨m,hm⟩ := exists_nat_one_div_lt hε
    have each : ∀ j : Fin (m+1), ∀ᶠ i in (U : Filter ι), (L i).PowerIn (A i) (a i) j.val := by
      intro j
      exact (localUltraPowerIn_mk_iff _ G L A a j.val).1 (hall j.val)
    have hf := Filter.eventually_all.2 each
    filter_upwards [hf,hA] with i hi hAi
    have hnorm := (L i).escapeNorm_le_of_powers (n := m) (fun n hn => hi ⟨n,by omega⟩)
    have hnonneg := (L i).escapeNorm_nonneg hAi (a i)
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg] using hnorm.trans_lt hm
  · have hex : ∃ n : ℕ, ¬ M.PowerIn B z n := by simpa using hall
    let N := Nat.find hex
    have hbad : ¬ M.PowerIn B z N := Nat.find_spec hex
    have hprev : ∀ n < N, M.PowerIn B z n := fun n hn => not_not.mp (Nat.find_min hex hn)
    have hz := M.escapeNorm_eq_inv_of_first_exit hB hbad hprev
    have hbad' : ∀ᶠ i in (U : Filter ι), ¬ (L i).PowerIn (A i) (a i) N := by
      apply (Ultrafilter.eventually_not).2
      intro he
      exact hbad ((localUltraPowerIn_mk_iff _ G L A a N).2 he)
    have each : ∀ j : Fin N, ∀ᶠ i in (U : Filter ι), (L i).PowerIn (A i) (a i) j.val := by
      intro j
      exact (localUltraPowerIn_mk_iff _ G L A a j.val).1 (hprev j.val j.isLt)
    have hf := Filter.eventually_all.2 each
    have he : (fun i => (L i).escapeNorm (A i) (a i)) =ᶠ[(U : Filter ι)]
        (fun _ => M.escapeNorm B z) := by
      filter_upwards [hf,hbad',hA] with i hi hbi hAi
      rw [hz]
      exact (L i).escapeNorm_eq_inv_of_first_exit hAi hbi (fun n hn => hi ⟨n,hn⟩)
    exact (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => M.escapeNorm B z) (U : Filter ι) (𝓝 (M.escapeNorm B z))).congr' he.symm
end DirectedCycles
