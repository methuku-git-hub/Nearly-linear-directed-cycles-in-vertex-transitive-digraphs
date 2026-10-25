module

public import DirectedCycles.LocalNestedSegmentComparison
public import DirectedCycles.LocalToLocalClosedScaledExponentLimit
public import DirectedCycles.LocalUltraproductEscape

@[expose] public section

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles

/-- A nested internal source containing the model kernel retains a positive
proportion of the selected central generator's outer scale. This yields a
uniform reciprocal-length escape bound, with no quotient NSS assumption. -/
theorem local_to_local_central_generator_escape_bound {ι H : Type*} (Q : LocalGroupAlgebra H)
    (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (A B : ∀ i, Set (G i)) (hB1 : ∀ i, (L i).one ∈ B i) (hBA : ∀ i, B i ⊆ A i)
    (hi : ∀ i, ∀ x ∈ A i, (L i).inv x ∈ A i)
    (u : ∀ i, G i) (N : ι → ℕ) (p : ∀ i, (L i).PowerSegment (u i) (2*N i))
    (hN0 : ∀ i, 0 < N i)
    (hN : ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i)
    (hprev : ∀ i, ∀ n < N i, (p i).power n ∈ A i)
    (hexit : ∀ i, (p i).power (N i) ∉ A i)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) Q)
    (V : Set H) (hNSS : ∀ x : H, ∀ q : Q.PowerSequence x, (∀ n, q.power n ∈ V) → x = Q.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V)
    (hkernel : ∀ z, π.toFun z = Q.one → z ∈ localUltraSet (U : Filter ι) G B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in (U : Filter ι),
      (L i).escapeNorm (B i) (u i) ≤ C/((N i : ℝ)+1) := by
  classical
  have hbad : ∀ i, ∃ k : ℕ, (p i).power k ∉ B i :=
    fun i => ⟨N i,fun h => hexit i (hBA i h)⟩
  let K := fun i => Nat.find (hbad i)
  have hKe : ∀ i, (p i).power (K i) ∉ B i := fun i => Nat.find_spec (hbad i)
  have hKN : ∀ i, K i ≤ N i := fun i => Nat.find_min' (hbad i) (fun h => hexit i (hBA i h))
  have hKprev : ∀ i, ∀ k < K i, (p i).power k ∈ B i := by
    intro i k hk
    exact not_not.mp (Nat.find_min (hbad i) hk)
  have hKpos : ∀ i, 0 < K i := by
    intro i
    by_contra hh
    have hk : K i = 0 := by omega
    exact hKe i (by rw [hk,(p i).zero]; exact hB1 i)
  have hnorm : ∀ i, (L i).escapeNorm (B i) (u i) = 1/(K i : ℝ) := by
    intro i
    apply (L i).escapeNorm_eq_inv_of_first_exit (hB1 i)
    · rintro ⟨x,hx,hp⟩
      have he := hp.unique (L i) ((p i).product (K i) (by have := hKN i; omega))
      exact hKe i (he ▸ hx)
    · intro n hn
      exact ⟨(p i).power n,hKprev i n hn,(p i).product n (by have := hKN i; omega)⟩
  obtain ⟨t,ht,hlim⟩ := bounded_nat_ratio_ultralimit U N K (Filter.Eventually.of_forall hKN)
  have htpos : 0 < t := by
    by_contra hh
    have ht0 : t = 0 := le_antisymm (le_of_not_gt hh) ht.1
    have he := local_to_local_model_scaled_exponent_limit_closed U G L Q hd hr A u N (fun i => 2*N i) p
      (fun i => (K i : ℤ)) 0 hN (Filter.Eventually.of_forall fun _ => le_rfl)
      (Filter.Eventually.of_forall hi) (Filter.Eventually.of_forall hprev)
      (Filter.Eventually.of_forall fun i => by simpa only [Int.natAbs_natCast] using hKN i) (by norm_num)
      (by simpa only [Int.cast_natCast,ht0] using hlim) π V hNSS himage
    rw [localScaledPower_zero,π.map_one] at he
    have hm := hkernel _ he
    have hevent := (localUltraMk_mem_iff (U : Filter ι) G B _).1 hm
    have hfalse : ∀ᶠ i in (U : Filter ι), False := hevent.mono fun i hh =>
      hKe i (by simpa only [(p i).signedPower_nat] using hh)
    obtain ⟨i,hiFalse⟩ := Filter.Eventually.exists hfalse
    exact hiFalse
  have hratio : ∀ᶠ i in (U : Filter ι), t/2 < (K i : ℝ)/(N i : ℝ) :=
    hlim.eventually (Ioi_mem_nhds (by linarith : t/2 < t))
  refine ⟨4/t,by positivity,?_⟩
  filter_upwards [hratio] with i hi'
  rw [hnorm i]
  have hkr : (0 : ℝ) < K i := by exact_mod_cast hKpos i
  have hnr : (0 : ℝ) < N i := by exact_mod_cast hN0 i
  have hn1 : (1 : ℝ) ≤ N i := by exact_mod_cast hN0 i
  have hh : (t/2)*(N i : ℝ) < K i := (lt_div_iff₀ hnr).1 hi'
  apply (div_le_div_iff₀ hkr (by positivity : (0 : ℝ) < (N i : ℝ)+1)).2
  rw [one_mul,show (4/t)*(K i : ℝ) = (4*(K i : ℝ))/t by ring]
  apply (le_div_iff₀ htpos).2
  nlinarith
end DirectedCycles
