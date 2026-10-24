import DirectedCycles.LocalEscapePowerCutoff
import DirectedCycles.LocalPowerSegmentCompression
import DirectedCycles.LocalUltraproductEscape
import DirectedCycles.LocalEscapeNSS
import DirectedCycles.LocalGroupHom

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Long powers in a set give powers of a certified segment endpoint in
that same set, with all bracketings supplied by word compression. -/
theorem powerIn_segment_endpoint {A : Set G} (hA : L.one ∈ A) {u : G} {N : ℕ}
    (p : L.PowerSegment u N) (k : ℕ)
    (hp : ∀ n ≤ k*N, L.PowerIn A u n) : L.PowerIn A (p.power N) k := by
  by_cases hk : k = 0
  · subst k
    exact (L.powerIn_zero _ _).2 hA
  have hNk : N ≤ k*N := Nat.le_mul_of_pos_left N (by omega)
  let q := L.powerSegmentOfPowerIn hp
  have he : q.power N = p.power N := (q.product N hNk).unique L (p.product N le_rfl)
  refine ⟨q.power (k*N),L.powerSegmentOfPowerIn_mem hp le_rfl,?_⟩
  rw [← he]
  exact q.product_power L hNk le_rfl
/-- The one-step power segment exists in every local group. -/
def singlePowerSegment (u : G) : L.PowerSegment u 1 where
  power n := if n = 0 then L.one else u
  product n hn := by
    rcases n with _ | n
    · simp only [List.replicate_zero]
      exact Product.nil
    · have hn0 : n = 0 := by omega
      subst n
      simpa only [Nat.zero_add,ite_eq_right (by omega : (1 : ℕ) ≠ 0),List.replicate_one] using Product.singleton (L := L) u

end LocalGroupAlgebra

variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- An endpoint whose scale times the source escape norm is infinitesimal
maps to the identity in a local target with no nontrivial complete power
sequences. This proves the quotient-model kernel step using actual domains. -/
theorem local_model_kills_negligible_escape_power {H : Type*} (T : LocalGroupAlgebra H)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (N i))
    (hA : ∀ᶠ i in (U : Filter ι), (L i).one ∈ A i)
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι),
      (L i).escapeNorm (A i) (u i)*(N i : ℝ) < ε)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) T)
    (V : Set H)
    (hNSS : ∀ x : H, ∀ q : T.PowerSequence x, (∀ n, q.power n ∈ V) → x = T.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V) :
    π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).power (N i))) = T.one := by
  classical
  let z := localUltraMk (U : Filter ι) G (fun i => (p i).power (N i))
  have hall : ∀ k : ℕ, T.PowerIn V (π.toFun z) k := by
    intro k
    have hcomponent : ∀ᶠ i in (U : Filter ι), (L i).PowerIn (A i) ((p i).power (N i)) k := by
      filter_upwards [hA,hN,hsmall (1/((k : ℝ)+1)) (by positivity)] with i hAi hNi hsi
      have hnonneg := (L i).escapeNorm_nonneg hAi (u i)
      have hNi' : (1 : ℝ) ≤ N i := by exact_mod_cast hNi
      have hcut : (L i).escapeNorm (A i) (u i) < 1/(((k*N i : ℕ) : ℝ)+1) := by
        apply (lt_div_iff₀ (by positivity : 0 < ((k*N i : ℕ) : ℝ)+1)).2
        have hh := (lt_div_iff₀ (by positivity : 0 < (k : ℝ)+1)).1 hsi
        have hmul := mul_le_mul_of_nonneg_left hNi' hnonneg
        push_cast
        nlinarith
      exact (L i).powerIn_segment_endpoint hAi (p i) k ((L i).powerIn_of_escapeNorm_lt hAi hcut)
    obtain ⟨y,hy,hprod⟩ := (localUltraPowerIn_mk_iff (U : Filter ι) G L A _ k).2 hcomponent
    refine ⟨π.toFun y,himage y hy,?_⟩
    simpa only [List.map_replicate] using hprod.map π
  let q : T.PowerSequence (π.toFun z) :=
    ⟨fun n => Classical.choose (hall n),fun n => (Classical.choose_spec (hall n)).2⟩
  exact hNSS _ q (fun n => (Classical.choose_spec (hall n)).1)
/-- Infinitesimal component escape maps to the identity in the same actual
local target. This is the zero-scale case needed before choosing a first-exit
curve for a least lift. -/
theorem local_model_kills_infinitesimal_escape {H : Type*} (T : LocalGroupAlgebra H)
    (A : ∀ i, Set (G i)) (u : ∀ i, G i)
    (hA : ∀ᶠ i in (U : Filter ι), (L i).one ∈ A i)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι), (L i).escapeNorm (A i) (u i) < ε)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) T)
    (V : Set H)
    (hNSS : ∀ x : H, ∀ q : T.PowerSequence x, (∀ n, q.power n ∈ V) → x = T.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) G A, π.toFun z ∈ V) :
    π.toFun (localUltraMk (U : Filter ι) G u) = T.one := by
  have he := local_model_kills_negligible_escape_power U G L T A u (fun _ => 1)
    (fun i => (L i).singlePowerSegment (u i)) hA (Filter.Eventually.of_forall fun _ => by omega)
    (fun ε hε => by simpa only [Nat.cast_one,mul_one] using hsmall ε hε) π V hNSS himage
  exact he
end DirectedCycles
