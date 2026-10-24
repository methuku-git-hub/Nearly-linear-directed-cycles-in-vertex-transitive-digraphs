import DirectedCycles.LocalProjectedEscapeKernel
import DirectedCycles.LocalNegligibleEscapePower
import DirectedCycles.LocalCentralQuotientUltraHom

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra.CentralQuotientData
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
    (P : ∀ i, Set (G i)) (D : ∀ i, (L i).CentralQuotientData (P i))

/-- An infinitesimal quotient/source escape ratio puts both the chosen
lift and its actual first-exit endpoint in the kernel of the quotient model.
The first-exit identity converts the ratio to the required scaled estimates. -/
theorem projected_negligible_lift_and_exit_kernel
    (hd : ∀ i, (L i).DivisionClosed) (hr : ∀ i, (L i).Reversible)
    (B : ∀ i, Finset (G i)) (u : ∀ i, G i) (N : ι → ℕ)
    (p : ∀ i, (L i).PowerSegment (u i) (N i))
    (hu : ∀ i, u i ∈ (D i).small)
    (hp : ∀ i, ∀ n ≤ N i, (p i).power n ∈ (D i).small)
    (hB1 : ∀ᶠ i in (U : Filter ι), (D i).algebra.one ∈ (D i).finiteImage (B i))
    (hN : ∀ᶠ i in (U : Filter ι), 0 < N i)
    (hnorm : ∀ i, (L i).escapeNorm (B i : Set (G i)) (u i) = 1/(N i : ℝ))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι),
      (D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier)
        ((D i).project ⟨u i,hu i⟩) < ε*(L i).escapeNorm (B i : Set (G i)) (u i))
    {H T : Type*} [Group H] (M : LocalGroupAlgebra T)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (F : LocalGroupHom (ultraproduct U G L P D).algebra M) (Q : Set H)
    (hkernel : ∀ a : (ultraproduct U G L P D).small,
      F.toFun ((ultraproduct U G L P D).project a) = M.one → π.toFun a.val ∈ Q)
    (V : Set T)
    (hNSS : ∀ x : T, ∀ q : M.PowerSequence x, (∀ n, q.power n ∈ V) → x = M.one)
    (himage : ∀ z ∈ localUltraSet (U : Filter ι) (fun i => (D i).Carrier)
        (fun i => ((D i).finiteImage (B i) : Set (D i).Carrier)),
      F.toFun ((quotientUltraHom U G L P D hd hr).toFun z) ∈ V) :
    π.toFun (localUltraMk (U : Filter ι) G u) ∈ Q ∧
    π.toFun (localUltraMk (U : Filter ι) G (fun i => (p i).power (N i))) ∈ Q := by
  have hscaled : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι),
      (D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier)
        ((D i).project ⟨u i,hu i⟩)*(N i : ℝ) < ε := by
    intro ε hε
    filter_upwards [hsmall ε hε,hN] with i hi hni
    rw [hnorm i,mul_one_div] at hi
    exact (lt_div_iff₀ (by exact_mod_cast hni)).1 hi
  have hexit := projected_negligible_escape_kernel U G L P D hd hr B u N p hu hp hB1 hN hscaled
    M π F Q hkernel V hNSS himage
  let p₁ : ∀ i, (L i).PowerSegment (u i) 1 := fun i =>
    ⟨fun n => if n = 0 then (L i).one else u i,by
      intro n hn
      have hh : n = 0 ∨ n = 1 := by omega
      rcases hh with rfl | rfl
      · simpa only [List.replicate_zero,ite_true] using (LocalGroupAlgebra.Product.nil (L := L i))
      · simpa only [List.replicate_one,ite_false,Nat.one_ne_zero] using (LocalGroupAlgebra.Product.singleton (L := L i) (u i))⟩
  have hp₁ : ∀ i, ∀ n ≤ 1, (p₁ i).power n ∈ (D i).small := by
    intro i n hn
    dsimp only [p₁]
    split_ifs
    · exact (D i).one_mem
    · exact hu i
  have hscaled₁ : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι),
      (D i).algebra.escapeNorm ((D i).finiteImage (B i) : Set (D i).Carrier)
        ((D i).project ⟨u i,hu i⟩)*((1 : ℕ) : ℝ) < ε := by
    intro ε hε
    filter_upwards [hscaled ε hε,hN,hB1] with i hi hni hbi
    have hb := (D i).algebra.escapeNorm_nonneg hbi ((D i).project ⟨u i,hu i⟩)
    have hni' : (1 : ℝ) ≤ N i := by exact_mod_cast hni
    norm_num only [Nat.cast_one,mul_one]
    nlinarith
  have hone := projected_negligible_escape_kernel U G L P D hd hr B u (fun _ => 1) p₁ hu hp₁
    hB1 (Filter.Eventually.of_forall fun _ => by omega) hscaled₁ M π F Q hkernel V hNSS himage
  exact ⟨by simpa only [p₁,Nat.one_ne_zero,ite_false] using hone,hexit⟩
end LocalGroupAlgebra.CentralQuotientData
end DirectedCycles
