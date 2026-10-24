import DirectedCycles.LocalQuotientMinimalLift
import DirectedCycles.LocalModelPowerLifting
import DirectedCycles.LocalUltraproductEscape
import DirectedCycles.LocalProductDomainTransfer

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (U : Ultrafilter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- A least-escape lift whose model image belongs to the actual progression
image has unbounded exit time. A representative of that progression image
constructs a same-fibre lift in the model kernel. Every fixed power of this
new lift stays in the inner set; finite minimization transfers the bound to
the chosen least lift. -/
theorem local_minimal_lift_exit_unbounded_of_kernel {H : Type*} [Group H]
    (hd : ∀ i, (L i).DivisionClosed)
    (B : ∀ i, Finset (G i)) (P C : ∀ i, Set (G i))
    (D : ∀ i, (L i).CentralQuotientData (P i)) (g : ∀ i, G i) (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) (hg : ∀ i, g i ∈ B i)
    (hB : ∀ i, (B i : Set (G i)) ⊆ (D i).small)
    (hBC : ∀ i, (B i : Set (G i)) ⊆ C i)
    (hB1 : ∀ i, (L i).one ∈ B i)
    (hBdom : ∀ i, (L i).AllProductsDefined (B i : Set (G i)) 2)
    (hPC : ∀ i, P i ⊆ C i)
    (hPi : ∀ i, ∀ x ∈ P i, (L i).inv x ∈ P i)
    (hCdom : ∀ i, (L i).AllProductsDefined (C i) 2)
    (hnorm : ∀ i, (L i).escapeNorm (B i : Set (G i)) (g i) = 1/(N i : ℝ))
    (hmin : ∀ i, ∀ z : (D i).small, z.val ∈ B i →
      (D i).project z = (D i).project ⟨g i,hB i (hg i)⟩ →
        (L i).escapeNorm (B i : Set (G i)) (g i) ≤ (L i).escapeNorm (B i : Set (G i)) z.val)
    (π : LocalGroupHom (localUltraAlgebra (U : Filter ι) G L) (LocalGroupAlgebra.ofGroup H))
    (hkernel : ∀ z, π.toFun z = 1 → z ∈ localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i))))
    (hgp : π.toFun (localUltraMk (U : Filter ι) G g) ∈
      π.toFun '' localUltraSet (U : Filter ι) G P) :
    ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n < N i := by
  classical
  obtain ⟨v,hvP,hvg⟩ := hgp
  obtain ⟨v,rfl⟩ := Quotient.exists_rep v
  have hv := (localUltraMk_mem_iff (U : Filter ι) G P v).1 hvP
  let h : ∀ i, G i := fun i => if hi : (L i).Defined ((L i).inv (v i)) (g i)
    then (L i).mul _ _ hi else (L i).one
  have hrel : ∀ᶠ i in (U : Filter ι), (L i).mulRel ((L i).inv (v i)) (g i) (h i) := by
    filter_upwards [hv] with i hvi
    obtain ⟨z,hz⟩ := hCdom i [(L i).inv (v i),g i] (by simp) (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl
      · exact hPC i (hPi i _ hvi)
      · exact hBC i (hg i))
    have hh : (L i).Defined ((L i).inv (v i)) (g i) :=
      ⟨z,(LocalGroupAlgebra.Product.pair_iff (L i) _ _ _).1 hz⟩
    dsimp only [h]
    rw [dite_eq_left hh]
    exact (L i).mul_spec _ _ hh
  let J := localUltraAlgebra (U : Filter ι) G L
  let S := localUltraSet (U : Filter ι) G (fun i => (B i : Set (G i)))
  let a := localUltraMk (U : Filter ι) G h
  have hrelJ : J.mulRel (J.inv (localUltraMk (U : Filter ι) G v))
      (localUltraMk (U : Filter ι) G g) a :=
    (localUltraMulRel_mk_iff (U : Filter ι) G L _ _ _).2 hrel
  have hπ : π.toFun a = 1 := by
    have he := π.map_mul hrelJ
    change π.toFun (J.inv (localUltraMk (U : Filter ι) G v))*
      π.toFun (localUltraMk (U : Filter ι) G g) = π.toFun a at he
    rw [π.map_inv] at he
    change (π.toFun (localUltraMk (U : Filter ι) G v))⁻¹*
      π.toFun (localUltraMk (U : Filter ι) G g) = π.toFun a at he
    rw [hvg,inv_mul_cancel] at he
    exact he.symm
  have ha : a ∈ S := hkernel _ hπ
  have hS1 : J.one ∈ S :=
    (localUltraMk_mem_iff (U : Filter ι) G _ _).2 (Filter.Eventually.of_forall hB1)
  have hSdom : J.AllProductsDefined S 2 :=
    (localUltra_allProductsDefined_iff U G L _ 2).2 (Filter.Eventually.of_forall hBdom)
  have hbinary : ∀ x ∈ S, ∀ y ∈ S, J.Defined x y := by
    intro x hx y hy
    obtain ⟨z,hz⟩ := hSdom [x,y] (by simp) (by aesop)
    exact ⟨z,(LocalGroupAlgebra.Product.pair_iff J _ _ _).1 hz⟩
  have hpowers : ∀ n : ℕ, J.PowerIn S a n := by
    intro n
    apply J.powerIn_of_model_powers S hS1 hbinary π {1} (fun z hz => hkernel z hz) ha n
    · intro k _
      simp only [hπ,one_pow,Set.mem_singleton_iff]
    · exact le_rfl
  have hmem := (localUltraMk_mem_iff (U : Filter ι) G _ h).1 ha
  have hcompare : ∀ᶠ i in (U : Filter ι),
      (L i).escapeNorm (B i : Set (G i)) (g i) ≤ (L i).escapeNorm (B i : Set (G i)) (h i) := by
    filter_upwards [hv,hrel,hmem] with i hvi hri hhi
    apply hmin i ⟨h i,hB i hhi⟩ hhi
    apply ((D i).project_eq_iff _ _).2
    exact ((D i).relation_iff _ _).2 ⟨(L i).inv (v i),hPi i _ hvi,(hd i).right hri⟩
  intro n
  have hp : ∀ j : Fin (n+2), ∀ᶠ i in (U : Filter ι), (L i).PowerIn (B i : Set (G i)) (h i) j.val :=
    fun j => (localUltraPowerIn_mk_iff (U : Filter ι) G L _ h j.val).1 (hpowers j.val)
  have hall := Filter.eventually_all.mpr hp
  filter_upwards [hcompare,hall] with i hci hpi
  have he := hci.trans ((L i).escapeNorm_le_of_powers (n := n+1) (fun j hj => hpi ⟨j,by omega⟩))
  rw [hnorm i] at he
  have hnpos : (0 : ℝ) < N i := by exact_mod_cast hN i
  have hnum := (div_le_div_iff₀ hnpos (by positivity : 0 < ((n+1 : ℕ) : ℝ)+1)).1 he
  have hnum' : (n : ℝ)+2 ≤ (N i : ℝ) := by
    simp only [one_mul,Nat.cast_add,Nat.cast_one] at hnum
    linarith
  have hbound : n+2 ≤ N i := by exact_mod_cast hnum'
  omega
end DirectedCycles
