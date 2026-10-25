module

public import DirectedCycles.FiniteAlmostPeriods

@[expose] public section

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
namespace FiniteAlmostPeriods
variable {G : Type*} [Group G] [DecidableEq G]

/-- The finite intersection of conjugate squares, with the identity
representative recorded explicitly. -/
def normalCoreSet (S X : Finset G) : Finset G :=
  (S^2).filter (fun g => ∀ x ∈ X, x⁻¹*g*x ∈ S^2)

theorem normalCoreSet_one (S X : Finset G) (hS : 1 ∈ S) : 1 ∈ normalCoreSet S X := by
  have h1 : 1 ∈ S^2 := Finset.one_mem_pow hS
  simp only [normalCoreSet,Finset.mem_filter,mul_one,inv_mul_cancel]
  exact ⟨h1,fun _ _ => h1⟩

theorem normalCoreSet_subset (S X : Finset G) : normalCoreSet S X ⊆ S^2 :=
  Finset.filter_subset _ _

theorem normalCoreSet_symm (S X : Finset G) (hi : S⁻¹ = S) :
    (normalCoreSet S X)⁻¹ = normalCoreSet S X := by
  have hpow : (S^2)⁻¹ = S^2 := by rw [← inv_pow,hi]
  have hmem : ∀ g : G, g⁻¹ ∈ S^2 ↔ g ∈ S^2 := by
    intro g
    rw [← Finset.mem_inv',hpow]
  ext g
  simp only [Finset.mem_inv',normalCoreSet,Finset.mem_filter,hmem]
  have he : ∀ x : G, x⁻¹*g⁻¹*x = (x⁻¹*g*x)⁻¹ := by intro x; group
  simp only [he,hmem]

omit [DecidableEq G] in
theorem conjugate_mem_pow (T U : Set G) (x : G)
    (h : ∀ g ∈ T, x⁻¹*g*x ∈ U) (n : ℕ) :
    ∀ g ∈ T^n, x⁻¹*g*x ∈ U^n := by
  induction n with
  | zero =>
    intro g hg
    have : g = 1 := by simpa using hg
    simp [this]
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg ⊢
    obtain ⟨a,ha,b,hb,rfl⟩ := hg
    refine ⟨x⁻¹*a*x,ih a ha,x⁻¹*b*x,h b hb,?_⟩
    group

/-- The cover must use x = y*s, with the representative on the left.
This order gives the stated conjugation bound in a noncommutative group. -/
theorem normalCoreSet_conjugate_power (S X : Finset G) (A : Set G)
    (hi : S⁻¹ = S) (hcover : A ⊆ (X : Set G)*(S : Set G)^2)
    (n : ℕ) :
    ∀ x ∈ A, ∀ g ∈ (normalCoreSet S X : Set G)^n,
      x⁻¹*g*x ∈ (S : Set G)^(2*n+4) := by
  intro x hx g hg
  obtain ⟨y,hy,s,hs,rfl⟩ := hcover hx
  have hh : y⁻¹*g*y ∈ ((S : Set G)^2)^n := conjugate_mem_pow
    (normalCoreSet S X : Set G) ((S : Set G)^2) y
    (fun z hz => by exact_mod_cast (Finset.mem_filter.mp hz).2 y hy) n g hg
  have his : (S : Set G)⁻¹ = S := by simpa only [Finset.coe_inv] using congrArg (fun T : Finset G => (T : Set G)) hi
  have hsinv : s⁻¹ ∈ (S : Set G)^2 := by
    have hxinv : s⁻¹ ∈ ((S : Set G)^2)⁻¹ := by simpa using hs
    simpa only [← inv_pow,his] using hxinv
  have hm : s⁻¹*(y⁻¹*g*y)*s ∈ (S : Set G)^2 * ((S : Set G)^2)^n * (S : Set G)^2 :=
    Set.mul_mem_mul (Set.mul_mem_mul hsinv hh) hs
  have he : (y*s)⁻¹*g*(y*s) = s⁻¹*(y⁻¹*g*y)*s := by group
  rw [he]
  convert hm using 1
  simp only [← pow_mul,← pow_add]
  congr 1
  omega

end FiniteAlmostPeriods
end DirectedCycles
