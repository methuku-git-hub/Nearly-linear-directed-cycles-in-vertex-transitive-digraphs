import DirectedCycles.LocalRestrictedProductNorm
import DirectedCycles.LocalFactorBump
import DirectedCycles.LocalEscapeMaps
import Mathlib.Data.Finset.Max

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- The regularized escape distance uses only A-by-A multiplication nodes.
Its limited subadditivity matches exactly the local bootstrap domain. -/
noncomputable def restrictedEscapeDistance (A : Set G) (ε : ℝ) : G → ℝ :=
  L.restrictedProductNorm A (fun g => L.escapeNorm A g+ε)

theorem restrictedEscapeDistance_nonneg {A : Set G} (hA : L.one ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) (g : G) : 0 ≤ L.restrictedEscapeDistance A ε g :=
  L.restrictedProductNorm_nonneg (fun x => add_nonneg (L.escapeNorm_nonneg hA x) hε) g

theorem restrictedEscapeDistance_one {A : Set G} (hA : L.one ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) : L.restrictedEscapeDistance A ε L.one = 0 :=
  L.restrictedProductNorm_one (fun x => add_nonneg (L.escapeNorm_nonneg hA x) hε)

theorem restrictedEscapeDistance_le {A : Set G} (hA : L.one ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) (g : G) : L.restrictedEscapeDistance A ε g ≤ L.escapeNorm A g+ε :=
  L.restrictedProductNorm_le_weight (fun x => add_nonneg (L.escapeNorm_nonneg hA x) hε) g

theorem restrictedEscapeDistance_mul_le {A : Set G} (hA : L.one ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) {a b c : G} (ha : a ∈ A) (hb : b ∈ A) (hm : L.mulRel a b c) :
    L.restrictedEscapeDistance A ε c ≤ L.restrictedEscapeDistance A ε a+L.restrictedEscapeDistance A ε b :=
  L.restrictedProductNorm_mul_le (fun x => add_nonneg (L.escapeNorm_nonneg hA x) hε) ha hb hm

theorem restrictedEscapeDistance_inv (hr : L.Reversible) {A : Set G}
    (hi : ∀ x ∈ A, L.inv x ∈ A) (ε : ℝ) (g : G) :
    L.restrictedEscapeDistance A ε (L.inv g) = L.restrictedEscapeDistance A ε g :=
  L.restrictedProductNorm_inv hr hi (fun x => by rw [L.escapeNorm_inv hr hi]) g

theorem le_restrictedEscapeDistance_of_not_mem {A : Set G} (hA : L.one ∈ A)
    {ε : ℝ} (hε : 0 ≤ ε) {g : G} (hg : g ∉ A) : ε ≤ L.restrictedEscapeDistance A ε g := by
  apply L.restrictedProductNorm_lower_of_ne_one (fun x => add_nonneg (L.escapeNorm_nonneg hA x) hε)
    (fun x _ => le_add_of_nonneg_left (L.escapeNorm_nonneg hA x))
  intro he
  exact hg (he.symm ▸ hA)

/-- The actual optimal local escape bump, with a point attaining the distance
to the complement. Its support and translation estimates include all domain
checks from the factor-bump construction. -/
theorem exists_optimal_escape_bump [Fintype G]
    (hd : L.DivisionClosed) (hr : L.Reversible) (A : Finset G) (hA : L.one ∈ A)
    (hi : ∀ x ∈ A, L.inv x ∈ A) (hdom : L.AllProductsDefined (A : Set G) 3)
    (hproper : ∃ b : G, b ∉ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, ∃ b : G, ε ≤ r ∧ b ∉ A ∧ L.restrictedEscapeDistance A ε b = r ∧
      (∀ g : G, g ∉ A → r ≤ L.restrictedEscapeDistance A ε g) ∧
      ∃ φ : G → ℝ, (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
        (∀ x ∈ A, φ x = 1) ∧
        (∀ x, x ∉ L.wordPower (A : Set G) 2 → φ x = 0) ∧
        (∀ g x, |L.derivative g φ x| ≤ L.restrictedEscapeDistance A ε g/r) := by
  classical
  have hcomp : (Aᶜ).Nonempty := by
    obtain ⟨b,hb⟩ := hproper
    exact ⟨b,Finset.mem_compl.mpr hb⟩
  obtain ⟨b,hb,hmin⟩ := (Aᶜ).exists_min_image (L.restrictedEscapeDistance A ε) hcomp
  have hbA : b ∉ A := by simpa only [Finset.mem_compl] using hb
  let r := L.restrictedEscapeDistance A ε b
  have hrε : ε ≤ r := L.le_restrictedEscapeDistance_of_not_mem hA hε.le hbA
  have hrpos : 0 < r := hε.trans_le hrε
  have hsep : ∀ g : G, g ∉ A → r ≤ L.restrictedEscapeDistance A ε g :=
    fun g hg => hmin g (Finset.mem_compl.mpr hg)
  refine ⟨r,b,hrε,hbA,rfl,hsep,?_⟩
  exact L.exists_factor_bump hd (hd.cancellative L hr)
    (L.restrictedEscapeDistance_nonneg hA hε.le) (L.restrictedEscapeDistance_one hA hε.le)
    (L.restrictedEscapeDistance_inv hr hi ε) A
    (fun ha hb hm => L.restrictedEscapeDistance_mul_le hA hε.le ha hb hm)
    hA hi hdom hrpos hsep
end LocalGroupAlgebra
end DirectedCycles
