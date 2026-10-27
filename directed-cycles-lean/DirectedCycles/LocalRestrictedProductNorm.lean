module

public import DirectedCycles.LocalGroupReversal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Costs of parenthesized local products whose two children at each internal
node both lie in A. Leaves can be arbitrary elements. This restriction is
needed for applying local derivative subadditivity in the bootstrap. -/
inductive RestrictedProductCost (A : Set G) (w : G → ℝ) : G → ℝ → Prop
  | one : RestrictedProductCost A w L.one 0
  | leaf (g : G) : RestrictedProductCost A w g (w g)
  | mul {a b c : G} {r s : ℝ} : RestrictedProductCost A w a r → RestrictedProductCost A w b s →
      a ∈ A → b ∈ A → L.mulRel a b c → RestrictedProductCost A w c (r+s)

variable {A : Set G}

theorem RestrictedProductCost.nonneg {w : G → ℝ} (hw : ∀ g, 0 ≤ w g)
    {g : G} {r : ℝ} (h : L.RestrictedProductCost A w g r) : 0 ≤ r := by
  induction h with
  | one => exact le_rfl
  | leaf g => exact hw g
  | mul _ _ _ _ _ ih ih' => exact add_nonneg ih ih'

theorem RestrictedProductCost.inv (hr : L.Reversible) (hAi : ∀ a ∈ A, L.inv a ∈ A)
    {w : G → ℝ} (hi : ∀ g, w (L.inv g) = w g)
    {g : G} {r : ℝ} (h : L.RestrictedProductCost A w g r) :
    L.RestrictedProductCost A w (L.inv g) r := by
  induction h with
  | one => simpa only [L.inv_one] using RestrictedProductCost.one (L := L) (A := A) (w := w)
  | leaf g => simpa only [hi g] using RestrictedProductCost.leaf (L := L) (A := A) (w := w) (L.inv g)
  | mul _ _ ha hb hm ih ih' =>
    simpa only [add_comm] using RestrictedProductCost.mul ih' ih (hAi _ hb) (hAi _ ha) (hr hm)

theorem RestrictedProductCost.lower_of_ne_one {w : G → ℝ} (hw : ∀ g, 0 ≤ w g)
    {ε : ℝ} (hε : ∀ g, g ≠ L.one → ε ≤ w g)
    {g : G} {r : ℝ} (h : L.RestrictedProductCost A w g r) (hg : g ≠ L.one) : ε ≤ r := by
  induction h with
  | one => exact (hg rfl).elim
  | leaf g => exact hε g hg
  | @mul a b c r s ha hb _ _ hm iha ihb =>
    by_cases ha1 : a = L.one
    · have hb1 : b ≠ L.one := by
        intro he
        have hc1 : c = L.one := L.unique (by simpa only [ha1,he] using hm) (L.one_mul L.one)
        exact hg hc1
      have hs := ihb hb1
      have hr := ha.nonneg L hw
      linarith
    · have hr := iha ha1
      have hs := hb.nonneg L hw
      linarith

noncomputable def restrictedProductNorm (A : Set G) (w : G → ℝ) (g : G) : ℝ :=
  sInf {r | L.RestrictedProductCost A w g r}

theorem restrictedProductCost_nonempty (A : Set G) (w : G → ℝ) (g : G) :
    {r | L.RestrictedProductCost A w g r}.Nonempty := ⟨w g,RestrictedProductCost.leaf g⟩

theorem restrictedProductCost_bddBelow {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (g : G) :
    BddBelow {r | L.RestrictedProductCost A w g r} := ⟨0,fun _ h => h.nonneg L hw⟩

theorem restrictedProductNorm_nonneg {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (g : G) :
    0 ≤ L.restrictedProductNorm A w g :=
  le_csInf (L.restrictedProductCost_nonempty A w g) (fun _ h => h.nonneg L hw)

theorem restrictedProductNorm_le_cost {w : G → ℝ} (hw : ∀ g, 0 ≤ w g)
    {g : G} {r : ℝ} (h : L.RestrictedProductCost A w g r) : L.restrictedProductNorm A w g ≤ r :=
  csInf_le (L.restrictedProductCost_bddBelow hw g) h

theorem restrictedProductNorm_le_weight {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (g : G) :
    L.restrictedProductNorm A w g ≤ w g := L.restrictedProductNorm_le_cost hw (RestrictedProductCost.leaf g)

theorem restrictedProductNorm_one {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) :
    L.restrictedProductNorm A w L.one = 0 :=
  le_antisymm (L.restrictedProductNorm_le_cost hw RestrictedProductCost.one) (L.restrictedProductNorm_nonneg hw L.one)

theorem restrictedProductNorm_mul_le {w : G → ℝ} (hw : ∀ g, 0 ≤ w g)
    {a b c : G} (ha : a ∈ A) (hb : b ∈ A) (hm : L.mulRel a b c) :
    L.restrictedProductNorm A w c ≤ L.restrictedProductNorm A w a+L.restrictedProductNorm A w b := by
  apply (sub_le_iff_le_add).mp
  apply le_csInf (L.restrictedProductCost_nonempty A w a)
  intro r hr
  have hb' : L.restrictedProductNorm A w c-r ≤ L.restrictedProductNorm A w b := by
    apply le_csInf (L.restrictedProductCost_nonempty A w b)
    intro s hs
    have hh := L.restrictedProductNorm_le_cost hw (RestrictedProductCost.mul hr hs ha hb hm)
    linarith
  linarith

theorem restrictedProductNorm_inv (hr : L.Reversible) (hAi : ∀ a ∈ A, L.inv a ∈ A)
    {w : G → ℝ} (hi : ∀ g, w (L.inv g) = w g) (g : G) :
    L.restrictedProductNorm A w (L.inv g) = L.restrictedProductNorm A w g := by
  unfold restrictedProductNorm
  congr 1
  ext r
  change L.RestrictedProductCost A w (L.inv g) r ↔ L.RestrictedProductCost A w g r
  constructor
  · intro h
    simpa only [L.inv_inv] using h.inv L hr hAi hi
  · exact fun h => h.inv L hr hAi hi

theorem restrictedProductNorm_lower_of_ne_one {w : G → ℝ} (hw : ∀ g, 0 ≤ w g)
    {ε : ℝ} (hε : ∀ g, g ≠ L.one → ε ≤ w g) {g : G} (hg : g ≠ L.one) :
    ε ≤ L.restrictedProductNorm A w g :=
  le_csInf (L.restrictedProductCost_nonempty A w g) (fun _ h => h.lower_of_ne_one L hw hε hg)

/-- The greatest-minorant property needs subadditivity only at the permitted
A-by-A nodes. This is the form required for local derivative norms. -/
theorem le_mul_restrictedProductNorm {w F : G → ℝ} {C : ℝ} (hC : 0 < C)
    (h1 : F L.one = 0) (hF : ∀ {a b c}, a ∈ A → b ∈ A → L.mulRel a b c → F c ≤ F a+F b)
    (hbound : ∀ g, F g ≤ C*w g) (g : G) : F g ≤ C*L.restrictedProductNorm A w g := by
  have hall : ∀ {g r}, L.RestrictedProductCost A w g r → F g ≤ C*r := by
    intro g r h
    induction h with
    | one => simp only [h1,mul_zero,le_refl]
    | leaf g => exact hbound g
    | mul _ _ ha hb hm ih ih' =>
      have ht := hF ha hb hm
      nlinarith
  suffices hh : F g/C ≤ L.restrictedProductNorm A w g by
    simpa only [mul_comm] using (div_le_iff₀ hC).mp hh
  apply le_csInf (L.restrictedProductCost_nonempty A w g)
  intro r hr
  exact (div_le_iff₀ hC).2 (by simpa only [mul_comm] using hall hr)
end LocalGroupAlgebra
end DirectedCycles
