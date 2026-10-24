import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace DirectedCycles

/-- Finite minimization turns failure of a uniform domination bound into
one actual family with infinitesimal ratio. No countable saturation or
countable incompleteness of the ultrafilter is assumed. -/
theorem finite_uniform_domination_of_no_infinitesimal {ι : Type*} (U : Ultrafilter ι)
    (X : ι → Type*) (x₀ : ∀ i, X i) (F : ∀ i, Finset (X i))
    (a b : ∀ i, X i → ℝ) (hb : ∀ i, ∀ x ∈ F i, 0 ≤ b i x)
    (hexclude : ∀ x : ∀ i, X i, (∀ᶠ i in (U : Filter ι), x i ∈ F i ∧ 0 < a i (x i)) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι), b i (x i) < ε*a i (x i)) → False) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in (U : Filter ι), ∀ x ∈ F i, a i x ≤ C*b i x := by
  classical
  by_contra hn
  have hbad : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι),
      ∃ x ∈ F i, 0 < a i x ∧ b i x < ε*a i x := by
    intro ε hε
    have he : ¬ (∀ᶠ i in (U : Filter ι), ∀ x ∈ F i, a i x ≤ (1/ε)*b i x) :=
      fun h => hn ⟨1/ε,by positivity,h⟩
    filter_upwards [Ultrafilter.eventually_not.mpr he] with i hi
    obtain ⟨x,hx,hax⟩ := by simpa only [not_forall,not_le,not_imp] using hi
    have hapos : 0 < a i x := lt_of_le_of_lt (mul_nonneg (by positivity) (hb i x hx)) hax
    refine ⟨x,hx,hapos,?_⟩
    have hm := (mul_lt_mul_iff_right₀ hε).2 hax
    have heq : ε*((1/ε)*b i x) = b i x := by field_simp
    rw [heq] at hm
    nlinarith
  let P := fun i => (F i).filter (fun x => 0 < a i x)
  have hchoice : ∀ i, ∃ p : X i, ∀ x ∈ P i,
      p ∈ P i ∧ b i p/a i p ≤ b i x/a i x := by
    intro i
    by_cases hi : (P i).Nonempty
    · obtain ⟨p,hp,hmin⟩ := (P i).exists_min_image (fun x => b i x/a i x) hi
      exact ⟨p,fun x hx => ⟨hp,hmin x hx⟩⟩
    · exact ⟨x₀ i,fun _ hx => (hi ⟨_,hx⟩).elim⟩
  choose p hp using hchoice
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (U : Filter ι),
      p i ∈ F i ∧ 0 < a i (p i) ∧ b i (p i) < ε*a i (p i) := by
    intro ε hε
    filter_upwards [hbad ε hε] with i hi
    obtain ⟨x,hx,ha,hxb⟩ := hi
    obtain ⟨hpi,hmin⟩ := hp i x (Finset.mem_filter.mpr ⟨hx,ha⟩)
    obtain ⟨hpF,hpa⟩ := Finset.mem_filter.mp hpi
    refine ⟨hpF,hpa,?_⟩
    have hxratio : b i x/a i x < ε := (div_lt_iff₀ ha).2 (by nlinarith)
    exact (div_lt_iff₀ hpa).1 (hmin.trans_lt hxratio)
  exact hexclude p ((hsmall 1 (by norm_num)).mono fun _ hi => ⟨hi.1,hi.2.1⟩)
    (fun ε hε => (hsmall ε hε).mono fun _ hi => hi.2.2)
end DirectedCycles
