import DirectedCycles.LocalPowerGrid
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Combining a short power segment with a segment of powers of its endpoint
constructs all intermediate powers up to the product of the two lengths.
All values lie in A^2 and all bracketings are certified. -/
theorem PowerSegment.exists_multiples {u : G} {m K : ℕ} (p : L.PowerSegment u m)
    (q : L.PowerSegment (p.power m) K) (hm : 1 ≤ m) (hK : 1 ≤ K)
    {A : Set G} (hA : L.one ∈ A) (hpA : ∀ n ≤ m, p.power n ∈ A)
    (hqA : ∀ n ≤ K, q.power n ∈ A) (hdom : L.AllProductsDefined A 4) :
    ∃ s : L.PowerSegment u (m*K), (∀ n ≤ m, s.power n = p.power n) ∧
      (∀ i ≤ K, s.power (i*m) = q.power i) ∧
      (∀ n ≤ m*K, s.power n ∈ L.wordPower A 2) := by
  classical
  have hm0 : 0 < m := by omega
  have hbin : ∀ i ≤ K, ∀ r ≤ m, L.Defined (q.power i) (p.power r) := by
    intro i hi r hr
    obtain ⟨z,hz⟩ := hdom [q.power i,p.power r] (by simp) (by aesop)
    exact ⟨z,(Product.pair_iff L _ _ _).1 hz⟩
  let F : ℕ → ℕ → G := fun i r => if h : i ≤ K ∧ r ≤ m then
    L.mul (q.power i) (p.power r) (hbin i h.1 r h.2) else L.one
  have hF : ∀ i ≤ K, ∀ r ≤ m, L.mulRel (q.power i) (p.power r) (F i r) := by
    intro i hi r hr
    dsimp only [F]
    rw [dite_eq_left ⟨hi,hr⟩]
    exact L.mul_spec _ _ _
  obtain ⟨hplain,hcarry⟩ := L.power_grid_add p q hm hA hpA hqA hdom F hF
  let f : ℕ → G := fun n => F (n/m) (n%m)
  have hdiv : ∀ n ≤ m*K, n/m ≤ K := by
    intro n hn
    calc
      n/m ≤ (K*m)/m := Nat.div_le_div_right (by nlinarith)
      _ = K := Nat.mul_div_cancel K hm0
  have hsmall : ∀ n < m, f n = p.power n := by
    intro n hn
    dsimp only [f]
    rw [Nat.div_eq_of_lt hn,Nat.mod_eq_of_lt hn]
    have hh := hF 0 (by omega) n hn.le
    rw [q.zero] at hh
    exact L.unique hh (L.one_mul _)
  have hend : ∀ i ≤ K, f (i*m) = q.power i := by
    intro i hi
    dsimp only [f]
    rw [Nat.mul_div_cancel i hm0,Nat.mul_mod_left]
    have hh := hF i hi 0 (by omega)
    rw [p.zero] at hh
    exact L.unique hh (L.mul_one _)
  have hfirst : ∀ n ≤ m, f n = p.power n := by
    intro n hn
    by_cases he : n = m
    · subst n
      have hh := hend 1 hK
      simpa only [Nat.one_mul,q.one hK] using hh
    · exact hsmall n (by omega)
  have h0 : f 0 = L.one := (hsmall 0 hm0).trans p.zero
  have h1 : f 1 = u := (hfirst 1 hm).trans (p.one hm)
  have hadd : ∀ n t, n+t ≤ m*K → L.mulRel (f n) (f t) (f (n+t)) := by
    intro n t hnt
    have hdnt := hdiv (n+t) hnt
    have hnr := Nat.mod_lt n hm0
    have htr := Nat.mod_lt t hm0
    dsimp only [f]
    by_cases hc : n%m+t%m < m
    · rw [Nat.add_div_eq_of_add_mod_lt hc,Nat.add_mod_of_add_mod_lt hc]
      apply hplain
      · simpa only [Nat.add_div_eq_of_add_mod_lt hc] using hdnt
      · exact hc
    · have hc' : m ≤ n%m+t%m := by omega
      have hmadd : (n+t)%m = n%m+t%m-m := by
        have hh := Nat.add_mod_add_of_le_add_mod hc'
        omega
      rw [Nat.add_div_eq_of_le_mod_add_mod hc' hm0,hmadd]
      apply hcarry
      · simpa only [Nat.add_div_eq_of_le_mod_add_mod hc' hm0] using hdnt
      · exact hnr
      · exact htr
      · exact hc'
  let s := PowerSegment.of_add L f h0 (fun _ => h1) hadd
  refine ⟨s,hfirst,hend,?_⟩
  intro n hn
  exact ⟨[q.power (n/m),p.power (n%m)],rfl,by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact hqA (n/m) (hdiv n hn)
    · exact hpA (n%m) (Nat.mod_lt n hm0).le,
    (Product.pair_iff L _ _ _).2 (hF (n/m) (hdiv n hn) (n%m) (Nat.mod_lt n hm0).le)⟩
end LocalGroupAlgebra
end DirectedCycles
