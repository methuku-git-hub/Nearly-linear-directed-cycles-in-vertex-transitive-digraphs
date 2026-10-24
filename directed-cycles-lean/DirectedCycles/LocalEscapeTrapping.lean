import DirectedCycles.LocalProductCompression
import DirectedCycles.LocalEscapeNorm

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Powers of a known power value are obtained by compressing equal blocks.
The original long all-bracketings product supplies every needed domain. -/
theorem PowerIn.iterate {A : Set G} {g x : G} {i j : ℕ}
    (hx : L.Product (List.replicate i g) x) (h : L.PowerIn A g (i*j)) :
    L.PowerIn A x j := by
  obtain ⟨y,hy,hp⟩ := h
  have hb : List.Forall₂ L.Product (List.replicate j (List.replicate i g)) (List.replicate j x) := by
    clear hp
    induction j with
    | zero => exact List.Forall₂.nil
    | succ j ih => exact List.Forall₂.cons hx ih
  have hp' : L.Product (List.replicate j (List.replicate i g)).flatten y := by
    simpa only [List.flatten_replicate_replicate,Nat.mul_comm] using hp
  exact ⟨y,hy,hp'.compress L hb⟩

theorem escapeNorm_le_mul_of_segments {A B : Set G} {a b : G} (hA : L.one ∈ A)
    (C : ℕ) (hC : 0 < C)
    (h : ∀ n : ℕ, (∀ i ≤ n, L.PowerIn A a i) → ∀ j ≤ n/C, L.PowerIn B b j) :
    L.escapeNorm B b ≤ (C : ℝ)*L.escapeNorm A a := by
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  suffices hh : L.escapeNorm B b/C ≤ L.escapeNorm A a by
    simpa only [mul_comm] using (div_le_iff₀ hCr).mp hh
  apply le_csInf (L.escapeValues_nonempty hA a)
  rintro x ⟨n,hn,rfl⟩
  rw [div_le_iff₀ hCr]
  have hb := L.escapeNorm_le_of_powers (h n hn)
  have hdiv : n+1 ≤ (n/C+1)*C := by
    have hr := Nat.mod_lt n hC
    have he := Nat.div_add_mod n C
    nlinarith
  have hr : (n : ℝ)+1 ≤ ((n/C : ℕ)+1 : ℝ)*C := by exact_mod_cast hdiv
  calc
    L.escapeNorm B b ≤ 1/((n/C : ℕ)+1 : ℝ) := hb
    _ ≤ 1/((n : ℝ)+1)*C := by
      rw [div_mul_eq_mul_div,_root_.one_mul]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      simpa only [mul_comm,_root_.one_mul] using hr

/-- The quantitative trapping bound remains valid in an actual local group.
Nested powers are justified by compression instead of a global power law. -/
theorem escapeNorm_le_mul_of_trapping {A B : Set G} (hB : L.one ∈ B)
    (C : ℕ) (hC : 0 < C)
    (htrap : ∀ x, (∀ j : ℕ, 1 ≤ j → j ≤ C → L.PowerIn B x j) → x ∈ A)
    (g : G) : L.escapeNorm A g ≤ (C : ℝ)*L.escapeNorm B g := by
  apply L.escapeNorm_le_mul_of_segments hB C hC
  intro n hn i hi
  have hin : i ≤ n := hi.trans (Nat.div_le_self n C)
  obtain ⟨x,hx,hp⟩ := hn i hin
  refine ⟨x,htrap x ?_,hp⟩
  intro j _ hj
  apply PowerIn.iterate L hp
  exact hn (i*j) ((Nat.mul_le_mul hi hj).trans (Nat.div_mul_le_self n C))
end LocalGroupAlgebra
end DirectedCycles
