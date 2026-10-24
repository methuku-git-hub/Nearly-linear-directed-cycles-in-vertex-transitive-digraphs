import DirectedCycles.LocalProductCompression
import DirectedCycles.LocalEscapeNorm

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- An iterated word power expands to the corresponding flat word power
within the certified original domain. -/
theorem wordPower_wordPower_subset {A : Set G} {N : ℕ}
    (hdom : L.AllProductsDefined A N) (m n : ℕ) (hmn : m*n ≤ N) :
    L.wordPower (L.wordPower A m) n ⊆ L.wordPower A (m*n) := by
  induction n with
  | zero => simp only [Nat.mul_zero,L.wordPower_zero,Set.Subset.refl]
  | succ n ih =>
    rw [Nat.mul_succ] at hmn
    have hi := ih (by omega)
    intro x hx
    obtain ⟨a,ha,b,hb,hm⟩ := L.wordPower_add_subset (L.wordPower A m) 1 n
      (by simpa only [Nat.add_comm] using hx)
    rw [L.wordPower_one] at ha
    rw [Nat.mul_succ,Nat.add_comm,L.wordPower_add hdom (by omega)]
    exact ⟨a,ha,b,hi hb,hm⟩
/-- Every finite power of a word value is an actual compressed word,
with its membership and all bracketings supplied by the original domain. -/
theorem powerIn_wordPower {A : Set G} {N m j : ℕ}
    (hdom : L.AllProductsDefined A N) (hmj : m*j ≤ N) {x : G}
    (hx : x ∈ L.wordPower A m) : L.PowerIn (L.wordPower A (m*j)) x j := by
  have hd := hdom.wordPower L hmj
  have hmem : ∀ a ∈ List.replicate j x, a ∈ L.wordPower A m := by
    intro a ha
    exact (List.mem_replicate.mp ha).2.symm ▸ hx
  obtain ⟨y,hy⟩ := hd (List.replicate j x) (by simp only [List.length_replicate,le_refl]) hmem
  exact ⟨y,L.wordPower_wordPower_subset hdom m j hmj
    ⟨List.replicate j x,List.length_replicate,hmem,hy⟩,hy⟩

end LocalGroupAlgebra
end DirectedCycles
