module

public import DirectedCycles.LocalOrderedGrid
public import DirectedCycles.LocalSignedInverseWord
public import DirectedCycles.LocalIteratedGeneratorCommutators
public import DirectedCycles.LocalProductCompression

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Each actual iterated generator commutator is represented by a bounded
signed word. Existence of all bracketings comes from the word budget, not
from an unsupported expansion of a local product. -/
theorem generatorCommutators_signedWord (hr : L.Reversible) {r : ℕ} (g : Fin r → G)
    (N : Fin r → ℕ) (S : Set G) (hwords : L.SignedWordsIn g N S)
    (c : ℕ) (hbudget : ∀ i, 4^(c+1) ≤ N i) :
    ∀ n ≤ c, ∀ x, L.GeneratorCommutators (Set.range g) n x →
      ∃ w : List (Fin r × Bool), w.length ≤ 4^(n+1) ∧
        x ∈ S ∧ L.Product (L.signedLetters g w) x := by
  have hbounded : ∀ w : List (Fin r × Bool), w.length ≤ 4^(c+1) →
      ∃ x ∈ S, L.Product (L.signedLetters g w) x := by
    intro w hw
    exact hwords w (fun i => (List.countP_le_length (p := fun a : Fin r × Bool => a.1 = i)).trans (hw.trans (hbudget i)))
  intro n
  induction n with
  | zero =>
    intro hn x hx
    cases hx with
    | base hx =>
      obtain ⟨i,rfl⟩ := hx
      obtain ⟨z,hz,hp⟩ := hbounded [(i,true)] (by
        have hp4 : 0 < 4^(c+1) := pow_pos (by decide) _
        simp only [List.length_cons,List.length_nil]; omega)
      have he : z = g i := hp.unique L (Product.singleton _)
      exact ⟨[(i,true)],by norm_num,he ▸ hz,Product.singleton _⟩
  | succ n ih =>
    intro hn z hz
    cases hz with
    | @step _ x y z hx hy hp =>
      obtain ⟨w,hw,hxS,hxw⟩ := ih (by omega) x hx
      obtain ⟨j,rfl⟩ := hy
      let v := w ++ [(j,true)] ++ inverseSignedWord w ++ [(j,false)]
      have hlen : v.length ≤ 4^(n+1+1) := by
        simp only [v,List.length_append,List.length_cons,List.length_nil,inverseSignedWord_length]
        rw [pow_succ]
        have hpow : 0 < 4^(n+1) := pow_pos (by decide) _
        nlinarith
      have hbig : v.length ≤ 4^(c+1) := hlen.trans (Nat.pow_le_pow_right (by decide) (by omega))
      obtain ⟨t,ht,htv⟩ := hbounded v hbig
      have hiw : L.Product (L.signedLetters g (inverseSignedWord w)) (L.inv x) := by
        rw [L.signedLetters_inverse]
        exact hxw.reverse_inv L hr
      have hblocks : List.Forall₂ L.Product
          [L.signedLetters g w,[g j],L.signedLetters g (inverseSignedWord w),[L.inv (g j)]]
          [x,g j,L.inv x,L.inv (g j)] :=
        .cons hxw (.cons (.singleton _) (.cons hiw (.cons (.singleton _) .nil)))
      have hflat : L.Product
          [L.signedLetters g w,[g j],L.signedLetters g (inverseSignedWord w),[L.inv (g j)]].flatten t := by
        simpa only [v,L.signedLetters_append,L.signedLetters_positive_singleton,
          L.signedLetters_negative_singleton,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc] using htv
      have he : z = t := hp.unique L (hflat.compress L hblocks)
      exact ⟨v,hlen,he.symm ▸ ht,he.symm ▸ htv⟩
end LocalGroupAlgebra
end DirectedCycles
