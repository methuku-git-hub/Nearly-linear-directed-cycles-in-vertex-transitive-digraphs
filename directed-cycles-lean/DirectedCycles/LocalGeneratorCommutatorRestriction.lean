import DirectedCycles.LocalCommutatorWordConstruction
import DirectedCycles.LocalWordProgressionMaps

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- Sufficient actual signed-word domains force every bounded-depth
ambient generator commutator to be the image of one in the restricted
local group. The restriction is constructed, not assumed. -/
theorem generatorCommutators_restrict (hr : L.Reversible) (S : Set G)
    (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S)
    {r : ℕ} (g : Fin r → S) (N : Fin r → ℕ)
    (hall : L.SignedWordsIn (fun i => (g i).val) N S)
    (c : ℕ) (hbudget : ∀ i, 4^(c+1) ≤ N i) :
    ∀ n ≤ c, ∀ x, L.GeneratorCommutators (Set.range (fun i => (g i).val)) n x →
      ∃ y : S, y.val = x ∧ (L.restrict S h1 hi).GeneratorCommutators (Set.range g) n y := by
  let M := L.restrict S h1 hi
  have hMr : M.Reversible := hr.restrict L S h1 hi
  have hwordsM : M.SignedWordsIn g N Set.univ := by
    intro w hw
    obtain ⟨x,hx,hp⟩ := hall w hw
    exact ⟨⟨x,hx⟩,Set.mem_univ _,L.signedWord_restrict S h1 hi g N hall w hw ⟨x,hx⟩ hp⟩
  intro n
  induction n with
  | zero =>
    intro hn x hx
    cases hx with
    | base hx =>
      obtain ⟨j,rfl⟩ := hx
      exact ⟨g j,rfl,.base ⟨j,rfl⟩⟩
  | succ n ih =>
    intro hn z hz
    cases hz with
    | @step _ x y z hx hy hp =>
      obtain ⟨xS,hxS,hxM⟩ := ih (by omega) x hx
      obtain ⟨j,rfl⟩ := hy
      obtain ⟨w,hw,_,hpw⟩ := M.generatorCommutators_signedWord hMr g N Set.univ hwordsM
        c hbudget n (by omega) xS hxM
      let v := w ++ [(j,true)] ++ inverseSignedWord w ++ [(j,false)]
      have hlen : v.length ≤ 4^(n+1+1) := by
        simp only [v,List.length_append,List.length_cons,List.length_nil,inverseSignedWord_length]
        rw [pow_succ]
        have hpow : 0 < 4^(n+1) := pow_pos (by decide) _
        nlinarith
      have hbig : v.length ≤ 4^(c+1) := hlen.trans (Nat.pow_le_pow_right (by decide) (by omega))
      obtain ⟨t,_,ht⟩ := hwordsM v (fun i =>
        (List.countP_le_length (p := fun a : Fin r × Bool => a.1 = i)).trans (hbig.trans (hbudget i)))
      have hm : M.Product [xS,g j,M.inv xS,M.inv (g j)] t :=
        M.commutator_of_signed_word hMr g w j hpw ht
      have hsource := hm.map (LocalGroupHom.inclusion L S h1 hi)
      change L.Product [xS.val,(g j).val,L.inv xS.val,L.inv (g j).val] t.val at hsource
      rw [hxS] at hsource
      exact ⟨t,hsource.unique L hp,.step hxM ⟨j,rfl⟩ hm⟩
end LocalGroupAlgebra
end DirectedCycles
