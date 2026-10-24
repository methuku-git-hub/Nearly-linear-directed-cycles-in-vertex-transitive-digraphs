import DirectedCycles.LocalProductSplits
import DirectedCycles.LocalGroupUltraproduct
import Mathlib.Order.Filter.Finite

set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))

/-- Fixed-length all-bracketings products transfer exactly. Both existence of
all intermediate products and their common value are checked componentwise. -/
theorem localUltraProduct_mk_iff (l : List (∀ i, G i)) (x : ∀ i, G i) :
    (localUltraAlgebra F G L).Product (l.map (localUltraMk F G)) (localUltraMk F G x) ↔
      ∀ᶠ i in F, (L i).Product (l.map (fun a => a i)) (x i) := by
  classical
  have all : ∀ n : ℕ, ∀ l : List (∀ i, G i), l.length = n → ∀ x : ∀ i, G i,
      (localUltraAlgebra F G L).Product (l.map (localUltraMk F G)) (localUltraMk F G x) ↔
        ∀ᶠ i in F, (L i).Product (l.map (fun a => a i)) (x i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hlen x
      by_cases hsmall : l.length ≤ 1
      · cases l with
        | nil =>
          simp only [List.map_nil,LocalGroupAlgebra.Product.nil_iff]
          exact localUltraMk_eq_iff F G x (fun i => (L i).one)
        | cons a l =>
          have he : l = [] := by simpa using hsmall
          subst l
          simp only [List.map_cons,List.map_nil,LocalGroupAlgebra.Product.singleton_iff]
          exact localUltraMk_eq_iff F G x a
      · have hlen2 : 2 ≤ l.length := by omega
        rw [LocalGroupAlgebra.mapped_product_iff_finite_splits _ _ hlen2]
        constructor
        · intro h
          have each : ∀ k : Fin (l.length+1), ∀ᶠ i in F,
              0 < k.val → k.val < l.length →
                ∃ u v : G i, (L i).Product ((l.take k.val).map (fun a => a i)) u ∧
                  (L i).Product ((l.drop k.val).map (fun a => a i)) v ∧ (L i).mulRel u v (x i) := by
            intro k
            by_cases hk : 0 < k.val ∧ k.val < l.length
            · obtain ⟨u,v,hu,hv,hm⟩ := h k hk.1 hk.2
              obtain ⟨a,rfl⟩ := Quotient.exists_rep u
              obtain ⟨b,rfl⟩ := Quotient.exists_rep v
              have htlen : (l.take k.val).length < n := by simp only [List.length_take]; omega
              have hdlen : (l.drop k.val).length < n := by simp only [List.length_drop]; omega
              have hleft := (ih (l.take k.val).length htlen (l.take k.val) rfl a).1 hu
              have hright := (ih (l.drop k.val).length hdlen (l.drop k.val) rfl b).1 hv
              have hmul := (localUltraMulRel_mk_iff F G L a b x).1 hm
              filter_upwards [hleft,hright,hmul] with i hai hbi hmi
              exact fun _ _ => ⟨a i,b i,hai,hbi,hmi⟩
            · exact Filter.Eventually.of_forall fun _ h1 h2 => (hk ⟨h1,h2⟩).elim
          have hall := Filter.eventually_all.2 each
          filter_upwards [hall] with i hi
          exact (LocalGroupAlgebra.mapped_product_iff_finite_splits (L i) (fun a => a i) hlen2).2 hi
        · intro h k hk hk'
          have hs : ∀ᶠ i in F, ∃ u v : G i,
              (L i).Product ((l.take k.val).map (fun a => a i)) u ∧
              (L i).Product ((l.drop k.val).map (fun a => a i)) v ∧ (L i).mulRel u v (x i) :=
            h.mono fun i hi =>
              (LocalGroupAlgebra.mapped_product_iff_finite_splits (L i) (fun a => a i) hlen2).1 hi k hk hk'
          let R := fun i (u v : G i) =>
            (L i).Product ((l.take k.val).map (fun a => a i)) u ∧
              (L i).Product ((l.drop k.val).map (fun a => a i)) v ∧ (L i).mulRel u v (x i)
          have hc : ∀ i, ∃ a b : G i, (∃ u v, R i u v) → R i a b := by
            intro i
            by_cases he : ∃ u v, R i u v
            · obtain ⟨a,b,hab⟩ := he
              exact ⟨a,b,fun _ => hab⟩
            · exact ⟨(L i).one,(L i).one,fun hh => (he hh).elim⟩
          choose a b hab using hc
          have hab' : ∀ᶠ i in F, R i (a i) (b i) := hs.mono fun i hi => hab i hi
          have htlen : (l.take k.val).length < n := by simp only [List.length_take]; omega
          have hdlen : (l.drop k.val).length < n := by simp only [List.length_drop]; omega
          refine ⟨localUltraMk F G a,localUltraMk F G b,?_,?_,?_⟩
          · exact (ih (l.take k.val).length htlen (l.take k.val) rfl a).2 (hab'.mono fun _ hi => hi.1)
          · exact (ih (l.drop k.val).length hdlen (l.drop k.val) rfl b).2 (hab'.mono fun _ hi => hi.2.1)
          · exact (localUltraMulRel_mk_iff F G L a b x).2 (hab'.mono fun _ hi => hi.2.2)
  exact all l.length l rfl x
end DirectedCycles
