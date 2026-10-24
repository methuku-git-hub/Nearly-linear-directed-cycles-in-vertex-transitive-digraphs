import DirectedCycles.OrbitCyclePaths
import DirectedCycles.TreePotentials

set_option autoImplicit false
namespace DirectedCycles
namespace OrbitCycleWalk
variable {G I : Type*} [Group G] {S : I → I → Set G} {a : G}

theorem point_injective (W : OrbitCycleWalk (VoltageDigraph S) a) (ha : a ≠ 1) :
    Function.Injective W.point := by
  have hlast : ∀ j : Fin W.length, W.point (Fin.last W.length) ≠ W.point j.castSucc := by
    intro j he
    rw [W.closes] at he
    have hi := congrArg (fun z : G × I => z.2) he
    change (W.point 0).2 = (W.point j.castSucc).2 at hi
    have hj : (⟨0,by have := W.two_le; omega⟩ : Fin W.length) = j := W.index_injective hi
    subst j
    have hg := congrArg Prod.fst he
    change a*(W.point 0).1 = (W.point 0).1 at hg
    exact ha (mul_right_cancel (hg.trans (one_mul _).symm))
  intro i j he
  by_cases hi : i.val < W.length
  · have hei : i = (⟨i.val,hi⟩ : Fin W.length).castSucc := Fin.ext rfl
    rw [hei] at he ⊢
    by_cases hj : j.val < W.length
    · have hej : j = (⟨j.val,hj⟩ : Fin W.length).castSucc := Fin.ext rfl
      rw [hej] at he ⊢
      exact congrArg Fin.castSucc (W.index_injective (congrArg Prod.snd he))
    · have hej : j = Fin.last W.length := Fin.ext (by simp only [Fin.val_last]; omega)
      exact (hlast ⟨i.val,hi⟩ (hej ▸ he.symm)).elim
  · have hei : i = Fin.last W.length := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [hei] at he ⊢
    by_cases hj : j.val < W.length
    · have hej : j = (⟨j.val,hj⟩ : Fin W.length).castSucc := Fin.ext rfl
      exact (hlast ⟨j.val,hj⟩ (hej ▸ he)).elim
    · exact Fin.ext (by simp only [Fin.val_last]; omega)

def toSimplePath (W : OrbitCycleWalk (VoltageDigraph S) a) (ha : a ≠ 1) :
    SimplePath (VoltageDigraph S) (W.point 0) (a*(W.point 0).1,(W.point 0).2) where
  vertices := List.ofFn W.point
  nodup := List.nodup_ofFn.mpr (W.point_injective ha)
  head := by simp [List.head?_eq_getElem?]
  last := by
    simp only [List.getLast?_eq_getElem?,List.length_ofFn,Nat.add_sub_cancel,List.getElem?_ofFn,
      dite_eq_left (Nat.lt_succ_self W.length)]
    exact congrArg some W.closes
  chain := by
    apply List.isChain_ofFn.mpr
    intro i hi
    exact W.step ⟨i,by omega⟩

noncomputable def changeRepresentatives (W : OrbitCycleWalk (VoltageDigraph S) a) (p : I → G) :
    OrbitCycleWalk (VoltageDigraph (gaugeLabels S p)) a where
  length := W.length
  two_le := W.two_le
  point i := (gaugeCoordinates p).symm (W.point i)
  index_injective := W.index_injective
  step i := by
    apply (gaugeLabels_arc S p _ _).mpr
    simpa using W.step i
  closes := by
    change (gaugeCoordinates p).symm (W.point (Fin.last W.length)) =
      (a*((W.point 0).1*(p (W.point 0).2)⁻¹),(W.point 0).2)
    rw [W.closes]
    apply Prod.ext
    · exact mul_assoc _ _ _
    · rfl

theorem changeRepresentatives_internal (W : OrbitCycleWalk (VoltageDigraph S) a) (p : I → G)
    (hp : ∀ k, p (W.orbitIndex k) = (W.point k.castSucc).1) (k : Fin W.length) :
    ((W.changeRepresentatives p).point k.castSucc).1 = 1 := by
  change (W.point k.castSucc).1*(p (W.orbitIndex k))⁻¹ = 1
  rw [hp,mul_inv_cancel]

end OrbitCycleWalk
end DirectedCycles
