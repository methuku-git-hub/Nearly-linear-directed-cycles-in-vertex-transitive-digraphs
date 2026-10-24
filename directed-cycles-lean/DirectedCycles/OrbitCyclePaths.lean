import DirectedCycles.OrbitCycleWalk
import DirectedCycles.BranchingPaths

set_option autoImplicit false
namespace DirectedCycles
namespace OrbitCycleWalk
variable {G I : Type*} [Group G] {S : I → I → Set G} {a : G}

def orbitIndex (W : OrbitCycleWalk (VoltageDigraph S) a) : Fin W.length ↪ I :=
  ⟨fun i => (W.point i.castSucc).2,W.index_injective⟩

theorem orbitIndex_succ (W : OrbitCycleWalk (VoltageDigraph S) a) (i : Fin W.length) :
    (W.point i.succ).2 = W.orbitIndex (finRotate W.length i) := by
  let : NeZero W.length := ⟨by have := W.two_le; omega⟩
  change (W.point i.succ).2 = (W.point (finRotate W.length i).castSucc).2
  by_cases hi : i.val+1 < W.length
  · have hind : i.succ = (finRotate W.length i).castSucc := by
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_castSucc,finRotate_apply]
      simp [Fin.val_add,Nat.mod_eq_of_lt (show 1 < W.length by have := W.two_le; omega),
        Nat.mod_eq_of_lt hi]
    rw [hind]
  · have hilast : i.succ = Fin.last W.length := by
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_last]
      omega
    have hizero : (finRotate W.length i).castSucc = 0 := by
      apply Fin.ext
      simp only [Fin.val_castSucc,finRotate_apply,Fin.val_zero]
      have he : i.val+1 = W.length := by omega
      simp [Fin.val_add,Nat.mod_eq_of_lt (show 1 < W.length by have := W.two_le; omega),he]
    rw [hilast,hizero,W.closes]

theorem orbitIndex_step (W : OrbitCycleWalk (VoltageDigraph S) a) (i : Fin W.length) :
    (S (W.orbitIndex i) (W.orbitIndex (finRotate W.length i))).Nonempty := by
  obtain ⟨s,hs,_⟩ := W.step i
  rw [W.orbitIndex_succ i] at hs
  exact ⟨s,hs⟩

def orbitCycle (W : OrbitCycleWalk (VoltageDigraph S) a) : Cycle (fun i j => (S i j).Nonempty) where
  length := W.length
  two_le := W.two_le
  vertex := W.orbitIndex
  arc := W.orbitIndex_step

noncomputable def outOrbitPath (W : OrbitCycleWalk (VoltageDigraph S) a) :
    SimplePath (fun i j => (S i j).Nonempty) (W.point 0).2
      (W.orbitIndex ⟨W.length-1,by have := W.two_le; omega⟩) where
  vertices := List.ofFn W.orbitIndex
  nodup := List.nodup_ofFn.mpr W.index_injective
  head := by
    rw [List.head?_eq_getElem?,List.getElem?_ofFn]
    simp only [dite_eq_left (show 0 < W.length by have := W.two_le; omega)]
    rfl
  last := by
    simp only [List.getLast?_eq_getElem?,List.length_ofFn,List.getElem?_ofFn,
      dite_eq_left (show W.length-1 < W.length by have := W.two_le; omega)]
  chain := (circularChain_ofFn W.orbitIndex W.orbitIndex_step).1

noncomputable def inOrbitPath (W : OrbitCycleWalk (VoltageDigraph S) a) :
    SimplePath (fun i j => (S i j).Nonempty)
      (W.point ⟨1,by have := W.two_le; omega⟩).2 (W.point 0).2 where
  vertices := List.ofFn (fun i : Fin W.length => (W.point i.succ).2)
  nodup := by
    apply List.nodup_ofFn.mpr
    intro i j he
    simp only [W.orbitIndex_succ] at he
    exact (finRotate W.length).injective (W.orbitIndex.injective he)
  head := by
    rw [List.head?_eq_getElem?,List.getElem?_ofFn]
    simp only [dite_eq_left (show 0 < W.length by have := W.two_le; omega)]
    rfl
  last := by
    simp only [List.getLast?_eq_getElem?,List.length_ofFn,List.getElem?_ofFn,
      dite_eq_left (show W.length-1 < W.length by have := W.two_le; omega)]
    have he : (⟨W.length-1,by have := W.two_le; omega⟩ : Fin W.length).succ = Fin.last W.length := by
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_last]
      have := W.two_le
      omega
    rw [he,W.closes]
  chain := by
    apply List.isChain_ofFn.mpr
    intro i hi
    have hstep := W.step ⟨i+1,hi⟩
    obtain ⟨s,hs,_⟩ := hstep
    exact ⟨s,hs⟩

end OrbitCycleWalk
end DirectedCycles
