module

public import DirectedCycles.VoltageQuotients
public import DirectedCycles.CycleContraction

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A directed walk from v to av whose orbit projection is a simple cycle.
The terminal vertex is recorded explicitly, and only the half-open orbit
indices are required to be distinct. -/
structure OrbitCycleWalk {G I : Type*} [Group G] (D : Digraph (G × I)) (a : G) where
  length : ℕ
  two_le : 2 ≤ length
  point : Fin (length+1) → G × I
  index_injective : Function.Injective (fun i : Fin length => (point i.castSucc).2)
  step : ∀ i : Fin length, D (point i.castSucc) (point i.succ)
  closes : point (Fin.last length) = (a*(point 0).1,(point 0).2)

namespace OrbitCycleWalk
variable {G H I : Type*} [Group G] [Group H] {S : I → I → Set G} {a : G}

/-- When the endpoint label dies in a quotient, the walk is a simple cycle
there, and its orbit-index injection is unchanged. -/
noncomputable def quotientCycle (W : OrbitCycleWalk (VoltageDigraph S) a)
    (q : G →* H) (ha : q a = 1) : Cycle (VoltageDigraph (fun i j => q '' S i j)) where
  length := W.length
  two_le := W.two_le
  vertex := ⟨fun i => (q (W.point i.castSucc).1,(W.point i.castSucc).2),by
    intro i j he
    have hs := congrArg (fun z : H × I => z.2) he
    exact W.index_injective hs⟩
  arc i := by
    let pi : G × I → H × I := fun x => (q x.1,x.2)
    have harc : VoltageDigraph (fun i j => q '' S i j) (pi (W.point i.castSucc)) (pi (W.point i.succ)) := by
      obtain ⟨s,hs,he⟩ := W.step i
      exact ⟨q s,⟨s,hs,rfl⟩,by change q (W.point i.succ).1=q (W.point i.castSucc).1*q s; rw [he,map_mul]⟩
    have hnext : pi (W.point i.succ) = pi (W.point (finRotate W.length i).castSucc) := by
      let : NeZero W.length := ⟨by have := W.two_le; omega⟩
      by_cases hi : i.val+1 < W.length
      · have hind : i.succ = (finRotate W.length i).castSucc := by
          apply Fin.ext
          simp only [Fin.val_succ,Fin.val_castSucc,finRotate_apply]
          simp [Fin.val_add,Nat.mod_eq_of_lt (show 1 < W.length by have := W.two_le; omega),
            Nat.mod_eq_of_lt hi]
        rw [hind]
      · have hilast : i.succ = Fin.last W.length := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_last]; omega
        have hizero : (finRotate W.length i).castSucc = 0 := by
          apply Fin.ext
          simp only [Fin.val_castSucc,finRotate_apply,Fin.val_zero]
          have he : i.val+1 = W.length := by omega
          simp [Fin.val_add,Nat.mod_eq_of_lt (show 1 < W.length by have := W.two_le; omega),he]
        rw [hilast,hizero,W.closes]
        change (q (a*(W.point 0).1),(W.point 0).2) = (q (W.point 0).1,(W.point 0).2)
        rw [map_mul,ha,one_mul]
    rw [hnext] at harc
    exact harc

theorem quotientCycle_indices_injective (W : OrbitCycleWalk (VoltageDigraph S) a)
    (q : G →* H) (ha : q a = 1) :
    Function.Injective (fun i => ((W.quotientCycle q ha).vertex i).2) := W.index_injective

end OrbitCycleWalk
end DirectedCycles
