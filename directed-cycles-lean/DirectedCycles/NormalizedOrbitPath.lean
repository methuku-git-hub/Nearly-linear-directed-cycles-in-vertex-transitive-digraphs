import DirectedCycles.OrbitWalkPaths
import DirectedCycles.TranslatedReturnPaths

set_option autoImplicit false
namespace DirectedCycles

theorem ofFn_dropLast {V : Type*} {n : ℕ} (f : Fin (n+1) → V) :
    (List.ofFn f).dropLast = List.ofFn (fun i : Fin n => f i.castSucc) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_dropLast,List.getElem_ofFn]
    rfl

namespace OrbitCycleWalk
variable {G I : Type*} [Group G] {S : I → I → Set G} {a : G}

def normalizedRootPath (W : OrbitCycleWalk (VoltageDigraph S) a)
    (ha : a ≠ 1) (hcoord : ∀ k : Fin W.length, (W.point k.castSucc).1 = 1) :
    SimplePath (VoltageDigraph S) (1,(W.point 0).2) (a,(W.point 0).2) where
  vertices := (W.toSimplePath ha).vertices
  nodup := (W.toSimplePath ha).nodup
  head := by
    have h0 : (W.point 0).1 = 1 := hcoord ⟨0,by have := W.two_le; omega⟩
    rw [(W.toSimplePath ha).head]
    congr 1
    exact Prod.ext h0 rfl
  last := by
    have h0 : (W.point 0).1 = 1 := hcoord ⟨0,by have := W.two_le; omega⟩
    rw [(W.toSimplePath ha).last,h0,mul_one]
  chain := (W.toSimplePath ha).chain

theorem normalizedRootPath_internal (W : OrbitCycleWalk (VoltageDigraph S) a)
    (ha : a ≠ 1) (hcoord : ∀ k : Fin W.length, (W.point k.castSucc).1 = 1)
    (x : G) (z : G × I)
    (hz : z ∈ ((W.normalizedRootPath ha hcoord).translateRoot x).vertices.dropLast) :
    z.1 = x ∧ z.2 ∈ Set.range W.orbitIndex := by
  change z ∈ ((List.ofFn W.point).map (voltageLeftTranslate x)).dropLast at hz
  rw [← List.map_dropLast,ofFn_dropLast,List.map_ofFn] at hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  constructor
  · change x*(W.point i.castSucc).1 = x
    rw [hcoord,mul_one]
  · exact ⟨i,rfl⟩

end OrbitCycleWalk
end DirectedCycles
