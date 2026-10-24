import DirectedCycles.LocalAdditivePowerSegment
import DirectedCycles.LocalGroupHom
import DirectedCycles.LocalCentralQuotientData

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G H : Type*} {L : LocalGroupAlgebra G} {T : LocalGroupAlgebra H}

/-- A local homomorphism maps every certified finite power segment. -/
def PowerSegment.map {u : G} {N : ℕ} (p : L.PowerSegment u N) (f : LocalGroupHom L T) :
    T.PowerSegment (f.toFun u) N where
  power n := f.toFun (p.power n)
  product n hn := by simpa only [List.map_replicate] using (p.product n hn).map f

/-- A segment can be restricted when all of its power values lie in the
restriction window. Its addition table certifies every bracketing there. -/
def PowerSegment.restrict {u : G} {N : ℕ} (p : L.PowerSegment u N)
    (S : Set G) (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S)
    (hu : u ∈ S) (hp : ∀ n ≤ N, p.power n ∈ S) :
    (L.restrict S h1 hi).PowerSegment ⟨u,hu⟩ N := by
  let f : ℕ → S := fun n => if hn : n ≤ N then ⟨p.power n,hp n hn⟩ else ⟨L.one,h1⟩
  apply PowerSegment.of_add (L.restrict S h1 hi) f
  · apply Subtype.ext
    simp only [f,dite_eq_left (Nat.zero_le N),p.zero]
    rfl
  · intro hN
    apply Subtype.ext
    simp only [f,dite_eq_left hN,p.one hN]
  · intro n m hnm
    change L.mulRel (f n).val (f m).val (f (n+m)).val
    simpa only [f,dite_eq_left (show n ≤ N by omega),dite_eq_left (show m ≤ N by omega),
      dite_eq_left hnm] using p.add hnm

theorem PowerSegment.restrict_value {u : G} {N : ℕ} (p : L.PowerSegment u N)
    (S : Set G) (h1 : L.one ∈ S) (hi : ∀ x ∈ S, L.inv x ∈ S)
    (hu : u ∈ S) (hp : ∀ n ≤ N, p.power n ∈ S) {n : ℕ} (hn : n ≤ N) :
    ((p.restrict S h1 hi hu hp).power n).val = p.power n := by
  simp only [PowerSegment.restrict,PowerSegment.of_add,dite_eq_left hn]

namespace CentralQuotientData
variable {P : Set G} (D : L.CentralQuotientData P)

/-- Project a real source power segment through the actual quotient window. -/
def projectPowerSegment {u : G} {N : ℕ} (p : L.PowerSegment u N)
    (hu : u ∈ D.small) (hp : ∀ n ≤ N, p.power n ∈ D.small) :
    D.algebra.PowerSegment (D.project ⟨u,hu⟩) N :=
  (p.restrict D.small D.one_mem D.inv_mem hu hp).map D.projectionHom

theorem projectPowerSegment_value {u : G} {N : ℕ} (p : L.PowerSegment u N)
    (hu : u ∈ D.small) (hp : ∀ n ≤ N, p.power n ∈ D.small) {n : ℕ} (hn : n ≤ N) :
    (D.projectPowerSegment p hu hp).power n = D.project ⟨p.power n,hp n hn⟩ := by
  change D.project ((p.restrict D.small D.one_mem D.inv_mem hu hp).power n) = _
  congr 1
  apply Subtype.ext
  exact p.restrict_value D.small D.one_mem D.inv_mem hu hp hn
end CentralQuotientData
end LocalGroupAlgebra
end DirectedCycles
