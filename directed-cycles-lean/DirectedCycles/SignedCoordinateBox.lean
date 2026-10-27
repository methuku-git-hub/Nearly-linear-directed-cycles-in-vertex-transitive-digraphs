module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

def signedCoordinateInterval (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ)

abbrev SignedCoordinates {r : ℕ} (N : Fin r → ℕ) := ∀ i, ↥(signedCoordinateInterval (N i))

theorem mem_signedCoordinateInterval (n : ℕ) (k : ℤ) :
    k ∈ signedCoordinateInterval n ↔ k.natAbs ≤ n := by
  simp only [signedCoordinateInterval,Finset.mem_Icc]
  omega

theorem signedCoordinateInterval_card (n : ℕ) : (signedCoordinateInterval n).card = 2*n+1 := by
  rw [signedCoordinateInterval,Int.card_Icc]
  omega

theorem signedCoordinates_card {r : ℕ} (N : Fin r → ℕ) :
    Fintype.card (SignedCoordinates N) = ∏ i, (2*N i+1) := by
  simp only [SignedCoordinates,Fintype.card_pi,Fintype.card_coe,signedCoordinateInterval_card]

theorem SignedCoordinates.bound {r : ℕ} {N : Fin r → ℕ} (k : SignedCoordinates N) (i : Fin r) :
    (k i).val.natAbs ≤ N i := (mem_signedCoordinateInterval _ _).1 (k i).property

/-- Adjoin a last signed coordinate without changing any earlier coordinate. -/
def SignedCoordinates.snoc {r : ℕ} {N : Fin (r+1) → ℕ}
    (k : SignedCoordinates (fun i => N i.castSucc)) (j : ↥(signedCoordinateInterval (N (Fin.last r)))) :
    SignedCoordinates N := Fin.lastCases j k

@[simp] theorem SignedCoordinates.snoc_castSucc {r : ℕ} {N : Fin (r+1) → ℕ}
    (k : SignedCoordinates (fun i => N i.castSucc)) (j : ↥(signedCoordinateInterval (N (Fin.last r)))) (i : Fin r) :
    (k.snoc j) i.castSucc = k i := by simp [SignedCoordinates.snoc]

@[simp] theorem SignedCoordinates.snoc_last {r : ℕ} {N : Fin (r+1) → ℕ}
    (k : SignedCoordinates (fun i => N i.castSucc)) (j : ↥(signedCoordinateInterval (N (Fin.last r)))) :
    (k.snoc j) (Fin.last r) = j := by simp [SignedCoordinates.snoc]

def SignedCoordinates.zero {r : ℕ} (N : Fin r → ℕ) : SignedCoordinates N :=
  fun i => ⟨0,(mem_signedCoordinateInterval _ _).2 (by simp)⟩

@[simp] theorem SignedCoordinates.zero_val {r : ℕ} (N : Fin r → ℕ) (i : Fin r) :
    (SignedCoordinates.zero N i).val = 0 := rfl

end DirectedCycles
