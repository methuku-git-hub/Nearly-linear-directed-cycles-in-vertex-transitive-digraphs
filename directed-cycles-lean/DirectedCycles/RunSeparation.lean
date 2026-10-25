module

public import DirectedCycles.RunResidues
public import Mathlib.Data.Int.Interval

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

def collisionForbiddenResidues (h D : ℕ) (e : ZMod h) : Finset (ZMod h) :=
  (Finset.Icc (-(D : ℤ)) (D : ℤ)).image (fun t : ℤ => e+(t : ZMod h))

theorem collisionForbiddenResidues_card (h D : ℕ) (e : ZMod h) :
    (collisionForbiddenResidues h D e).card ≤ 2*D+1 := by
  have hh := Finset.card_image_le (s := Finset.Icc (-(D : ℤ)) (D : ℤ))
    (f := fun t => e+(t : ZMod h))
  rw [Int.card_Icc] at hh
  have he : ((D : ℤ)+1-(-(D : ℤ))).toNat = 2*D+1 := by omega
  simpa only [collisionForbiddenResidues,he] using hh

theorem collision_residue_excluded (h D : ℕ) (e v w : ZMod h)
    (hv : w-v ∉ collisionForbiddenResidues h D e)
    (u u' : ℕ) (hu : u ≤ D) (hu' : u' ≤ D) :
    w-v ≠ e+(u : ZMod h)-(u' : ZMod h) := by
  intro he
  apply hv
  apply Finset.mem_image.mpr
  refine ⟨(u : ℤ)-(u' : ℤ),Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
  rw [he]
  push_cast
  abel

/-- The target interval of the preceding connector is disjoint from
both the source interval and its one-step translate. -/
theorem separated_source_target (h D l : ℕ) [NeZero h]
    (hl : 1 ≤ l) (hupper : l ≤ h-2*D-2) (hh : 2*D+2 ≤ h)
    (u u' : ℕ) (hu : u ≤ D+1) (hu' : u' ≤ D) :
    (u : ZMod h) ≠ -(l : ZMod h)-(D : ZMod h)+(u' : ZMod h) := by
  intro he
  have hleft : u+l+D < h := by omega
  have hright : u' < h := by omega
  have he' : ((u+l+D : ℕ) : ZMod h) = (u' : ZMod h) := by
    push_cast
    rw [he]
    abel
  have hv := congrArg ZMod.val he'
  rw [ZMod.val_natCast_of_lt hleft,ZMod.val_natCast_of_lt hright] at hv
  omega

end DirectedCycles
