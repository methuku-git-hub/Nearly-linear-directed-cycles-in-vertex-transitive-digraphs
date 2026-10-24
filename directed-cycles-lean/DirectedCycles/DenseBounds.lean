import DirectedCycles.DenseCoordinates
import DirectedCycles.NilpotentCoordinates

set_option autoImplicit false
open scoped BigOperators
namespace DirectedCycles

/-- Ordered coordinates may be padded by identity elements. -/
theorem hasPowerCoordinates_mono {G : Type*} [Group G] {n m : ℕ}
    (h : HasPowerCoordinates G n) (hnm : n ≤ m) : HasPowerCoordinates G m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  obtain ⟨u,hu⟩ := h
  refine ⟨Fin.append u (fun _ : Fin k => 1),?_⟩
  intro g
  obtain ⟨a,ha⟩ := hu g
  refine ⟨Fin.append a (fun _ : Fin k => 0),?_⟩
  rw [powerWord_append,ha]
  simp [powerWord]

/-- A concrete side length with the strict density inequality needed by
Schwartz--Zippel and a linear inverse-density upper bound. -/
theorem dense_grid_side_bound (d e g : ℕ) (he : 0 < e) (heg : e ≤ g) :
    let L : ℕ := d*g/e+1
    0 < L ∧ d*g < e*L ∧ (L : ℝ) ≤ (d+1 : ℕ) * ((g : ℝ)/e) := by
  dsimp only
  have hmod := Nat.mod_lt (d*g) he
  have heq := Nat.mod_add_div (d*g) e
  have hdiv := Nat.div_mul_le_self (d*g) e
  refine ⟨by positivity,by nlinarith,?_⟩
  have hb : (d*g/e+1)*e ≤ (d+1)*g := by nlinarith
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  rw [← mul_div_assoc]
  apply (le_div_iff₀ heR).mpr
  exact_mod_cast hb

def denseMultiplierPower (n D : ℕ) : ℕ := (n+2*n*(D-1))*D^n

def denseMultiplierConstant (n D : ℕ) : ℕ :=
  (D^n).factorial * (n*(D-1)+1)^denseMultiplierPower n D

def denseMultiplierExponent (n D : ℕ) : ℕ := denseMultiplierPower n D + 1

theorem denseMultiplierConstant_pos (n D : ℕ) : 0 < denseMultiplierConstant n D := by
  unfold denseMultiplierConstant
  positivity

theorem denseMultiplierExponent_pos (n D : ℕ) : 0 < denseMultiplierExponent n D := by
  exact Nat.succ_pos _

/-- A uniform polynomial inverse-density bound for the augmentation multiplier,
for any finite group with a fixed number of ordered power coordinates. -/
theorem dense_power_coordinate_generation {G : Type*} [Group G] [Finite G]
    (n D : ℕ) (hcoords : HasPowerCoordinates G n) (E : Finset G) (hE : E.Nonempty) :
    ∃ M : ℕ, 0 < M ∧
      (M : ℝ) ≤ denseMultiplierConstant n D *
        ((Nat.card G : ℝ)/E.card)^denseMultiplierExponent n D ∧
      ∀ x : TruncatedGroupRing G D,
        M • x ∈ AddSubgroup.closure (truncatedElement G D '' (E : Set G)) := by
  classical
  let _ := Fintype.ofFinite G
  have he : 0 < E.card := Finset.card_pos.mpr hE
  have heg : E.card ≤ Fintype.card G := Finset.card_le_univ E
  let d := n*(D-1)
  let L := d*Fintype.card G/E.card+1
  obtain ⟨hL,hsize,hupper⟩ := dense_grid_side_bound d E.card (Fintype.card G) he heg
  obtain ⟨u,hu⟩ := hcoords
  obtain ⟨M,hM,hbound,hspan⟩ := dense_coordinate_multiplier D L hL u hu E hsize
  refine ⟨M,hM,?_,hspan⟩
  let deltaInv : ℝ := Fintype.card G / E.card
  have hdelta : 1 ≤ deltaInv := by
    apply (le_div_iff₀ (by exact_mod_cast he)).mpr
    simpa using (show (E.card : ℝ) ≤ Fintype.card G by exact_mod_cast heg)
  have hb : (M : ℝ) ≤ ((D^n).factorial : ℝ) * (L : ℝ)^denseMultiplierPower n D := by
    exact_mod_cast hbound
  rw [Nat.card_eq_fintype_card]
  change (M : ℝ) ≤ denseMultiplierConstant n D * deltaInv^denseMultiplierExponent n D
  calc
    (M : ℝ) ≤ ((D^n).factorial : ℝ) * (L : ℝ)^denseMultiplierPower n D := hb
    _ ≤ ((D^n).factorial : ℝ) * (((d+1 : ℕ) : ℝ) * deltaInv)^denseMultiplierPower n D := by
      gcongr
    _ = (denseMultiplierConstant n D : ℝ) * deltaInv^denseMultiplierPower n D := by
      simp [denseMultiplierConstant,mul_pow,d,mul_assoc]
    _ ≤ (denseMultiplierConstant n D : ℝ) * deltaInv^denseMultiplierExponent n D := by
      gcongr
      exact Nat.le_succ _

/-- The multiplier assertion of manuscript Theorem 5.4, with explicit constants
depending only on r, c and D. The separate Passi-group index assertion is not
included in this theorem. -/
theorem nilpotent_dense_generation {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (r c D : ℕ) (hr : Group.rank G ≤ r) (hc : Group.nilpotencyClass G ≤ c)
    (E : Finset G) (hE : E.Nonempty) :
    let R := ∑ i ∈ Finset.range c, r^(i+1)
    ∃ M : ℕ, 0 < M ∧
      (M : ℝ) ≤ denseMultiplierConstant R D *
        ((Nat.card G : ℝ)/E.card)^denseMultiplierExponent R D ∧
      ∀ x : TruncatedGroupRing G D,
        M • x ∈ AddSubgroup.closure (truncatedElement G D '' (E : Set G)) := by
  obtain ⟨n,hn,hcoords⟩ := nilpotent_power_coordinates r c hr hc
  exact dense_power_coordinate_generation _ D (hasPowerCoordinates_mono hcoords hn) E hE

end DirectedCycles
