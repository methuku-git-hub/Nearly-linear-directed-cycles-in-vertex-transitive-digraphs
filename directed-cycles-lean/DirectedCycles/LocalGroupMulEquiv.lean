import DirectedCycles.LocalGroupHom

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupHom
variable {G H : Type*} {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}

/-- A bijection reflecting the partial multiplication relation preserves the
identity, as a consequence of the actual local identity and uniqueness axioms. -/
theorem mulEquiv_map_one (e : G ≃ H)
    (he : ∀ x y z, L.mulRel x y z ↔ M.mulRel (e x) (e y) (e z)) : e L.one = M.one := by
  have hh := (he L.one (e.symm M.one) (e.symm M.one)).1 (L.one_mul (e.symm M.one))
  simp only [e.apply_symm_apply] at hh
  exact (M.unique hh (M.mul_one (e L.one))).symm

/-- Cancellation then identifies the actual inverses. -/
theorem mulEquiv_map_inv (hM : M.Cancellative) (e : G ≃ H)
    (he : ∀ x y z, L.mulRel x y z ↔ M.mulRel (e x) (e y) (e z)) (x : G) :
    e (L.inv x) = M.inv (e x) := by
  have hh := (he (L.inv x) x L.one).1 (L.inv_mul x)
  rw [mulEquiv_map_one e he] at hh
  exact hM.right_cancel hh (M.inv_mul (e x))

def ofMulEquiv (hM : M.Cancellative) (e : G ≃ H)
    (he : ∀ x y z, L.mulRel x y z ↔ M.mulRel (e x) (e y) (e z)) : LocalGroupHom L M where
  toFun := e
  map_one := mulEquiv_map_one e he
  map_inv := mulEquiv_map_inv hM e he
  map_mul := (he _ _ _).1

def inverseOfMulEquiv (hL : L.Cancellative) (e : G ≃ H)
    (he : ∀ x y z, L.mulRel x y z ↔ M.mulRel (e x) (e y) (e z)) : LocalGroupHom M L :=
  ofMulEquiv hL e.symm (by
    intro x y z
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y) (e.symm z)).symm)
end LocalGroupHom
end DirectedCycles
