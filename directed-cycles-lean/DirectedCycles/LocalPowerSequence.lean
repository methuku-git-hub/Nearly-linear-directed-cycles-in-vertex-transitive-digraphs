module

public import DirectedCycles.LocalGroupProducts

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

/-- A sequence of powers whose every finite product, with every bracketing,
is actually defined. This is stronger than a left-associated recursion. -/
structure PowerSequence (g : G) where
  power : ℕ → G
  product : ∀ n, L.Product (List.replicate n g) (power n)

namespace PowerSequence
variable {L} {g : G} (p : L.PowerSequence g)

theorem zero : p.power 0 = L.one := (Product.nil_iff L).1 (p.product 0)

theorem one : p.power 1 = g := (Product.singleton_iff L).1 (p.product 1)

theorem add (n m : ℕ) : L.mulRel (p.power n) (p.power m) (p.power (n+m)) := by
  by_cases hn : n = 0
  · subst n
    simpa only [p.zero,Nat.zero_add] using L.one_mul (p.power m)
  by_cases hm : m = 0
  · subst m
    simpa only [p.zero,Nat.add_zero] using L.mul_one (p.power n)
  obtain ⟨x,y,hx,hy,hxy⟩ := (p.product (n+m)).split L (List.replicate_add n m g)
    (by simpa using hn) (by simpa using hm)
  have hx' := hx.unique L (p.product n)
  have hy' := hy.unique L (p.product m)
  simpa only [hx',hy'] using hxy

theorem exists_period [Finite G] (hL : L.Cancellative) : ∃ m : ℕ, 0 < m ∧ p.power m = L.one := by
  obtain ⟨i,j,hij,he⟩ := Finite.exists_ne_map_eq_of_infinite p.power
  have step : ∀ i j : ℕ, i < j → p.power i = p.power j →
      ∃ m : ℕ, 0 < m ∧ p.power m = L.one := by
    intro i j hij he
    refine ⟨j-i,by omega,?_⟩
    have h := p.add i (j-i)
    rw [Nat.add_sub_of_le hij.le,← he] at h
    exact hL.left_cancel h (L.mul_one (p.power i))
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact step i j hij he
  · exact step j i hji he.symm

theorem period_mul {m : ℕ} (hm : p.power m = L.one) (k : ℕ) : p.power (m*k) = L.one := by
  induction k with
  | zero => simpa using p.zero
  | succ k ih =>
    have h := p.add (m*k) m
    rw [ih,hm] at h
    have he := L.unique h (L.one_mul L.one)
    simpa only [Nat.mul_succ] using he

theorem inv_mem_range_of_period {m : ℕ} (hmpos : 0 < m) (hm : p.power m = L.one) (n : ℕ) :
    L.inv (p.power n) ∈ Set.range p.power := by
  let k := m*(n+1)-n
  have hn : n ≤ m*(n+1) := by nlinarith
  have he : n+k = m*(n+1) := Nat.add_sub_of_le hn
  have h := p.add n k
  rw [he,p.period_mul hm (n+1)] at h
  exact ⟨k,L.right_inverse_unique h⟩

/-- Finite cancellative local groups turn a complete sequence of defined powers
into an inverse-closed, total local cyclic subgroup. -/
theorem range_closed [Finite G] (hL : L.Cancellative) :
    L.one ∈ Set.range p.power ∧
    (∀ x ∈ Set.range p.power, L.inv x ∈ Set.range p.power) ∧
    (∀ x ∈ Set.range p.power, ∀ y ∈ Set.range p.power,
      ∃ z ∈ Set.range p.power, L.mulRel x y z) := by
  obtain ⟨m,hmpos,hm⟩ := p.exists_period hL
  refine ⟨⟨0,p.zero⟩,?_,?_⟩
  · rintro x ⟨n,rfl⟩
    exact p.inv_mem_range_of_period hmpos hm n
  · rintro x ⟨n,rfl⟩ y ⟨k,rfl⟩
    exact ⟨p.power (n+k),⟨n+k,rfl⟩,p.add n k⟩
end PowerSequence
end LocalGroupAlgebra
end DirectedCycles
