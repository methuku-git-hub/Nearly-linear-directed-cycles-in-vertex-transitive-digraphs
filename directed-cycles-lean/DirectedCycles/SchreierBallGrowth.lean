import DirectedCycles.BallCardinalityGrowth
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Index

set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles

/-- Positive words suffice to generate a finite group. -/
theorem exists_mem_set_pow {G : Type*} [Group G] [Finite G] (S : Set G)
    (hgen : Subgroup.closure S = ⊤) (g : G) : ∃ n : ℕ, g ∈ S^n := by
  let M : Submonoid G := {
    carrier := {g | ∃ n : ℕ, g ∈ S^n}
    one_mem' := ⟨0,rfl⟩
    mul_mem' := by
      rintro x y ⟨n,hn⟩ ⟨m,hm⟩
      exact ⟨n+m,by rw [pow_add]; exact Set.mul_mem_mul hn hm⟩ }
  have hM : Submonoid.closure S ≤ M := by
    apply Submonoid.closure_le.mpr
    intro s hs
    exact ⟨1,by simpa only [pow_one] using hs⟩
  have htop : Submonoid.closure S = ⊤ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite,hgen,Subgroup.top_toSubmonoid]
  exact hM (by rw [htop]; trivial)

def schreierDigraph {G V : Type*} [Group G] [MulAction G V] (S : Set G) : Digraph V :=
  fun x y => ∃ s ∈ S, s • x = y

theorem schreier_reachable_pow {G V : Type*} [Group G] [MulAction G V]
    (S : Set G) (e : V) (n : ℕ) (g : G) (hg : g ∈ S^n) :
    Reachable (schreierDigraph S) e (g • e) := by
  induction n generalizing g with
  | zero =>
    have he : g = 1 := hg
    subst g
    rw [one_smul]
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    rw [pow_succ'] at hg
    obtain ⟨a,ha,b,hb,rfl⟩ := hg
    exact (ih b hb).tail ⟨a,ha,(mul_smul a b e).symm⟩

theorem finite_schreier_stronglyConnected {G V : Type*} [Group G] [Finite G] [MulAction G V]
    (S : Set G) (hgen : Subgroup.closure S = ⊤)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) : StronglyConnected (schreierDigraph S : Digraph V) := by
  intro x y
  obtain ⟨g,rfl⟩ := ht x y
  obtain ⟨n,hn⟩ := exists_mem_set_pow S hgen g
  exact schreier_reachable_pow S x n g hn

theorem schreier_ball_eq_image {G V : Type*} [Group G] [MulAction G V]
    (S : Set G) (h1 : 1 ∈ S) (e : V) (n : ℕ) :
    relationBall (schreierDigraph S) e n = (fun g : G => g • e) '' (S^n) := by
  induction n with
  | zero => simp [relationBall]
  | succ n ih =>
    ext y
    constructor
    · rintro ⟨x,hx,hy⟩
      rw [ih] at hx
      obtain ⟨g,hg,rfl⟩ := hx
      rcases hy with hy | ⟨a,ha,hy⟩
      · refine ⟨g,?_,hy.symm⟩
        rw [pow_succ']
        exact ⟨1,h1,g,hg,one_mul g⟩
      · refine ⟨a*g,?_,?_⟩
        · rw [pow_succ']; exact Set.mul_mem_mul ha hg
        · exact (mul_smul a g e).trans hy
    · rintro ⟨g,hg,rfl⟩
      rw [pow_succ'] at hg
      obtain ⟨a,ha,b,hb,rfl⟩ := hg
      refine ⟨b • e,?_,Or.inr ⟨a,ha,(mul_smul a b e).symm⟩⟩
      rw [ih]
      exact ⟨b,hb,rfl⟩

/-- The finite form of TT Lemma 6.7: the first m-1 powers meet at least
m cosets whenever the index is at least m. No symmetry is needed in a finite group. -/
theorem finite_coset_growth {G : Type*} [Group G] [Finite G]
    (S : Set G) (h1 : 1 ∈ S) (hgen : Subgroup.closure S = ⊤)
    (H : Subgroup G) (m : ℕ) (hm : m ≤ H.index) :
    m ≤ Nat.card ↥((Quotient.mk'' : G → G ⧸ H) '' (S^(m-1))) := by
  by_cases hm0 : m = 0
  · subst m; exact Nat.zero_le _
  let e : G ⧸ H := Quotient.mk'' 1
  have ht : ∀ x y : G ⧸ H, ∃ g : G, g • x = y := by
    intro x y
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b => exact ⟨b*a⁻¹,by change Quotient.mk'' (b*a⁻¹*a) = Quotient.mk'' b; simp⟩
  have hc := finite_schreier_stronglyConnected S hgen ht
  have hb := relationBall_card_lower_bound (schreierDigraph S) e hc (m-1)
  rw [schreier_ball_eq_image S h1] at hb
  have he : (fun g : G => g • e) = (Quotient.mk'' : G → G ⧸ H) := by
    funext g
    change Quotient.mk'' (g*1) = Quotient.mk'' g
    rw [mul_one]
  rw [he,show m-1+1 = m by omega,← H.index_eq_card,min_eq_left hm] at hb
  exact hb

/-- TT Lemma 6.8 for finite groups, with the actual normal core. -/
theorem finite_normal_core_index {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    H.normalCore ≤ H ∧ H.normalCore.Normal ∧ H.normalCore.index ≤ H.index.factorial := by
  refine ⟨H.normalCore_le,inferInstance,?_⟩
  have hd : H.normalCore.index ∣ H.index.factorial := by
    rw [Subgroup.normalCore_eq_ker,Subgroup.index_ker,Subgroup.index_eq_card,← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card (MulAction.toPermHom G (G ⧸ H)).range
  exact Nat.le_of_dvd (Nat.factorial_pos _) hd

end DirectedCycles
