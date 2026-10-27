module

public import DirectedCycles.Paths

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

/-- A finite directed walk, with repetitions allowed. -/
inductive Walk {V : Type*} (D : Digraph V) (x : V) : V → Type _
  | nil : Walk D x x
  | cons {y z : V} : Walk D x y → D y z → Walk D x z

def Walk.length {V : Type*} {D : Digraph V} {x y : V} : Walk D x y → ℕ
  | .nil => 0
  | .cons W _ => W.length + 1

def Walk.comp {V : Type*} {D : Digraph V} {x y z : V}
    (P : Walk D x y) : Walk D y z → Walk D x z
  | .nil => P
  | .cons W h => (P.comp W).cons h

@[simp] theorem Walk.length_comp {V : Type*} {D : Digraph V} {x y z : V}
    (P : Walk D x y) (Q : Walk D y z) : (P.comp Q).length = P.length + Q.length := by
  induction Q with
  | nil => rfl
  | cons Q h ih => exact congrArg (· + 1) ih

/-- Appending an arc and erasing a possible loop increases simple-path length
by at most one. -/
theorem SimplePath.extend {V : Type*} {D : Digraph V} {x y z : V}
    (P : SimplePath D x y) (hyz : D y z) :
    ∃ Q : SimplePath D x z, Q.length ≤ P.length + 1 := by
  classical
  by_cases hz : z ∈ P.vertices
  · obtain ⟨l, r, he⟩ := List.mem_iff_append.mp hz
    have he' : P.vertices = (l ++ [z]) ++ r := by simpa using he
    have hn := P.nodup
    have hc := P.chain
    rw [he'] at hn hc
    have hh : (l ++ [z]).head? = some x := by
      have hh := P.head
      rw [he] at hh
      cases l <;> simpa using hh
    let Q : SimplePath D x z := ⟨l ++ [z], (List.nodup_append.mp hn).1, hh,
      by simp, hc.left_of_append⟩
    refine ⟨Q, ?_⟩
    have hlen : (l ++ [z]).length ≤ P.vertices.length := by rw [he']; simp
    have hle := Nat.sub_le_sub_right hlen 1
    exact le_trans hle (Nat.le_add_right P.length 1)
  · have hnd : (P.vertices ++ [z]).Nodup := P.nodup.append (by simp) (by simpa using hz)
    have hh : (P.vertices ++ [z]).head? = some x := by
      simpa only [List.head?_append_of_ne_nil _ P.nonempty] using P.head
    have hc : (P.vertices ++ [z]).IsChain D := by
      apply P.chain.append (.singleton z)
      intro a ha b hb
      have ha' : a = y := by simpa only [P.last, Option.mem_some_iff, eq_comm] using ha
      have hb' : b = z := by simpa [eq_comm] using hb
      subst a; subst b
      exact hyz
    let Q : SimplePath D x z := ⟨P.vertices ++ [z], hnd, hh, by simp, hc⟩
    refine ⟨Q, ?_⟩
    have hp := List.length_pos_iff.mpr P.nonempty
    dsimp [Q, SimplePath.length]
    simp only [List.length_append, List.length_singleton]
    omega

/-- Loop erasure preserves endpoints without increasing the number of arcs. -/
theorem simplePath_of_walk {V : Type*} {D : Digraph V} {x y : V}
    (W : Walk D x y) : ∃ P : SimplePath D x y, P.length ≤ W.length := by
  induction W with
  | nil => exact ⟨⟨[x], by simp, rfl, rfl, .singleton x⟩, by simp [SimplePath.length]⟩
  | cons W e ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨Q, hQ⟩ := P.extend e
    exact ⟨Q, hQ.trans (Nat.add_le_add_right hP 1)⟩

/-- A chain list determines a walk with exactly one fewer arc than vertices. -/
theorem walk_of_chain {V : Type*} {D : Digraph V} (l : List V) :
    ∀ x y, l.IsChain D → l.head? = some x → l.getLast? = some y →
      ∃ W : Walk D x y, W.length = l.length - 1 := by
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton a =>
    intro x y _ hx hy
    have hx' : a = x := by simpa using hx
    have hy' : a = y := by simpa using hy
    subst x; subst y
    exact ⟨.nil, rfl⟩
  | cons_cons a b t _ ih =>
    intro x y hc hx hy
    have hx' : a = x := by simpa using hx
    subst x
    have hy' : (b :: t).getLast? = some y := by simpa using hy
    obtain ⟨W, hW⟩ := ih b b y hc.tail rfl hy'
    let first : Walk D a b := Walk.cons .nil hc.rel
    refine ⟨first.comp W, ?_⟩
    rw [Walk.length_comp, hW]
    simp [first, Walk.length, List.length_cons, Nat.add_comm]

def ReachWithin {V : Type*} (D : Digraph V) (t : ℕ) (x y : V) : Prop :=
  ∃ W : Walk D x y, W.length ≤ t

theorem reachWithin_iff_simplePath {V : Type*} {D : Digraph V} {t : ℕ} {x y : V} :
    ReachWithin D t x y ↔ ∃ P : SimplePath D x y, P.length ≤ t := by
  constructor
  · rintro ⟨W, hW⟩
    obtain ⟨P, hP⟩ := simplePath_of_walk W
    exact ⟨P, hP.trans hW⟩
  · rintro ⟨P, hP⟩
    obtain ⟨W, hW⟩ := walk_of_chain P.vertices x y P.chain P.head P.last
    exact ⟨W, by rw [hW]; exact hP⟩

theorem ReachWithin.refl {V : Type*} {D : Digraph V} (x : V) (t : ℕ) :
    ReachWithin D t x x := ⟨Walk.nil, Nat.zero_le t⟩

theorem ReachWithin.mono {V : Type*} {D : Digraph V} {s t : ℕ} {x y : V}
    (h : ReachWithin D s x y) (hst : s ≤ t) : ReachWithin D t x y := by
  obtain ⟨W, hW⟩ := h
  exact ⟨W, hW.trans hst⟩

theorem ReachWithin.trans {V : Type*} {D : Digraph V} {s t : ℕ} {x y z : V}
    (h₁ : ReachWithin D s x y) (h₂ : ReachWithin D t y z) : ReachWithin D (s + t) x z := by
  obtain ⟨W₁, h₁⟩ := h₁
  obtain ⟨W₂, h₂⟩ := h₂
  exact ⟨W₁.comp W₂, by simpa only [Walk.length_comp] using Nat.add_le_add h₁ h₂⟩

theorem ReachWithin.arc {V : Type*} {D : Digraph V} {x y : V} (h : D x y) :
    ReachWithin D 1 x y := ⟨Walk.cons .nil h, le_rfl⟩

noncomputable def Walk.map {V U : Type*} {D : Digraph V} {E : Digraph U} {x y : V}
    (W : Walk D x y) (f : V → U) (hf : ∀ a b, D a b → E (f a) (f b)) : Walk E (f x) (f y) := by
  induction W with
  | nil => exact .nil
  | cons _ e ih => exact ih.cons (hf _ _ e)

theorem Walk.map_length {V U : Type*} {D : Digraph V} {E : Digraph U} {x y : V}
    (W : Walk D x y) (f : V → U) (hf : ∀ a b, D a b → E (f a) (f b)) :
    (W.map f hf).length = W.length := by
  induction W with
  | nil => rfl
  | cons W e ih => exact congrArg (· + 1) ih

theorem ReachWithin.map {V U : Type*} {D : Digraph V} {E : Digraph U} {t : ℕ} {x y : V}
    (h : ReachWithin D t x y) (f : V → U) (hf : ∀ a b, D a b → E (f a) (f b)) :
    ReachWithin E t (f x) (f y) := by
  obtain ⟨W, hW⟩ := h
  exact ⟨W.map f hf, by simpa only [Walk.map_length] using hW⟩

theorem reachWithin_invariant {G V : Type*} [Group G] [MulAction G V]
    (D : Digraph V) (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y) :
    ∀ (g : G) t x y, ReachWithin D t (g • x) (g • y) ↔ ReachWithin D t x y := by
  intro g t x y
  constructor
  · intro h
    have hm := h.map (fun z => g⁻¹ • z) (fun a b hab => (hD g⁻¹ a b).mpr hab)
    simpa only [inv_smul_smul] using hm
  · intro h
    exact h.map (fun z => g • z) (fun a b hab => (hD g a b).mpr hab)

end DirectedCycles
