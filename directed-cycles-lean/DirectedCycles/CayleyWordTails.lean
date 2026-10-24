import DirectedCycles.CayleyWords

set_option autoImplicit false
namespace DirectedCycles

/-- The half-open vertices of a word path, omitting its final endpoint. -/
def wordTails {G : Type*} [Group G] (x : G) : List G → List G
  | [] => []
  | a::xs => x :: wordTails (x*a) xs

@[simp] theorem wordTails_length {G : Type*} [Group G] (x : G) (xs : List G) :
    (wordTails x xs).length = xs.length := by
  induction xs generalizing x with
  | nil => rfl
  | cons a xs ih => simp only [wordTails,List.length_cons,ih]

theorem wordVertices_eq_tails_append {G : Type*} [Group G] (x : G) (xs : List G) :
    wordVertices x xs = wordTails x xs ++ [x*xs.prod] := by
  induction xs generalizing x with
  | nil => simp [wordVertices,wordTails]
  | cons a xs ih => simp only [wordVertices,wordTails,List.cons_append,ih,List.prod_cons,mul_assoc]

@[simp] theorem wordVertices_dropLast {G : Type*} [Group G] (x : G) (xs : List G) :
    (wordVertices x xs).dropLast = wordTails x xs := by
  rw [wordVertices_eq_tails_append,List.dropLast_concat]

theorem wordTails_append {G : Type*} [Group G] (x : G) (xs ys : List G) :
    wordTails x (xs++ys) = wordTails x xs ++ wordTails (x*xs.prod) ys := by
  induction xs generalizing x with
  | nil => simp [wordTails]
  | cons a xs ih => simp only [List.cons_append,wordTails,ih,List.prod_cons,mul_assoc]

/-- The exact outgoing coordinates in a repeated distinguished-generator run. -/
theorem wordTails_replicate {G : Type*} [Group G] (x a : G) (n : ℕ) :
    wordTails x (List.replicate n a) = List.ofFn (fun k : Fin n => x*a^k.val) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,wordTails,ih,List.ofFn_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ',mul_assoc]

/-- A connector consists of its outgoing portion, including the s-edge tail,
followed by its incoming portion, excluding the final endpoint. -/
theorem wordTails_connector {G : Type*} [Group G] (x a s : G) (D j : ℕ) :
    wordTails x (List.replicate j a ++ [s] ++ List.replicate (D-j) a) =
      List.ofFn (fun k : Fin (j+1) => x*a^k.val) ++
      List.ofFn (fun k : Fin (D-j) => (x*a^j*s)*a^k.val) := by
  rw [wordTails_append,wordTails_append,wordTails_replicate,wordTails_replicate]
  simp only [List.prod_replicate,wordTails]
  rw [List.ofFn_succ']
  simp only [Fin.val_castSucc,Fin.val_last]
  simp only [List.concat_eq_append,List.prod_append,List.prod_replicate,List.prod_singleton,mul_assoc]

/-- The incoming portion also has exact backwards coordinates from the end. -/
theorem connector_incoming_coordinate {G : Type*} [Group G]
    (x a s : G) (D j k : ℕ) (hk : k < D-j) :
    x*a^j*s*a^k = (x*a^j*s*a^(D-j))*a^(-((D-j-k : ℕ) : ℤ)) := by
  rw [mul_assoc (x*a^j*s),← zpow_natCast a (D-j),← zpow_add]
  have he : ((D-j : ℕ) : ℤ)+ -((D-j-k : ℕ) : ℤ) = (k : ℤ) := by omega
  rw [he,zpow_natCast]

end DirectedCycles
