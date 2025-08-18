import Mathlib
--修改

variable {α : Type*}

open Matrix Equiv Nat List

section Basic

variable {n m} (M : Matrix (Fin n) (Fin m) α)
def swap_rows  (i j : Fin n) : Matrix (Fin n) (Fin m) α :=
    M.submatrix (swap i j : Perm (Fin n)) id
    -- submatrix M (swap i j : Perm (Fin n)) id

def swap_cols  (i j : Fin m) : Matrix (Fin n) (Fin m) α :=
   (swap_rows M.transpose i j).transpose

#check swap_cols !![0,1;2,1] 0 1

#eval swap_cols !![0,1;2,1] 0 1

variable {𝕜} [SMul 𝕜 α]

def scale_row (i : Fin n) (c : 𝕜) : Matrix (Fin n) (Fin m) α :=
    updateRow M i <| c • (M i)
#eval scale_row !![0,0;1,1] 1 2

def add_row_multiple [Add α] (i j : Fin n) (c : 𝕜) : Matrix (Fin n) (Fin m) α :=
    updateRow M i <| (M i) + c • (M j)

#eval add_row_multiple !![0,0;1,1] 0 1 2

def gaussian_update [Add α] [Mul α] [Sub α]
    (i k : Fin n) (a b : α) : (Fin m) → α :=
  if k ≤ i then M k else a • M k - b • M i

def gaussian_update_row [Add α] [Mul α] [Sub α]
  (i : Fin n) (j : Fin m):
  Matrix (Fin n) (Fin m) α :=
  fun k => gaussian_update M i k (M i j) (M k j)

-- def gaussian_update_col [Add α] [Mul α] [Sub α] [Neg α][NeZero n] [NeZero m]
--   (i : Fin n) (hi : i < m) : Matrix (Fin n) (Fin m) α :=
--   (gaussian_update_row (M.transpose) ⟨i, hi⟩ (by simp)).transpose

end Basic

structure Gaussian (n m α) [Ring α] where
  P : Matrix (Fin n) (Fin n) α
  R : Matrix (Fin n) (Fin m) α
  Q : Matrix (Fin m) (Fin m) α
  M : Matrix (Fin n) (Fin m) α
  hm : P * M * Q = R
  -- P M Q = [I_r, 0;
            -- 0, 0]

def Gaussian.transpose {n m α}[Ring α](M : Gaussian n m α) : Gaussian m n α where
  P := M.Q.transpose
  R := M.R.transpose
  Q := M.P.transpose
  M := M.M.transpose
  hm := by
    rw [← M.hm]
    sorry


section Gauss


variable {n m} [Ring α] (M : Gaussian n m α) [NeZero n] [NeZero m]

-- def finListRec {n : ℕ} (i : Fin n) : List (Fin n)
-- | ⟨i, hi⟩ =>
--   if h : i + 1 < n then
--     ⟨i, hi⟩ :: finListRec ⟨i + 1, h⟩
--   else
--     [⟨i, hi⟩]

#eval (List.finRange 2).rtake 1
#check List.rtake

-- def finListRec {n : ℕ} : Fin n → List (Fin n)
--   | ⟨i, hi⟩ => go i hi
-- where
--   go : ∀ (i : ℕ) (_ : i < n), List (Fin n)
--     | i, hi =>
--       if h : i + 1 < n then
--         ⟨i, hi⟩ :: go (i + 1) h
--       else
--         [⟨i, hi⟩]
/-
 ****
 ****
 ****
-/
omit [NeZero n] in
def find_pivot_col [LinearOrder α] (M : Fin n → α) (i : Fin n): Fin n :=
  -- (List.argmax (abs ∘ M) (List.ofFn (id : Fin n → Fin n))).getD 0
  -- (List.argmax (abs ∘ M) (finListRec i)).getD 0
  (argmax (abs ∘ M) ((finRange n).rtake (n - i))).getD 0

-- def find_pivot_col_row [LinearOrder α] (M : Matrix (Fin n) (Fin m) α) (i : Fin n): Fin n :=
  -- (List.argmax (abs ∘ M) (List.ofFn (id : Fin n → Fin n))).getD 0
  -- (List.argmax (abs ∘ M) (finListRec i)).getD 0
  -- (List.argmax (abs ∘ M) ((List.finRange n).rtake (n - i))).getD 0
#check Finset.Ici
#check List.range
#check List.range'

#eval find_pivot_col (fun (i : Fin 4) =>(if i = 0 then -4 else 5 : ℤ) )

-- 目前进行到(i,j)，接下来选取按行来消元
/-
1 2 3
4 5 6
7 8 9

[A, I]
=>
[PA, P]

-/
def gaussian_elimination_step_row (i : Fin n) (j : Fin m) (hM : M.R i j ≠ 0)
    : Gaussian n m α where
  P := fun k => gaussian_update M.P i k (M.R i j) (M.R k j)
  R := gaussian_update_row M.R i j
  Q := M.Q
  M := M.M
  -- gaussian_update_scale M.M
  hm := sorry

-- def gaussian_elimination_step_col (i : Fin n) (hi : i < m) (hM : M.R i ⟨i, hi⟩ ≠ 0)
--     : Gaussian n m α where
--   P := M.P
--   R := gaussian_update_col M.R i hi
--   Q := fun k => gaussian_update M.Q.transpose ⟨i,hi⟩ k (M.R i ⟨i, hi⟩) (M.R k ⟨i, hi⟩)
--   M := M.M
--   hm := sorry

-- #eval! gaussian_elimination_step_row (Gaussian.mk 1 !![(3 : ℤ),2;2,3] 1 !![(3 : ℤ),2;2,3] (by simp)) 0 (by simp) (by simp)

-- #eval! gaussian_elimination_step_row (Gaussian.mk 1 !![(2 : ℤ),2;2,3] 1 !![(2 : ℤ),2;2,3] (by simp)) 0 (by simp) (by simp)


#eval find_pivot_col (fun n : Fin 2 => if n = 0 then (2 : ℤ) else 3)
/-
1 2 3
4 5 6
7 8 9

[A, I]
=>
[PA, P]
-/
-- 目前进行到(i,j)，接下来选取列主元
def gaussian_elimination_pivot_row [LinearOrder α] (i : Fin n) (j : Fin m) :
    Gaussian n m α :=
  -- 取出第j列，从第i行开始的最大元素的下标
  let z := (find_pivot_col (fun k => M.R k j) i)
  -- 如果最大元素的下标和本身一样，。。。
  if z = i then M
  else
    {
    P := swap_rows M.P z i
    R := swap_rows M.R z i
    Q := M.Q
    M := M.M
    hm := sorry
    }

  -- Nat.add_comm a b

def gaussian_elimination_row_aux [LinearOrder α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    Gaussian n m α :=

  let rown : Fin n := ⟨row, hr⟩
  let colm : Fin m := ⟨col, hc⟩

  let pivotA := gaussian_elimination_pivot_row M rown colm
/-
  1 1 1
  0 3 2
  0 0 3
-/
  if ht : (row < n - 1) ∧ (col < m - 1) then
    if h : pivotA.R rown colm = 0 then
      gaussian_elimination_row_aux pivotA row hr (col + 1) (add_lt_of_lt_sub ht.2)

    else
      let nextA := gaussian_elimination_step_row pivotA rown colm h
      gaussian_elimination_row_aux nextA (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2)
  else
    pivotA
termination_by (n + m) - (row + col)
decreasing_by
  rw [tsub_lt_tsub_iff_left_of_le]
  simp; linarith
  rw [tsub_lt_tsub_iff_left_of_le]
  linarith; linarith

def gaussian_elimination_row [LinearOrder α] : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then gaussian_elimination_row_aux M 0 h.1 0 h.2
  else M

-- #check Gaussian.mk 1 !![(2 : ℤ),2;2,3] 1 !![(2 : ℤ),2;2,3] (by simp)

#check Gaussian.mk

#check (Gaussian.mk 1 !![(3 : ℤ),2;2,3] 1 !![(3 : ℤ),2;2,3] (by simp))

#check (⟨1, !![(3 : ℤ),2;2,3], 1, !![(3 : ℤ),2;2,3], by simp⟩ : Gaussian _ _ _)

#eval! gaussian_elimination_row (Gaussian.mk 1 !![(3 : ℤ),2;2,3] 1 !![(3 : ℤ),2;2,3] (by simp))

#eval !![1, 0; -2, 3] * !![3, 2; 2, 3]

#eval !![3, 2; 0, 5]

#eval! gaussian_elimination_row (Gaussian.mk 1 !![(3 : ℤ),2;2,3] 1 !![(3 : ℤ),2;2,3] (by simp))
-- #eval (!![1, 0; -3, 3]) * (!![3, 2; 2, 3])

#eval! gaussian_elimination_row (Gaussian.mk 1 !![(2 : ℤ),2,4;7,3,1;300,9,10] 1 !![(2 : ℤ),2,4;7,3,1;300,9,10] (by simp))

#eval !![0, 0, 1; 0, 300, -7; 251100, -174600, 2400] * !![2, 2, 4; 7, 3, 1; 300, 9, 10]
-- #eval (!![0, 1, 0; 0, -3, 7; 378, -84, -56]) * (!![2, 2, 4; 7, 3, 1; 3, 9, 10])

-- -- !! [3, 7, 9, 10; 7, 6, 2 ,1 ; 10, 13, 11, 11]
#eval! gaussian_elimination_row (Gaussian.mk 1 !![3, 7, 9, (10 : ℤ); 7, 6, 2 ,1 ; 10, 13, 11, 11] 1 !![3, 7, 9, (10 : ℤ); 7, 6, 2 ,1 ; 10, 13, 11, 11] (by simp))

-- #eval! gaussian_elimination_row (Gaussian.mk 1 !![3, 7, 9, (10 : ℤ); 3, 7, 11, 11 ; 2, 6, 2 ,1 ] 1 !![3, 7, 9, (10 : ℤ); 3, 7, 11, 11; 2, 6, 2 ,1] (by simp)) (by simp)

#eval! gaussian_elimination_row (Gaussian.mk 1 !![3, 7, 9, (10 : ℤ); 3, 7, 9, 10 ; 3, 7, 2 ,1 ] 1 !![3, 7, 9, (10 : ℤ); 3, 7, 9, 10; 3, 7, 2 ,1] (by simp))

def gaussian_elimination_col_aux [LinearOrder α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    Gaussian n m α :=

  let rown : Fin n := ⟨row, hr⟩
  let colm : Fin m := ⟨col, hc⟩

  if ht : (row < n - 1) ∧ (col < m - 1) then
    if h : M.R rown colm = 0 then gaussian_elimination_col_aux M (row + 1) (add_lt_of_lt_sub ht.1) col hc
    else
      let nextA := gaussian_elimination_step_row M rown colm h
      gaussian_elimination_col_aux nextA (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2)
  else
    M
termination_by (n + m) - (row + col)
decreasing_by
  rw [tsub_lt_tsub_iff_left_of_le]
  simp; linarith
  rw [tsub_lt_tsub_iff_left_of_le]
  linarith; linarith

def gaussian_elimination_col [LinearOrder α] : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then (gaussian_elimination_col_aux M.transpose 0 h.2 0 h.1).transpose
  else M

#eval!  gaussian_elimination_col <| (Gaussian.mk 1 !![3, 7, (9 : ℤ) ; 3, 7, 9] 1 !![3, 7, 9; 3, 7, 9] (by simp))

#eval! gaussian_elimination_col <| gaussian_elimination_row <| (Gaussian.mk 1 !![3, 7, 9, (10 : ℤ); 3, 7, 9, 10 ; 3, 7, 2 ,1 ] 1 !![3, 7, 9, (10 : ℤ); 3, 7, 9, 10; 3, 7, 2 ,1] (by simp))

#eval !![1, 0, 0; -3, 0, 3; 63, -63, 0] * !![3, 7, 9, (10 : ℤ); 3, 7, 9, 10; 3, 7, 2, 1] * !![1, -7, -9, -99; 0, 3, 0, 0; 0, 0, 3, 243; 0, 0, 0, -189]
-- def get_nezero_index (u : Matrix (Fin n) (Fin m) α) : List (Fin m) :=
--   match u with
--   | fun i j =>
--     if u i = 0 then []
--     else []
--   | []

#check List.zip_swap
#check Equiv.swap
#check List.swapFirstTwo
-- def swap_nezero [Ring α] (u : Fin m → α) : Fin m :=
--   match u with
--   | u =>

def firstNonZeroIndex [DecidableEq α] (u : Fin m → α) (i : Fin m):
    Option (Fin m) :=
  ((finRange m).rtake (m - i)) |>.find? (fun i => u i ≠ 0)

-- def find? (p : α → Bool) : List α → Option α :=
--   fun x =>
--     match x with
--     | [] => none
--     | a :: as => sorry
  -- | []    => none
  -- | a::as => match p a with
  --   | true  => some a
  --   | false => find? p as

-- |> <|

/-
1 0 0 0
0 0 1 0
0 0 0 2
0 0 0 0

=>

1 0 0 0
0 1 0 0
-/
def findNonZeroIndex [DecidableEq α] (u : Matrix (Fin n) (Fin m) α) (i : Fin n) (j : Fin m) :
    (Fin n) × (Fin m) :=
  let col := (firstNonZeroIndex (u i) j).getD j
  let row := (firstNonZeroIndex (fun k => u k j) i).getD i
  (row, col)

#eval findNonZeroIndex !![1, 0, (0 : ℤ), 0 ; 0, 0, (0: ℤ), 1] 1 1

def gaussian_elimination_step_final [LinearOrder α] (i : Fin n) (j : Fin m) :
    Gaussian n m α :=
  -- 取出第j列，从第i行开始的不为0的下标
  let z := findNonZeroIndex M.R i j
  -- 如果下标和本身一样，。。。
  if z = (i, j) then M
  else if z.1 = i then
    {
      P := M.P
      R := swap_cols M.R z.2 j
      Q := swap_cols M.Q z.2 j
      M := M.M
      hm := sorry
    }
  else
    {
    P := swap_rows M.P z.1 i
    R := swap_rows M.R z.1 i
    Q := M.Q
    M := M.M
    hm := sorry
    }

def gaussian_elimination_final_aux [LinearOrder α] (M : Gaussian n m α)
    (idx : ℕ) (h : idx < n ∧ idx < m) :
    Gaussian n m α :=
  let nextM := gaussian_elimination_step_final M ⟨idx, h.1⟩ ⟨idx, h.2⟩
  if ht : (idx < n - 1) ∧ (idx < m - 1) then
    gaussian_elimination_final_aux nextM (idx + 1) ⟨add_lt_of_lt_sub ht.1, add_lt_of_lt_sub ht.2⟩
  else
    nextM
termination_by min n m - idx
-- decreasing_by
--   rw [tsub_lt_tsub_iff_left_of_le]
--   simp; simpa using ⟨le_of_lt <| add_lt_of_lt_sub ht.1, le_of_lt <| add_lt_of_lt_sub ht.2⟩

def gaussian_elimination_final [LinearOrder α] : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then gaussian_elimination_final_aux M 0 h
  else M

#eval! gaussian_elimination_final (Gaussian.mk 1 !![1, 0, (0 : ℤ), 0 ; 0, 0, (0: ℤ), 5] 1 !![1, 0, (0 : ℤ), 0 ; 0, 0, (0: ℤ), 5] (by simp))

    -- where
  -- P := M.P
  -- R := fun k =>
  --   let kn := firstNonZeroIndex (M.R k)
  --   if kn = none then M.R k
  --   else
  --    fun j =>
  --     if j = k.1 then M.R k (kn.getD 0)
  --     else 0
  -- Q :=
  --   let olaux : Fin n → (Option <| Fin m) :=
  --     fun k => firstNonZeroIndex (M.R k)
  --   -- let ol : List <| Option <| Fin m := List.ofFn olaux
  --   Fin.foldl n (fun (current : Matrix (Fin m) (Fin m) α) (k : Fin n) =>
  --     match olaux k with
  --     | some j => swap_cols current j ⟨k, sorry⟩
  --     | none => current
  --     ) M.Q
    -- sorry

  -- M := M.M
  -- -- gaussian_update_scale M.M
  -- hm := sorry

def gaussian_elimination [LinearOrder α] : Gaussian n m α :=
  gaussian_elimination_final <| gaussian_elimination_col <| gaussian_elimination_row M

def Gaussian.init (A : Matrix (Fin n) (Fin m) α) : Gaussian n m α :=
    ⟨1, A, 1, A, by simp⟩

#eval! gaussian_elimination
  (Gaussian.init !![1, 2, (3 : ℤ), 4 ;
                    1, 2, (5 : ℤ), 6 ;
                    1, 2, (7 : ℤ), 8 ])
#eval !![1, 0, 0; -1, 0, 1; -2, 4, -2] * !![1, 2, (3 : ℤ), 4; 1, 2, 5, 6; 1, 2, 7, 8] * !![1, -3, -2, -4; 0, 0, 1, 0; 0, 1, 0, -4; 0, 0, 0, 4]

def rankStdBlock (K : Type*) [Zero K] [One K]
    (m n r : ℕ) : Matrix (Fin m) (Fin n) K :=
  fun i j => if (i : ℕ) < r ∧ (j : ℕ) < r then
            if (i : ℕ) = j then 1 else 0
          else 0

end Gauss


section Classification

variable {K : Type*} [CommRing K]
variable {m n : ℕ}

def rankEquiv (A B : Matrix (Fin m) (Fin n) K) : Prop :=
  ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K), B = P.1 * A * Q.1

theorem rankEquiv_iff_rank_eq (A B : Matrix (Fin m) (Fin n) K) :
    rankEquiv A B ↔ rank A = rank B := by sorry

instance rankEquiv_setoid : Setoid (Matrix (Fin m) (Fin n) K) where
 r := rankEquiv
 iseqv := sorry

theorem rankEquiv_to_rankStdBlock [Field K] (A : Matrix (Fin m) (Fin n) K) :
    rankEquiv A (rankStdBlock K m n A.rank) := by sorry

end Classification

section Row

open Submodule Set
variable {K : Type*} [CommRing K]
variable {m n : ℕ}

theorem rowSpace_left_mul_invariant
    (P : GL (Fin m) K) (A : Matrix (Fin m) (Fin n) K) :
    span K (range (P.1 * A)) = span K (range A) := by
  sorry

theorem rowSpace_guass_invariant [NeZero n] [NeZero m] [LinearOrder K] (M : Gaussian n m K) :
    span K (range (gaussian_elimination_row M).R) = span K (range M.R) := by
  sorry

end Row

section RankNormalForm

variable {m n : ℕ} {K : Type*} (A : Matrix (Fin m) (Fin n) K)

theorem Matrix.exists_rank_normal_form [CommRing K] :
    ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K),
      ∀ (i : Fin m) (j : Fin n),
          if (i : ℕ) < A.rank ∧ (j : ℕ) < A.rank ∧ (i : ℕ) = j then
            (P.1 * A * Q.1) i j ≠ 0
          else (P.1 * A * Q.1) i j = 0 := by
  sorry

#check finSumFinEquiv



theorem Matrix.exists_rank_standard_form [Field K]:
    ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K),
      P.1 * A * Q.1 = rankStdBlock K m n A.rank := by
  sorry

end RankNormalForm

section LU

open Equiv Equiv.Perm
variable {K : Type*} [Ring K]

#check Matrix.BlockTriangular
#check Equiv.Perm.permMatrix

theorem Matrix.exists_LU_decomposition
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    ∃ (σ : Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) K),
      L.BlockTriangular id   ∧
      U.BlockTriangular (-id) ∧
      (∀ i, L i i = 1) ∧
      (permMatrix K σ) * A = L * U := by
  sorry

end LU

section Fullrankfactorization

variable {K : Type*} [CommRing K]

theorem exists_fullRank_factorization {m n}
    (A : Matrix (Fin m) (Fin n) K) :
    ∃ (B : Matrix (Fin m) (Fin A.rank) K) (C : Matrix (Fin A.rank) (Fin n) K),
    A = B * C := by sorry

end Fullrankfactorization
