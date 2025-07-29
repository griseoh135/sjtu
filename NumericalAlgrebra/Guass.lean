import Mathlib

variable {α : Type*}

#check Matrix.swap
#check Matrix.updateRow

#check Matrix.submatrix
#check Matrix.det_permute'
open Matrix Equiv
#check det_updateRow_add_self
section Basic

variable {n m} (M : Matrix (Fin n) (Fin m) α)
def swap_rows  (i j : Fin n) : Matrix (Fin n) (Fin m) α :=
    M.submatrix  (swap i j : Perm (Fin n)) id

#eval swap_rows !![0,0;1,1] 0 1

variable {𝕜} [SMul 𝕜 α]

def scale_row (i : Fin n) (c : 𝕜) : Matrix (Fin n) (Fin m) α :=
    updateRow M i <| c • (M i)
#eval scale_row !![0,0;1,1] 1 2

def add_row_multiple [Add α] (i j : Fin n) (c : 𝕜) : Matrix (Fin n) (Fin m) α :=
    updateRow M i <| (M i) + c • (M j)

#eval add_row_multiple !![0,0;1,1] 0 1 2

-- def gaussian_update [Add α] [Mul α] [Sub α] [Neg α] (hm : 0 < m)
--     (i j : Fin n) : Matrix (Fin n) (Fin m) α :=
--     -- updateRow M i <| (M j ⟨0, sorry⟩) • (M i) - (M i ⟨0,sorry⟩) • (M j)
--     add_row_multiple (scale_row M i (M j ⟨0, hm⟩)) i j (-M i ⟨0, hm⟩)
def gaussian_update [Add α] [Mul α] [Sub α] [Neg α][NeZero n] [NeZero m]
  (a b : α) (k : Fin n) : (Fin m) → α := if k = 0 then M k else a • M k - b • M 0

def gaussian_update_row [Add α] [Mul α] [Sub α] [Neg α][NeZero n] [NeZero m]:
  Matrix (Fin n) (Fin m) α :=
  -- gaussian_update (M 0 0) (M k 0)
  fun k => gaussian_update M (M 0 0) (M k 0) k
  -- if k = 0 then M k else (M 0 0) • M k - (M k 0) • M 0

def gaussian_update_scale_row [Add α] [Mul α] [Sub α] [Neg α][NeZero n] [NeZero m]
  (a : α) (k : Fin n) : (Fin m) → α := if k = 0 then M k else a • M k

def gaussian_update_scale [Add α] [Mul α] [Sub α] [Neg α][NeZero n] [NeZero m] :
  Matrix (Fin n) (Fin m) α :=
  fun k => gaussian_update_scale_row M ((M 0 0) * (M 0 0)) k

def A := !![2,1,3;1,2,8;9,10,11]
#eval gaussian_update_row !![2,1,3;1,2,8;9,10,11]
#eval gaussian_update_scale !![2,1,3;1,2,8;9,10,11] 2
end Basic

-- structure Gaussian (n m α)  where
--   P : Matrix n n α
--   R : Matrix n m α
--   Q : Matrix m m α
structure Gaussian (n m α) [Ring α] where
  P : Matrix (Fin n) (Fin n) α
  R : Matrix (Fin n) (Fin m) α
  Q : Matrix (Fin m) (Fin m) α
  M : Matrix (Fin n) (Fin m) α
  hm : P * R * Q = M
-- M = P * [I_r,0;0,0] * Q
section Gauss


variable {n m} [Ring α] (M : Gaussian n m α) [NeZero n] [NeZero m]

omit [NeZero n] in
def find_pivot_row [LinearOrder α] (M : Fin n → α) : Fin n :=
  (List.argmax (abs ∘ M) (List.ofFn (id : Fin n → Fin n))).getD 0
  -- (List.ofFn (abs ∘ M))

#eval find_pivot_row (fun (i : Fin 4) =>(if i = 0 then -4 else 5 : ℤ) )
-- + (2 : Fin 4)
-- def gauss_elim_i (hn : 0 < n) (hm : 0 < m) (hM : M.R ⟨0,hn⟩ ⟨0,hm⟩ ≠ 0) (i: Fin n):
--     Gaussian n m α :=
--     let s := M.M ⟨0,hn⟩ ⟨0, hm⟩
--     let z : Fin n := ⟨0,hn⟩
--     {
--   P := fun k => if i = 0 then M.P z else s  • M.P i - s • M.P z
--   R := gaussian_update M.R hm i ⟨0, hn⟩
--   Q := M.Q
--   M :=
--      fun k => if i = 0 then M.M 0 else s • M.M i

--   hm := sorry
--     }


    -- updateRow M i <| (M j ⟨0, sorry⟩) • (M i) - (M i ⟨0,sorry⟩) • (M j)
    -- add_row_multiple (scale_row M i (M j ⟨0, hm⟩)) i j (-M i ⟨0, hm⟩)

def gaussian_elimination_step_row (i : Fin n) (hi : i < m) (hM : M.R i ⟨i, hi⟩ ≠ 0)
    : Gaussian n m α where
  P := fun k => gaussian_update M.P (M.R i ⟨i, hi⟩) (M.R i ⟨i, hi⟩) k
  R := gaussian_update_row M.R
  -- gaussian_update M.R hm i ⟨0, hn⟩
  Q := M.Q
  M := gaussian_update_scale M.M
  -- fun k => gaussian_update_scale M.M ((M.M 0 0) * (M.M 0 0)) k
  -- scale_row M.M i ((M.M ⟨0,hn⟩ ⟨0, hm⟩) * (M.M ⟨0,hn⟩ ⟨0, hm⟩))
  hm := sorry
  -- }
#check LinearOrder
#check abs
-- Fin m
#check List.maximum
#check FinEnum.toList
#check Fin.repeat
#check List.ofFn
#check AkraBazziRecurrence.max_bi
#check List.argmax_eq_some_iff
-- #check Fin.toList




  -- letI : FinEnum (Fin n → α) := by infer_instance
  -- #check List.maximum M
-- pivot_row
#check find_pivot_row
def gaussian_elimination_pivot_row [LinearOrder α] (i : Fin n) (hi : i < m) :
    Gaussian n m α :=
  let j := (find_pivot_row (fun k => M.R k ⟨i, hi⟩))
  {
  P := swap_rows M.P j i
  R := swap_rows M.R j i
  Q := M.Q
  M := M.M
  hm := sorry
  }

-- 依次应用函数 f_start, f_{start+1}, ..., f_{end-1} 到 A
-- def apply_functions_indexed_rec (start_idx end_idx : ℕ) : α :=
--   if start_idx < end_idx then
--     let next_A := f start_idx A -- 应用当前索引对应的函数
--     -- apply_functions_indexed_rec next_A (start_idx + 1) end_idx -- 递归调用处理下一个索引
--     sorry
--   else
    -- A -- 达到终止条件，返回最终结果
-- termination_by _ => end_idx - start_idx -- 终止性证明：区间长度递减
-- decreasing_by simp_wf ; omega
#check List.range
#check InnerProductSpace.gramSchmidt
#eval (0 - 1 : Fin 2)
-- def gaussian_elimination_row [LinearOrder α] (hnm : n ≤ m) (idx : ℕ) : Gaussian n m α :=
--     if idx = 0 then M
--     else if h : idx < n then
--       let idxn := ⟨idx, h⟩
--       let pivotA := gaussian_elimination_pivot_row M idxn (lt_of_lt_of_le h hnm)
--       -- if M.R idxn idxn = 0 then
--       --   let nextA := gaussian_elimination_pivot_row M idxn (lt_of_lt_of_le h hnm)

--       -- else
--       let nextA : Gaussian n m α :=
--         gaussian_elimination_step_row pivotA idxn (Nat.lt_of_lt_of_le h hnm) sorry
--       gaussian_elimination_row hnm (idx + 1)
--     else M
-- termination_by idx = n
-- decreasing_by sorry
def gaussian_elimination_row_aux [LinearOrder α] (M : Gaussian n m α) (hnm : n ≤ m) (idx : ℕ) (hidx : idx < n) :
    Gaussian n m α :=
  have hi := lt_of_lt_of_le hidx hnm
  let idxn : Fin n := ⟨idx, hidx⟩
  let pivotA := gaussian_elimination_pivot_row M idxn hi
  let nextA := if h : pivotA.R idxn ⟨idx, hi⟩ = 0 then pivotA
    else gaussian_elimination_step_row pivotA idxn hi h
  if ht : idx < n - 1 then
    gaussian_elimination_row_aux nextA hnm (idx + 1) (Nat.add_lt_of_lt_sub ht)
  else
    nextA
termination_by n - idx
decreasing_by
  rw [tsub_lt_tsub_iff_left_of_le]
  simp
  linarith

def gaussian_elimination_row [LinearOrder α] (hnm : n ≤ m) : Gaussian n m α :=
  -- let rec go (idx : ℕ) (hidx : idx < n) (A : Gaussian n m α) : Gaussian n m α :=
  --   have hi := lt_of_lt_of_le hidx hnm
  --   let idxn : Fin n := ⟨idx, hidx⟩
  --   let pivotA := gaussian_elimination_pivot_row A idxn hi
  --   let nextA := if h : pivotA.R idxn ⟨idx, hi⟩ = 0 then pivotA
  --     else gaussian_elimination_step_row pivotA idxn hi h
  --   if ht : idx < n - 1 then
  --     go (idx + 1) (Nat.add_lt_of_lt_sub ht) nextA
  --   else
  --     nextA
  -- termination_by n - idx
  -- decreasing_by
  --   rw [tsub_lt_tsub_iff_left_of_le]
  --   simp
  --   linarith

  if h : 0 < n then
    gaussian_elimination_row_aux M hnm 0 h
  else
    M
-- termination_by n - idx.val -- 终止性证明：剩余未处理的元素数量递减
-- decreasing_by simp
-- decreasing_by simp_wf ; omega
  -- for i in List.range n do
  -- sorry
  -- match n with
  -- | 0 => M
  -- | 1 => M
  -- | k + 1 => if (hM : M.R i ⟨i, hi⟩ ≠ 0)

-- def gaussian_elimination :

end Gauss
