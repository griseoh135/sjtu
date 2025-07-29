import Mathlib

variable {α : Type*}

open Matrix Equiv Nat List

section Basic

variable {n m} (M : Matrix (Fin n) (Fin m) α)

def swap_rows  (i j : Fin n) : Matrix (Fin n) (Fin m) α :=
    M.submatrix (swap i j : Perm (Fin n)) id

def swap_cols  (i j : Fin m) : Matrix (Fin n) (Fin m) α :=
   (swap_rows M.transpose i j).transpose

def gaussian_update [Add α] [Mul α] [Sub α]
    (i k : Fin n) (a b : α) : (Fin m) → α :=
  if k ≤ i then M k else a • M k - b • M i

def gaussian_update_row [Add α] [Mul α] [Sub α]
  (i : Fin n) (j : Fin m):
  Matrix (Fin n) (Fin m) α :=
  fun k => gaussian_update M i k (M i j) (M k j)

end Basic

structure Gaussian (n m α) [Ring α] where
  P : Matrix (Fin n) (Fin n) α
  R : Matrix (Fin n) (Fin m) α
  Q : Matrix (Fin m) (Fin m) α
  M : Matrix (Fin n) (Fin m) α
  hm : P * M * Q = R
  -- P M Q = [I_r, 0;
            -- 0, 0]
namespace Gaussian

variable {n m : ℕ}

def transpose [CommRing α] (M : Gaussian n m α) : Gaussian m n α where
  P := M.Q.transpose
  R := M.R.transpose
  Q := M.P.transpose
  M := M.M.transpose
  hm := by
    rw [← M.hm, transpose_mul (M.P * M.M) M.Q, transpose_mul]
    apply Matrix.mul_assoc

variable [Ring α]

instance  : SMul (Matrix (Fin n) (Fin n) α) (Gaussian n m α) where
  smul := fun P B => (⟨P * B.P, P * B.R, B.Q, B.M, by simp [B.hm, Matrix.mul_assoc];⟩ : Gaussian n m α)

instance : SMul (Matrix (Fin m) (Fin m) α) (Gaussian n m α) where
  smul := fun Q B => (⟨B.P, B.R * Q, B.Q * Q, B.M, by rw [← B.hm]; simp [Matrix.mul_assoc];⟩ : Gaussian n m α)

/-- Unfolds smul to its def -/
lemma smul_def_right (B : Gaussian n m α) (Q : Matrix (Fin m) (Fin m) α):
  Q • B = (⟨B.P, B.R * Q, B.Q * Q, B.M, by rw [← B.hm]; simp [Matrix.mul_assoc];⟩ : Gaussian n m α)
  := rfl

/-- `(Q * P) • M = P • (Q • M)` -/
lemma mul_smul_right (M : Gaussian n m α)
  (P : Matrix (Fin m) (Fin m) α) (Q : Matrix (Fin m) (Fin m) α) : (Q * P) • M = P • (Q • M) := by
  rcases M with ⟨ MP, MR, MQ, MM, Mhm ⟩
  simp [smul_def_right, Matrix.mul_assoc]

/-- Unfolds smul to its def-/
lemma smul_def_left (P : Matrix (Fin n) (Fin n) α) (B : Gaussian n m α) :
  P • B = (⟨P * B.P, P * B.R, B.Q, B.M, by rw [← B.hm]; simp [Matrix.mul_assoc];⟩ : Gaussian n m α)
  := rfl

/-- `(P * Q) • M = P • (Q • M)` -/
lemma mul_smul_left (M: Gaussian n m α)
  (P : Matrix (Fin n) (Fin n) α) (Q : Matrix (Fin n) (Fin n) α) : (P * Q) • M = P • (Q • M) := by
  rcases M with ⟨ MP, MR, MQ, MM, Mhm ⟩
  simp [smul_def_left, Matrix.mul_assoc]

@[simp] lemma smul_eq_right (M : Gaussian n m α):
  (1 : Matrix (Fin m) (Fin m) α) • M = M := by
  rcases M with ⟨ MP, MR, MQ, MM, Mhm ⟩
  simp [smul_def_right]

@[simp] lemma smul_eq_left (M : Gaussian n m α):
  (1 : Matrix (Fin n) (Fin n) α) • M = M := by
  rcases M with ⟨ MP, MR, MQ, MM, Mhm ⟩
  simp [smul_def_left]

end Gaussian

section Gauss

section

def firstNonZeroIndex {m} [DecidableEq α] [Zero α] (u : Fin m → α) (i : Fin m):
    Option (Fin m) :=
  ((finRange m).rtake (m - i)) |>.find? (fun i => u i ≠ 0)

end

def find_pivot_col {n} [Lattice α][AddGroup α][DecidableLT α][NeZero n] (M : Fin n → α) (i : Fin n): Fin n :=
  (argmax (abs ∘ M) ((finRange n).rtake (n - i))).getD 0

variable {n m : ℕ}  [NeZero n] [NeZero m]

-- 目前进行到(i,j)，接下来选取按行来消元
def Gaussian.gaussian_elimination_step_row [CommRing α] (M : Gaussian n m α) (i : Fin n) (j : Fin m)
    : Gaussian n m α where
  P := fun k => gaussian_update M.P i k (M.R i j) (M.R k j)
  R := gaussian_update_row M.R i j
  Q := M.Q
  M := M.M
  hm := by
    funext k
    simp only [gaussian_update, gaussian_update_row, Matrix.mul_apply_eq_vecMul,
      Matrix.vecMul_vecMul, ← M.hm]
    split_ifs with h_le
    simp
    simp [sub_vecMul, Matrix.vecMul_smul, Matrix.vecMul_smul]

/-
`gaussian_elimination_step_row` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
omit [NeZero n] [NeZero m] in
lemma Gaussian.gaussian_elimination_step_row_eq_left_mul [Field α] (M : Gaussian n m α) (i : Fin n) (j : Fin m) (MR_ij_nonzero : M.R i j ≠ 0):
    ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_step_row i j := by
  let P₁ := M.P
  let R₁ := M.R
  let P₂ := (M.gaussian_elimination_step_row i j).P
  let R₂ := (M.gaussian_elimination_step_row i j).R
  let E : Matrix (Fin n) (Fin n) α := fun k => gaussian_update (1 : Matrix (Fin n) (Fin n) α) i k (M.R i j) (M.R k j)
  let E_inv : Matrix (Fin n) (Fin n) α := fun k => gaussian_update (1 : Matrix (Fin n) (Fin n) α) i k (-M.R i j) (M.R k j)

  have h₀ : E * P₁ = P₂ := by
    ext k l
    simp only [E, gaussian_update, mul_apply, ite_apply]
    split_ifs with hk
    · simp [Matrix.one_apply]
      simp [P₁, P₂, Gaussian.gaussian_elimination_step_row, gaussian_update]
      split_ifs
      rfl
    · simp [Pi.sub_apply, Pi.smul_apply, Matrix.one_apply, mul_comm]
      have : ∑ x, P₁ x l * ((if k = x then M.R i j else 0) - if i = x then M.R k j else 0)
        = ∑ x, ((if k = x then P₁ x l * (M.R i j) else 0) - (if i = x then P₁ x l * M.R k j else 0))  := by
        congr; ext z; split_ifs <;> ring
      rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
      simp
      simp [P₁, P₂, Gaussian.gaussian_elimination_step_row, gaussian_update]
      split_ifs
      simp [Pi.sub_apply, mul_comm]

  have h₁ : E * R₁ = R₂ := by
    have h1 : P₁ * M.M * M.Q = R₁ := M.hm
    have h2 : P₂ * (M.gaussian_elimination_step_row i j).M * (M.gaussian_elimination_step_row i j).Q = R₂ := (M.gaussian_elimination_step_row i j).hm
    have : (M.gaussian_elimination_step_row i j).M = M.M := by rfl
    rw [this] at h2
    have : (M.gaussian_elimination_step_row i j).Q = M.Q := by rfl
    rw [this, ← h₀, Matrix.mul_assoc E, Matrix.mul_assoc E (P₁ * M.M) M.Q, h1] at h2
    exact h2

  have E_diagonal_nonzero : ∀ i, E i i ≠ 0 := by
    intro j
    simp [E, gaussian_update]
    split_ifs with h_le
    simp
    have : i ≠ j := by exact Ne.symm (ne_of_not_le h_le)
    simp [this, MR_ij_nonzero]

  have E_lowertrangular : E.BlockTriangular ⇑OrderDual.toDual := by
    simp [E, BlockTriangular]
    intro k l k_lt_l
    simp [gaussian_update]
    have k_neq_l : k ≠ l := by exact Fin.ne_of_lt k_lt_l
    split_ifs with h
    exact one_apply_ne' (id (Ne.symm k_neq_l))
    simp; simp at h
    have : i < l := by exact lt_trans h k_lt_l
    have i_neq_l : i ≠ l := by exact Fin.ne_of_lt this
    simp [k_neq_l, i_neq_l]

  have E_det_nonzero : E.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular]
    exact Finset.prod_ne_zero_iff.mpr fun a a_1 => E_diagonal_nonzero a
    apply E_lowertrangular

  have E_invertible : IsUnit E.det := by exact Ne.isUnit E_det_nonzero

  let P : GL (Fin n) α := E.nonsingInvUnit E_invertible
  use P
  simp [P, nonsingInvUnit, SMul.smul, HSMul.hSMul, gaussian_elimination_step_row]
  constructor
  · rw [h₀]; rfl
  · rw [h₁]; rfl

-- 目前进行到(i,j)，接下来选取列主元
def Gaussian.gaussian_elimination_pivot_row [Lattice α] [DecidableLT α] [CommRing α]
    (M : Gaussian n m α)  (i : Fin n) (j : Fin m) :
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
    hm := by
      funext k
      simp only [←M.hm]
      rfl
    }

/-
`gaussian_elimination_pivot_row` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
omit [NeZero m] in
lemma Gaussian.gaussian_elimination_pivot_row_eq_left_mul [Lattice α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)  (i : Fin n) (j : Fin m) :
    ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_pivot_row i j := by
  let P₁ := M.P
  let R₁ := M.R
  let P₂ := (M.gaussian_elimination_pivot_row i j).P
  let R₂ := (M.gaussian_elimination_pivot_row i j).R
  let z := (find_pivot_col (fun k => M.R k j) i)
  have hz : z = find_pivot_col (fun k => M.R k j) i := by rfl
  let E : Matrix (Fin n) (Fin n) α := swap_rows (1 : Matrix (Fin n) (Fin n) α) z i
  have hE : E = swap_rows (1 : Matrix (Fin n) (Fin n) α) z i := by rfl

  have swap_self : swap_rows (1 : Matrix (Fin n) (Fin n) α) i i = 1 := by
    ext k l
    simp [swap_rows]
    exact rfl

  have h₀ : E * P₁ = P₂ := by
    simp [P₁, P₂, gaussian_elimination_pivot_row, E]
    split_ifs with h
    · simp [z]; rw [h]
      rw [swap_self]
      exact Matrix.one_mul M.P

    · simp [swap_rows, submatrix, one_apply, Equiv.swap, swapCore]; rw [← hz]
      funext k l
      simp
      split_ifs with h' h''
      · simp [Matrix.mul_apply]; simp [h']
      · simp [Matrix.mul_apply]; simp [h'']; split_ifs with h'''; simp [h''']; rfl
      · simp [Matrix.mul_apply]; simp [h', h'']

  have h₁ : E * R₁ = R₂ := by
    have h1 : P₁ * M.M * M.Q = R₁ := M.hm
    have h2 : P₂ * (M.gaussian_elimination_pivot_row i j).M * (M.gaussian_elimination_pivot_row i j).Q = R₂ := (M.gaussian_elimination_pivot_row i j).hm
    have : (M.gaussian_elimination_pivot_row i j).M = M.M := by
      simp [gaussian_elimination_pivot_row]
      split_ifs; rfl; rfl
    rw [this] at h2
    have : (M.gaussian_elimination_pivot_row i j).Q = M.Q := by
      simp [gaussian_elimination_pivot_row]
      split_ifs; rfl; rfl
    rw [this, ← h₀, Matrix.mul_assoc E, Matrix.mul_assoc E (P₁ * M.M) M.Q, h1] at h2
    exact h2

  have : E * E = 1 := by simp [E, swap_rows]
  let P : GL (Fin n) α := ⟨E, E, this, this⟩
  use P
  simp [P, gaussian_elimination_pivot_row, E]
  split_ifs with h
  simp [z]; rw [h]; rw [swap_self]; simp; simp [SMul.smul, HSMul.hSMul]
  constructor
  rw [← hE, h₀]; simp [P₂, gaussian_elimination_pivot_row]; split_ifs; rfl;
  rw [← hE, h₁]; simp [R₂, gaussian_elimination_pivot_row]; split_ifs; rfl;

def Gaussian.gaussian_elimination_row_aux [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    Gaussian n m α :=

  let rown : Fin n := ⟨row, hr⟩
  let colm : Fin m := ⟨col, hc⟩

  let pivotA := Gaussian.gaussian_elimination_pivot_row M rown colm
  if ht : (row < n - 1) ∧ (col < m - 1) then
    if pivotA.R rown colm = 0 then
      gaussian_elimination_row_aux M row hr (col + 1) (add_lt_of_lt_sub ht.2)

    else
      let nextA := Gaussian.gaussian_elimination_step_row pivotA rown colm
      gaussian_elimination_row_aux nextA (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2)
  else
    pivotA

-- lemma aa : n > 0 := by exact pos_of_neZero n

/-
`gaussian_elimination_pivot_row` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
omit [NeZero m] in
lemma Gaussian.gaussian_elimination_step_pivot_row_eq_left_mul [Lattice α] [DecidableLT α] [Field α] (M : Gaussian n m α) (i : Fin n) (j : Fin m) (pivot_nonzero : (M.gaussian_elimination_pivot_row i j).R i j ≠ 0):
    ∃ (P : GL (Fin n) α), P.1 • M = (M.gaussian_elimination_pivot_row i j).gaussian_elimination_step_row i j := by
  rcases (Gaussian.gaussian_elimination_pivot_row_eq_left_mul M i j) with ⟨E₁, h₀⟩
  rcases (Gaussian.gaussian_elimination_step_row_eq_left_mul (M.gaussian_elimination_pivot_row i j) i j pivot_nonzero) with ⟨E₂, h₁⟩
  use (E₂ * E₁); simp; rw [Gaussian.mul_smul_left, h₀, h₁]

-- lemma gaussian_elimination_row_aux_step_pivot [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)
--     (row : ℕ) (col : ℕ) (ht : (row < n - 1) ∧ (col < m - 1)) :
--   let rown : Fin n := ⟨row, lt_of_lt_pred ht.1⟩
--   let colm : Fin m := ⟨col, lt_of_lt_pred ht.2⟩
--   M.gaussian_elimination_row_aux row rown.2 col colm.2 =
--   ((M.gaussian_elimination_pivot_row rown colm).gaussian_elimination_step_row rown colm).gaussian_elimination_row_aux
--         (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2) := sorry

-- lemma gaussian_elimination_row_aux_step_not_pivot [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)
--     (row : ℕ) (col : ℕ) (ht : (row < n - 1) ∧ (col < m - 1))
--     (hp : (M.gaussian_elimination_pivot_row ⟨row, lt_of_lt_pred ht.1⟩ ⟨col, lt_of_lt_pred ht.2⟩).R ⟨row, lt_of_lt_pred ht.1⟩ ⟨col, lt_of_lt_pred ht.2⟩ = 0) :
--   let rown : Fin n := ⟨row, lt_of_lt_pred ht.1⟩
--   let colm : Fin m := ⟨col, lt_of_lt_pred ht.2⟩
--   M.gaussian_elimination_row_aux row rown.2 col colm.2 =
--         (M.gaussian_elimination_step_row rown colm).gaussian_elimination_row_aux
--         row rown.2 (col + 1) (add_lt_of_lt_sub ht.2) := sorry

/-
`gaussian_elimination_row_aux` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
omit [NeZero m] in
lemma Gaussian.gaussian_elimination_row_aux_eq_left_mul [Lattice α] [DecidableEq α] [DecidableLT α] [Field α] (M : Gaussian n m α)  (i : Fin n) (j : Fin m) :
    ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_row_aux i.1 i.2 j.1 j.2 := by
  set row := i.1
  set col := j.1
  have hi : row < n := i.2
  have hj : col < m := j.2
  -- 使用强归纳法，k 代表 (n - row) + (m - col)
  have h : ∀ (k : ℕ), ∀ (row col : ℕ) (hr : row < n) (hc : col < m),
      k = (n - row) + (m - col) →
      ∀ (M : Gaussian n m α), ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_row_aux row hr col hc := by
    intro k
    induction' k using Nat.strong_induction_on with k IH
    intro row col hr hc hk M

    unfold gaussian_elimination_row_aux
    split_ifs with h
    · -- 递归情况
      simp
      split_ifs with h0
      · -- 主元为零的情况
        let col' := col + 1
        have hc' : col' < m := by
          omega  -- 利用 h: col < m - 1
        have hk' : (n - row) + (m - col') < k := by
          have : (n - row) + (m - col') < (n - row) + (m - col) := by
            have : m - col' < m - col := by
              apply Nat.sub_lt_sub_left
              · linarith
              · simp [col']
            linarith
          linarith [hk]
        have IH_rec := IH ((n - row) + (m - col')) hk' row col' hr hc' (by simp [col']) M
        exact IH_rec
      · -- 主元非零的情况
        rw [← ne_eq] at h0
        let pivotA := M.gaussian_elimination_pivot_row ⟨row, hr⟩ ⟨col, hc⟩
        obtain ⟨P_pivot, h_pivot⟩ := Gaussian.gaussian_elimination_pivot_row_eq_left_mul M ⟨row, hr⟩ ⟨col, hc⟩
        let nextA := pivotA.gaussian_elimination_step_row ⟨row, hr⟩ ⟨col, hc⟩
        obtain ⟨P_step, h_step⟩ := pivotA.gaussian_elimination_step_row_eq_left_mul ⟨row, hr⟩ ⟨col, hc⟩ h0
        let row' := row + 1
        let col' := col + 1
        have hr' : row' < n := by
          omega  -- 利用 h: row < n - 1
        have hc' : col' < m := by
          omega  -- 利用 h: col < m - 1
        have hk' : (n - row') + (m - col') < k := by
          have : (n - row') + (m - col') < (n - row) + (m - col) := by
            have h1 : n - row' < n - row := by
              apply Nat.sub_lt_sub_left
              · linarith
              · simp [row']
            have h2 : m - col' < m - col := by
              apply Nat.sub_lt_sub_left
              · linarith
              · simp [col']
            linarith
          linarith [hk]
        have IH_rec := IH ((n - row') + (m - col')) hk' row' col' hr' hc' rfl nextA
        simp at IH_rec
        obtain ⟨P_rec, h_rec⟩ := IH_rec
        use P_rec * P_step * P_pivot
        rw [GeneralLinearGroup.coe_mul, Gaussian.mul_smul_left, h_pivot,GeneralLinearGroup.coe_mul,
            Gaussian.mul_smul_left, h_step, h_rec]
    · -- 基本情况：到达边界
      obtain ⟨P_pivot, h_pivot⟩ := Gaussian.gaussian_elimination_pivot_row_eq_left_mul M ⟨row, hr⟩ ⟨col, hc⟩
      use P_pivot
  -- 应用我们的辅助引理
  exact h ((n - row) + (m - col)) row col hi hj (by rfl) M




def Gaussian.gaussian_elimination_row [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)  : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then gaussian_elimination_row_aux M 0 h.1 0 h.2
  else M

def gaussian_elimination_col_aux [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)
    (row : ℕ) (hr : row < n) (col : ℕ) (hc : col < m) :
    Gaussian n m α :=

  let rown : Fin n := ⟨row, hr⟩
  let colm : Fin m := ⟨col, hc⟩

  if ht : (row < n - 1) ∧ (col < m - 1) then
    if M.R rown colm = 0 then gaussian_elimination_col_aux M (row + 1) (add_lt_of_lt_sub ht.1) col hc
    else
      let nextA := Gaussian.gaussian_elimination_step_row M rown colm
      gaussian_elimination_col_aux nextA (row + 1) (add_lt_of_lt_sub ht.1) (col + 1) (add_lt_of_lt_sub ht.2)
  else
    M


def Gaussian.gaussian_elimination_col [Lattice α] [DecidableEq α] [DecidableLT α]  [CommRing α] (M : Gaussian n m α)  : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then (gaussian_elimination_col_aux M.transpose 0 h.2 0 h.1).transpose
  else M

def findNonZeroIndex [DecidableEq α] [Zero α] (u : Matrix (Fin n) (Fin m) α) (i : Fin n) (j : Fin m) :
    Fin m := (firstNonZeroIndex (u i) j).getD j

def Gaussian.gaussian_elimination_step_final [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α]
    (M : Gaussian n m α) (i : Fin n) (j : Fin m) : Gaussian n m α :=
  -- 取出第j列，从第i行开始的不为0的下标
  let z := findNonZeroIndex M.R i j
  -- 如果下标和本身一样，。。。
  if z = j then M
  else
    {
      P := M.P
      R := swap_cols M.R z j
      Q := swap_cols M.Q z j
      M := M.M
      hm := by
        funext k
        simp only [←M.hm]
        rfl
    }

/--
`gaussian_elimination_step_final` 的整体效果等价于
在原矩阵右侧乘以某个可逆矩阵
-/
lemma Gaussian.gaussian_elimination_step_final_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α]
    [CommRing α] (M : Gaussian n m α) (i : Fin n) (j : Fin m) :
    ∃ (Q : GL (Fin m) α), Q.1 • M = M.gaussian_elimination_step_final i j := by
  -- 待补证明
  sorry

def gaussian_elimination_final_aux [Lattice α] [DecidableEq α] [DecidableLT α]
    [CommRing α] (M : Gaussian n m α) (idx : ℕ) (h : idx < n ∧ idx < m) :
    Gaussian n m α :=
  let nextM := M.gaussian_elimination_step_final ⟨idx, h.1⟩ ⟨idx, h.2⟩
  if ht : (idx < n - 1) ∧ (idx < m - 1) then
    gaussian_elimination_final_aux nextM (idx + 1) ⟨add_lt_of_lt_sub ht.1, add_lt_of_lt_sub ht.2⟩
  else
    nextM
termination_by min n m - idx

/-- Lemma for `gaussian_elimination_final_aux_eq_right_mul`.-/
lemma Gaussian._GEFA_pred_min_m_n_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α]
  [CommRing α] (M : Gaussian n m α) (h) :
  ∃ (Q : GL (Fin m) α), Q.1 • M = gaussian_elimination_final_aux M (m.min n -1) h := by
  unfold gaussian_elimination_final_aux
  have : m≠ 0 := NeZero.ne m
  have : n≠ 0 := NeZero.ne n
  simp
  split_ifs with hif
  · have ⟨ Q1, hQ1⟩ := gaussian_elimination_step_final_eq_right_mul M
      ⟨ m.min n -1, by omega⟩ ⟨m.min n -1, by omega⟩
    rw [← hQ1]
    have: m.min n-1+1 = m.min n := by
      have: m.min n ≠ 0:= by intro h;simp at h;cases h;contradiction;contradiction
      omega
    simp [this]
    simp at hif
    have := (min_eq_iff (a:=m) (b:=n) (c:=m.min n)).1 rfl;
    cases this
    · omega
    · omega
  · exact
    gaussian_elimination_step_final_eq_right_mul M
      ⟨m.min n - 1, gaussian_elimination_final_aux._proof_1 (m.min n - 1) h⟩
      ⟨m.min n - 1, gaussian_elimination_final_aux._proof_2 (m.min n - 1) h⟩

/-- Lemma for `gaussian_elimination_final_aux_eq_right_mul`.-/
lemma Gaussian._GEFA_eq_right_mul_of_GEFA_succ_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (idx h₁ h₂) :
  (∀ M:Gaussian n m α, ∃ (Q : GL (Fin m) α), Q.1 • M = gaussian_elimination_final_aux M (idx+1) h₁)
  →
  ∀ M:Gaussian n m α, ∃ (Q : GL (Fin m) α), Q.1 • M = gaussian_elimination_final_aux M (idx) h₂
  := by
  intro h M
  unfold gaussian_elimination_final_aux
  simp
  split_ifs with ht
  · let ⟨Q2, hQ2⟩ :=
      Gaussian.gaussian_elimination_step_final_eq_right_mul M ⟨idx, h₂.1⟩ ⟨idx, h₂.2⟩
    rw [← hQ2]
    specialize h (Q2.1 • M)
    obtain ⟨ Q1, hQ1⟩ := h
    use Q2 * Q1
    rw [← hQ1]
    simp [Gaussian.mul_smul_right]
  · simp at ht
    omega

/--
`gaussian_elimination_final_aux` 的整体效果等价于
在原矩阵右侧乘以某个可逆矩阵
-/
lemma Gaussian.gaussian_elimination_final_aux_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)  (idx h) :
    ∃ (Q : GL (Fin m) α), Q.1 • M = gaussian_elimination_final_aux M idx h := by
  have := NeZero.ne m; have := NeZero.ne n
  by_cases h1 : idx = m.min n -1
  · simp [h1]
    apply Gaussian._GEFA_pred_min_m_n_eq_right_mul
  · by_cases h2 : idx > m.min n -1
    · simp at h2;
      have hh:m.min n ≤ idx := by omega
      simp at hh
      omega
    · have h2: idx < m.min n - 1:= by omega --now idx < m.min n - 1
      unfold gaussian_elimination_final_aux
      simp
      split_ifs with h3
      · have ⟨ Q1, hQ1⟩ :=
          Gaussian.gaussian_elimination_step_final_eq_right_mul M ⟨ idx, h.1⟩ ⟨ idx, h.2⟩
        rw [← hQ1]
        have ⟨ Q2, hQ2⟩ :=
          Gaussian.gaussian_elimination_final_aux_eq_right_mul (M:=Q1.1 • M) (idx+1) (by omega)
        rw [← hQ2]
        use Q1 * Q2
        simp [mul_smul_right]
      · exact
        gaussian_elimination_step_final_eq_right_mul M
          ⟨idx, gaussian_elimination_final_aux._proof_1 idx h⟩
          ⟨idx, gaussian_elimination_final_aux._proof_2 idx h⟩

def Gaussian.gaussian_elimination_final [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)  : Gaussian n m α :=
  if h : 0 < n ∧ 0 < m then gaussian_elimination_final_aux M 0 h
  else M

/--
`gaussian_elimination_final` 的整体效果等价于
在原矩阵右侧乘以某个可逆矩阵
-/
lemma Gaussian.gaussian_elimination_final_eq_right_mul [Lattice α] [DecidableEq α] [DecidableLT α][ CommRing α] (M : Gaussian n m α)  :
  ∃ (Q : GL (Fin m) α), Q.1 • M = gaussian_elimination_final M := by
  unfold Gaussian.gaussian_elimination_final
  split_ifs with h
  · exact Gaussian.gaussian_elimination_final_aux_eq_right_mul M 0 (by omega)
  · use (1 : GL (Fin m) α); simp

def Gaussian.gaussian_elimination [Lattice α] [DecidableEq α] [DecidableLT α] [CommRing α] (M : Gaussian n m α)  : Gaussian n m α :=
  M.gaussian_elimination_row.gaussian_elimination_col.gaussian_elimination_final

def Gaussian.init [Ring α] (A : Matrix (Fin n) (Fin m) α) : Gaussian n m α :=
    ⟨1, A, 1, A, by simp⟩

-- #check Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec
-- #eval!
--   (Gaussian.init !![1, 2, (3 : ℤ), 4 ;
--                     1, 2, (5 : ℤ), 6 ;
--                     1, 2, (7 : ℤ), 8 ]).gaussian_elimination
-- #eval !![1, 0, 0; -1, 0, 1; -2, 4, -2] * !![1, 2, 3, (4 : ℤ); 1, 2, 5, 6; 1, 2, 7, 8] * !![1, -3, -2, -4; 0, 0, 1, 0; 0, 1, 0, -4; 0, 0, 0, 4]
def rankStdBlock (K : Type*) [Zero K] [One K]
    (m n r : ℕ) : Matrix (Fin m) (Fin n) K :=
  fun i j => if (i : ℕ) < r ∧ (j : ℕ) < r then
            if (i : ℕ) = j then 1 else 0
          else 0

end Gauss

section

variable {m n : ℕ }
variable [NeZero m] [DecidableEq α] [Zero α] (M : Matrix (Fin n) (Fin m) α)

def Matrix.NonZeroIndex := fun i ↦ firstNonZeroIndex (M i) 0

structure Matrix.IsRowEchelon : Prop where
  row_structure :
    ∀ i,
      (match M.NonZeroIndex i with
        | none   => ∀ k, M i k = 0
        | some c => ∀ k, k < c → M i k = 0)
  pivot_right_move :
    ∀ {i j c₁ c₂}, i < j →
      M.NonZeroIndex i = some c₁ → M.NonZeroIndex j = some c₂ → c₁ < c₂

#check  (Matrix.IsRowEchelon !![1,0;0,1])
structure Matrix.IsReducedRowEchelon extends Matrix.IsRowEchelon M where
  pivot_column_zero :
    ∀ {i j c}, M.NonZeroIndex i = some c → i ≠ j → M j c = 0

end

section Lemmas

variable  {α : Type*} {n m : ℕ} [Field α] (M : Gaussian n m α) [NeZero n] [NeZero m]
  [Lattice α] [DecidableEq α] [DecidableLT α]

/-- ① `gaussian_elimination_row` 产出的 `R` 为行阶梯形矩阵 -/
lemma gaussian_elimination_row_is_row_echelon :
    M.gaussian_elimination_row.R.IsRowEchelon := by
  -- 待补证明
  sorry

/--
② `gaussian_elimination_row` 的整体效果等价于
在原矩阵左侧乘以某个可逆矩阵
-/
lemma Gaussian.gaussian_elimination_row_eq_left_mul:
    ∃ (P : GL (Fin n) α), P.1 • M = M.gaussian_elimination_row := by
  -- 待补证明
  sorry

/--
`gaussian_elimination_col` preserves row‑echelon structure:

若 `M.R` 已满足 `IsRowEchelon`,  则消除列主元得到的 `(gaussian_elimination_col M).R` 仍然行阶梯形。
-/
lemma gaussian_elimination_col_preserves_row_echelon
    (hM : M.R.IsRowEchelon) : M.gaussian_elimination_col.R.IsRowEchelon := by sorry


/-- `gaussian_elimination_row` + `gaussian_elimination_col` 产出的 `R` 为简化行阶梯形矩阵 -/
lemma gaussian_elimination_row_col_is_row_reduced_echelon :
    M.gaussian_elimination_row.gaussian_elimination_col.R.IsReducedRowEchelon := by
  -- 待补证明
  sorry

-- /--
-- `gaussian_elimination_final` 保持行阶梯结构：
-- 若输入 `G.R` 是行阶梯形矩阵，则执行该函数后得到的 `R` 仍为行阶梯形。
-- -/
-- lemma gaussian_elimination_final_preserves_row_echelon
--     (hM : M.R.IsRowEchelon) : M.gaussian_elimination_final.R.IsRowEchelon := by
--   sorry

-- /--
-- `gaussian_elimination_final` 保持简化阶梯结构：
-- 若输入 `G.R` 是简化行阶梯形（RREF），则执行该函数后仍为 RREF。
-- -/
-- lemma gaussian_elimination_final_preserves_rref
--     (hM : M.R.IsReducedRowEchelon) : M.gaussian_elimination_final.R.IsReducedRowEchelon := by
--   sorry

end Lemmas



section Row

open Submodule Set
variable {K : Type*}
variable {m n : ℕ}

lemma left_mul_in_span [CommRing K] (P : GL (Fin m) K) (A : Matrix (Fin m) (Fin n) K) (i : Fin m) :
    (P.1 * A) i ∈ span K (Set.range A) := by
  show (fun k => dotProduct (P.1 i) (A · k)) ∈ _
  simp only [dotProduct]
  rw [mem_span_range_iff_exists_fun]
  use P.1 i
  ext k
  simp

theorem rowSpace_left_mul_invariant_mp [CommRing K] {x}
    (P : GL (Fin m) K) (A : Matrix (Fin m) (Fin n) K) :
     x ∈ span K (Set.range (P.1 * A)) → x ∈ span K (Set.range A) := by
  let P' := (P : Matrix (Fin m) (Fin m) K)
  let Q := P⁻¹
  intro hx
  rw [mem_span_set] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  refine sum_mem ?_
  intro c hc
  have hc_ne_zero : s c ≠ 0 := Finsupp.mem_support_iff.mp hc
  have hc_range : c ∈ Set.range (P' * A) := by
    apply hs
    exact Finsupp.mem_support_iff.mpr hc_ne_zero
  rw [Set.mem_range] at hc_range
  obtain ⟨i, rfl⟩ := hc_range
  show s ((P' * A) i) • (P' * A) i ∈ span K (range A)
  exact smul_mem _ _ (left_mul_in_span P A i)

theorem rowSpace_left_mul_invariant_mpr {x} [CommRing K]
    (P : GL (Fin m) K) (A : Matrix (Fin m) (Fin n) K) :
     x ∈ Submodule.span K (Set.range A) → x ∈ Submodule.span K (Set.range (P.1 * A)) := by
  let P' := (P : Matrix (Fin m) (Fin m) K)
  let Q := P⁻¹
  intro hx
  rw [mem_span_set] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  refine sum_mem ?_
  intro c hc
  have hc_ne_zero : s c ≠ 0 := Finsupp.mem_support_iff.mp hc
  have hc_range : c ∈ Set.range A := by
    apply hs
    exact Finsupp.mem_support_iff.mpr hc_ne_zero
  rw [Set.mem_range] at hc_range
  obtain ⟨i, rfl⟩ := hc_range
  show s (A i) • A i ∈ span K (range (P' * A))
  have h_row : A i = (Q.1 * (P' * A)) i := by
    rw [←Matrix.mul_assoc]
    unfold Q P'
    simp only [coe_units_inv, isUnits_det_units, nonsing_inv_mul, Matrix.one_mul]
  rw [h_row]
  exact smul_mem _ _ (left_mul_in_span Q (P' * A) i)


theorem rowSpace_left_mul_invariant [CommRing K]
    (P : GL (Fin m) K) (A : Matrix (Fin m) (Fin n) K) :
    span K (range (P.1 * A)) = span K (range A) := by
  let P' := (P : Matrix (Fin m) (Fin m) K)
  let Q := P⁻¹
  apply Submodule.ext
  intro x
  constructor
  · exact rowSpace_left_mul_invariant_mp P A
  · exact rowSpace_left_mul_invariant_mpr P A

theorem rowSpace_gauss_invariant [Field K] [NeZero n] [NeZero m] [Lattice K]
    [DecidableEq K] [DecidableLT K] (M : Gaussian n m K) :
    span K (range M.gaussian_elimination_row.R) = span K (range M.R) := by
  obtain ⟨P, hP⟩ := M.gaussian_elimination_row_eq_left_mul
  rw [← hP]
  have h : (P.1 • M).R = P.1 * M.R := by rfl
  rw [h, ← M.hm]
  exact rowSpace_left_mul_invariant _ _

end Row

section RankNormalForm


variable {m n : ℕ} [NeZero m] [NeZero n] {K : Type*} [Lattice K] [DecidableEq K] [DecidableLT K] (A : Matrix (Fin m) (Fin n) K)

theorem Matrix.gaussian_elimination_rank_normal_form [CommRing K] [NoZeroDivisors K] :
  ∀ (i : Fin m) (j : Fin n),
          if (i : ℕ) < A.rank ∧ (j : ℕ) < A.rank ∧ (i : ℕ) = j then
              (Gaussian.init A).gaussian_elimination.R i j ≠ 0
          else (Gaussian.init A).gaussian_elimination.R i j = 0 := by
   sorry

theorem Matrix.exists_rank_normal_form [CommRing K] [NoZeroDivisors K] :
    ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K),
      ∀ (i : Fin m) (j : Fin n),
          if (i : ℕ) < A.rank ∧ (j : ℕ) < A.rank ∧ (i : ℕ) = j then
            (P.1 * A * Q.1) i j ≠ 0
          else (P.1 * A * Q.1) i j = 0 := by
  sorry

#checkBasis.SmithNormalForm
theorem Matrix.exists_rank_standard_form [Field K]:
    ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K),
      P.1 * A * Q.1 = rankStdBlock K m n A.rank := by
  sorry

end RankNormalForm

section Classification

variable {K : Type*}  -- Extra condition : K is nontrivial
variable {m n : ℕ} [NeZero m] [NeZero n]

def rankEquiv [CommRing K] [Nontrivial K] (A B : Matrix (Fin m) (Fin n) K) : Prop :=
  ∃ (P : GL (Fin m) K) (Q : GL (Fin n) K), B = P.1 * A * Q.1

omit [NeZero m] [NeZero n] in
theorem rankEquiv_to_rank_eq_on_CommRing [CommRing K] [Nontrivial K] (A B : Matrix (Fin m) (Fin n) K) :
    rankEquiv A B → rank A = rank B := by
      rintro ⟨P, Q, h⟩
      rw [h]
      have h₀ : StrongRankCondition K := by apply commRing_strongRankCondition
      have h1 : rank (A * Q.1) = rank A := by
        apply le_antisymm
        apply rank_mul_le_left
        have h₁ : A * Q.1 * (Q⁻¹).1 = A := by simp
        have h₂ : rank A ≤ rank (A * Q.1) := by
          nth_rw 1 [← h₁]
          apply rank_mul_le_left
        exact h₂
      have h2 : rank (P.1 * A * Q.1) = rank (A * Q.1) := by
        have h₁ : P.1 * (A * Q.1) = P.1 * A * Q.1 := by
          rw [← Matrix.mul_assoc]
        rw [← h₁]
        apply le_antisymm
        apply rank_mul_le_right
        have h₂ : (P⁻¹).1 * (P.1 * (A * Q.1)) = (A * Q.1) := by simp
        nth_rw 1 [← h₂]
        apply rank_mul_le_right
      rw [h2, h1]

theorem rankEquiv_to_rank_eq_on_Field [Field K] [Lattice K] [DecidableEq K] [DecidableLT K] (A B : Matrix (Fin m) (Fin n) K) :
    rankEquiv A B ↔ rank A = rank B := by
      constructor
      apply rankEquiv_to_rank_eq_on_CommRing
      rintro rank_eq
      rcases exists_rank_standard_form A with ⟨P₁, Q₁, hA⟩
      rcases exists_rank_standard_form B with ⟨P₂, Q₂, hB⟩
      have : P₁.1 * A * Q₁.1 = P₂.1 * B * Q₂.1 := by
        rw [hA, hB, rank_eq]
      have h : (P₂⁻¹).1 * (P₁.1 * A * Q₁.1) * (Q₂⁻¹).1 = B := by
        rw [this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.mul_assoc, Units.mul_inv]
        simp
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at h
      have h' : ((P₂⁻¹) * P₁).1 * A * (Q₁ * (Q₂⁻¹)).1 = B := by
        simp
        rw [← Matrix.mul_assoc, ← coe_units_inv, ← coe_units_inv, h]
      use ((P₂⁻¹) * P₁)
      use (Q₁ * (Q₂⁻¹))
      rw [h']

instance rankEquiv_setoid [CommRing K] [Nontrivial K]: Setoid (Matrix (Fin m) (Fin n) K) where
  r := rankEquiv
  iseqv := by
    apply Equivalence.mk
    · intro A
      use 1, 1
      simp only [Matrix.one_mul, Matrix.mul_one, Units.val_one]
    · intro A B ⟨P, Q, h⟩
      use P⁻¹, Q⁻¹
      rw [h]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      simp only [coe_units_inv, isUnits_det_units, nonsing_inv_mul, Matrix.one_mul,
        mul_nonsing_inv_cancel_right]
    · intro A B C ⟨P₁, Q₁, h₁⟩ ⟨P₂, Q₂, h₂⟩
      use P₂ * P₁, Q₁ * Q₂
      rw [h₂, h₁]
      simp only [← Matrix.mul_assoc, Units.val_mul]

theorem rankEquiv_to_rankStdBlock [Field K] [Lattice K] [DecidableEq K] [DecidableLT K] (A : Matrix (Fin m) (Fin n) K) :
    rankEquiv A (rankStdBlock K m n A.rank) := by
      rcases exists_rank_standard_form A with ⟨P, Q, h⟩
      use P; use Q; rw [h]

end Classification

section LU

open Equiv Equiv.Perm
variable {K : Type*} [Field K]

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

variable {K : Type*} [CommRing K] [Lattice K] [DecidableEq K] [Nontrivial K]
  [DecidableLT K] [NoZeroDivisors K]

def fullRank_factorization_of_rank_normal_form (m n r : ℕ) (M : Matrix (Fin m) (Fin n) K)
    (h_rm : r ≤ m)
    (h_elem : ∀ (i : Fin m) (j : Fin n),
      if i < r ∧ j < r ∧ (i : ℕ) = j then M i j ≠ 0 else M i j = 0) :
    {D : (Matrix (Fin m) (Fin r) K) × (Matrix (Fin r) (Fin n) K) // M = D.1 * D.2} := by
  constructor; swap
  · exact ⟨rankStdBlock K m r r,
    fun i j => if (i : ℕ) = j then M (Fin.mk i.1 (by omega)) j else 0⟩
  · ext i j
    unfold rankStdBlock; simp [mul_apply]; specialize h_elem i j
    let f (x : Fin r) := if (x : ℕ) = j then if i < r then if (i : ℕ) = x
      then M ⟨x, Fin.val_lt_of_le x h_rm⟩ j
    else 0 else 0 else 0
    split_ifs at h_elem with ifs
    · obtain ⟨ir, jr, ij⟩ := ifs
      have : M i j = f (Fin.mk i.1 (by omega)) := by
        unfold f; simp only [← ij]; exact Eq.symm (if_pos ir)
      rw [this]; symm
      apply Finset.sum_eq_single (Fin.mk i ir)
      · simp
        intro b bnei beqj
        have : b = ⟨i.1, ir⟩ := Fin.eq_mk_iff_val_eq.mpr (by simp [ij, beqj])
        contradiction
      · simp
    · rw [h_elem]; symm
      exact Fintype.sum_eq_zero f (by
        intro k; unfold f; simp only [ite_eq_right_iff]
        intro kj ir ik; simp [kj, ik] at ifs; omega)

theorem exists_fullRank_factorization {m n} (A : Matrix (Fin m) (Fin n) K) :
    ∃ (B : Matrix (Fin m) (Fin A.rank) K) (C : Matrix (Fin A.rank) (Fin n) K),
    A = B * C := by
  induction m with
  | zero =>
    use Fin.elim0, fun _ _ => 0
    exact ext_of_single_vecMul (congrFun rfl)
  | succ => induction n with
    | zero =>
      use fun _ _ => 0, fun _ j => Fin.elim0 j
      exact Eq.symm (ext_of_mulVec_single (congrFun rfl))
    | succ =>
      have ⟨P, Q, is_normal⟩ := Matrix.exists_rank_normal_form A
      have ⟨⟨M,N⟩, heq⟩ := fullRank_factorization_of_rank_normal_form _ _ A.rank
        (h_rm := Matrix.rank_le_height A) (h_elem := is_normal)
      use P.1⁻¹ * M, N * Q.1⁻¹
      calc
        _ = (P.1⁻¹ * P.1) * A * (Q.1 * Q.1⁻¹) := by simp
        _ = P.1⁻¹ * (P.1 * A * Q.1) * Q.1⁻¹ := by simp only [Matrix.mul_assoc]
        _ = _ := by simp only [heq, Matrix.mul_assoc]



end Fullrankfactorization
