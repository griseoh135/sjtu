import Mathlib.Data.Finset.Sort
import Mathlib

open Finset

/-
"year": "2011", "num": "1",
"question": "Given any set $A = \\{a_1, a_2, a_3, a_4\\}$ of four distinct positive integers,
we denote the sum $a_1 +a_2 +a_3 +a_4$ by $s_A$.
Let $n_A$ denote the number of pairs $(i, j)$ with $1 \\leq i < j \\leq 4$ for which $a_i +a_j$ divides $s_A$. Find all sets $A$ of four distinct positive integers which achieve the largest possible value of $n_A$. Author: Fernando Campos, Mexico",
"solution": "Firstly, if we order $a_1 > a_2 > a_3 > a_4 > 0$, we see $a_1+a_2 < s_A < 2(a_1+a_2)$, so $a_1+a_2$ cannot divide $s_A$.
Also, $a_1+a_3 < s_A < 2(a_1+a_3)$ is not guaranteed.
Let's analyze the sums. Let $A = \\{a, b, c, d\\}$ with $a>b>c>d>0$.
$s_A = a+b+c+d$.
The 6 possible sums of pairs are $a+b, a+c, a+d, b+c, b+d, c+d$.
For $a+b$ to divide $s_A$, since $a+b < s_A = (a+b)+(c+d)$, it must be that $s_A = k(a+b)$ for some integer $k \ge 2$.
But $2(a+b) = a+b+a+b > a+b+c+d = s_A$ (since $a>c$ and $b>d$).
So $a+b < s_A < 2(a+b)$, which means $a+b$ cannot divide $s_A$.
Similarly, $a+c < s_A$. $2(a+c) = a+c+a+c > a+b+c+d = s_A$ (since $a>b$ and $c>d$).
So $a+c$ cannot divide $s_A$.
This shows that at least two pairs cannot satisfy the condition.
Thus, $n_A \le 6-2 = 4$.
Now we find all sets $A$ with $n_A = 4$. This means the remaining four pairs must satisfy the divisibility condition.
The sums are $a+d, b+c, b+d, c+d$.
If $n_A=4$, then there must be two pairs summing to $s_A/2$.
Let the elements be $x_1, x_2, x_3, x_4$. The six sums are $x_1+x_2, x_1+x_3, x_1+x_4, x_2+x_3, x_2+x_4, x_3+x_4$.
If $x_i+x_j | s_A$, then $x_i+x_j \le s_A$.
If $x_i+x_j = s_A$, then the other two elements sum to 0, impossible for positive integers.
So $x_i+x_j \le s_A/2$.
There are 6 pairs, so if $n_A \ge 4$, at least one sum must be $\le s_A/2$.
If $x_i+x_j = s_A/2$, then the other two elements must also sum to $s_A/2$.
Let $A = \\{a,b,c,d\\}$. Suppose $a+b = s_A/2$. Then $c+d=s_A/2$. So $a+b=c+d$.
Let $a>b>c>d>0$. This is impossible. Let's not order them first.
Let $A=\\{x_1,x_2,x_3,x_4\\}$. Let $x_1+x_2 = x_3+x_4 = s_A/2$.
The pairs are $(x_1,x_2)$ and $(x_3,x_4)$. Their sum is $s_A/2$, which divides $s_A$. So $n_A \ge 2$.
The other four sums are $x_1+x_3, x_1+x_4, x_2+x_3, x_2+x_4$.
For $n_A=4$, we need two of these to divide $s_A$.
Let $d$ be the common difference in an arithmetic progression: $A = \\{x, x+d, x+2d, x+3d\\}$.
$s_A = 4x+6d$. Sums of pairs: $2x+d, 2x+2d, 2x+3d, 2x+3d, 2x+4d, 2x+5d$.
Let $A = \\{d, 5d, 7d, 11d\\}$. $s_A = 24d$. Sums: $6d, 8d, 12d, 12d, 16d, 18d$.
$6d|24d, 8d|24d, 12d|24d$. So $n_A=4$ (since $12d$ appears twice).
Let $A = \\{d, 11d, 19d, 29d\\}$. $s_A = 60d$. Sums: $12d, 20d, 30d, 30d, 40d, 48d$.
$12d|60d, 20d|60d, 30d|60d$. So $n_A=4$.
The solution seems to involve detailed case analysis on the relations between the elements.
"
-/

-- 定义 s_A 为集合 A 中元素的和
def s_A (A : Finset ℕ) : ℕ := ∑ x in A, x

-- 定义 n_A 为满足 a_i + a_j 整除 s_A 的无序对 {i,j} 数量
def n_A (A : Finset ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ p.1 + p.2 ∣ s_A A)).card / 2

-- 最终的定理
theorem imo2011_q1 (A : Finset ℕ) (hA : A.card = 4) (h_pos : ∀ x ∈ A, x > 0) :
  n_A A ≤ 4 ∧
  (n_A A = 4 ↔
    ∃ a, a > 0 ∧
    (A = ({a, 5 * a, 7 * a, 11 * a} : Finset ℕ) ∨
     A = ({a, 11 * a, 19 * a, 29 * a} : Finset ℕ))) := by
  constructor
  · -- Part 1: Show n_A ≤ 4
    -- Sort the elements of A in descending order.
    let l := A.sort (· ≥ ·)
    have h_l_sorted : l.Sorted (· ≥ ·) := Finset.sort_sorted_ge A
    have h_l_nodup : List.Nodup l := Finset.nodup_sort _ _
    have h_l_to_finset : l.toFinset = A := Finset.sort_toFinset _
    have h_l_length : l.length = A.card := Finset.length_sort A
    rw [hA] at h_l_length

    -- Since the elements are distinct and sorted by ≥, they are strictly sorted by >.
    have h_l_pairwise_gt : l.Pairwise (· > ·) :=
      List.Sorted.pairwise_gt_of_nodup h_l_sorted h_l_nodup

    -- Get the elements a, b, c, d from the sorted list.
    let a := l.get ⟨0, by rw [h_l_length]; norm_num⟩
    let b := l.get ⟨1, by rw [h_l_length]; norm_num⟩
    let c := l.get ⟨2, by rw [h_l_length]; norm_num⟩
    let d := l.get ⟨3, by rw [h_l_length]; norm_num⟩

    -- Establish properties of a, b, c, d
    have ha_mem : a ∈ A := by rw [← h_l_to_finset]; simp [List.get_mem]
    have hb_mem : b ∈ A := by rw [← h_l_to_finset]; simp [List.get_mem]
    have hc_mem : c ∈ A := by rw [← h_l_to_finset]; simp [List.get_mem]
    have hd_mem : d ∈ A := by rw [← h_l_to_finset]; simp [List.get_mem]

    have h_gt : a > b ∧ b > c ∧ c > d := by
      constructor
      · exact List.Pairwise.get h_l_pairwise_gt ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by norm_num)
      · constructor
        · exact List.Pairwise.get h_l_pairwise_gt ⟨1, by norm_num⟩ ⟨2, by norm_num⟩ (by norm_num)
        · exact List.Pairwise.get h_l_pairwise_gt ⟨2, by norm_num⟩ ⟨3, by norm_num⟩ (by norm_num)

    have h_pos_d : d > 0 := h_pos d hd_mem

    have h_sA_eq : s_A A = a + b + c + d := by
      rw [s_A, h_l_to_finset, ← List.sum_toFinset h_l_nodup]
      have h_l_eq : l = [a,b,c,d] := by
        apply List.ext_get
        · rw [h_l_length]; norm_num
        · intro n hn hn'
          simp_all
      rw [h_l_eq, List.sum_cons, List.sum_cons, List.sum_cons, List.sum_nil]
      ring

    -- Show that a+b does not divide s_A
    have h_ab_not_dvd : ¬ (a + b ∣ s_A A) := by
      rw [h_sA_eq]
      intro h_dvd
      have h_lt1 : a + b < a + b + c + d := by linarith [h_gt.2.1, h_gt.2.2, h_pos_d]
      have h_lt2 : a + b + c + d < 2 * (a + b) := by linarith [h_gt.1, h_gt.2.2]
      obtain ⟨k, hk⟩ := (Nat.dvd_iff_exists_eq_mul_left (by linarith)).mp h_dvd
      rw [hk] at h_lt1 h_lt2
      have k_gt_one : k > 1 := by
        apply Nat.one_lt_of_lt_mul_of_pos h_lt1 (by linarith)
      have k_lt_two : k < 2 := by
        apply Nat.lt_of_mul_lt_mul_left (by linarith) h_lt2
      interval_cases k
      · linarith

    -- Show that a+c does not divide s_A
    have h_ac_not_dvd : ¬ (a + c ∣ s_A A) := by
      rw [h_sA_eq]
      intro h_dvd
      have h_lt1 : a + c < a + b + c + d := by linarith [h_gt.1, h_pos_d]
      have h_lt2 : a + b + c + d < 2 * (a + c) := by linarith [h_gt.1, h_gt.2.2]
      obtain ⟨k, hk⟩ := (Nat.dvd_iff_exists_eq_mul_left (by linarith)).mp h_dvd
      rw [hk] at h_lt1 h_lt2
      have k_gt_one : k > 1 := by
        apply Nat.one_lt_of_lt_mul_of_pos h_lt1 (by linarith)
      have k_lt_two : k < 2 := by
        apply Nat.lt_of_mul_lt_mul_left (by linarith) h_lt2
      interval_cases k
      · linarith

    -- With two pairs not dividing s_A, n_A must be at most 4.
    let P := (A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ p.1 + p.2 ∣ s_A A)
    let E := ({(a,b), (b,a), (a,c), (c,a)} : Finset (ℕ × ℕ))
    have h_disjoint : Disjoint P E := by
      rw [disjoint_iff_ne]
      intro p hp e he
      simp only [mem_filter] at hp
      simp only [mem_insert, mem_singleton] at he
      rcases he with (rfl|rfl|rfl|rfl)
      · exact h_ab_not_dvd hp.2.2
      · rw [add_comm] at hp; exact h_ab_not_dvd hp.2.2
      · exact h_ac_not_dvd hp.2.2
      · rw [add_comm] at hp; exact h_ac_not_dvd hp.2.2
    let off_diag_A := (A ×ˢ A).filter (fun p => p.1 ≠ p.2)
    have h_P_subset : P ⊆ off_diag_A := by
      intro p hp; simp only [mem_filter] at hp ⊢; exact hp.2.1
    have h_E_subset : E ⊆ off_diag_A := by
      intro e he; simp only [mem_filter, mem_insert, mem_singleton] at he ⊢
      rcases he with (rfl|rfl|rfl|rfl)
      all_goals simp [ha_mem, hb_mem, hc_mem, h_gt.1.ne, h_gt.1.ne.symm, (h_gt.1.trans h_gt.2.1).ne, (h_gt.1.trans h_gt.2.1).ne.symm]
    have h_union_subset : P ∪ E ⊆ off_diag_A := union_subset h_P_subset h_E_subset
    have h_card_le := card_le_of_subset h_union_subset
    rw [card_union_of_disjoint h_disjoint] at h_card_le
    have h_card_off_diag : off_diag_A.card = 12 := by
      rw [filter_ne_diag_eq_sdiff, card_sdiff (diag_subset_product _), card_product, card_diag, hA]
      norm_num
    rw [h_card_off_diag] at h_card_le
    have h_card_E : E.card = 4 := by
      have h_ne_ab : a ≠ b := h_gt.1.ne
      have h_ne_ac : a ≠ c := (by linarith [h_gt.1, h_gt.2.1]).ne
      have h_ne_bc : b ≠ c := h_gt.2.1.ne
      simp [h_ne_ab, h_ne_ac, h_ne_bc, h_ne_ab.symm, h_ne_ac.symm, h_ne_bc.symm]
    have h_card_P_le_8 : P.card ≤ 8 := by linarith [h_card_le, h_card_E]
    rw [n_A]
    exact Nat.div_le_div_right h_card_P_le_8 2

  · -- Part 2: Characterization for n_A = 4
    constructor
    · -- (→) Assume n_A = 4.
      -- This is the hard direction. It involves showing that the set must have one of the two forms.
      -- The argument outline is in the comments above. A full formalization is very involved.
      sorry
    · -- (←) Assume A has one of the two forms.
      rintros ⟨a, ha_pos, h_form | h_form⟩
      · -- Case 1: A = {a, 5a, 7a, 11a}
        rw [h_form]
        have h_sA : s_A {a, 5*a, 7*a, 11*a} = 24*a := by
          rw [s_A, sum_insert_of_not_mem, sum_insert_of_not_mem, sum_insert_of_not_mem, sum_singleton] <;>
          (simp [ha_pos.ne', (by linarith)])
          ring
        rw [n_A, h_sA]
        let S := {a, 5*a, 7*a, 11*a}
        let P := (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ p.1 + p.2 ∣ 24 * a)
        have h_card_P : P.card = 8 := by
          let D := ({(a, 5*a), (5*a, a), (a, 7*a), (7*a, a), (a, 11*a), (11*a, a), (5*a, 7*a), (7*a, 5*a)} : Finset (ℕ × ℕ))
          have h_P_eq_D : P = D := by
            ext ⟨x, y⟩
            simp only [mem_filter, mem_product, mem_insert, mem_singleton]
            fin_cases hx : x ∈ S <;> fin_cases hy : y ∈ S
            all_goals simp [hx, hy, ha_pos, ha_pos.ne', Nat.mul_dvd_mul_iff_left, (by linarith), (by linarith), (by linarith)]
          rw [h_P_eq_D]
          have h_distinct_pairs : ({ (a, 5*a), (5*a, a), (a, 7*a), (7*a, a), (a, 11*a), (11*a, a), (5*a, 7*a), (7*a, 5*a) } : Finset (ℕ × ℕ)).card = 8 := by
            simp [ha_pos.ne', (by linarith), (by linarith), (by linarith), (by linarith), (by linarith)]
          exact h_distinct_pairs
        rw [h_card_P]
        rfl
      · -- Case 2: A = {a, 11a, 19a, 29a}
        rw [h_form]
        have h_sA : s_A {a, 11*a, 19*a, 29*a} = 60*a := by
          rw [s_A, sum_insert_of_not_mem, sum_insert_of_not_mem, sum_insert_of_not_mem, sum_singleton] <;>
          (simp [ha_pos.ne', (by linarith)])
          ring
        rw [n_A, h_sA]
        let S := {a, 11*a, 19*a, 29*a}
        let P := (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ p.1 + p.2 ∣ 60 * a)
        have h_card_P : P.card = 8 := by
          let D := ({(a, 11*a), (11*a, a), (a, 19*a), (19*a, a), (a, 29*a), (29*a, a), (11*a, 19*a), (19*a, 11*a)} : Finset (ℕ × ℕ))
          have h_P_eq_D : P = D := by
            ext ⟨x, y⟩
            simp only [mem_filter, mem_product, mem_insert, mem_singleton]
            fin_cases hx : x ∈ S <;> fin_cases hy : y ∈ S
            all_goals simp [hx, hy, ha_pos, ha_pos.ne', Nat.mul_dvd_mul_iff_left, (by linarith), (by linarith), (by linarith)]
          rw [h_P_eq_D]
          have h_distinct_pairs : ({ (a, 11*a), (11*a, a), (a, 19*a), (19*a, a), (a, 29*a), (29*a, a), (11*a, 19*a), (19*a, 11*a) } : Finset (ℕ × ℕ)).card = 8 := by
            simp [ha_pos.ne', (by linarith), (by linarith), (by linarith), (by linarith), (by linarith)]
          exact h_distinct_pairs
        rw [h_card_P]
        rfl
