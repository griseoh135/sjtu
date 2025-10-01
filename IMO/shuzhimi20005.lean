import Mathlib
/-- 定义 Korean 数：满足 n | 2^n + 1 的正整数 -/
def IsKorean (n : ℕ) := n > 1 ∧ n ∣ 2^n + 1
lemma pol (n:ℕ ): 2^(3*n)+1=(2^n+1)*(1-2^n+2^(2*n)) := by
  sorry
/-- 若 n 是 Korean 数且 n > 3，则存在新素数 p 不整除 n，使 n*p 也是 Korean 数 -/
lemma korean_induction_step {n : ℕ} (hn : IsKorean (3*n)) (h1 : n > 0) :
    ∃ p, p>3 ∧ Nat.Prime p ∧ ¬ (p ∣ n) ∧ IsKorean (3*n * p) := by
  rcases hn with ⟨hn_pos, hn_div⟩
  rw[pol] at hn_div
  let m := 2^(2*n)-2^n+1
  let p := (2^(2*n)-2^n+1).minFac
  -- 3. p 是一个素数
  have hp_prime : Nat.Prime p := Nat.minFac_prime (Ne.symm (ne_of_lt (by
                   simp;rw [propext (Nat.pow_lt_pow_iff_right Nat.le.refl)];rw [propext
                   (Nat.lt_mul_iff_one_lt_left h1)] ;simp)))
  -- 4. p 整除 m
  have hp_dvd_m : p ∣ m := Nat.minFac_dvd m
  -- 5. p 不整除 n
  have hp_n : ¬ (p ∣ n) := by
    intro h
    sorry
  have h3pn:3*n*p∣ 2^(3*n)+1 := by
    sorry
  have h3pn2: 2 ^ (3 * n) + 1 ∣ 2 ^ (3 * n*p) + 1 := by

    sorry
  have h4pn: IsKorean (3*n*p) := by
    constructor
    · refine  Nat.one_lt_mul_iff.mpr ?_
      constructor
      · linarith
      · constructor
        · exact Nat.minFac_pos (2 ^ (2 * n) - 2 ^ n + 1)
        · left;tauto;
    · exact Nat.dvd_trans h3pn h3pn2
  use p
  constructor
  · sorry
  ·
   sorry
/-- 主定理：存在恰有 2000 个不同素因子的 Korean 数 -/
theorem imo2000_p5 : ∃ n, IsKorean n ∧ n.primeFactors.card = 2000 := by
  -- 从 n = 9 开始，它有 1 个素因子
  have h0 : IsKorean 9 := ⟨by norm_num, by norm_num⟩
  have h1 : (9).primeFactors.card = 1 := by native_decide
  -- 通过 1999 次归纳构造，每次引入一个新素因子
  have h2 : ∀ k, ∃ n, IsKorean (3*n) ∧ (3*n).primeFactors.card = k + 1 := by
    intro k
    induction k with
    | zero =>
      use 1
      constructor
      · unfold IsKorean; norm_num
      · norm_num
    | succ k ih =>
      rcases ih with ⟨n, hn, hcard⟩
      have h1 : n > 0 := by
        by_contra h
        have h4 : n ≤ 3 := by linarith
        have h5 : n.primeFactors.card ≤ 2 := by
          interval_cases n; native_decide
        interval_cases n
        · unfold IsKorean at hn
          simp at hn
      rcases korean_induction_step hn h1 with ⟨p,p3, hp, hp_n, hnp⟩
      use n * p
      constructor
      · rwa [Nat.mul_assoc] at hnp
      · have h6 : (3*n * p).primeFactors.card = (3*n).primeFactors.card + 1 := by
          rw [Nat.primeFactors_mul (by omega) (by exact Nat.Prime.ne_zero hp)]
          have hnp3 :¬ (p∣ (3*n)) := by refine Nat.Prime.not_dvd_mul hp ?_ hp_n;
                                         refine Nat.not_dvd_of_pos_of_lt ?_ p3 ;
                                         linarith
          simp [hp, hnp3]
        rw [← Nat.mul_assoc]
        rw [h6, hcard]
  -- 取 k = 1999，得到具有 2000 个素因子的 Korean 数
  specialize h2 1999
  rcases h2 with ⟨n, hn, hcard⟩
  use 3*n
