import Mathlib
/-- 定义 Korean 数：满足 n | 2^n + 1 的正整数 -/
def IsKorean (n : ℕ) := n > 0 ∧ n ∣ 2^n + 1

/-- 若 n 是 Korean 数且 n > 3，则存在新素数 p 不整除 n，使 n*p 也是 Korean 数 -/
lemma korean_induction_step {n : ℕ} (hn : IsKorean n) (h3 : n > 3) :
    ∃ p, Nat.Prime p ∧ ¬ (p ∣ n) ∧ IsKorean (n * p) := by
  rcases hn with ⟨hn_pos, hn_div⟩
  have h1 : n ∣ 2^n + 1 := hn_div
  have h2 : 2^n + 1 ∣ 2^(2*n) - 1 := by
    have h3'' : 2^n + 1 > 1 := by
      apply Nat.lt_of_sub_pos
      simp [pow_pos]
    have h4'' : 2^(2*n) - 1 = (2^n - 1) * (2^n + 1) := by
      rw [mul_comm (2^n - 1)  (2^n + 1) ,← Nat.sq_sub_sq (2^n)  1]
      ring_nf;
    rw[ h4'']
    exact Nat.dvd_mul_left (2^n + 1) (2^n - 1)
  have h3' : n ∣ 2^n + 1 := h1
  have h4 : 2^(2*n) + 1 > 1 := by
    apply Nat.lt_of_sub_pos
    simp [pow_pos]
  obtain ⟨p, hp, hp_div⟩ := Nat.exists_prime_and_dvd (show 2^(2*n) + 1 ≠ 1 by omega)
  use p
  have hp_not_dvd_n :¬ (p ∣ n):= by
    by_contra h
    have h5 : p ∣ 2^n + 1 := dvd_trans h h1
    have h6 : p ∣ 2^(2*n) - 1 := dvd_trans h5 h2
    have h7 : p ∣ (2^(2*n) + 1) - (2^(2*n) - 1) := Nat.dvd_sub hp_div h6
    have h8 : (2^(2*n) + 1) - (2^(2*n) - 1) = 2 := by omega
    rw [h8] at h7
    have h9 : p = 2 := by
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h7
    have h10 : 2 ∣ 2^(2*n) + 1 := by
      rw [ h9] at hp_div
      exact hp_div
    have h11 : ¬ (2 ∣ 2^(2*n) + 1) := by
      intro h
      have : 2^(2*n) % 2 = 0 := by
        have h1 : ∀ k > 0, 2^k % 2 = 0 := by
          intro k hk
          induction k with
          | zero => linarith
          | succ k ih =>
            cases k with
            | zero => simp
            | succ k => simp [pow_succ] at ih ⊢;
        specialize h1 (2*n) (by omega)
        assumption
      omega
    contradiction
  have hp_odd : p % 2 = 1 := by
    have h : p ∣ 2^(2*n) + 1 := hp_div
    have h1 : p % 2 = 1 := by
      by_contra h2
      have h2 : p % 2 = 0 := by omega
      have h3 : p = 2 := by
        have h4 : p ∣ 2 := by
          have h5 : p ∣ 2^(2*n) + 1 := h
          have h6 : 2^(2*n) % 2 = 0 := by
            have h7 : ∀ k > 0, 2^k % 2 = 0 := by
              intro k hk
              induction k with
              | zero => linarith
              | succ k ih =>
                cases k with
                | zero => simp
                | succ k => simp [pow_succ] at ih ⊢;
            specialize h7 (2*n) (by omega)
            assumption
          have h7 : (2^(2*n) + 1) % 2 = 1 := by omega
          have h8 : p % 2 = 0 := h2
          have h9 : p ∣ 2^(2*n) + 1 := h5
          have h10 : 2 ∣ 2^(2*n) + 1 := by
            exact dvd_trans (show 2 ∣ p by omega) h9
          omega
        have h5 : p = 2 := by
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4
        assumption
      rw [h3] at h
      have h4 : ¬ (2 ∣ 2^(2*n) + 1) := by
        intro h
        have : 2^(2*n) % 2 = 0 := by
          have h1 : ∀ k > 0, 2^k % 2 = 0 := by
            intro k hk
            induction k with
            | zero => linarith
            | succ k ih =>
              cases k with
              | zero => simp
              | succ k => simp [pow_succ] at ih ⊢;
          specialize h1 (2*n) (by omega)
          assumption
        omega
      contradiction
    assumption
  have hnp : (n * p) ∣ 2^(n * p) + 1 := by
    have hn1 : n ∣ 2^(n * p) + 1 := by
      have h1 : 2^n ≡ -1 [ZMOD n] := by
        have h2 : n ∣ 2^n + 1 := h1
        have h3 : (2^n + 1 : ℤ) ≡ 0 [ZMOD n ] := by refine Dvd.dvd.modEq_zero_int ?_
                                                    refine Int.ofNat_dvd_left.mpr ?_
                                                    norm_cast
        have h4 : (2^n : ℤ) ≡ -1 [ZMOD n] := by
          have h5 : (2^n + 1 : ℤ) ≡ 0 [ZMOD n] := h3
          symm at h5 ⊢
          exact Int.ModEq.add_right_cancel' 1 h5
        exact h4
      have h2 : (2^(n * p) : ℤ) ≡ (-1)^p [ZMOD n] := by
        rw [show (2^(n * p) : ℤ) = (2^n)^p by ring]
        exact Int.ModEq.pow p h1
      have h3 : (-1 : ℤ)^p = -1 := by
        have hp_odd' : Odd p := ⟨p / 2, by omega⟩
        exact Odd.neg_one_pow hp_odd'
      have h4 : (2^(n * p) : ℤ) ≡ -1 [ZMOD n] := by
        rw [h3] at h2
        exact h2
      have h5 : (2^(n * p) + 1 : ℤ) ≡ 0 [ZMOD n] := by
        have h6 : (2^(n * p) : ℤ) ≡ -1 [ZMOD n] := h4
        have h7 : (2^(n * p) + 1 : ℤ) ≡ (-1 + 1) [ZMOD n] := by
          exact Int.ModEq.add_right 1 h6
        simp at h7 ⊢
        exact h7
      norm_cast at h5 ⊢
      apply Int.ofNat_dvd.mp
      exact Int.dvd_of_emod_eq_zero h5
    have hp1 : p ∣ 2^(n * p) + 1 := by
      have h1 : 2^(2 * n) ≡ -1 [ZMOD p] := by
        have h2 : p ∣ 2^(2 * n) + 1 := hp_div
        have h3 : (2^(2 * n) + 1 : ℤ) ≡ 0 [ZMOD p] := by refine Dvd.dvd.modEq_zero_int ?_;norm_cast
                  --exact Int.modEq_zero_iff_dvd.mpr (Int.ofNat_dvd_left.mpr h2)
        have h4 : (2^(2 * n) : ℤ) ≡ -1 [ZMOD p] := by
          have h5 : (2^(2 * n) + 1 : ℤ) ≡ 0 [ZMOD p] := h3
          symm at h5 ⊢
          exact Int.ModEq.add_right_cancel' 1 h5
        exact h4
      have h2 : p ∣ n * p := by
        simp [Nat.dvd_mul_left]
      have h3 : 2^(n * p) ≡ -1 [ZMOD p] := by

        have h4 : (2^(n * p) : ℤ) = (2^(2 * n))^(p / 2) := by
          have hp_even : p % 2 = 1 := hp_odd
          have hp_div2 : p = (p / 2) * 2 + 1 := by omega
          ring_nf
          sorry

        rw [h4]
        have h5 : (2^(2 * n) : ℤ) ≡ -1 [ZMOD p] := h1
        have h6 : (2^(2 * n))^(p / 2) ≡ (-1)^(p / 2) [ZMOD p] := by
          exact Int.ModEq.pow (p / 2) h5

        have h7 : (-1 : ℤ)^(p / 2) = -1 := by
          have h8 : p % 4 = 1 ∨ p % 4 = 3 := by
            have h9 : p % 2 = 1 := hp_odd
            omega
          cases h8 with
          | inl h10 =>
            have h11 : (p / 2) % 2 = 0 := by omega
            have h12 : (-1 : ℤ)^(p / 2) = 1 := by
              have h13 : (p / 2) % 2 = 0 := h11
              have h14 : (-1 : ℤ)^(p / 2) = (-1)^(2 * ((p / 2) / 2)) := by
                congr
                omega
              rw [h14]
              rw [pow_mul]
              simp
            sorry
          | inr h10 =>
            have h11 : (p / 2) % 2 = 1 := by omega
            have h12 : (-1 : ℤ)^(p / 2) = -1 := by
              have h13 : (p / 2) % 2 = 1 := h11
              have h14 : (-1 : ℤ)^(p / 2) = -1 := by
                have h15 : (p / 2) = 2 * ((p / 2) / 2) + 1 := by omega
                rw [h15]
                rw [pow_add, pow_mul]
                simp
                <;> omega
              exact h14
            exact h12
        have h8 : (2^(n * p) : ℤ) ≡ -1 [ZMOD p] := by
          rw [h7] at h6
          sorry
        sorry
      have h4 : (2^(n * p) + 1 : ℤ) ≡ 0 [ZMOD p] := by
        have h5 : (2^(n * p) : ℤ) ≡ -1 [ZMOD p] := h3
        have h6 : (2^(n * p) + 1 : ℤ) ≡ (-1 + 1) [ZMOD p] := by
          exact Int.ModEq.add_right 1 h5
        simp at h6 ⊢
        exact h6

      sorry

    --exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by simp [hp_not_dvd_n]) hn1 hp1
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd ;
    · refine Nat.gcd_eq_one_iff.mpr ?_
      intro c
      intro nc
      intro pc
      have ht:=Nat.Prime.eq_one_or_self_of_dvd hp c pc
      cases ht with
      | inl h1 =>
        exact h1
      | inr h1 =>
        exfalso
        rw[← h1] at hp_not_dvd_n
        tauto
    · exact hn1
    · exact hp1
  --exact ⟨hp, hp_not_dvd_n, ⟨by omega, hnp⟩⟩
  exact ⟨hp, hp_not_dvd_n, ⟨ by simp;exact ⟨ hn_pos, Nat.Prime.pos hp⟩ , hnp⟩⟩


/-- 主定理：存在恰有 2000 个不同素因子的 Korean 数 -/
theorem imo2000_p5 : ∃ n, IsKorean n ∧ n.primeFactors.card = 2000 := by
  -- 从 n = 9 开始，它有 1 个素因子
  have h0 : IsKorean 9 := ⟨by norm_num, by norm_num⟩
  have h1 : (9).primeFactors.card = 1 := by native_decide
  -- 通过 1999 次归纳构造，每次引入一个新素因子
  have h2 : ∀ k, ∃ n, IsKorean n ∧ n.primeFactors.card = k + 1 := by
    intro k
    induction k with
    | zero =>
      use 9
    | succ k ih =>
      rcases ih with ⟨n, hn, hcard⟩
      have h3 : n > 3 := by
        by_contra h
        have h4 : n ≤ 3 := by linarith
        have h5 : n.primeFactors.card ≤ 2 := by
          interval_cases n <;> native_decide

        sorry
      rcases korean_induction_step hn h3 with ⟨p, hp, hp_n, hnp⟩
      use n * p
      constructor
      · exact hnp
      · have h6 : (n * p).primeFactors.card = n.primeFactors.card + 1 := by
          rw [Nat.primeFactors_mul (by omega) (by exact Nat.Prime.ne_zero hp)]
          simp [hp, hp_n]
        rw [h6, hcard]
  -- 取 k = 1999，得到具有 2000 个素因子的 Korean 数
  specialize h2 1999
  rcases h2 with ⟨n, hn, hcard⟩
  use n
