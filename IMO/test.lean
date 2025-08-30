theorem test_theorem :
  (∑ k ∈ Icc (1:ℕ) 70, (k:ℝ) / (1 + (k:ℝ)))
    = (∑ k ∈ Icc (1:ℕ) 70, (k:ℝ) * ∏ j ∈ (Icc (1:ℕ) 70).erase k, (1 + (j:ℝ)))
        / (∏ j ∈ Icc (1:ℕ) 70, (1 + (j:ℝ))) := by
  classical
  -- 公共分母非零
  have hP_ne : (∏ j ∈ Icc (1:ℕ) 70, (1 + (j:ℝ))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    have : (0:ℝ) < 1 + (j:ℝ) := by positivity
    exact ne_of_gt this
  -- 交叉相乘
  apply (eq_div_iff hP_ne).2
  -- 展开左侧乘公共分母
  have h_expand :=
    Finset.sum_mul (s:=Icc (1:ℕ) 70)
      (f:=fun k => (k:ℝ)/(1 + (k:ℝ)))
      (a:=∏ j ∈ Icc (1:ℕ) 70, (1 + (j:ℝ)))
  -- 化简为逐项，再对每项通分
  calc
    (∑ k ∈ Icc (1:ℕ) 70, (k:ℝ)/(1 + (k:ℝ))) * (∏ j ∈ Icc (1:ℕ) 70, (1 + (j:ℝ)))
        = ∑ k ∈ Icc (1:ℕ) 70, ((k:ℝ)/(1 + (k:ℝ))) * (∏ j ∈ Icc (1:ℕ) 70, (1 + (j:ℝ))) := by
          simpa using h_expand
    _ = ∑ k ∈ Icc (1:ℕ) 70, (k:ℝ) * ∏ j ∈ (Icc (1:ℕ) 70).erase k, (1 + (j:ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          -- 分解整体乘积 (∏ 全部) = (∏ 删 k)*(1+k)
          have hfac0 :
              (∏ j ∈ (Icc (1:ℕ) 70).erase k, (1 + (j:ℝ))) * (1 + (k:ℝ))
                = ∏ j ∈ Icc (1:ℕ) 70, (1 + (j:ℝ)) :=
            Finset.prod_erase_mul
              (s:=Icc (1:ℕ) 70) (a:=k) (f:=fun j => (1 + (j:ℝ))) hk
          have hfac : (∏ j ∈ Icc (1:ℕ) 70, (1 + (j:ℝ)))
                = (∏ j ∈ (Icc (1:ℕ) 70).erase k, (1 + (j:ℝ))) * (1 + (k:ℝ)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hfac0
          have hk_ne : (1 + (k:ℝ)) ≠ 0 := by
            have : (0:ℝ) < 1 + (k:ℝ) := by positivity
            exact ne_of_gt this
          calc
            ((k:ℝ)/(1 + (k:ℝ))) * (∏ j ∈ Icc (1:ℕ) 70, (1 + (j:ℝ)))
                = ((k:ℝ)/(1 + (k:ℝ))) * ((∏ j ∈ (Icc (1:ℕ) 70).erase k, (1 + (j:ℝ))) * (1 + (k:ℝ))) := by
                  simpa [hfac]
            _ = (k:ℝ) * ∏ j ∈ (Icc (1:ℕ) 70).erase k, (1 + (j:ℝ)) := by
                  field_simp [hk_ne]; ring
  -- 用 hs 把 s 换回原来的 Icc 表达
  simpa [hs] using this
    -- 证明完成
