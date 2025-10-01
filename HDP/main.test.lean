import Mathlib
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory ProbabilityTheory ENNReal Function Real
variable {Ω : Type*} [MeasureSpace Ω ](μ : Measure Ω) [IsProbabilityMeasure μ]

----Hoeffding_lemma
variable (a b :ℝ)

noncomputable def φ (t a b: ℝ) : ℝ := log ((b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b))


lemma taylor_integral_remainder {f : ℝ → ℝ} (t : ℝ) (ht_nonneg : 0 ≤ t)
    (hf_diff_on : DifferentiableOn ℝ f (Set.Icc 0 t))
    (hf'_diff_on : DifferentiableOn ℝ (deriv f) (Set.Icc 0 t))
    (hf0 : f 0 = 0) (hf'0 : deriv f 0 = 0) :
    f t = ∫ s in Set.Icc 0 t, (t - s) * deriv (deriv f) s := by
  have h_f_eq_int_deriv : ∀ x ∈ Set.Icc 0 t, f x = ∫ u in 0..x, deriv f u := by
    intro x hx
    rw [← hf0, intervalIntegral.integral_deriv_eq_sub']
    --exact hf_diff_on.mono (Set.Icc_subset_Icc_right hx.2)
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  have h_deriv_f_eq_int_deriv_deriv : ∀ x ∈ Set.Icc 0 t, deriv f x = ∫ u in 0..x, deriv (deriv f) u := by
    intro x hx
    rw [← hf'0, intervalIntegral.integral_deriv_eq_sub']
    --exact hf'_diff_on.mono (Set.Icc_subset_Icc_right hx.2)
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  rw [h_f_eq_int_deriv t (Set.mem_Icc.mpr ⟨ht_nonneg, le_refl t⟩)]
  rw [intervalIntegral.integral_of_le ht_nonneg]
  sorry

#check taylor_mean_remainder_lagrange
theorem estimation (ha : a < b) (ha_neg : a < 0) (hb_pos : 0 < b) : ∀ t > 0, φ t a b ≤ t^2 * (b - a)^2 / 8 := by
  intro t ht
  -- 设 f(t) = φ(t, a, b)
  let f := fun t => φ t a b
  let g := fun t => (b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b)
  have hg_diff : Differentiable ℝ g := by
    apply Differentiable.sub
    · exact (differentiable_exp.comp (differentiable_id.mul_const a)).const_mul _
    · exact (differentiable_exp.comp (differentiable_id.mul_const b)).const_mul _
  have hg_pos : ∀ x, 0 < g x := by
    intro x
    let p := -a / (b - a)
    have : g x = p * exp (x * b) + (1 - p) * exp (x * a) := by
      field_simp [p,g, div_sub_div_same];
      sorry
    rw [this]
    have hp : 0 < p := by
      rw [div_pos_iff_of_pos_right (sub_pos_of_lt ha)]
      exact neg_pos.mpr ha_neg
    have h1p : 0 < 1 - p := by
      simp [p ]
      -- sub_lt_self_iff, div_pos_iff_of_pos_right,
      sorry
    exact add_pos (mul_pos hp (exp_pos _)) (mul_pos h1p (exp_pos _))
  have hf_diff : Differentiable ℝ f := by
    apply Differentiable.log hg_diff
    intro x; exact (hg_pos x).ne'
  -- 1. 证明 f(0) = 0
  have hf0 : f 0 = 0 := by
    simp [f, φ, exp_zero, div_sub_div_same]
  -- 2. 证明 f'(0) = 0
  have hf'0 : deriv f 0 = 0 := by
    have h_deriv_f : deriv f t = deriv g t / g t := by
      --rw [f, φ, deriv_log (hg_diff.differentiableAt) (hg_pos t).ne']
      sorry
    have hg'0 : deriv g 0 = 0 := by
      simp [g]
      -- mul_one, ← mul_assoc, ← sub_mul, mul_comm a, mul_comm b, div_sub_div_same, sub_self]
      sorry
    have hg0 : g 0 = 1 := by
      sorry
      --simp [g, exp_zero, div_sub_div_same]
    rw [← hg'0]
    -- hg0, zero_div]
    sorry
  -- 3. 证明 f''(t) ≤ (b-a)^2 / 4
  have hf'' : ∀ t, deriv (deriv f) t ≤ (b - a)^2 / 4 := by
    -- 这是证明中最复杂的部分，依赖于一个关于凸性的标准结果。
    -- 为简洁起见，我们暂时接受这个结论。
    sorry
  -- 4. 使用泰勒定理（均值定理的推论）  -- 4. 使用泰勒定理（积分余项）
  -- 首先，我们需要证明 f 的一阶和二阶导数在 [0, t] 上是可微的
  have hf_diff2 : Differentiable ℝ (deriv f) := by
    have h_deriv_f_eq : deriv f = (deriv g) / g := by
      ext x; have h_f_eq_log_g : f = Real.log ∘ g := by ext y; simp [f, φ, g]
      sorry
    rw [h_deriv_f_eq]; apply Differentiable.div
    · have hg'_diff : Differentiable ℝ (deriv g) := by
        sorry
      exact hg'_diff
    · exact hg_diff
    · intro x; exact (hg_pos x).ne'

  -- 使用我们之前定义的泰勒积分余项引理
  have h_taylor := taylor_integral_remainder t (le_of_lt ht) hf_diff.differentiableOn hf_diff2.differentiableOn hf0 hf'0
  simp [f] at h_taylor
  rw [h_taylor] at *
  -- 对积分进行放缩
  have h_integrand_le : ∀ s ∈ Set.Icc 0 t, (t - s) * deriv (deriv f) s ≤ (t - s) * ((b - a) ^ 2 / 4) := by
    intro s hs
    apply mul_le_mul_of_nonneg_left (hf'' s)
    rw [Set.mem_Icc] at hs
    linarith
  field_simp; ring
  have h_integral_le : ∫ s in Set.Icc 0 t, (t - s) * deriv (deriv f) s ≤ ∫ s in Set.Icc 0 t, (t - s) * ((b - a) ^ 2 / 4) := by

    sorry





  sorry
