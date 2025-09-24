import Mathlib

open MeasureTheory ProbabilityTheory ENNReal Function Real
variable {Ω : Type*} [MeasureSpace Ω ](μ : Measure Ω) [IsProbabilityMeasure μ]


----Hoeffding_lemma
variable (a b :ℝ) (ha  : a < b)
noncomputable def φ (t a b: ℝ) : ℝ := log ((b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b))
theorem estimation :∀ t >0 , φ t a b ≤ t^2 * (b - a)^2 / 8 := by
  -- 设 f(t) = φ(t, a, b)
  let f := fun t => φ t a b
  -- 1. 证明 f(0) = 0
  have hf0 : f 0 = 0 := by
    simp [f, φ, div_sub_div_same, exp_zero]
  -- 2. 证明 f'(0) = 0
  have hf'0 : deriv f 0 = 0 := by
    let g := fun t => (b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b)
    have hg_diff : Differentiable ℝ g := by
      apply Differentiable.sub
      · exact (differentiable_exp.comp (differentiable_id.mul_const a)).const_mul _
      · exact (differentiable_exp.comp (differentiable_id.mul_const b)).const_mul _
    have hg_pos : ∀ t, 0 < g t := by
      intro t
      let p := -a / (b-a)
      have : g t = p * exp (t * b) + (1 - p) * exp (t * a) := by
        field_simp [p]; ring
      rw [this]
      have hp : 0 < p := by
        rw [div_pos_iff_of_pos_right (sub_pos_of_lt ha)]; exact neg_pos.mpr h_ab_zero.1
      have h1p : 0 < 1 - p := by
        field_simp [p, ha.ne.symm]; rw [div_pos_iff_of_pos_right (sub_pos_of_lt ha)]; exact h_ab_zero.2
      exact add_pos (mul_pos hp (exp_pos _)) (mul_pos h1p (exp_pos _))
    have h_deriv_f : deriv f t = deriv g t / g t := by
      rw [f, φ, deriv_log (hg_diff t) (hg_pos t).ne']
    simp only [h_deriv_f, deriv.sub, deriv.const_mul, deriv_exp, deriv.mul_const, mul_one]
    have hg'0 : deriv g 0 = 0 := by
      simp [g, exp_zero, mul_one, ← mul_assoc, ← sub_mul, mul_comm a, mul_comm b, div_sub_div_same, sub_self, mul_zero]
    have hg0 : g 0 = 1 := by simp [g, exp_zero, div_sub_div_same, sub_self]
    rw [hg'0, hg0, zero_div]
  -- 3. 证明 f''(t) ≤ (b-a)^2 / 4
  have hf'' : ∀ t, deriv (deriv f) t ≤ (b - a)^2 / 4 := by
    -- 这是证明中最复杂的部分，依赖于一个关于凸性的标准结果。
    -- 为简洁起见，我们暂时接受这个结论。
    sorry
  -- 4. 使用泰勒定理（均值定理的推论）
  intro t
  -- 均值定理的推论：f(t) = f(0) + t * f'(0) + (t^2 / 2) * f''(c) for some c
  -- 由于 f(0)=0, f'(0)=0, 我们有 f(t) = (t^2 / 2) * f''(c)
  -- 结合 f''(c) ≤ (b-a)^2/4, 得到 f(t) ≤ (t^2/2) * (b-a)^2/4 = t^2 * (b-a)^2/8
  rcases taylor_mean_value_thm_on_Icc (Set.Icc_mk 0 t) hf0 hf'0 (by linarith) with ⟨c, hc, h_taylor⟩
  rw [h_taylor, hf0, hf'0, zero_add, zero_mul, add_zero]
  gcongr
  exact hf'' c
theorem Hoeffding_lemma (X : Ω → ℝ)(h_measurable:Measurable X) (h0  : μ[X] = 0)(t : ℝ)
    (hbdd : ∀ω,a ≤ X ω ∧ X ω ≤ b) :∀t > 0 ,μ[fun ω => exp (t * X ω)] ≤ exp (t^2 * (b - a)^2 / 8) := by
  ---Using convexity for the estimation of exp(tX)
  intro t ht
  have h1:∀ ω , exp (t * X ω) ≤ (b - X ω) / (b - a) * exp (t * a) + (X ω - a) / (b - a) * exp (t * b) := sorry
  ----两边同时取期望
  have h2:μ[fun ω => exp (t * X ω)] ≤ b / (b - a) * exp (t * a) - a / (b - a) * exp (t * b) := by sorry
  have h :(b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b) >0 := sorry
  have h3:(b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b) ≤ exp (t^2 * (b - a)^2 / 8) := by
    suffices h_log : log ((b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b)) ≤  t^2 * (b - a)^2 / 8 from by exact (log_le_iff_le_exp h).mp h_log
    apply estimation
    apply ht -----h3的代码应该能简略一点。
  exact le_trans h2 h3
/-
按这个链接来写的，然后我觉得可能有问题的地方就是那个phi那里（因为phi（t）应该是一个与t有关的函数，但在lean里得传a b t三个参数进去？你可以试着改一下）感觉这里的这些sorry最困难的就是这个phi（t）的估计了，然后我们可以分工写一下这里的几个sorry
-/



theorem Hoeffding_general {X : ℕ → Ω → ℝ}  (h_indep : iIndepFun X μ)  {n : ℕ}(hn:n>0)
   (m M:ℕ→ ℝ)( h:∀ i ,M i > m i)(hbdd : ∀ i ∈Finset.range n ,∀ ω, m i ≤ X i ω ∧ X i ω ≤ M i) (t : ℝ) (ht : 0 < t) :
   μ.real {ω | (∑ i∈ Finset.range n, (X i ω - μ[X i])) ≥ t} ≤
     exp ((-2 * t^2) / (∑ i∈ Finset.range n, (M i - m i)^2)) := by
  have hindep: iIndepFun (fun i ω => X i ω - μ[X i]) μ:= by
    suffices iIndepFun (fun i => (fun x => x - (∫ a, X i a ∂μ)) ∘ X i) μ by
      -- 2. 证明原始目标可以从这个新目标推导出来。
      apply this
    apply iIndepFun.comp h_indep
    intro i
  -- 证明对于每个 i，(fun x => x - c) 是可测的。
    exact Measurable.sub measurable_id measurable_const

  have he:∀ i ∈ Finset.range n, μ[fun ω =>X i ω - μ[X i]]=0 := by
    intro i hi
    have h_measurable : Measurable (X i) := by
      sorry
    have h_integrable : Integrable (X i) μ := by
      apply MeasureTheory.Integrable.of_bound
      · exact h_measurable.stronglyMeasurable.aestronglyMeasurable
      · have h_bounded : ∀ ω, m i ≤ X i ω ∧ X i ω ≤ M i := hbdd i hi
        let f_bound : Ω → ℝ := fun _ => max |m i| |M i|
        have h_ae_bounded : ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ f_bound ω := by
          filter_upwards with ω
          specialize h_bounded ω
          simp [f_bound]
          cases le_or_gt 0 (X i ω) with
          | inl h_nonneg =>
          right
          rw [abs_of_nonneg h_nonneg]
          have hM_nonneg : 0 ≤ M i := le_trans h_nonneg h_bounded.2
          rw [abs_of_nonneg hM_nonneg]
          exact h_bounded.2
          | inr h_neg =>
          left
          rw [abs_of_neg ]
          have hm_nonpos : m i ≤ 0 := le_of_lt (lt_of_le_of_lt h_bounded.1 h_neg)
          rw [abs_of_nonpos hm_nonpos]
          exact neg_le_neg_iff.mpr h_bounded.1
          exact h_neg
        exact h_ae_bounded
    simp [integral_sub h_integrable (integrable_const _), integral_const]

  have h_subG : ∀ i ∈ Finset.range n, HasSubgaussianMGF (fun ω =>X i ω - μ[X i]) (((M i - m i).toNNReal ^ 2)/4) μ := by sorry
  apply le_trans
  apply ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep h_subG
  linarith
  have h1 :∀ i ,max (M i - m i) 0 =M i -m i  := by
    intro i
    simp;exact le_of_lt (h i)
  simp[h1]
  refine (div_le_div_iff₀ ?_ ?_).mpr ?_
  simp
  apply Finset.sum_pos';intro i hi ;positivity;
  use 0;constructor
  simp[hn];simp[h]
  apply Finset.sum_pos';intro i hi ;positivity;
  use 0;constructor
  simp[hn];simp[h]
  simp
  apply le_of_eq
  have :∑ x ∈ Finset.range n, (M x - m x) ^ 2 / 4=(∑ x ∈ Finset.range n, (M x - m x) ^ 2)/4:= by
    exact Eq.symm (Finset.sum_div (Finset.range n) (fun i => (M i - m i) ^ 2) 4)
  simp[this,←mul_assoc];
  calc
  2 * t ^ 2 * 2 * ((∑ x ∈ Finset.range n, (M x - m x) ^ 2) / 4)= 2 * t ^ 2 * 2 * ((∑ x ∈ Finset.range n, (M x - m x) ^ 2)) / 4:=by
    exact mul_div_assoc' (2 * t ^ 2 * 2) (∑ x ∈ Finset.range n, (M x - m x) ^ 2) 4
  _=(2*t^2*2/4) * ∑ x ∈ Finset.range n, (M x - m x) ^ 2:= by rw [@mul_div_right_comm]
  _=  t ^ 2 * ∑ x ∈ Finset.range n, (M x - m x) ^ 2:= by ring
