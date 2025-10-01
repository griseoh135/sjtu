import Mathlib
noncomputable section
open MeasureTheory ProbabilityTheory ENNReal Function Real
variable {Ω : Type*} [MeasureSpace Ω ](μ : Measure Ω) [IsProbabilityMeasure μ]


----Hoeffding_lemma
variable (a b :ℝ) (ha  : a < b)
noncomputable def φ (t a b: ℝ) : ℝ := log ((b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b))

lemma a_nonpos_and_b_nonneg (X : Ω → ℝ)(h_measurable: Measurable X)(h_range : ∀ ω, X ω ∈ Set.Icc a b)
    (h_exp : μ[X]= 0) : a ≤ 0 ∧ 0 ≤ b := by
  constructor
  by_contra h
  push_neg at h----反设0 < a，则 X 几乎必然 > 0，于是期望 > 0，矛盾
  have h1 : ∀ ω, 0 < X ω := by
    intro ω
    specialize h_range ω
    rcases h_range with ⟨h2, h3⟩
    linarith
  have h2 : 0 < ∫ ω, X ω ∂μ := by
    refine (integral_pos_iff_support_of_nonneg ?_ ?_).mpr ?_
    exact StrongLT.le h1
    refine Integrable.of_mem_Icc ?_ ?_ ?_ ?_
    apply a
    apply b
    exact h_measurable.aemeasurable
    exact ae_of_all μ h_range
    unfold support
    have h2 : {x | X x ≠ 0} = Set.univ := by
      ext x
      simp
      specialize h1 x
      linarith
    rw [h2]
    -- 概率测度下，整个空间测度为 1
    simp [MeasureTheory.measure_univ]
  linarith
  ----- 0 ≤ b的情况是类似的
  by_contra h
  push_neg at h
  let s:= -X
  have h1 : ∀ ω, 0 > X ω := by
    intro ω
    specialize h_range ω
    rcases h_range with ⟨h2, h3⟩
    linarith
  have h1': ∀ ω, 0 < s ω := by
    unfold s
    simp[h1]
  have hs_measurable :Measurable s := by
    unfold s
    exact h_measurable.neg
  have h2 : 0 < ∫ ω, s ω ∂μ := by
    refine (integral_pos_iff_support_of_nonneg ?_ ?_).mpr ?_
    exact StrongLT.le h1'
    refine Integrable.of_mem_Icc ?_ ?_ ?_ ?_
    apply -b
    apply -a
    exact hs_measurable.aemeasurable
    apply ae_of_all μ
    intro ω
    obtain ⟨h1, h2⟩ := h_range ω
    unfold s
    refine Set.mem_Icc.mpr ?_;constructor
    simp[h2];simp[h1]
    unfold support
    have h22 : {x | s x ≠ 0} = Set.univ := by
      ext x
      simp
      specialize h1' x
      linarith
    rw[h22]
    -- 概率测度下，整个空间测度为 1
    simp [MeasureTheory.measure_univ]
  have h2': 0> ∫ (ω : Ω), X ω ∂μ := by
    unfold s at h2
    simp at h2
    simpa [integral_neg] using h2
  linarith

theorem estimation (ha : a < b) : ∀ t > 0, φ t a b ≤ t^2 * (b - a)^2 / 8 := by
  intro t ht
  let f := fun t => φ t a b
  let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
  have hg_pos : ∀ x, 0 < g x := by
    intro x
    -- We show g(x) ≥ 1 using Jensen's inequality for the convex function exp.
    let p := -a / (b - a)
    have hp_pos : 0 < p := by sorry
    have h_one_minus_p : 1 - p = b / (b - a) := by sorry
    sorry

  have h_deriv_f_eq : deriv f = deriv g / g := by
    ext x
    have hg_diff_at : DifferentiableAt ℝ g x := by
      apply DifferentiableAt.sub <;> apply DifferentiableAt.const_mul <;>
      (apply DifferentiableAt.exp; apply DifferentiableAt.mul_const)
      sorry
      sorry
    sorry
  have hf0 : f 0 = 0 := by
    simp [f]
    sorry
  have hf'0 : deriv f 0 = 0 := by
    rw [h_deriv_f_eq]
    have hg0 : g 0 = 1 := by sorry
    have hg'0 : deriv g 0 = 0 := by ring_nf;sorry
    sorry
  have hf_cont_diff_on : ContDiffOn ℝ 1 f (Set.Icc 0 t) := by
    apply ContDiffOn.log
    { apply ContDiff.contDiffOn; apply ContDiff.sub
      <;> sorry }
    intro x _; linarith [hg_pos x]
  have hf'_diff_on : DifferentiableOn ℝ (iteratedDerivWithin 1 f (Set.Icc 0 t)) (Set.Ioo 0 t) := by
    have h_f_is_C2 : ContDiff ℝ 2 f := by
      apply ContDiff.log
      { apply ContDiff.sub
        <;> sorry }
      intro x; linarith [hg_pos x]
    sorry
  have hf'' : ∀ s, deriv (deriv f) s ≤ (b - a)^2 / 4 := by sorry
  -- Use Taylor's theorem with n=1 to get a remainder with the 2nd derivative.
  rcases taylor_mean_remainder_lagrange (n := 1) ht hf_cont_diff_on hf'_diff_on with ⟨c, hc, h_taylor⟩
  -- The theorem gives: f t - (f 0 + f' 0 * t) = f''(c)/2! * t^2
  rw [taylorWithinEval, ] at h_taylor
  rw [ sub_zero] at h_taylor
  simp [f]at h_taylor
  simp_all
  have h_iterated_deriv_2 : iteratedDeriv 2 f c = deriv (deriv f) c := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h_deriv_2_eq :iteratedDerivWithin 2 (fun t ↦ φ t a b) (Set.Icc 0 t) c = deriv (deriv f) c  := by
    sorry
  have taylor01 :(PolynomialModule.eval t) (taylorWithin (fun t ↦ φ t a b) 1 (Set.Icc 0 t) 0)
  =0 := by
    unfold taylorWithin

    --simp [taylorWithinEval_succ, taylorWithinEval_zero]
    -- The goal is now: f 0 + derivWithin f (Set.Icc 0 t) 0 * (t - 0) = 0
    --simp [derivWithin_of_mem_nhds (by simp), sub_zero]
    -- The goal is now: f 0 + deriv f 0 * t = 0
    --rw [hf0, hf'0, zero_mul, add_zero]
    simp_all [f, hf0]

    sorry
  simp_all
  rw [h_taylor, h_iterated_deriv_2, taylor01] at *
  calc
  _≤  (b - a) ^ 2 / 4 * t ^ 2 / 2 := by
    have : 0 ≤  t ^ 2 / 2:= by
      apply div_nonneg
      apply mul_nonneg
      · simp[npowRec]
        linarith
      · linarith
      · linarith
    have hfc_le : deriv (deriv g/g) c ≤ (b - a) ^ 2 / 4 := by
      exact hf'' c
    apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_right (hfc_le)
      linarith
    · linarith
  _= t^2 * (b - a)^2 / 8 := by ring


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

-----把t>0的条件推广到t为全体实数
theorem Hoeffding_lemma_expansion (X : Ω → ℝ)(h_measurable:Measurable X) (h0  : μ[X] = 0)(t : ℝ)
    (hbdd : ∀ω,a ≤ X ω ∧ X ω ≤ b)(ha :a <b) :μ[fun ω => exp (t * X ω)] ≤ exp (t^2 * (b - a)^2 / 8) := by
  wlog h_pos : t > 0 generalizing t
  ---剩下的
  by_cases h_zero : t = 0
  calc
    ∫ (x : Ω), (fun ω ↦ rexp (t * X ω)) x ∂μ = 1 := by simp[h_zero]
    _ ≤ rexp (t ^ 2 * (b - a) ^ 2 / 8) := by
      apply Real.one_le_exp
      positivity
  ----处理t<0的情况
  have ht_neg : t < 0 := by
    simp at h_pos h_zero
    by_contra h;simp at h
    have : t=0 := by linarith
    contradiction
  let s := -t
  have hs_pos : s > 0 := by simp [s]; linarith
  -- 把 exp(tX) 写成 exp(s(-X))
  have h_eq : μ[fun ω => exp (t * X ω)] = μ[fun ω => exp (s * (-X ω))] := by
    congr with ω
    simp [s, neg_mul]
  -- 对 Y = -X 应用已证的 t > 0 情形
  have h_Y : μ[fun ω => exp (s * (-X ω))] ≤ exp (s^2 * (b - a)^2 / 8) := by
    have h1: Measurable fun x ↦ -X x:= by exact Measurable.neg h_measurable
    have h2:  ∫ (x : Ω), -X x ∂μ = 0 := by simp [integral_neg, h0]
    have h3: ∀ (ω : Ω), -b ≤ -X ω ∧ -X ω ≤ -a := by
      intro ω
      constructor
      linarith[(hbdd ω).2]
      linarith[(hbdd ω).1]
    have h4: -b < -a := by linarith
    apply le_trans
    apply Hoeffding_lemma <;> try assumption
    simp;exact le_of_eq (by ring)
  rw [h_eq]
  apply le_trans h_Y
  apply le_of_eq
  rw [show s^2 = t^2 by simp [s]]
  apply Hoeffding_lemma   <;> try assumption


----thm2.2.6
theorem Hoeffding_general {X : ℕ → Ω → ℝ}  (h_indep : iIndepFun X μ)  {n : ℕ}(hn:n>0)(h_measurable:∀i,Measurable (X i))
   (m M:ℕ→ ℝ)( h:∀ i ,M i > m i)(hbdd : ∀ i ∈Finset.range n , ∀ω,m i ≤ X i ω ∧ X i ω ≤ M i) (t : ℝ) (ht : 0 < t) :
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
    exact fun i a ↦ expectation_of_centered_random_variable μ m M hbdd h_measurable i a
  have hbd:∀ i ∈Finset.range n , ∀ω,m i-μ[X i] ≤ X i ω - μ[X i] ∧ X i ω - μ[X i]≤ M i -μ[X i]:= by
    simp
    intro i hi ω
    exact hbdd i (Finset.mem_range.mpr hi) ω
  have h_subG : ∀ i ∈ Finset.range n,HasSubgaussianMGF (fun ω =>X i ω - μ[X i]) (((M i - m i).toNNReal ^ 2)/4) μ :=by
    intro i hi
    have mgf_le1 : ∀ (t : ℝ), mgf (fun ω ↦ X i ω - ∫ (x : Ω), X i x ∂μ) μ t
         ≤ rexp (((M i - m i).toNNReal ^ 2 / 4) * t ^ 2 / 2):= by
      intro t
      unfold mgf
      apply le_trans
      apply Hoeffding_lemma_expansion
      exact Measurable.add_const (h_measurable i) (-∫ (x : Ω), X i x ∂μ)
      exact he i hi
      exact fun ω ↦ hbd i hi ω
      exact sub_lt_sub_right (h i) (∫ (x : Ω), X i x ∂μ)
      apply exp_le_exp.mpr
      calc
        t ^ 2 * (M i - μ[X i] - (m i - μ[X i])) ^ 2 / 8 = t ^ 2 * (M i - m i) ^ 2 / 8 := by ring
        _ = t ^ 2 * (M i - m i) ^ 2 / 4 / 2 := by ring
        _ = ((M i - m i).toNNReal ^ 2 / 4) * t ^ 2 / 2 := by
          simp
          have : max (M i - m i) 0 =(M i - m i) :=  by
            apply max_eq_left
            linarith [h i]
          simp[this]
          ring
      simp

    refine { integrable_exp_mul := ?_, mgf_le := ?_ }
    ----上面这个have可以证明第二个子目标
    intro t
    refine ⟨?_, ?_⟩ ----按照定义证明可积
    ----证明可测
    sorry
    ----证明积分有限
    sorry
    intro t
    apply mgf_le1
  sorry
end
