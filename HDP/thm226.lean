import Mathlib

open MeasureTheory ProbabilityTheory ENNReal Function Real
open scoped Real
noncomputable section

variable {Ω : Type*} [MeasureSpace Ω ](μ : Measure Ω) [IsProbabilityMeasure μ]
-- #check MeasureTheory.Integrable.of_bound
#check ProbabilityTheory.iIndepFun_iff_finset
#check ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun

-----E[X-E[X]]=0 for bounded random variable ---
theorem expectation_of_centered_random_variable {X : ℕ → Ω → ℝ}{n : ℕ}
    (m M:ℕ→ ℝ)(hbdd : ∀ i ∈Finset.range n ,∀ω, m i ≤ X i ω ∧ X i ω ≤ M i)
    (h_measurable1:∀i,Measurable (X i)):∀ i ∈ Finset.range n, μ[fun ω =>X i ω - μ[X i]]=0 := by
  intro i hi
  have h_measurable : Measurable (X i) := h_measurable1 i
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


----Hoeffding_lemma
section
variable (a b : ℝ)
noncomputable def φ (t a b: ℝ) : ℝ :=
  Real.log ((b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b))
theorem estimation (ha : a < b) (ha_nonpos:a ≤ 0)(hb_nonneg: b ≥ 0): ∀ t > 0, φ t a b ≤ t^2 * (b - a)^2 / 8 := by
  intro t ht
  let f := fun t => φ t a b
  let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
  have hg_pos : ∀ x, 0 < g x := by
    intro x
    -- We show g(x) ≥ 1 using Jensen's inequality for the convex function exp.
    let p := -a / (b - a)
    have hp_pos : 0 ≤ p := by
      apply div_nonneg
      linarith;linarith
    have hp_pos' :0 ≤ 1-p := by
      simp
      unfold p
      apply (div_le_one (by linarith)).mpr
      linarith
    have h_one_minus_p : 1 - p = b / (b - a) := by
      unfold p
      field_simp;rw [@sub_eq_iff_eq_add]
      field_simp
      refine Eq.symm (IsUnit.div_self ?_)
      simp;linarith
    have : p+(1-p)=1 := by simp
    --Above are some preparations.Now we prove the Jensen's inequality below.
    have exp: ∀t,p * Real.exp (t * b) + (1-p) * Real.exp (t * a)
          ≥ rexp ( p * (t * b) + (1 - p)*(t * a)):= by
      intro t
      have h_jensen := (convexOn_exp).2
      have h1: t * a ∈ Set.univ := by simp
      have h2: t * b ∈ Set.univ := by simp
      have h := h_jensen h2 h1 hp_pos hp_pos' this
      simpa
    --apply lemma 'exp',then prove g(x)>0 for any x
    unfold g
    rw[h_one_minus_p] at exp
    unfold p at exp
    calc
      0 < rexp (-a / (b - a) * (x * b) + b / (b - a) * (x * a)) := by
        exact exp_pos (-a / (b - a) * (x * b) + b / (b - a) * (x * a))
      _ ≤ -a / (b - a) * rexp (x * b) + b / (b - a) * rexp (x * a) := by exact exp x
      _ = b / (b - a) * rexp (x * a) - a / (b - a) * rexp (x * b) := by ring
  have h_deriv_f_eq : deriv f = deriv g / g := by
    ext x
    have h_comp : f = Real.log ∘ g := by
      funext t
      simp [f, g, φ]
    rw [h_comp]
    apply deriv.log
    -- g 可导
    apply Differentiable.sub ---分别证明两部分可导
    · apply Differentiable.const_mul
      simp
    apply Differentiable.const_mul
    simp
    -- g x ≠ 0
    exact Ne.symm (ne_of_lt (hg_pos x))
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
    simp [taylorWithin, taylorCoeffWithin, Finset.sum]
    have h1 : φ 0 a b =0  := by 
      simp [φ];right;left
      field_simp [ha] 
      apply div_self
      linarith
    simp [h1] at *
    right
    have h2 : deriv (fun t ↦ φ t a b) 0 =0 := by
      rw [h_deriv_f_eq]
      have hg0 : g 0 = 1 := by sorry
      have hg'0 : deriv g 0 = 0 := by ring_nf;sorry
      sorry
    unfold derivWithin
    have h_mem : 0 ∈ Set.Icc 0 t := by
      constructor<;>linarith
    have h_diff_on := hf_cont_diff_on.differentiableOn (by norm_num) 
    
-- 正确用法：将 h_diff_on 应用于具体点 0 和成员证明 h_mem
    have h_diff_within : DifferentiableWithinAt ℝ f (Set.Icc (0 : ℝ) t) 0 := h_diff_on 0 h_mem

-- 现在可以得到局部的导数存在（HasFDerivWithinAt）
    have h_hasF_within := h_diff_within.hasFDerivWithinAt
    have h_fderiv_within_eq : fderivWithin ℝ f (Set.Icc (0 : ℝ) t) 0 = (0 : ℝ →L[ℝ] ℝ) := by 
      have h_cont_at : ContDiffAt ℝ 1 f 0 := by sorry
      have h_differentiable_at : DifferentiableAt ℝ f 0 := by sorry
      have h_has_fderiv_at : HasFDerivAt f (fderiv ℝ f 0) 0 := by sorry
      have h_fderiv_zero : fderiv ℝ f 0 = 0 := by 
        simp [f]
        have h_fderiv_apply_one_eq_deriv : (fderiv ℝ f 0) 1 = deriv f 0 :=
        by 
          sorry
        have h_fderiv_apply_one_is_zero : (fderiv ℝ f 0) 1 = 0 :=
        by rw [h_fderiv_apply_one_eq_deriv, h2]
        apply ContinuousLinearMap.ext_ring
        exact h_fderiv_apply_one_is_zero
      have h_fderiv_within_eq_fderiv : fderivWithin ℝ f (Set.Icc 0 t) 0 = fderiv ℝ f 0 := by 
        
        sorry
      rw [h_fderiv_within_eq_fderiv, h_fderiv_zero]
      
      
    have final : (fderivWithin ℝ f (Set.Icc 0 t) 0) 1 = 0 := by
      rw [h_fderiv_within_eq]
      simp -- 因为 (0 : ℝ →L[ℝ] ℝ) 1 = 0
    simp [f] at final
    exact final
    

    
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
    (hbdd : ∀ω,a ≤ X ω ∧ X ω ≤ b)(ha :a <b) :∀t > 0 ,μ[fun ω => exp (t * X ω)] ≤ exp (t^2 * (b - a)^2 / 8) := by
  ---Using convexity for the estimation of exp(tX)
  intro t ht
  have h1:∀ ω , exp (t * X ω) ≤ (b - X ω) / (b - a) * exp (t * a) + (X ω - a) / (b - a) * exp (t * b) := sorry
  ----两边同时取期望
  have h2:μ[fun ω => exp (t * X ω)] ≤ b / (b - a) * exp (t * a) - a / (b - a) * exp (t * b) := by sorry
  have h :(b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b) >0 := sorry
  have h3:(b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b) ≤ exp (t^2 * (b - a)^2 / 8) := by
    apply (log_le_iff_le_exp h).mp
    apply estimation <;> try assumption
    sorry
    sorry
  exact le_trans h2 h3

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


end section



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
    intro s
    have h_aesm : AEStronglyMeasurable (fun ω ↦ rexp (s * (X i ω - ∫ (x : Ω), X i x ∂μ))) μ :=  (Measurable.exp (Measurable.const_mul  (Measurable.sub (h_measurable i) measurable_const) s)).aestronglyMeasurable
    refine ⟨?_, ?_⟩ ----按照定义证明可积
    ----证明可测
    -- 假设 h_meas : Measurable (X i)
    · exact h_aesm
    ----证明积分有限
    · apply Integrable.hasFiniteIntegral
      let C := max (rexp (s * (m i - ∫ x, X i x ∂μ))) (rexp (s * (M i - ∫ x, X i x ∂μ)))
      apply Integrable.of_bound h_aesm C
      -- 解决第一个目标：提供上界 C
-- 我们用 let 来定义这个常数，然后用 exact 提供它。
      unfold C
      apply ae_of_all
      intro ω
      simp only [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
      specialize hbd i hi ω
      by_cases hs : s ≥ 0
      · apply le_max_of_le_right
        apply exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left hbd.2 hs
      · apply le_max_of_le_left
        apply exp_le_exp.mpr
        have hs_neg : s ≤  0 := by linarith
        apply mul_le_mul_of_nonpos_left hbd.1 hs_neg
        
    intro t
    apply mgf_le1
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
  _=t ^ 2 * ∑ x ∈ Finset.range n, (M x - m x) ^ 2 := by ring


end section

#check taylorCoeffWithin
#check taylor_mean_remainder_lagrange
#check Integrable
#check Set.mem_Icc
#check DifferentiableWithinAt.hasFDerivWithinAt 
#check DifferentiableWithinAt.hasDerivWithinAt 

#check HasFDerivAt.hasFDerivWithinAt 

#check fderivWithin #check fderiv #check deriv
#check HasFDerivWithinAt
#check HasFDerivAt
#check HasFDerivAt.fderiv
#check HasFDerivAt.hasFDerivWithinAt
#check HasFDerivWithinAt.fderivWithin
#check DifferentiableWithinAt.hasFDerivWithinAt
#check DifferentiableAt.hasFDerivAt

#check fderivWithin
#check fderiv
#check deriv
#check UniqueDiffWithinAt
