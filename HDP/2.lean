import Mathlib
noncomputable section
variable (a b : ℝ)
noncomputable def φ (t a b: ℝ) : ℝ :=
  Real.log ((b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b))
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
end
