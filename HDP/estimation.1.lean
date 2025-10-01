import Mathlib

noncomputable section

variable (a b : ℝ)

-- φ(t) = log(E[e^{tX}]) where X is a random variable with P(X=a) = p and P(X=b) = 1-p
-- Here p = b/(b-a) and 1-p = -a/(b-a)
-- This requires a < 0 < b, but the formula is more general.
-- Let's define it directly.
noncomputable def φ (t a b: ℝ) : ℝ :=
  Real.log ((b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b))

-- Hoeffding's Lemma states that φ(t) ≤ t^2(b-a)^2/8
theorem estimation (ha : a < b) : ∀ t > 0, φ t a b ≤ t^2 * (b - a)^2 / 8 := by
  intro t ht
  let f := fun t => φ t a b
  let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)

  have hg_pos : ∀ x, g x > 0 := by
    intro x
    let h := fun t => (b * Real.exp (t*a) - a * Real.exp (t*b))
    suffices 1 * (b-a) ≤ h x by
      sorry
    let p := fun t => a * b * (Real.exp (t * a) - Real.exp (t * b))
    have hp : deriv h = p := by
      ext t
      simp [ h]
      simp [ p]
      ring_nf
      sorry
    have h_p_x_0 : p x = 0 ↔ x = 0 := by
      simp [p]
      have : b*a ≠ 0 := by sorry -- need a<0, b>0
      have h_exp_eq : Real.exp (x * a) = Real.exp (x * b) ↔ x * a = x * b := by exact Real.exp_eq_exp
      sorry
    sorry -- to be continued from here

  have hg_diff : Differentiable ℝ g := by
    simp [g]
    sorry

  have hf_diff : Differentiable ℝ f := by
    apply Differentiable.log hg_diff
    intro x
    linarith [hg_pos x]

  have h_deriv_f_eq : deriv f = deriv g / g := by
    ext x
    simp [f]
    sorry

  have hf0 : f 0 = 0 := by
    simp [f]
    sorry

  have hf'0 : deriv f 0 = 0 := by sorry

  have hf_cont_diff_on : ContDiffOn ℝ 2 f (Set.Icc 0 t) := by
    apply ContDiffOn.log
    · sorry
    · sorry

  have hf'' : ∀ s ∈ Set.Icc 0 t, deriv (deriv f) s ≤ (b - a)^2 / 4 := by
    intro s _
    sorry

  have h_deriv_2_diff_on : DifferentiableOn ℝ (iteratedDerivWithin 2 f (Set.Icc 0 t)) (Set.Ioo 0 t) := by
    have h_f_cont_diff_3 : ContDiff ℝ 3 f := by
      apply ContDiff.log
      · sorry
      · sorry
    sorry
  rcases taylor_mean_remainder_lagrange ht hf_cont_diff_on h_deriv_2_diff_on with ⟨c, hc, h_taylor⟩

  have h_iterated_deriv_2 : iteratedDeriv 2 f c = deriv (deriv f) c := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  simp_all


  sorry
end
