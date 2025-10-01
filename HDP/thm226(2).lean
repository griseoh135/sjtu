import Mathlib

open MeasureTheory ProbabilityTheory ENNReal Function Real
open scoped Real
open Filter Set
open Topology Filter Classical Real
noncomputable section

variable {Ω : Type*} [MeasureSpace Ω ](μ : Measure Ω) [IsProbabilityMeasure μ]
-- #check MeasureTheory.Integrable.of_bound
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
------if E[X]=0,then we have a ≤ 0 ≤ b
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



section lemma_about_deriv_contdiff
variable {a b :ℝ}
theorem deriv_of_linearfunction :∀ c:ℝ ,∀ x:ℝ, deriv (fun t ↦ c*t ) x =  c := by
  intro c x
  rw[deriv_const_mul]
  simp;exact differentiableAt_id

theorem deriv_of_exp:deriv (fun t ↦ b * rexp (a * t)) = (fun t ↦ b * (a * rexp (a * t))) := by
  funext x
  simp
  left
  have h : DifferentiableAt ℝ (fun x ↦ a* x) x := by
    have h11: DifferentiableAt ℝ (fun x ↦ x) x := by simp
    apply DifferentiableAt.const_smul h11 a
  rw[_root_.deriv_exp h]
  simp[mul_comm]
  apply deriv_of_linearfunction

theorem specialize_of_deriv_of_exp:deriv (fun t ↦ rexp (a * t))=(fun t ↦ a * rexp (a * t)) := by
  have :deriv (fun t ↦ 1 * rexp (a * t)) = (fun t ↦ 1 * (a * rexp (a * t))) := by apply deriv_of_exp
  simpa

theorem DifferentiableAt_of_exp_compose_linear_function :∀x,
    DifferentiableAt ℝ (fun t ↦ b * rexp (a * t)) x := by
  intro x
  have :DifferentiableAt ℝ (fun t ↦  rexp (a * t)) x := by
    refine DifferentiableAt.fun_comp' x ?_ ?_  ----note that it is a function composed by two function
    · simp   ----exp is Differentiableat x
    have h11: DifferentiableAt ℝ (fun x ↦ x) x := by simp
    apply DifferentiableAt.const_smul h11 a   ---linear function is Differentiableat x
  apply DifferentiableAt.const_smul this b

theorem DifferentiableAt_of_exp_compose_linear_function' :∀x,
    DifferentiableAt ℝ (fun t ↦ b/(b-a) * rexp (a * t)) x := by
  simp[DifferentiableAt_of_exp_compose_linear_function]

theorem DifferentiableAt_of_exp_compose_linear_function'':∀x,
    DifferentiableAt ℝ (fun t ↦ a / (b - a) * rexp (t * b)) x := by
  have : ∀t, a / (b - a) * rexp (b * t) = -(a / (a - b) * rexp (b * t)):= by
    intro t
    field_simp
    simp[←div_neg]
  rw[show (fun t ↦ a / (b - a) * rexp (t * b)) = (fun t ↦ a / (b - a) * rexp (b * t)) by simp[mul_comm]]
  rw[show (fun x ↦ a / (b - a) * rexp (b * x)) = (fun x ↦ -(a / (a - b) * rexp (b * x))) by funext t;simp[this]]
  intro x
  have :DifferentiableAt ℝ (fun t ↦ (a / (a - b) * rexp (b * t))) x := by
    simp[DifferentiableAt_of_exp_compose_linear_function']
  simp[this]


theorem Const_DifferentiableAt_of_exp_compose_linear_function'' :∀x,
    DifferentiableAt ℝ (fun t ↦ a * b / (b - a) * rexp (t * b)) x := by
  rw[mul_comm]
  intro x
  have h:DifferentiableAt ℝ (b • fun t ↦ a / (b - a) * rexp (t * b)) x := by
    apply DifferentiableAt.const_smul (DifferentiableAt_of_exp_compose_linear_function'' x) b
  have :(fun t ↦ b * a / (b - a) * rexp (t * b))= (b • fun t ↦ a / (b - a) * rexp (t * b)) := by
    funext x
    simp[←mul_assoc,mul_div]
  simp[this,h]


theorem deriv_of_exp' : deriv (fun t ↦ b * rexp (a * t) - a * rexp (b * t))=
    fun t ↦ a * b * (rexp (a * t) - rexp (b * t)) := by
  funext x
  rw[show (fun t ↦ b * rexp (a * t) - a * rexp (b * t))=((fun t ↦ b * rexp (a * t)) -fun t ↦ a * rexp (b * t)) by congr]
  rw[deriv_sub,deriv_of_exp,deriv_of_exp]
  simp[mul_sub,←mul_assoc,mul_comm]
  apply DifferentiableAt_of_exp_compose_linear_function
  apply DifferentiableAt_of_exp_compose_linear_function

theorem ContDiff_of_exp : ContDiff ℝ 1 fun x ↦ b / (b - a) * rexp (x * a) := by
  have : ContDiff ℝ 1 fun x ↦  rexp (x * a):= by
    refine ContDiff.exp ?_
    apply ContDiff.mul contDiff_fun_id contDiff_const
  refine ContDiff.mul ?_ this
  apply contDiff_const

theorem ContDiff_of_exp' :ContDiff ℝ 1 fun x ↦ a / (b - a) * rexp (x * b)
 := by
  have : ContDiff ℝ 1 fun x ↦  rexp (x * b):= by
    refine ContDiff.exp ?_
    apply ContDiff.mul contDiff_fun_id contDiff_const
  refine ContDiff.mul ?_ this
  apply contDiff_const


theorem ContDiff2_of_exp: ContDiff ℝ 2 fun x ↦ b / (b - a) * rexp (x * a) := by
  refine ContDiff.mul ?_ ?_
  · apply contDiff_const
  apply ContDiff.exp
  apply ContDiff.mul contDiff_fun_id contDiff_const

theorem ContDiff2_of_exp':ContDiff ℝ 2 fun x ↦ a / (b - a) * rexp (x * b) := by
  have : ∀t, a / (b - a) * rexp (t * b) = -(a / (a - b) * rexp (t * b)):= by
    intro t
    field_simp
    simp[←div_neg]
  rw[show (fun x ↦ a / (b - a) * rexp (x * b)) = (fun x ↦ -(a / (a - b) * rexp (x * b))) by funext t;simp[this]]
  have h:ContDiff ℝ 2 fun x ↦ a / (a - b) * rexp (x * b):= by apply ContDiff2_of_exp
  apply ContDiff.neg h

noncomputable def φ (t a b: ℝ) : ℝ :=
  Real.log ((b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b))

theorem calc_of_deriv_g :
    let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
    deriv g  = fun t => (a * b / (b - a)) * (Real.exp (t * a)-Real.exp (t * b)):= by
  intro g ;unfold g
  rw[show (fun t ↦ b / (b - a) * rexp (t * a) - a / (b - a) * rexp (t * b))=((fun t ↦ b / (b - a) * rexp (t * a))
    -((fun t ↦a / (b - a) * rexp (t * b)))) by congr]
  funext x
  rw[deriv_sub]
  simp
  ring
  rw[show (fun t ↦ b / (b - a) * rexp (t * a)) = (fun t ↦ b / (b - a) * rexp (a * t)) by simp[mul_comm]]
  apply DifferentiableAt_of_exp_compose_linear_function' x
  apply DifferentiableAt_of_exp_compose_linear_function'' x

theorem calc_of_second_deriv_g :
   let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
   deriv (deriv g) = fun t => (a * b / (b - a)) * a * Real.exp (t * a)- a * b / (b - a)*b*Real.exp (t * b):= by
  intro g
  rw[calc_of_deriv_g]
  funext x
  rw[show (fun t ↦ a * b / (b - a) * (rexp (t * a) - rexp (t * b)))=
    (fun t ↦ a * b / (b - a) * (rexp (t * a)))- (fun t ↦ a * b / (b - a) * (rexp (t * b))) by
      simp[mul_sub];congr]
  rw[deriv_sub]
  congr
  · field_simp
    simp[specialize_of_deriv_of_exp,←mul_assoc];ring
  ----repeat(It is similar cases)
  field_simp
  simp[specialize_of_deriv_of_exp,←mul_assoc];ring
  ---Differentiable
  have :(fun t ↦ a * b / (b - a) * rexp (t * a)) =(fun t ↦ a * b / (b - a) * rexp (a * t)) :=by
    funext x
    simp[mul_comm]
  · rw[this]
    simp[DifferentiableAt_of_exp_compose_linear_function]
  simp[Const_DifferentiableAt_of_exp_compose_linear_function'']

theorem hg_pos (ha : a < b)(ha_nonpos:a ≤ 0)(hb_nonneg: b ≥ 0):
    let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
    ∀ x, 0 < g x := by
  intro g x
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
  --apply lemma 'exp',then prove g(x)>0 for any x ,first we should unfold the 'p' and 'g'
  rw[h_one_minus_p] at exp
  unfold p at exp
  calc
    0 < rexp (-a / (b - a) * (x * b) + b / (b - a) * (x * a)) := by
      exact exp_pos (-a / (b - a) * (x * b) + b / (b - a) * (x * a))
    _ ≤ -a / (b - a) * rexp (x * b) + b / (b - a) * rexp (x * a) := by exact exp x
    _ = b / (b - a) * rexp (x * a) - a / (b - a) * rexp (x * b) := by ring

theorem hg_pos' (ha : a < b)(ha_nonpos:a ≤ 0)(hb_nonneg: b ≥ 0):∀ x,b * rexp (a * x) - a * rexp (b * x) >0 := by
  intro x
  have h1: b-a >0 := by linarith
  have h:(b / (b - a)) * Real.exp (x * a) - (a / (b - a)) * Real.exp (x * b) >0 := by
    apply hg_pos <;> try assumption
  have :(b-a)*(b / (b - a) * rexp (x * a) - a / (b - a) * rexp (x * b) ) >0 := by
    simp[h]
    linarith
  field_simp at this
  exact this

theorem Differentiable_of_g:
    let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
    Differentiable ℝ g :=  by
  apply Differentiable.sub ---分别证明两部分可导
  · apply Differentiable.const_mul
    simp
  apply Differentiable.const_mul
  simp

theorem calc_of_deriv_f(ha : a < b)(ha_nonpos:a ≤ 0)(hb_nonneg: b ≥ 0):
    let f := fun t => φ t a b
    let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
    deriv f = deriv g / g := by
    intro f g
    ext x
    have h_comp : f = Real.log ∘ g := by
      funext t
      simp [f, g, φ]
    rw [h_comp]
    apply deriv.log
    -- g 可导
    apply Differentiable_of_g
    -- g x ≠ 0
    exact Ne.symm (ne_of_lt (hg_pos ha ha_nonpos hb_nonneg x))

theorem Differentiable_of_f(ha : a < b)(ha_nonpos:a ≤ 0)(hb_nonneg: b ≥ 0):
    let f := fun t => φ t a b
    Differentiable ℝ f :=  by
  intro f
  let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
  have :Differentiable ℝ g :=  by
    apply Differentiable.sub ---分别证明两部分可导
    · apply Differentiable.const_mul
      simp
    apply Differentiable.const_mul
    simp
  refine Differentiable.log this ?_
  intro x
  have :  b / (b - a) * rexp (x * a) - a / (b - a) * rexp (x * b) > 0 := by
    apply hg_pos <;> try assumption
  linarith

theorem calc_of_derivwithin_f (ha : a < b)(ha_nonpos:a ≤ 0)(hb_nonneg: b ≥ 0):
    let f := fun t => φ t a b
    let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
    ∀ t > 0, ∀ c ∈ Set.Ioo 0 t,derivWithin f (Icc 0 t) c =(deriv g / g) c:= by
  intro f g t ht c hc
  have :derivWithin f (Ioo 0 t) c =derivWithin f (Icc 0 t) c := by
    have h1:  (Ioo 0 t) ∈ 𝓝 c := by
      apply isOpen_iff_mem_nhds.mp
      exact isOpen_Ioo
      exact hc
    have h2:  (Icc 0 t) ∩ (Ioo 0 t) = (Ioo 0 t):= by
      ext x
      simp
      intro hx hxt
      constructor
      linarith;linarith
    have :derivWithin f ((Icc 0 t)∩(Ioo 0 t))  c =derivWithin f (Icc 0 t) c :=by
      apply derivWithin_inter h1
    rw[h2]  at this
    rw[this]
  rw[←this]
  apply Eq.trans
  apply derivWithin_of_isOpen (by exact isOpen_Ioo) hc
  have :deriv f = deriv g / g  := by
    apply calc_of_deriv_f  <;> try assumption
  simp[this]

theorem Differentiable_of_deriv_g:
    let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
    Differentiable ℝ (deriv g ):=  by
  intro g x
  rw[calc_of_deriv_g]
  simp[mul_sub]
  have :(fun t ↦ a * b / (b - a) * rexp (t * a)) =(fun t ↦ a * b / (b - a) * rexp (a * t)) :=by
    funext x
    simp[mul_comm]
  apply DifferentiableAt.sub
  · rw[this]
    simp[DifferentiableAt_of_exp_compose_linear_function]
  · simp[Const_DifferentiableAt_of_exp_compose_linear_function'']

theorem derivwithin_f_eq_deriv_f_in_nhds (ha : a < b)(ha_nonpos:a ≤ 0)(hb_nonneg: b ≥ 0):
    ∀ t > 0, ∀ c ∈ Set.Ioo 0 t, derivWithin (fun t ↦ φ t a b) (Icc 0 t) =ᶠ[𝓝 c] deriv fun t ↦ φ t a b:= by
  intro t ht c hc
  simp at hc
  have :min (c/2) ((t-c)/2) >0 := by
     apply lt_min <;> linarith
  apply Eventually.mono
  exact eventually_abs_sub_lt c this
  intro x hx
  unfold abs at hx
  simp at hx
  have : x ∈ Set.Ioo 0 t := by
    simp
    constructor
    rcases hx with ⟨h1,h2,h3⟩
    rcases h1 with ⟨h11,h12⟩
    linarith
    linarith
  apply Eq.trans
  apply calc_of_derivwithin_f <;> try assumption
  rw[calc_of_deriv_f] <;> try assumption

theorem calc_of_second_deriv_f (ha : a < b)(ha_nonpos:a ≤ 0)(hb_nonneg: b ≥ 0) :
    let f := fun t => φ t a b
    ∀ x, deriv (deriv f) x ≤ (b - a)^2 / 4 := by
  let g := fun t => (b / (b - a)) * Real.exp (t * a) - (a / (b - a)) * Real.exp (t * b)
  intro f  x
  have :deriv f = deriv g / g := by
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
    exact Ne.symm (ne_of_lt (hg_pos ha ha_nonpos hb_nonneg x))
  have :deriv (deriv f)  = deriv (deriv g)  / g  - (deriv g  / g ) ^ 2 := by
    funext x
    rw[this,deriv_div]
    have :(deriv (deriv g) / g - (deriv g / g) ^ 2) x = (deriv (deriv g) / g) x -((deriv g / g) ^ 2) x := by simp
    simp[this]
    rw[←div_sub_div_same]
    field_simp[show (deriv g x * deriv g x / g x ^ 2)=((deriv g x / g x) ^ 2) by field_simp]
    ----可微性证明
    apply Differentiable_of_deriv_g
    · unfold g
      rw[show (fun t ↦ b / (b - a) * rexp (t * a) - a / (b - a) * rexp (t * b))=((fun t ↦ b / (b - a) * rexp (t * a))
      -((fun t ↦a / (b - a) * rexp (t * b)))) by congr]
      apply DifferentiableAt.sub
      rw[show (fun t ↦ b / (b - a) * rexp (t * a)) = (fun t ↦ b / (b - a) * rexp (a * t)) by simp[mul_comm]]
      apply DifferentiableAt_of_exp_compose_linear_function' x
      apply DifferentiableAt_of_exp_compose_linear_function'' x
    -- g x ≠ 0
    exact Ne.symm (ne_of_lt (hg_pos ha ha_nonpos hb_nonneg x))
  -----next we unfold the equation
  ---hard work
  rw[this,calc_of_second_deriv_g,calc_of_deriv_g]
  unfold g
  field_simp
  simp
  rw[div_div]
  rw[div_div_div_eq]
  simp [mul_assoc, mul_comm, mul_left_comm]
  suffices a * (b * (a * rexp (a * x) - b * rexp (b * x))) / ((b - a) * ((b * rexp (a * x) - a * rexp (b * x)) / (b - a))) -
      (a * (b * ((b - a) * (rexp (a * x) - rexp (b * x)))) / ((b - a) * (b * rexp (a * x) - a * rexp (b * x)))) ^ 2
      ≤(b - a) ^ 2 / 4 by linarith
  rw[div_pow]
  have : (a * (b * ((b - a) * (rexp (a * x) - rexp (b * x))))) ^ 2 / ((b - a) * (b * rexp (a * x) - a * rexp (b * x))) ^ 2
      = (a * (b * (rexp (a * x) - rexp (b * x)))) ^ 2 / ((b * rexp (a * x) - a * rexp (b * x))) ^ 2:=by
    have h11:(a * (b * ((b - a) * (rexp (a * x) - rexp (b * x))))) ^ 2
        =(b-a)^2 *(a * (b * (rexp (a * x) - rexp (b * x)))) ^ 2 := by field_simp
    have h12 :  ((b - a) * (b * rexp (a * x) - a * rexp (b * x))) ^ 2
        =(b-a)^2 *((b * rexp (a * x) - a * rexp (b * x))) ^ 2 := by field_simp
    simp[h11,h12]
    refine
      IsUnit.mul_div_mul_left ?_ ((a * (b * (rexp (a * x) - rexp (b * x)))) ^ 2)
        ((b * rexp (a * x) - a * rexp (b * x)) ^ 2)
    simp;linarith[ha]
  rw[this]
  have : a * (b * (a * rexp (a * x) - b * rexp (b * x))) / ((b - a) * ((b * rexp (a * x) - a * rexp (b * x)) / (b - a)))
      = a * (b * (a * rexp (a * x) - b * rexp (b * x))) /((b * rexp (a * x) - a * rexp (b * x))):= by
      field_simp
      rw[mul_comm]
      refine
        IsUnit.mul_div_mul_left ?_ (a * b * (a * rexp (a * x) - b * rexp (b * x)))
          (b * rexp (a * x) - a * rexp (b * x))
      simp;linarith[ha]
  rw[this] -----we can only simp step by step in this stupid way, because the inequality is so complex.
  rw[div_sub_div]
  field_simp
  have :(a * rexp (a * x) - b * rexp (b * x))* (b * rexp (a * x) - a * rexp (b * x)) -
      a * b * (rexp (a * x) - rexp (b * x)) ^ 2 = -(a - b) ^ 2 * rexp (a * x)*rexp (b * x) :=by
    rw[mul_sub,sub_mul,sub_mul,sub_sq,mul_add,mul_sub]
    field_simp
    have :-(rexp (a * x) * rexp (x * b) * (a - b) ^ 2) =
        -rexp (a * x) * rexp (x * b) *a^2 -rexp (a * x) * rexp (x * b) * b^2 +rexp (a * x) * rexp (x * b) * 2*a*b
        := by
      simp[sub_sq,mul_sub,mul_add]
      field_simp
      ring
    rw[this]
    field_simp
    ring
  rw[this]
  ----now we get the equation in 'zhihu' ，next we need to apply some inequality
  rw[show (a * b * (-(a - b) ^ 2 * rexp (a * x) * rexp (b * x)))=
      (b-a)^2 *- (a * b* rexp (a * x) * rexp (b * x)) by ring]
  rw [←div_one ((b - a) ^ 2)]
  apply (div_le_div_iff₀ (sq_pos_of_pos (hg_pos' ha ha_nonpos hb_nonneg x)) (by norm_num)).mpr
  norm_num
  rw[←sub_nonpos]
  field_simp
  apply mul_nonpos_of_nonneg_of_nonpos
  positivity
  rw[sub_sq]
  suffices (b * a * rexp (a * x) * rexp (b * x) * 4) +
    ((b * rexp (a * x)) ^ 2 - 2 * (b * rexp (a * x)) * (a * rexp (b * x)) + (a * rexp (b * x)) ^ 2) ≥ 0 by linarith
  have :b * a * rexp (a * x) * rexp (b * x) * 4 +
    ((b * rexp (a * x)) ^ 2 - 2 * (b * rexp (a * x)) * (a * rexp (b * x)) + (a * rexp (b * x)) ^ 2)=
    ((b * rexp (a * x)) ^ 2 + 2 * (b * rexp (a * x)) * (a * rexp (b * x)) + (a * rexp (b * x)) ^ 2):= by
    field_simp
    ring
  rw[this,←add_sq]
  positivity
  · apply ne_of_gt
    apply hg_pos' ha ha_nonpos hb_nonneg
  · apply ne_of_gt
    apply sq_pos_of_pos
    apply hg_pos' ha ha_nonpos hb_nonneg

theorem Differentiable_of_deriv_f(ha : a < b)(ha_nonpos:a ≤ 0)(hb_nonneg: b ≥ 0):
    let f := fun t => φ t a b
    Differentiable ℝ (deriv f ):=  by
  intro f
  rw[calc_of_deriv_f]
  refine Differentiable.div ?_ ?_ ?_
  --- goal1 :Differentiable ℝ (deriv fun t ↦ b / (b - a) * rexp (t * a) - a / (b - a) * rexp (t * b))
  apply Differentiable_of_deriv_g
  ---goal 2:Differentiable ℝ fun t ↦ b / (b - a) * rexp (t * a) - a / (b - a) * rexp (t * b)
  apply  Differentiable_of_g
  -- g x ≠ 0
  intro x
  exact Ne.symm (ne_of_lt (hg_pos ha ha_nonpos hb_nonneg x ));apply ha ; apply ha_nonpos ; apply hb_nonneg


end lemma_about_deriv_contdiff

theorem estimation (ha : a < b)(ha_nonpos:a ≤ 0)(hb_nonneg: b ≥ 0) : ∀ t > 0, φ t a b ≤ t^2 * (b - a)^2 / 8 := by
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
    --apply lemma 'exp',then prove g(x)>0 for any x ,first we should unfold the 'p' and 'g'
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
    simp [f,φ]
    field_simp[show b-a ≠ 0 by linarith]
    simp
  have hf'0 : deriv f 0 = 0 := by
    rw [h_deriv_f_eq]
    have hg0 : g 0 = 1 := by
      simp[g]
      field_simp
      simp[show b-a ≠ 0 by linarith]
    have hg'0 : deriv g 0 = 0 := by
      unfold g
      field_simp
      simp [deriv_div_const]
      left
      rw[show (fun x ↦ b * rexp (a * x) - a * rexp (b * x)) = ((fun x ↦ b * rexp (a * x))-(fun x ↦ a * rexp (b * x))) by congr]
      rw[deriv_sub,deriv_of_exp,deriv_of_exp]
      simp[mul_comm]
      exact DifferentiableAt_of_exp_compose_linear_function  0
      exact DifferentiableAt_of_exp_compose_linear_function  0
    simp;left;exact hg'0
  have hf_cont_diff_on : ContDiffOn ℝ 1 f (Set.Icc 0 t) := by
    apply ContDiffOn.log
    { apply ContDiff.contDiffOn; apply ContDiff.sub;apply ContDiff_of_exp;apply ContDiff_of_exp' }
    intro x _; linarith [hg_pos x]
  have hf'_diff_on : DifferentiableOn ℝ (iteratedDerivWithin 1 f (Set.Icc 0 t)) (Set.Ioo 0 t) := by
    have h_f_is_C2 : ContDiff ℝ 2 f := by
      apply ContDiff.log
      { apply ContDiff.sub;apply ContDiff2_of_exp ;apply ContDiff2_of_exp'}
      intro x; linarith [hg_pos x]
    have hf'_diff_on' : DifferentiableOn ℝ (iteratedDerivWithin 1 f (Set.Icc 0 t)) (Set.Icc 0 t) := by
      apply ContDiffOn.differentiableOn_iteratedDerivWithin
      exact ContDiff.contDiffOn h_f_is_C2
      norm_num
      exact uniqueDiffOn_Icc ht
    have :(Set.Ioo 0 t)≤ (Set.Icc 0 t) := by
      intro x hx;
      simp at hx
      rcases hx with ⟨h1,h2⟩
      constructor
      linarith;linarith
    exact DifferentiableOn.mono hf'_diff_on' this
  have hf'' : ∀ s, deriv (deriv f) s ≤ (b - a)^2 / 4 := by
    apply calc_of_second_deriv_f <;> try assumption
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
    unfold f
    apply Eq.trans
    apply iteratedDerivWithin_eq_iterate ----iteratedDerivWithin to DerivWithin
    simp
    apply Eq.trans
    apply DifferentiableAt.derivWithin  ---derivWithin to deriv
    have h1:derivWithin (fun t ↦ φ t a b) (Icc 0 t) =ᶠ[𝓝 c] deriv fun t ↦ φ t a b := by
      apply derivwithin_f_eq_deriv_f_in_nhds <;> try assumption
    have h2:DifferentiableAt ℝ (deriv (fun t ↦ φ t a b) ) c:=by
      apply Differentiable_of_deriv_f  <;> try assumption
    exact (EventuallyEq.differentiableAt_iff (id (EventuallyEq.symm h1))).mp h2
    apply uniqueDiffOn_Icc ht
    constructor;linarith;linarith
    have :derivWithin (fun t ↦ φ t a b) (Icc 0 t) c=  deriv (fun t ↦ φ t a b) c:= by
      refine DifferentiableAt.derivWithin ?_ ?_
      apply Differentiable_of_f <;> try assumption
      apply uniqueDiffOn_Icc ht
      constructor;linarith;linarith
    refine EventuallyEq.deriv_eq ?_
    apply derivwithin_f_eq_deriv_f_in_nhds <;> try assumption



  have taylor01 :(PolynomialModule.eval t) (taylorWithin (fun t ↦ φ t a b) 1 (Set.Icc 0 t) 0)
  =0 := by
    rw [taylorWithin, PolynomialModule.eval, Finset.sum_range_succ]
    simp
-- taylorCoeffWithin 1 f (Icc 0 t) 0 = deriv f 0 / 1!
    have hdf0 : deriv f 0 = 0 := by
      rcases hf'0 with h1 | h1
      ·
        rw [h_deriv_f_eq]
        simp [h1]
      · -- g 0 = 0（实际上不会发生，因为 hg_pos 0 > 0）
        exfalso
        have := hg_pos 0
        linarith
    have h0 : taylorCoeffWithin (fun t ↦ φ t a b) 0 (Icc 0 t) 0 = 0 := by
        simpa [taylorCoeffWithin, hf0]
    have h1 : taylorCoeffWithin (fun t ↦ φ t a b) 1 (Icc 0 t) 0 = 0 := by
        simp [taylorCoeffWithin]
        have : derivWithin (fun t ↦ φ t a b) (Icc 0 t) 0 = deriv f 0 := by
          apply DifferentiableAt.derivWithin
          · apply Differentiable_of_f <;> try assumption
          · apply uniqueDiffOn_Icc ht
            constructor; linarith; linarith
        rw [this, hdf0]
    simp [h0, h1, Finsupp.sum]
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

theorem Hoeffding_lemma (X : Ω → ℝ)(h_measurable:Measurable X) (h0  : μ[X] = 0)
    (hbdd : ∀ω,a ≤ X ω ∧ X ω ≤ b)(ha :a <b) :∀t > 0 ,μ[fun ω => exp (t * X ω)] ≤ exp (t^2 * (b - a)^2 / 8) := by
  have leammah1: ∀ (ω : Ω), X ω ∈ Icc a b := by
      intro ω
      exact ⟨(hbdd ω).1,(hbdd ω).2⟩
  rcases a_nonpos_and_b_nonneg μ a b X h_measurable leammah1 h0 with ⟨ha_nonpos, hb_nonneg⟩
  ---Using convexity for the estimation of exp(tX)
  intro t ht
  have hX_bdd : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ max |a| |b| := by
        filter_upwards with ω
        have := leammah1 ω
        simp only [norm_eq_abs]
        simp [abs_le]
        simp [abs]
        simp_all [hbdd ω]
        by_cases h: X ω ≥ 0
        · right
          linarith
        · push_neg at h
          left
          right
          linarith
  have hX_int : Integrable X μ := by
        exact Integrable.of_bound h_measurable.aestronglyMeasurable (max |a| |b|) hX_bdd
  have h1:∀ ω , exp (t * X ω) ≤ (b - X ω) / (b - a) * exp (t * a) + (X ω - a) / (b - a) * exp (t * b) := by
    intro ω
    have hX : X ω ∈ Icc a b := leammah1 ω
    have h_exp_bdd : ∀ x ∈ Icc a b, exp (t * x) ≤ (b - x) / (b - a) * exp (t * a) + (x - a) / (b - a) * exp (t * b) := by
      intro x hx
      have h00: a≤ x ∧ x≤ b := by simp [Icc]  at hx; exact hx
      have h_jensen := (convexOn_exp).2
      have h1: t * a ∈ Set.univ := by simp
      have h2: t * b ∈ Set.univ := by simp
      have ht_pos : 0 < t := by linarith
      have h3 : t * x ∈ Icc (t * a) (t * b) := by
        have h₁ : t * x ≤ t * b := by
          apply mul_le_mul_of_nonneg_left (hx.2) (le_of_lt ht_pos)
        have h₂ : t * a ≤ t * x := by
          apply mul_le_mul_of_nonneg_left (hx.1) (le_of_lt ht_pos)
        exact ⟨h₂, h₁⟩
      have hp_pos : 0 ≤ (b - x) / (b - a) := by
        apply div_nonneg
        simp
        exact h00.2
        linarith
      have hp_pos' :0 ≤ (x - a) / (b - a) := by
        apply div_nonneg
        simp
        exact h00.1
        linarith
      have h4 : exp (t * x) ≤ (b - x) / (b - a) * exp (t * a) + (x - a) / (b - a) * exp (t * b) := by
        have h0₁: (b - a) ≠ 0 := by linarith
        have h₁: (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
          field_simp
          ring_nf
        have h := h_jensen h1 h2 hp_pos hp_pos' h₁
        simp at h
        have funxt:(b - x) / (b - a) * (t * a) + (x - a) / (b - a) * (t * b)= t * x := by
          field_simp
          ring_nf
        rw[funxt] at h
        exact h
      exact h4
    exact h_exp_bdd (X ω) hX
  ----两边同时取期望
  have h2:μ[fun ω => exp (t * X ω)] ≤ b / (b - a) * exp (t * a) - a / (b - a) * exp (t * b) := by
    have inter: ∫ (x : Ω), exp (t * X x) ∂μ ≤ ∫ (x : Ω), (b - X x) / (b - a) * exp (t * a) + (X x - a) / (b - a) * exp (t * b) ∂μ := by
      apply integral_mono
      · have h_exp_bdd : ∀ᵐ x ∂μ, |rexp (t * X x)| ≤ max (rexp (t * a)) (rexp (t * b)) := by
          filter_upwards [hX_bdd] with x hx
          have h₁ : t * X x ≤ t * b := by
            apply mul_le_mul_of_nonneg_left (hbdd x).2 (le_of_lt ht)
          have h₂ : t * a ≤ t * X x := by
            apply mul_le_mul_of_nonneg_left (hbdd x).1 (le_of_lt ht)
          have h_min : t * X x ∈ Icc (t * a) (t * b) := ⟨h₂, h₁⟩
          have : rexp (t * X x) ≤ max (rexp (t * a)) (rexp (t * b)) := by
            exact le_max_of_le_right (Real.exp_le_exp.mpr  h₁ )
          have tth1: 0 ≤ rexp (t * X x) := by
            apply Real.exp_pos _ |>.le
          rw [abs_of_nonneg tth1]
          exact this
        exact Integrable.of_bound (Measurable.exp (h_measurable.const_mul t)).aestronglyMeasurable (max (rexp (t * a)) (rexp (t * b)))  h_exp_bdd
      · apply Integrable.add
        · have : (fun x ↦ (b - X x) / (b - a) * rexp (t * a))
      = (fun x ↦ (b / (b - a)) * rexp (t * a) - (X x / (b - a)) * rexp (t * a)) := by
            funext x
            field_simp
          rw [this]
          apply Integrable.sub
          · exact integrable_const _
          · have : (fun x ↦ X x / (b - a) * rexp (t * a)) = (fun x ↦ X x * (1 / (b - a) * rexp (t * a))) := by
             funext x
             field_simp
            rw [this]
            exact Integrable.mul_const hX_int ((1 : ℝ) / (b - a) * rexp (t * a))
        · have : (fun x ↦ (X x - a) / (b - a) * rexp (t * b))
      = (fun x ↦ X x * (1 / (b - a) * rexp (t * b)) - a / (b - a) * rexp (t * b)) := by
            funext x
            field_simp
          rw [this]
          apply Integrable.sub
          · exact Integrable.mul_const hX_int ((1 : ℝ) / (b - a) * rexp (t * b))
          · exact integrable_const _
      · exact h1
    apply le_trans inter
    rw [ show (fun ω ↦ (b - X ω) / (b - a) * exp (t * a) + (X ω - a) / (b - a) * exp (t * b))
          = (fun ω ↦ (b / (b-a) * exp (t * a) - a / (b-a) * exp (t * b))+ X ω * ((exp (t * b) - exp (t * a)) / (b-a))) by funext; field_simp; ring]
    rw [ integral_add, integral_const] at ⊢
    -- 证明可积性
    · have hμ : μ.real univ = 1 := by simp
      rw [hμ, one_smul, ←add_zero (b / (b - a) * rexp (t * a) - a / (b - a) * rexp (t * b))]
      have hX : ∫ (a_1 : Ω), X a_1 * ((rexp (t * b) - rexp (t * a)) / (b - a)) ∂μ = ((rexp (t * b) - rexp (t * a)) / (b - a)) * ∫ (a_1 : Ω), X a_1 ∂μ := by
        rw [integral_mul_const]
        ring
      rw [hX, h0, mul_zero, add_zero]
    · exact integrable_const _
    · exact Integrable.mul_const hX_int _

  have h :(b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b) >0 := by
    simp
    let htt:= hg_pos ha ha_nonpos hb_nonneg t
    simp at htt
    exact htt
  have h3:(b / (b - a)) * exp (t * a) - (a / (b - a)) * exp (t * b) ≤ exp (t^2 * (b - a)^2 / 8) := by
    apply (log_le_iff_le_exp h).mp
    apply estimation <;> try assumption
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
    apply Integrable.hasFiniteIntegral
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
