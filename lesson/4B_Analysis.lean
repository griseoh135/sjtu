import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Calculus.Gradient.Basic


open Set Filter Topology

/-
# Introduction of ENNReal and EReal
-/
section Number_set

#check Real
#check ENNReal
#check EReal

#check Real.toEReal
#check EReal.toReal

example {a b c d : ℝ} (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  exact add_lt_add h1 h2

example {a b c d : EReal} (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  exact EReal.add_lt_add h1 h2

example {a b c d : ℝ} (h1 : a < b) (h2 : c < d) : a < b + d - c := by
  linarith

example {a b c d : EReal} (h1 : a < b) (h2 : c < d) : a < b + d - c := by
  sorry

example : Bot.bot = (⊥:EReal) := rfl

#check Top.top
example : (1:EReal) + Bot.bot = Bot.bot := rfl
example : (⊤:EReal) * 0  = 0 := mul_eq_zero_of_right ⊤ rfl
example : (⊤:EReal) + (⊥:EReal) = ⊥ := rfl
example : (⊤ : EReal) - (⊤ : EReal) = ⊥ := rfl
example : EReal.toReal ⊥ = 0 := rfl


example {x y: EReal} (hx : x + y > 1) : x > 1 - y := by
  have hy_not_bot : y ≠ ⊥ := by sorry
  have hx_not_bot : x ≠ ⊥ := by sorry

  sorry




end Number_set



/-
# Introduction of Euclidean space
-/
section EuclideanSpace

variable {n : Type _}[Fintype n]{x : EuclideanSpace ℝ n}
#check EuclideanSpace.norm_eq

#check EuclideanSpace
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]



end EuclideanSpace



/-
# Definition of Filter
* Definition and examples of Filter
* `atTop` and `𝓝`
-/
section Filter_def

#check Filter

/-
* Examples of Filter
-/
#check atTop
#check nhds

example : {n:ℕ | n > 2} ∈ atTop := by
  simp [atTop]
  exact mem_iInf_of_mem (Nat.succ 2) fun ⦃a⦄ a ↦ a

example : {n:ℕ | n ≥ 2} ∈ atTop := by
  simp [atTop]
  exact mem_iInf_of_mem 2 fun ⦃a⦄ a ↦ a

variable {E : Type*} [MetricSpace E]

#check Ioo_mem_nhds
#check Ioc_mem_nhds
#check Ico_mem_nhds
#check Icc_mem_nhds

example (x : ℝ) (r : ℝ) (hr : r > 0) : Ioo (x-r) (x+r) ∈ nhds x := by
  refine Ioo_mem_nhds ?_ ?_
  <;> linarith

example (x : ℝ) (r : ℝ) (hr : r > 0) : Ioo (x-r) (x+r+1) ∈ nhds x := by
  refine Ioo_mem_nhds ?_ ?_
  <;> linarith

example (x : ℝ) (r : ℝ) (hr : r > 0) : Ioc (x-r) (x+r+1) ∈ nhds x := by
  refine Ioc_mem_nhds ?_ ?_
  <;> linarith

#check exists_open_set_nhds
#check IsCompact.elim_nhds_subcover

-- #check normed_field

end Filter_def



/-
# Definition of Limit
* Definition and examples of limit
-/
section limit_def
variable {x : ℕ → ℝ} (α β: Type*) (f: α → β) (F1: Filter α) (F2: Filter β)


/-
* Pre-image of a mapping
The preimage of s : Set β by f : α → β, written f ⁻¹' s,
is the set of x : α such that f x ∈ s.
-/
#check preimage
example : x ⁻¹' (Ioo (-1) 1) = {n:ℕ | x n ∈ (Ioo (-1) 1)} := by rfl
/-
* Composition of preimages
preimage_comp
-/
#check preimage_comp
/-
* The forward map of a filter
Note that this is not a mapping, it is defined as a filter.
-/
#check Filter.map
#check Filter.map x atTop
example :(Ioo (-1) 1) ∈ Filter.map x atTop ↔ x⁻¹' (Ioo (-1) 1) ∈ atTop := mem_map
example (V : Set ℝ): V ∈ Filter.map x atTop ↔ x⁻¹' V ∈ atTop := mem_map
/-
* Partial order of Filters: for two filters (F:Filter X) and (G:Filter X),
we define F ≤ G as: ∀ (a:Set X), a ∈ F → a ∈ G.
-/
#check le_def

/-
* Definition of Tendsto is based on the forward map and the partial order of filters.
-/
#check Tendsto f F1 F2
example (x0 : ℝ): Tendsto x atTop (𝓝 x0) ↔ Filter.map x atTop ≤ 𝓝 x0 := by
  rfl



/-
* A direct impression is that the preimage under `x` of any neighborhood of `x0`
  can fall into `atTop`. That is to say, if you give any neighhood around `x`, we can
  find a large enough `n` such that `x n ∈ Ioo (x0-1) (x0+1)`, which is exactly the
  `ε-N` definition of limit.
-/
example (x0 : ℝ) (h : Tendsto x atTop (𝓝 x0)) : x⁻¹' (Ioo (x0-1) (x0+1)) ∈ atTop := by
  sorry
  -- have h1: Filter.map x atTop ≤ 𝓝 x0 := h
  -- apply mem_map.1
  -- apply h1
  -- refine Ioo_mem_nhds ?_ ?_
  -- <;> linarith

/-
* In mathlib, there is an equivalent theorem of definition defined by filters and the
  `ε-N` definition. Note that this needs the concept of Metric Space.
-/
example (a : ℝ): Tendsto x atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - a| < ε := by
  exact Metric.tendsto_atTop

example (a : ℝ) :
    Tendsto x atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, x n ∈ Ioo (a - ε) (a + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis

  rw [this.tendsto_iff (nhds_basis_Ioo_pos a)]
  simp


/-
* An example of how to use filters to prove the theorems of limits.
-/
#check Tendsto.comp
#check preimage_comp
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) : Tendsto (g ∘ f) F H := by
    -- exact Tendsto.comp hg hf
    simp [Tendsto, LE.le] at *
    intro a ha
    rw [preimage_comp]
    specialize hg ha
    -- rw [mem_map] at hg
    exact hf hg

    -- rwa [mem_map] at hf


example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) : Tendsto (g ∘ f) F H :=
    -- exact Tendsto.comp hg hf
    -- simp [Tendsto, LE.le] at *
    fun _ ha => (hf (hg ha))
    -- exact fun ⟨a,ha⟩ => (hf (hg ha))
    -- intro a ha
    -- -- rw [preimage_comp]
    -- -- specialize hg ha
    -- -- rw [mem_map] at hg
    -- exact hf $ hg ha

/-
* One can construct a sub-sequence by a strict monotone mapping.
-/
example (a : ℝ) (hx : Tendsto x atTop (𝓝 a)) (φ : ℕ → ℕ) (hφ: StrictMono φ):
  Tendsto (x ∘ φ) atTop (𝓝 a) := by
  sorry

example {a b: ℝ} {x' : ℕ → ℝ} {y' : ℕ → ℝ} (hf : Tendsto x' atTop (𝓝 a))
  (hg : Tendsto y' atTop (𝓝 b)) : Tendsto (fun n => (x' n + y' n)) atTop (𝓝 (a + b)) := by
  exact Tendsto.add hf hg

example {a b: ℝ} {x' : ℕ → ℝ} {y' : ℕ → ℝ} (hf : Tendsto x' atTop (𝓝 a))
  (hg : Tendsto y' atTop (𝓝 b)) : Tendsto (fun n => (x' n) * (y' n)) atTop (𝓝 (a * b)) := by
  exact Tendsto.mul hf hg


/-
* Something will eventually happen.
-/
example (P : ℕ → Prop) : (∀ᶠ n in atTop, P n) ↔ {n | P n} ∈ atTop := .rfl
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ


end limit_def




/-
# Definition of Metric Space
* Definition of Metric Space, distance function
* Definition of (open) metric ball
-/
section Metric_space

variable {X : Type*}


variable {X : Type*} [MetricSpace X] (a b c : X)
#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

#check MetricSpace

/-
# Definition of Metric Ball
-/
variable (r : ℝ)
example : Metric.ball a r = { b | dist b a < r } := rfl
example : Metric.closedBall a r = { b | dist b a ≤ r } := rfl


example (u : ℕ → X) (a : X): Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε := by
  exact Metric.tendsto_atTop

example (u : ℕ → X): CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε := Metric.cauchySeq_iff

example :(∀ (u : ℕ → X), CauchySeq u → ∃ a, Tendsto u atTop (nhds a)) → CompleteSpace X :=
  Metric.complete_of_cauchySeq_tendsto

variable [CompleteSpace X]

end Metric_space




/-
# Definition of Normed Space
* Definition of additive commutative group equipped with a real-valued norm function
* Definition of Normed Space and Banach Space
-/
section Normed_space

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example (x : E) : 0 ≤ ‖x‖ := norm_nonneg x
example {x : E} : ‖x‖ = 0 ↔ x = 0 := norm_eq_zero
example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ := norm_smul a x

/-- A normed group is an additive group endowed with a norm for which `dist x y = ‖x - y‖` defines a
metric space structure. -/
example : MetricSpace E := by infer_instance


/- Banach Space is a complete normed space. -/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
/- Finite dimension vector space is complete. -/
example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance


end Normed_space



/-
# Definition of Inner Product Space
-/
section InnerProductSpace

#check InnerProductSpace

/-
* Inner product space
-/
variable {E : Type*}[SeminormedAddCommGroup E][InnerProductSpace ℝ E]
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂
#check inner

example {x y : E}: ⟪x+y, x+y⟫ = ⟪x,x⟫ + 2 * ⟪x,y⟫ + ⟪y,y⟫ := by
  exact real_inner_add_add_self x y

/-
* Hilbert space
-/
variable {E : Type*}[SeminormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]

end InnerProductSpace


/-
# Definition of open sets and closed sets
* Open and closed sets
* Closure of a set
* Open (closed) sets and filters
-/
section open_and_closed_sets
variable {X : Type*} [MetricSpace X] (a : X)
#check Metric.ball
#check Metric.closedBall
example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

#check IsClosed
example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) := isOpen_compl_iff.symm


/-
Open and closed sets, filters
-/
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff

#check closure
#check interior


end open_and_closed_sets



/-
# Continuity of functions on Metric Space
-/
section continuous_func

#check Continuous
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

/-
continuity and continuity?
-/
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity

#check ContinuousAt
#check ContinuousWithinAt
#check ContinuousOn
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
  Continuous f ↔ ContinuousOn f univ := by
    exact continuous_iff_continuousOn_univ

/-
continuity?
-/
variable {X : Type*}[MetricSpace X]
example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
  apply Continuous.comp'
  · simp_all only
  · apply Continuous.add
    · apply Continuous.pow
      apply continuous_id'
    · apply continuous_id'


end continuous_func



/-
# Definition of Continuous Linear Map
* Continuous linear map between two normed space
* Bounded linear map
* Banach–Steinhaus theorem
-/
section Continuous_linear_map
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-
A linear map is an operator satisfying
* `f(x + y) = f(x) + f(y)`
* `f(c • x) = c • f(x)`
-/

variable (f : E →L[𝕜] F)

#check LinearMap
#check ContinuousLinearMap


example : Continuous f := f.cont
example (x y : E) : f (x + y) = f x + f y := f.map_add x y
example (a : 𝕜) (x : E) : f (a • x) = a • f x := f.map_smul a x

example : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E


/-
On a normed space, continuous linear map is equivalent to a bounded linear map.
-/
example : Continuous f ↔ IsBoundedLinearMap 𝕜 f := by
  constructor
  · exact fun a ↦ ContinuousLinearMap.isBoundedLinearMap f
  · exact fun a ↦ ContinuousLinearMap.continuous f


/-
Norm of an operator.
-/
#check ContinuousLinearMap.opNorm
example (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x


/-
Banach-Steinhaus theorem
-/
example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by sorry


end Continuous_linear_map



/-
# Definition of derivative
* Frechet derivative and derivative
* differentiable
* gradient
-/
section Differential

variable {E F: Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` converges along the filter `L` This definition
is designed to be specialized for `L = 𝓝 x` (in `HasFDerivAt`), giving rise to the usual notion
of Fréchet derivative, and for `L = 𝓝[s] x` (in `HasFDerivWithinAt`), giving rise to
the notion of Fréchet derivative along the set `s`-/
#check HasFDerivAtFilter
#check HasFDerivAt
#check HasFDerivWithinAt

/- A function `f` is differentiable at a point `x` if it admits a derivative there (possibly
non-unique). -/
#check DifferentiableAt
/- A function `f` is differentiable at a point `x` within a set `s` if it admits a derivative
there (possibly non-unique). -/
#check DifferentiableWithinAt


/- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
#check fderiv
/- If `f` has a derivative at `x` within `s`, then `fderivWithin 𝕜 f s x` is such a derivative.
Otherwise, it is set to `0`. We also set it to be zero, if zero is one of possible derivatives. -/
#check fderivWithin


/- `DifferentiableOn 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`. -/
#check DifferentiableOn
/- `Differentiable 𝕜 f` means that `f` is differentiable at any point. -/
#check Differentiable

variable (f : E → F)
example : DifferentiableOn ℝ f univ ↔ Differentiable ℝ f := differentiableOn_univ



/- `f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`. -/
#check HasDerivAtFilter

/- `f` has the derivative `f'` at the point `x` within the subset `s`. -/
#check HasDerivWithinAt
/- `f` has the derivative `f'` at the point `x`. -/
#check HasDerivAt


/- Derivative of `f` at the point `x` within the set `s`, if it exists. -/
#check derivWithin
/- Derivative of `f` at the point `x`, if it exists -/
#check deriv



#check HasGradientAtFilter

#check HasGradientWithinAt
#check HasGradientAt

#check gradientWithin
#check gradient

end Differential



-- /-
-- # Elementary Integration
-- * Examples of integral
-- * The fundamental theorem of calculus
-- * Convolution
-- -/
-- section Integration

-- open Set Filter Topology MeasureTheory intervalIntegral Interval
-- -- this introduces the notation `[[a, b]]` for the segment from `min a b` to `max a b`

-- #check intervalIntegral

-- example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 := integral_id
-- example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, 1 / x) = Real.log (b / a) := integral_one_div h

-- example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
--     (h' : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
--   integral_eq_sub_of_hasDerivAt h h'


-- end Integration
