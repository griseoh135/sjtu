import Mathlib

-- set_option linter.unusedTactic false
-- set_option linter.unusedVariables false

-- ============ Introduction：基本数系的代数结构概览 ============

namespace AlgebraicStructuresOverview

-- 路径1：群论方向
-- Magma → Semigroup → Monoid → Group → AbelianGroup
#check Mul                   -- 乘法运算
#check Semigroup             -- 半群：具有结合律的乘法运算
#check Monoid                -- 幺半群：有单位元的半群
#check Group                 -- 群：有逆元的幺半群
#check CommGroup             -- 交换群：满足交换律的群
#check AddCommGroup          -- 加法交换群：使用加法记号的交换群

-- 路径2：环论方向
-- Ring → CommRing → IntegralDomain → Field
#check Ring                  -- 环：具有两个运算的代数结构
#check CommRing              -- 交换环：乘法满足交换律的环
#check IsDomain              -- 整环：无零因子的交换环
#check Field                 -- 域：每个非零元素都有乘法逆元的整环

-- 路径3：模论方向
-- Module → VectorSpace
#check Module                -- 模：环上的加法阿贝尔群配以标量乘法
#check FiniteDimensional     -- 有限维向量空间

-- 具体数系的代数结构实例
example : AddCommGroup ℤ := inferInstance
example : CommRing ℤ := inferInstance
example : IsDomain ℤ := inferInstance

noncomputable example : Field ℚ := inferInstance
noncomputable example : Field ℝ := inferInstance
noncomputable example : Field ℂ := inferInstance

-- 有限域的例子
example (p : ℕ) [Fact (Nat.Prime p)] : Field (ZMod p) := inferInstance

-- 多项式环
noncomputable example (R : Type*) [CommRing R] : CommRing (Polynomial R) := inferInstance

-- 矩阵环（非交换环的例子）
example (n : ℕ) (R : Type*) [Ring R] : Ring (Matrix (Fin n) (Fin n) R) := inferInstance

-- 模的例子
example (R : Type*) [Ring R] : Module R R := inferInstance

-- 任何阿贝尔群都是ℤ-模
example (A : Type*) [AddCommGroup A] : Module ℤ A := inferInstance

-- 向量空间的例子
example (F : Type*) [Field F] (n : ℕ) : Module F (Fin n → F) := inferInstance

-- 复数作为实向量空间
noncomputable example : Module ℝ ℂ := inferInstance

end AlgebraicStructuresOverview

-- ============ Part 1：群论方向 ============
-- 路径1：群论方向
-- Magma → Semigroup → Monoid → Group → AbelianGroup

namespace GroupTheoryPath

-- 1.1 Magma：最基础的代数结构
/-
定义：原群(Magma)是一个代数结构 (M, ·)，其中 M 是非空集合，· 是 M 上的二元运算
M × M → M，即对于任意 a, b ∈ M，都有 a · b ∈ M (封闭性)。
-/
-- Magma是配备了一个二元运算的集合，不要求任何公理
-- 注意：Mathlib4中没有单独的Magma类型类，而是使用Mul
namespace MagmaBasics

variable {α : Type*} [Mul α]

-- Magma的基本性质：仅有二元运算
#check (· * · : α → α → α)  -- 二元运算：α × α → α

-- Magma不要求任何公理，运算可以是任意的
-- 例如：减法运算在自然数上不满足结合律，但仍构成Magma

end MagmaBasics

-- 1.2 Semigroup：引入结合律
/-
定义：半群(Semigroup)是一个代数结构 (S, ·)，其中 S 是非空集合，· 是 S 上的二元运算，
且满足结合律：对于任意 a, b, c ∈ S，都有 (a · b) · c = a · (b · c)。
-/
-- Semigroup是满足结合律的Magma
-- 与Magma的区别：增加了结合律公理
namespace SemigroupBasics

variable {β : Type*} [Semigroup β]

-- Semigroup继承Magma的运算
#check Semigroup
-- 新增的核心性质：结合律
#check mul_assoc  -- 结合律：(a * b) * c = a * (b * c)

-- 结合律的意义：允许省略括号，使得运算顺序明确
example (a b c d : β) : a * b * c * d = a * (b * (c * d)) := by
  rw [mul_assoc, mul_assoc]

-- 结合律使得我们可以定义幂运算
-- 例如：a^n 的意义是明确的

end SemigroupBasics

-- 1.3 Monoid：引入单位元
/-
定义：幺半群(Monoid)是一个代数结构 (M, ·, e)，其中 (M, ·) 是半群，e ∈ M 是单位元，
满足：对于任意 a ∈ M，都有 e · a = a · e = a。
-/
-- Monoid是具有单位元的Semigroup
-- 与Semigroup的区别：增加了单位元的存在性和性质
namespace MonoidBasics

variable {α : Type*} [Monoid α]

-- Monoid继承Semigroup的所有性质
#check Monoid
-- 新增的核心性质：单位元
#check one_mul    -- 左单位元性质：1 * a = a
#check mul_one    -- 右单位元性质：a * 1 = a

-- 单位元的唯一性（可以证明）
theorem monoid_id_unique {e : α} (h1 : ∀ a, e * a = a) :
    e = 1 := by
  rw [← h1 1, mul_one]

-- 1.4 CommMonoid：引入交换律
/-
定义：交换幺半群(CommMonoid)是一个代数结构 (M, ·, e)，其中 (M, ·, e) 是幺半群，
且运算 · 满足交换律：对于任意 a, b ∈ M，都有 a · b = b · a。
-/
-- CommMonoid是满足交换律的Monoid
-- 与Monoid的区别：增加了交换律
variable {β : Type*} [CommMonoid β]

-- CommMonoid继承Monoid的所有性质
#check mul_comm   -- 交换律：a * b = b * a

-- 交换律与结合律的结合应用
example (a b c : β) : a * b * c = c * a * b := by
  rw [mul_assoc, mul_comm , mul_assoc, mul_comm ]

end MonoidBasics

-- 1.5 Group：引入逆元
/-
定义：群(Group)是一个代数结构 (G, ·, e, ⁻¹)，其中 (G, ·, e) 是幺半群，
⁻¹ 是逆元运算，满足：对于任意 a ∈ G，都有 a · a⁻¹ = a⁻¹ · a = e。
-/
-- Group是每个元素都有逆元的Monoid
-- 与Monoid的区别：增加了逆元的存在性和性质
namespace GroupBasics

variable {G : Type*} [Group G]

-- Group继承Monoid的所有性质
#check Group
-- 新增的核心性质：逆元
#check inv_mul_cancel -- 左逆元性质：a⁻¹ * a = 1
#check mul_inv_cancel -- 右逆元性质：a * a⁻¹ = 1

-- 群的重要性质
theorem group_mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  exact mul_inv_cancel a

theorem group_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
  exact mul_left_cancel h

-- 逆元的基本性质
theorem group_inv_inv (a : G) : (a⁻¹)⁻¹ = a := by
  exact inv_inv a

theorem group_mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  exact mul_inv_rev a b

-- 群运算的例子集合
namespace GroupExamples

variable {G : Type*} [Group G]

-- 例子1：基本群运算
example (a b : G) : a * b * b⁻¹ * a⁻¹ = 1 := by group

-- 例子2：逆元的逆元
example (a : G) : (a⁻¹)⁻¹ = a := by group

-- 例子3：单位元的性质
example (a : G) : a * 1 * a⁻¹ = 1 := by group

-- 例子4：结合律的应用
example (a b c : G) : (a * b) * c * c⁻¹ * b⁻¹ * a⁻¹ = 1 := by group

-- 例子5：交换与逆元的关系
example (x y : G) : x * y * x⁻¹ * y⁻¹ = 1 ↔ x * y = y * x := by
  constructor
  · intro h
    have : x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    rw [h, one_mul] at this
    exact this
  · intro h
    rw [h]
    group

-- 例子6：共轭运算
example (g h : G) : g * h * g⁻¹ * g = g * h := by group

-- 例子7：多个元素的组合
example (a b c d : G) : a * b * c * d * d⁻¹ * c⁻¹ * b⁻¹ * a⁻¹ = 1 := by group

-- 例子8：幂运算性质
example (a : G) : a * a * a⁻¹ = a := by group

end GroupExamples

end GroupBasics

-- 1.6 AbelianGroup：引入交换性
/-
定义：阿贝尔群(Abelian Group)是一个代数结构 (G, +, 0, -)，其中 (G, +, 0, -) 是群，
且运算 + 满足交换律：对于任意 a, b ∈ G，都有 a + b = b + a。
通常阿贝尔群使用加法记号，单位元记作 0，逆元记作 -a。
-/
-- AbelianGroup是满足交换律的Group
-- 与Group的区别：增加了交换律，通常使用加法记号
namespace AbelianGroupBasics

variable {A : Type*} [AddCommGroup A]

-- AbelianGroup继承Group的所有性质
#check add_comm        -- 交换律：a + b = b + a
#check neg_add_cancel  -- 逆元性质：-a + a = 0
#check zero_add        -- 单位元性质：0 + a = a

-- abel策略专门处理阿贝尔群的运算
example (a b c d : A) : (a + b) + (c + d) - (b + c) = a + d := by abel

example (x y z : A) : x + y + z - y = x + z := by abel

-- 阿贝尔群中的标量乘法
example (a b : A) : 2 • a + 3 • b - a = a + 3 • b := by abel

end AbelianGroupBasics

-- 群论的高级应用
namespace GroupAdvanced

variable {G : Type*} [Group G]

-- 共轭运算的定义和性质
def conjugate (g h : G) : G := g * h * g⁻¹

theorem conjugate_one (g : G) : conjugate g 1 = 1 := by
  unfold conjugate
  group

theorem conjugate_mul (g a b : G) :
    conjugate g (a * b) = conjugate g a * conjugate g b := by
  unfold conjugate
  group

-- 交换子的定义和性质
def commutator' (a b : G) : G := a * b * a⁻¹ * b⁻¹

theorem commutator_eq_one_iff (a b : G) :
    commutator' a b = 1 ↔ a * b = b * a := by
  simp [commutator']
  constructor
  · intro h
    have : a * b * a⁻¹ * b⁻¹ * b * a = b * a := by
      group
      exact commutatorElement_eq_one_iff_mul_comm.mp h
    rw [h, one_mul] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  · intro h
    rw [h]
    group

end GroupAdvanced

end GroupTheoryPath

-- ============ Part 2：环论方向 ============
-- 路径2：环论方向
-- Ring → CommRing → IntegralDomain → Field

namespace RingTheoryPath

-- 2.1 Ring：双运算结构
/-
定义：环(Ring)是一个代数结构 (R, +, ·, 0, 1)，其中：
1. (R, +, 0) 是阿贝尔群（加法结构）
2. (R, ·, 1) 是幺半群（乘法结构）
3. 乘法对加法满足左右分配律：a·(b+c) = a·b + a·c 和 (a+b)·c = a·c + b·c
-/
-- Ring是同时具有加法阿贝尔群结构和乘法幺半群结构的代数系统，
-- 且两个运算通过分配律相连接
namespace RingBasics

variable {R : Type*} [Ring R]

-- Ring的三重结构
-- 1. 加法阿贝尔群结构
#check add_assoc      -- 加法结合律
#check add_comm       -- 加法交换律
#check zero_add       -- 零元性质
#check neg_add_cancel -- 加法逆元

-- 2. 乘法幺半群结构
#check mul_assoc      -- 乘法结合律
#check one_mul        -- 乘法单位元
#check mul_one

-- 3. 分配律：连接加法和乘法的桥梁
#check mul_add        -- 左分配律：a * (b + c) = a * b + a * c
#check add_mul        -- 右分配律：(a + b) * c = a * c + b * c

-- 环的基本定理
theorem ring_zero_mul (a : R) : 0 * a = 0 := by
  exact zero_mul a

theorem ring_mul_zero (a : R) : a * 0 = 0 := by
  exact mul_zero a

theorem ring_neg_mul (a b : R) : (-a) * b = -(a * b) := by
  exact neg_mul a b

theorem ring_mul_neg (a b : R) : a * (-b) = -(a * b) := by
  exact mul_neg a b

theorem ring_sub_eq_add_neg (a b : R) : a - b = a + (-b) := by
  exact sub_eq_add_neg a b

theorem ring_neg_neg (a : R) : -(-a) = a := by
  exact neg_neg a

theorem ring_two_mul (a : R) : 2 * a = a + a := by
  exact two_mul a

end RingBasics

-- 2.2 CommRing：引入乘法交换律
/-
定义：交换环(CommRing)是一个环 (R, +, ·, 0, 1)，其中乘法运算 · 满足交换律：
对于任意 a, b ∈ R，都有 a · b = b · a。
-/
-- CommRing是乘法满足交换律的Ring
-- 与Ring的区别：增加了乘法交换律
namespace CommRingBasics

variable {R : Type*} [CommRing R]

-- CommRing继承Ring的所有性质
#check mul_comm  -- 新增的核心性质：乘法交换律

-- ring策略专门处理交换环中的多项式运算
example (a b c d : R) : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by ring

example (a b : R) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

example (a b : R) : (a + b) * (a - b) = a^2 - b^2 := by ring

-- 结合其他策略的使用
example (a b c d : R) (h : c = d * a + b) (h' : b = a * d) : c = 2 * a * d := by
  rw [h, h']
  ring

-- 多项式展开
example (a b : R) : (a + b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3 := by ring

-- 因式分解验证
example (a b : R) : a^3 - b^3 = (a - b) * (a^2 + a*b + b^2) := by ring

-- 复杂的代数恒等式
example (x y z : R) : (x + y + z)^2 = x^2 + y^2 + z^2 + 2*x*y + 2*x*z + 2*y*z := by ring

-- 与nth_rewrite结合使用
example (a b c : R) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

-- 环论计算的例子集合
namespace RingExamples

variable {R : Type*} [CommRing R]

-- 二项式定理的验证
theorem binomial_square (a b : R) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

theorem binomial_cube (a b : R) :
    (a + b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3 := by ring

-- 因式分解
theorem difference_of_squares (a b : R) : a^2 - b^2 = (a + b) * (a - b) := by ring

theorem sum_of_cubes (a b : R) :
    a^3 + b^3 = (a + b) * (a^2 - a*b + b^2) := by ring

-- 恒等式验证
example (x y : R) : (x + y)^4 - (x - y)^4 = 8*x*y*(x^2 + y^2) := by ring

example (a b c : R) : (a + b + c)^2 - a^2 - b^2 - c^2 = 2*(a*b + b*c + c*a) := by ring

end RingExamples

end CommRingBasics

-- 2.3 IntegralDomain：引入无零因子性
/-
定义：整环(Integral Domain)是一个交换环 (R, +, ·, 0, 1)，其中 0 ≠ 1，
且无零因子：对于任意 a, b ∈ R，若 a · b = 0，则 a = 0 或 b = 0。
-/
-- IntegralDomain是无零因子的CommRing
-- 与CommRing的区别：增加了无零因子性质
-- 注意：在Mathlib4中使用IsDomain而不是IntegralDomain
namespace IntegralDomainBasics

variable {D : Type*} [CommRing D] [IsDomain D]

-- IntegralDomain继承CommRing的所有性质
-- 新增的核心性质：无零因子性
#check mul_eq_zero    -- a * b = 0 ↔ a = 0 ∨ b = 0

-- 消去律（无零因子性的直接后果）
theorem integral_domain_cancel {a b c : D} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  exact mul_left_cancel₀ ha h

-- 幂运算的性质
theorem integral_domain_pow_eq_zero {a : D} {n : ℕ} (hn : n > 0) :
    a^n = 0 ↔ a = 0 := by
  rw [pow_eq_zero_iff]
  exact Nat.ne_zero_of_lt hn

-- 重要推论
theorem integral_domain_sq_eq_zero {a : D} : a^2 = 0 ↔ a = 0 := by
  exact sq_eq_zero_iff

example {a b : D} (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b := by
  have : (a - b) * (a + b) = 0 := by
    calc (a - b) * (a + b)
      = a^2 - b^2     := by ring
      _ = 0           := by rw [h, sub_self]
  cases mul_eq_zero.mp this with
  | inl h1 =>
    left
    exact eq_of_sub_eq_zero h1
  | inr h2 =>
    right
    exact eq_neg_of_add_eq_zero_left h2

end IntegralDomainBasics

-- 2.4 Field：引入乘法逆元
/-
定义：域(Field)是一个整环 (F, +, ·, 0, 1)，其中每个非零元素都有乘法逆元：
对于任意 a ∈ F 且 a ≠ 0，存在 a⁻¹ ∈ F 使得 a · a⁻¹ = a⁻¹ · a = 1。
-/
-- Field是每个非零元素都有乘法逆元的IntegralDomain
-- 与IntegralDomain的区别：增加了乘法逆元的存在性
namespace FieldBasics

variable {F : Type*} [Field F]

-- Field继承IntegralDomain的所有性质
-- 新增的核心性质：乘法逆元
#check mul_inv_cancel  -- a ≠ 0 → a * a⁻¹ = 1
#check inv_mul_cancel  -- a ≠ 0 → a⁻¹ * a = 1

-- 除法的定义
theorem field_div_eq_mul_inv (a b : F) : a / b = a * b⁻¹ := by
  exact div_eq_mul_inv a b

-- 域中的基本运算
theorem field_div_self {a : F} (ha : a ≠ 0) : a / a = 1 := by
  exact div_self ha

theorem field_one_div {a : F} (ha : a ≠ 0) : 1 / a = a⁻¹ := by
  exact one_div a

theorem field_inv_inv {a : F} (ha : a ≠ 0) : (a⁻¹)⁻¹ = a := by
  exact inv_inv a

-- field_simp策略专门处理域中的分式运算
example (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a / b) * (b / a) = 1 := by field_simp

example (a b c : F) (hb : b ≠ 0) (hc : c ≠ 0) :
    a / b / c = a / (b * c) := by field_simp

example (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a + b) / (a * b) = 1/b + 1/a := by
    field_simp
    left; ring

-- 结合ring策略处理复杂表达式
example (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ((x + y) / x) * ((x + y) / y) = (x + y)^2 / (x * y) := by
  field_simp
  ring

-- 分式的化简
example (a b c : F) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a / b) / (c / b) = a / c := by field_simp

-- 复杂的分式运算
example (x y z : F) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x / y + y / z) * (y * z) / x = z + y^2 / x := by
  field_simp
  ring

-- 域的重要性质
example : IsDomain F := inferInstance

-- 域中每个非零元素都是单位
theorem field_isUnit_of_ne_zero {a : F} (ha : a ≠ 0) : IsUnit a := by
  exact IsUnit.mk0 a ha

-- 线性方程的解
example (a b : F) (ha : a ≠ 0) : ∃! x, a * x = b := by
  use b / a
  constructor
  · field_simp
  · intro y hy
    have : a * y = a * (b / a) := by rw [← hy]; field_simp
    exact mul_left_cancel₀ ha this

-- 域论计算的例子集合
namespace FieldExamples

variable {F : Type*} [Field F]

-- 分式化简
example (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a/b + b/c) / (a/c) = c/b + b/a := by
  field_simp
  ring

-- 复杂分式运算
example (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    1/(x + y) = 1/(x + y) * (x*y)/(x*y) := by
  field_simp

-- 有理函数恒等式
example (a b : F) (hab : a + b ≠ 0) :
    a/(a + b) + b/(a + b) = 1 := by
  rw [← add_div]
  field_simp

end FieldExamples

end FieldBasics

-- 有限整环是域的重要定理
namespace FiniteFieldExamples

variable (R : Type*) [CommRing R] [IsDomain R] [Finite R]

-- 有限整环必为域
#check Finite.isField_of_domain R

-- 有限整环的单位群是循环群
variable [DecidableEq R] [Fintype R]
#check Fintype.fieldOfDomain R

-- 有限群在整环中的性质
variable {G : Type*} [Group G] [Fintype G] (f : G →* R) (hf : f ≠ 1)
#check sum_hom_units_eq_zero f hf

end FiniteFieldExamples

end RingTheoryPath

-- ============ Part 3：模论方向 ============
-- 路径3：模论方向
-- Module → VectorSpace

namespace ModuleTheoryPath

-- 3.1 Module：环上的线性结构
/-
定义：模(Module)是一个代数结构，由环 R 和阿贝尔群 (M, +, 0) 以及标量乘法
· : R × M → M 组成，满足：
1. 1_R · m = m （单位元性质）
2. (r * s) · m = r · (s · m) （结合律）
3. (r + s) · m = r · m + s · m （左分配律）
4. r · (m + n) = r · m + r · n （右分配律）
-/
-- Module是环R上的加法阿贝尔群M配以标量乘法运算R × M → M，
-- 满足分配律和结合律
namespace ModuleBasics

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

-- Module的基本结构
-- 1. 底层的加法阿贝尔群结构（继承自AddCommGroup M）
-- 2. 标量乘法运算及其性质
#check one_smul        -- 单位元性质：1 • x = x
#check mul_smul        -- 结合律：(a * b) • x = a • (b • x)
#check add_smul        -- 左分配律：(a + b) • x = a • x + b • x
#check smul_add        -- 右分配律：a • (x + y) = a • x + a • y

-- 模的基本定理
theorem module_zero_smul (x : M) : (0 : R) • x = 0 := by
  exact zero_smul R x

theorem module_smul_zero (a : R) : a • (0 : M) = 0 := by
  exact smul_zero a

theorem module_neg_smul (a : R) (x : M) : (-a) • x = -(a • x) := by
  exact neg_smul a x

-- 标量乘法的分配性质
example (a b : R) (x y : M) : a • x + b • y = a • x + b • y := rfl

example (a : R) (x y z : M) : a • (x + y + z) = a • x + a • y + a • z := by
  rw [smul_add, smul_add, add_assoc]

-- 模与向量空间的例子集合
namespace ModuleExamples

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

-- 线性组合
example (a b c : F) (u v w : V) :
    a • u + b • v + c • w = a • u + (b • v + c • w) := by
  rw [add_assoc]

end ModuleExamples

end ModuleBasics

-- 3.2 VectorSpace：域上的模
/-
定义：向量空间(Vector Space)是域 F 上的模，即满足模的所有公理的代数结构，
其中标量环是域。由于域中每个非零元素都有逆元，向量空间具有许多优良性质，
如线性无关、基、维数等概念都有良好的定义。
-/
-- VectorSpace是域上的Module，继承了域的所有良好性质
-- 与Module的区别：标量环是域而非一般的环
namespace VectorSpaceBasics

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

-- VectorSpace继承Module的所有性质
-- 注意：在Mathlib4中，VectorSpace只是Module的别名
example : Module F V := inferInstance

-- 向量空间的基本性质
example (a b : F) (v w : V) : a • v + b • w ∈ Set.univ := trivial

-- 向量空间的高级概念
#check LinearIndependent F   -- 线性无关
#check Basis F V             -- 基
#check FiniteDimensional F V -- 有限维

end VectorSpaceBasics


namespace LinearAlgebraExamples

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

-- 线性变换
example : Module K (V →ₗ[K] V) := inferInstance

-- 对偶空间
example : Module K (Module.Dual K V) := inferInstance

-- 张量积
example {W : Type*} [AddCommGroup W] [Module K W] :
    Module K (TensorProduct K V W) := inferInstance

end LinearAlgebraExamples

end ModuleTheoryPath
