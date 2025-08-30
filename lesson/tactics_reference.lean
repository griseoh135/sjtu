import Mathlib
import Mathlib.Logic.Basic
import MIL.Common
import Mathlib.Data.Real.Basic

/-!
# Lean 4 策略（Tactics）参考手册

本文件系统整理了 Lean 4 中常用策略的用法和示例。
by_cases

rintro

oemga

contradiction
contrapose


tuato

exact 自动开启一个fun proof

## 目录

### 一、基础构造策略 🏗️
1. [constructor - 构造子策略](#constructor)
2. [left/right - 析取选择](#leftright)
3. [use/exists - 存在量词见证](#use)
4. [exact - 精确匹配](#exact)

### 二、分解和分析策略 🔍
5. [cases - 基本分解](#cases)
6. [rcases - 递归分解](#rcases)
7. [by_cases - 条件分类](#by_cases)
8. [obtain - 解构存在量词](#obtain)




### 三、逻辑推理策略 🧠
9. [intro - 引入变量/假设](#intro)
10. [assumption - 自动假设匹配](#assumption)
11. [contrapose! - 逆否命题](#contrapose)
12. [push_neg - 否定简化](#push_neg)
13. [tauto - 重言式自动证明](#tauto)

### 四、矛盾处理策略 ⚡
14. [contradiction - 自动矛盾](#contradiction)
15. [absurd - 逻辑矛盾](#absurd)
16. [exfalso - 爆炸原理](#exfalso)

### 五、数值计算策略 🔢
17. [norm_num - 数值计算](#norm_num)
18. [linarith - 线性算术](#linarith)
19. [ring - 环论化简](#ring)
20. [field_simp - 域化简](#field_simp)

oemga

### 六、等式和重写策略 ✏️
21. [rw - 重写](#rw)
22. [simp - 简化](#simp)
23. [subst - 替换](#subst)
24. [convert - 类型转换](#convert)

### 七、函数应用策略 🎯
25. [apply - 函数应用](#apply)
26. [refine - 精炼应用](#refine)
27. [ext - 函数外延性](#ext)
28. [congr - 同余性](#congr)

### 八、归纳和递归策略 🔄
29. [induction - 归纳法](#induction)
30. [strong_induction - 强归纳](#strong_induction)
31. [well_founded - 良基归纳](#well_founded)

### 九、专门数学策略 📐
32. [le_antisymm - 反对称性](#le_antisymm)
33. [lt_irrefl - 反自反性](#lt_irrefl)
34. [le_or_gt - 线性序](#le_or_gt)
35. [Classical.em - 排中律](#classical_em)

### 十、调试和辅助策略 🛠️
36. [have - 中间步骤](#have)
37. [sorry - 占位符](#sorry)
38. [trace - 调试信息](#trace)
39. [#check/#eval - 类型检查](#check_eval)

---
-/


/-! ## 一、基础构造策略 🏗️ -/

/-! ### constructor - 构造子策略 -/

-- 自动选择合适的构造子来证明归纳类型的目标
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor  -- 分解为两个子目标
  · exact hp
  · exact hq

-- 对于析取，constructor 选择第一个构造子
example (p q : Prop) (hp : p) : p ∨ q := by
  constructor  -- 等价于 left
  exact hp

-- 对于双条件（双向蕴含）
example (p : Prop) : p ↔ p := by
  constructor
  · intro hp; exact hp  -- 正向：p → p
  · intro hp; exact hp  -- 反向：p → p

-- 策略组合：<;> 对所有子目标应用后续策略
example : 1 + 1 = 2 ∧ 2 * 3 = 6 := by
  constructor <;> norm_num

/-! ### left/right - 析取选择 -/

-- 明确选择析取的左分支或右分支
example (p q : Prop) (hp : p) : p ∨ q := by
  left; exact hp

example (p q : Prop) (hq : q) : p ∨ q := by
  right; exact hq

/-! ### use/exists - 存在量词见证 -/

-- use 为存在量词提供具体的见证
example : ∃ x : ℝ, x > 0 := by
  use 1
  norm_num

-- exists 是 use 的别名
example : ∃ x : ℝ, x^2 = 4 := by
  exists 2
  norm_num

-- 复杂见证的构造
example : ∃ f : ℝ → ℝ, ∀ x, f x = x + 1 := by
  use fun x => x + 1
  intro x
  rfl

/-! ### exact - 精确匹配 -/

-- exact 提供精确匹配目标的项
example (x : ℝ) (h : x > 0) : x > 0 := by exact h

-- 与函数组合
example (x y : ℝ) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  exact le_antisymm h1 h2




/-! ## 二、分解和分析策略 🔍 -/

/-! ### cases - 基本分解 -/

-- 按构造子分解归纳类型
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h with
  | intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

-- 处理析取
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- 具名分支处理
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

/-! ### rcases - 递归分解 -/

-- 一次性分解嵌套结构
example (p q r : Prop) (h : (p ∧ q) ∧ r) : p := by
  rcases h with ⟨⟨hp, hq⟩, hr⟩
  exact hp

-- 处理析取的模式
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq

-- 与定理结合使用
example (y : ℝ) : y ≤ 0 ∨ 0 < y := by
  rcases le_or_gt y 0 with h | h
  · left; exact h
  · right; exact h

/-! ### by_cases - 条件分类 -/

-- 对命题进行分类讨论
example (x : ℝ) : x ≤ |x| := by
  by_cases h : x ≥ 0
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (not_le.mp h)]
    linarith

-- 与排中律的关系
example (P : Prop) : P ∨ ¬P := by
  by_cases h : P
  · left; exact h
  · right; exact h

/-! ### obtain - 解构存在量词 -/

-- 从存在性陈述中提取见证和证明
example (h : ∃ x : ℝ, x > 0) : ∃ y : ℝ, y^2 > 0 := by
  obtain ⟨x, hx⟩ := h
  use x
  exact pow_pos hx 2




/-! ## 三、逻辑推理策略 🧠 -/

/-! ### intro - 引入变量/假设 -/

-- 引入函数参数或蕴含的前提
example (p q : Prop) : p → (q → p) := by
  intro hp    -- 引入假设 hp : p
  intro hq    -- 引入假设 hq : q
  exact hp

-- 一次引入多个参数
example (p q r : Prop) : p → q → r → p := by
  intro hp hq hr
  exact hp

/-! ### assumption - 自动假设匹配 -/

-- 在上下文中寻找与目标完全匹配的假设
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption  -- 找到 h₀ : x ≤ y
  · intro h
    apply h₁
    rw [h]

/-! ### contrapose! - 逆否命题 -/

-- 将 P → Q 转换为 ¬Q → ¬P，并自动简化否定
example (f : ℝ → ℝ) : (∀ a, ∃ x, f x > a) → ¬(∃ a, ∀ x, f x ≤ a) := by
  contrapose!
  intro h
  exact h

-- 极限相关的应用
example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

/-! ### push_neg - 否定简化 -/

-- 自动简化复杂的否定表达式
example (h : ¬∀ x : ℝ, x ≥ 0) : ∃ x : ℝ, x < 0 := by
  push_neg at h
  exact h

-- 常用的否定简化规则：
-- ¬(∀ x, P x) ↔ ∃ x, ¬P x
-- ¬(∃ x, P x) ↔ ∀ x, ¬P x
-- ¬(P ∧ Q) ↔ ¬P ∨ ¬Q
-- ¬(P ∨ Q) ↔ ¬P ∧ ¬Q

example : ¬(∀ x : ℝ, ∃ y : ℝ, x < y) ↔ ∃ x : ℝ, ∀ y : ℝ, y ≤ x := by
  push_neg
  rfl

/-! ### tauto - 重言式自动证明 -/

-- tauto 专门用于自动证明经典命题逻辑中的重言式（永真命题）
-- 它能处理涉及 ∧、∨、¬、→、↔ 的逻辑表达式

-- 基本逻辑恒等式
example (p q : Prop) : p ∧ q → q ∧ p := by tauto
example (p q : Prop) : p ∨ q → q ∨ p := by tauto
example (p q r : Prop) : (p ∧ q) ∨ r ↔ (p ∨ r) ∧ (q ∨ r) := by tauto

-- 德摩根定律
example (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by tauto
example (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by tauto

-- 在集合论中的应用
example {α : Type*} (r s t : Set α) (x : α) :
  x ∈ r ∩ (s ∪ t) → x ∈ r ∩ s ∨ x ∈ r ∩ t := by
  intro h
  simp [Set.mem_inter_iff, Set.mem_union] at h ⊢
  tauto

-- 在有限集合中的应用
example {α : Type*} [DecidableEq α] (r s t : Finset α) (x : α) :
  x ∈ r ∩ (s ∪ t) → x ∈ r ∩ s ∨ x ∈ r ∩ t := by
  simp [Finset.mem_inter, Finset.mem_union]
  tauto

-- 复杂逻辑表达式的简化
example (p q r : Prop) :
  (p → q) ∧ (q → r) → (p → r) := by tauto

-- 注意：tauto 只处理经典命题逻辑，不能处理量词或数学运算






/-! ## 四、矛盾处理策略 ⚡ -/

/-! ### contradiction - 自动矛盾 -/

-- 自动寻找上下文中的矛盾
example (p : Prop) (h1 : p) (h2 : ¬p) : False := by
  contradiction

-- 双重否定消除中的应用
example (P : Prop) : ¬¬P → P := by
  intro h
  cases Classical.em P with
  | inl hp => exact hp
  | inr hnp => contradiction

/-! ### absurd - 逻辑矛盾 -/

-- absurd : {a : Prop} → a → ¬a → False
example (h : 0 < 0) (a : ℝ) : a > 37 :=
  absurd h (lt_irrefl 0)

-- 处理直接的逻辑矛盾
example (p : Prop) (h1 : p) (h2 : ¬p) : False :=
  absurd h1 h2

/-! ### exfalso - 爆炸原理 -/

-- 将目标转换为 False，基于"从假可推出任何东西"
example (h : 0 < 0) (a : ℝ) : a > 37 := by
  exfalso
  exact lt_irrefl 0 h

/-! ## 五、数值计算策略 🔢 -/

/-! ### norm_num - 数值计算 -/

-- 自动解决数值计算相关的目标
example : (2 : ℝ) + 3 = 5 := by norm_num
example : (1 : ℝ) < 2 := by norm_num
example : (0 : ℝ) ≤ 5 := by norm_num

-- 在复杂表达式中
example : (2 : ℝ)^3 + 3 * 2^2 = 20 := by norm_num

-- 用于矛盾检测
example (h : (1 : ℕ) = 2) : False := by norm_num at h

/-! ### linarith - 线性算术 -/

-- 解决线性不等式和等式
example (x y : ℝ) (h1 : x > 0) (h2 : y > 0) : x + y > 0 := by linarith

-- 在复杂的线性推理中
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b < c) : a < c := by
  linarith

-- 与其他策略组合
example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

/-! ### ring - 环论化简 -/

-- 自动化简环结构中的表达式
example (x y : ℝ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by ring

-- 在ext中的应用
example : (fun x y : ℝ ↦ (x + y)^2) = fun x y : ℝ ↦ x^2 + 2*x*y + y^2 := by
  ext x y
  ring

-- 证明代数恒等式
example (a b : ℝ) : a * b - b * a = 0 := by ring

/-! ### field_simp - 域化简 -/

-- 处理分数和除法运算
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a/b) * (b/a) = 1 := by
  field_simp

/-! ## 六、等式和重写策略 ✏️ -/

/-! ### rw - 重写 -/

-- 使用等式重写目标或假设
example (x : ℝ) : x + 0 = x := by rw [add_zero]

-- 多步重写
example (x y : ℝ) : x + y = y + x := by
  rw [add_comm]

-- 在假设中重写
example (x y : ℝ) (h : x = y + 1) : x - 1 = y := by
  rw [h]
  ring

-- 条件重写
example (x : ℝ) (h : x ≥ 0) : |x| = x := by
  rw [abs_of_nonneg h]

/-! ### simp - 简化 -/

-- 使用简化规则自动简化表达式
example (x : ℝ) : x + 0 - 0 * x = x := by simp

-- 指定简化规则
example (xs : List ℝ) : xs ++ [] = xs := by simp [List.append_nil]

-- simp_all 简化所有内容
example (x y : ℝ) (h : x = 0) : x + y = y := by
  simp_all

/-! ### subst - 替换 -/

-- 直接用等式替换变量
example (x y : ℝ) (h : x = y) : x + 1 = y + 1 := by
  subst h
  rfl

/-! ### convert - 类型转换 -/

-- 处理类型稍有不同但本质相同的目标
example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]  -- 证明 a = 1 * a
  exact lt_trans zero_lt_one h  -- 证明 0 < a

/-! ## 七、函数应用策略 🎯 -/

/-! ### apply - 函数应用 -/

-- 链式应用
example (a b c : ℝ) (hab : a < b) (hbc : b < c) : a < c := by
  apply lt_trans hab hbc

-- 部分应用
example (f : ℝ → ℝ → ℝ) (h : ∀ x y, f x y > 0) (a : ℝ) : f a a > 0 := by
  apply h

/-! ### refine - 精炼应用 -/

-- 更精确的函数应用，允许占位符
example (a b c : ℝ) (hab : a < b) (hbc : b < c) : a < c := by
  refine lt_trans ?_ hbc
  exact hab

/-! ### ext - 函数外延性 -/

-- 证明函数相等通过证明对所有输入相等
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y  -- 引入变量 x, y
  ring     -- 展开并化简

-- 单变量函数
example (f g : ℕ → ℝ) (h : ∀ n, f n = g n) : f = g := by
  ext n
  exact h n

/-! ### congr - 同余性 -/

-- 证明函数应用的同余性
example (a b : ℝ) : |a| = |a - b + b| := by
  congr  -- 证明参数相等即可
  ring   -- 证明 a = a - b + b

-- 在复杂表达式中
example (f : ℝ → ℝ) (x y : ℝ) (h : x = y) : f (x + 1) = f (y + 1) := by
  congr

/-! ## 八、归纳和递归策略 🔄 -/

/-! ### induction - 归纳法 -/

-- 标准自然数归纳（简单例子）
example : ∀ n : ℕ, n + 0 = n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.succ_add, ih]

-- 列表归纳
example (l : List ℕ) : l.reverse.reverse = l := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [ih]

/-! ### strong_induction - 强归纳 -/

-- 强归纳的基本框架（留作练习）
-- example : ∀ n : ℕ, n ≥ 2 → ∃ p : ℕ, p.Prime ∧ p ∣ n := sorry

/-! ### well_founded - 良基归纳 -/

-- 良基递归的基本概念
-- def gcd_rec : ℕ → ℕ → ℕ := sorry

/-! ## 九、专门数学策略 📐 -/

/-! ### le_antisymm - 反对称性 -/

-- le_antisymm : 从 a ≤ b 和 b ≤ a 推出 a = b
#check le_antisymm  -- le_antisymm : a ≤ b → b ≤ a → a = b

-- 典型应用
example {x y : ℝ} (h1 : x ≤ y) (h2 : y ≤ x) : x = y :=
  le_antisymm h1 h2

-- 在逆否证明中的应用
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

/-! ### lt_irrefl - 反自反性 -/

-- lt_irrefl : 严格序关系的反自反性
#check lt_irrefl  -- lt_irrefl : ∀ (a : α), ¬a < a

-- 用于构造矛盾
example (h : (0 : ℝ) < 0) : False := lt_irrefl 0 h

-- 在absurd中的应用
example (h : (0 : ℝ) < 0) (a : ℝ) : a > 37 :=
  absurd h (lt_irrefl 0)

/-! ### le_or_gt - 线性序 -/

-- le_or_gt : 线性序上的三分法
#check le_or_gt  -- le_or_gt : ∀ (a b : α), a ≤ b ∨ b < a

-- 典型用法：案例分析
example (x : ℝ) : |x| = x ∨ |x| = -x := by
  rcases le_or_gt 0 x with h | h
  · left; exact abs_of_nonneg h
  · right; exact abs_of_neg h

-- 其他有用的线性序定理
#check lt_trichotomy  -- lt_trichotomy : ∀ (a b : α), a < b ∨ a = b ∨ b < a
#check le_total      -- le_total : ∀ (a b : α), a ≤ b ∨ b ≤ a

/-! ### Classical.em - 排中律 -/

-- 经典逻辑的排中律：对任何命题 P，要么 P 要么 ¬P
#check Classical.em  -- Classical.em : ∀ (a : Prop), a ∨ ¬a

-- 用于双重否定消除
example (P : Prop) : ¬¬P → P := by
  intro h
  cases Classical.em P with
  | inl hp => exact hp
  | inr hnp => contradiction

-- 用于by_cases的基础
example (P : Prop) : P ∨ ¬P := Classical.em P

/-! ## 十、调试和辅助策略 🛠️ -/

/-! ### have - 中间步骤 -/

-- 构造中间结果来简化证明
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  have h3 : a ≤ c := le_trans h1 h2
  exact h3

-- 在复杂证明中分步处理
example (x y : ℝ) : (x + y)^2 ≥ 0 := by
  have h1 : (x + y)^2 = (x + y) * (x + y) := by ring
  rw [h1]
  apply mul_self_nonneg

/-! ### sorry - 占位符 -/

-- 用于跳过证明的部分（仅用于开发阶段）
-- example (p : Prop) : p := sorry

/-! ### trace - 调试信息 -/

-- 在证明过程中输出调试信息（高级功能）
example (x : ℝ) (h : x > 0) : x + 1 > 1 := by
  -- trace 用于调试，这里直接证明
  linarith

/-! ### #check/#eval - 类型检查 -/

-- 检查表达式的类型
#check le_antisymm  -- 查看函数类型
#check (1 : ℝ)      -- 检查数值类型

-- 计算表达式的值
#eval 2 + 3         -- 输出 5
#eval ([] : List ℕ).length  -- 输出 0

/-! ## 常用证明模式总结 🎯 -/

/-! ### 模式1：反证法 -/
example (x : ℝ) : x ≠ x + 1 := by
  intro h
  have : (0 : ℝ) = 1 := by linarith [h]
  norm_num at this

/-! ### 模式2：分类讨论 -/
example (x : ℝ) : x ≤ |x| := by
  by_cases h : x ≥ 0
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (not_le.mp h)]
    linarith

/-! ### 模式3：存在性证明 -/
example : ∃ x : ℝ, x^2 = 4 ∧ x > 0 := by
  use 2
  constructor <;> norm_num

/-! ### 模式4：函数等式证明 -/
example (f g : ℝ → ℝ) (h : ∀ x, f x = g x) : f = g := by
  ext x
  exact h x

/-! ### 模式5：序关系的传递性 -/
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : b < c) (h3 : c ≤ d) : a < d := by
  apply lt_of_le_of_lt h1
  apply lt_of_lt_of_le h2 h3

/-! ### 模式6：constructor + assumption组合 -/
example (p q r : Prop) (hp : p) (hq : q) : p ∧ q ∧ r → p ∧ q := by
  intro h
  constructor <;> assumption

/-! ### 模式7：rcases + 复杂模式匹配 -/
example (h : ∃ x, x > 0 ∧ x < 1) : ∃ y, 0 < y := by
  rcases h with ⟨x, hpos, _⟩
  use x

/-! ### 模式8：contrapose! + linarith -/
example (x y : ℝ) (h : x + y > 2) : x > 1 ∨ y > 1 := by
  contrapose! h
  linarith

/-! ## 策略选择快速指南 📋 -/

/-
🏗️ **构造目标时**：
- `constructor` - 自动选择构造子
- `left/right` - 明确选择析取分支
- `use` - 提供存在量词见证
- `ext` - 证明函数相等

🔍 **分解假设时**：
- `cases` - 基本分解
- `rcases` - 复杂嵌套分解
- `obtain` - 存在量词解构
- `by_cases` - 条件分类

🧠 **逻辑推理时**：
- `intro` - 引入参数/假设
- `assumption` - 自动匹配假设
- `contrapose!` - 逆否证明
- `push_neg` - 否定简化
- `tauto` - 重言式自动证明

⚡ **处理矛盾时**：
- `contradiction` - 自动矛盾检测
- `absurd` - 明确逻辑矛盾
- `exfalso` - 爆炸原理

🔢 **数值计算时**：
- `norm_num` - 数值计算
- `linarith` - 线性算术
- `ring` - 环论化简
- `field_simp` - 域运算

✏️ **等式重写时**：
- `rw` - 基本重写
- `simp` - 自动简化
- `subst` - 变量替换
- `convert` - 类型转换

🎯 **函数应用时**：
- `exact` - 精确匹配
- `apply` - 函数应用
- `refine` - 精炼应用
- `congr` - 同余性证明

🔄 **归纳证明时**：
- `induction` - 标准归纳
- 配合 `with | zero => | succ =>`

🛠️ **调试技巧**：
- `have` - 中间步骤
- `#check` - 类型检查
- `sorry` - 临时占位
-/

/-! ## 十二、错误调试技巧 -/

-- 使用 #check 检查类型
-- #check le_antisymm  -- 查看函数类型

-- 使用 have 构造中间步骤
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  have h3 : a ≤ c := le_trans h1 h2
  exact h3

-- 分解复杂目标
example (x y : ℝ) : (x + y)^2 ≥ 0 := by
  have h1 : (x + y)^2 = (x + y) * (x + y) := by ring
  rw [h1]
  apply mul_self_nonneg

-- 使用 dsimp 定义简化
def double (x : ℝ) : ℝ := x + x

example (x : ℝ) : double x = 2 * x := by
  dsimp [double]  -- 展开 double 的定义
  ring

-- 在复杂证明中清理目标
example (s t : ℕ → ℝ) (a b : ℝ) :
  (fun _ : ℕ => s 0 + t 0) = (fun _ : ℕ => a + b) → True := by
  intro h
  simp

/-! ## 附录：完整示例 📚 -/

-- 综合示例：证明函数单调性
example (f : ℝ → ℝ) (hf : ∀ x y, x ≤ y → f x ≤ f y) (a b : ℝ) (h : a < b) : f a < f b ∨ f a = f b := by
  have h1 : a ≤ b := le_of_lt h
  have h2 : f a ≤ f b := hf a b h1
  by_cases h3 : f a = f b
  · right; exact h3
  · left; exact lt_of_le_of_ne h2 h3

-- 综合示例：存在性构造
example : ∃ f : ℝ → ℝ, (∀ x, f (f x) = x) ∧ (∀ x y, x ≠ y → f x ≠ f y) := by
  use fun x => -x
  constructor
  · intro x; simp
  · intro x y h; contrapose! h; linarith

-- 综合示例：绝对值性质（简化版本）
example (x y : ℝ) : |x + y| ≤ |x| + |y| :=
  abs_add _ _

/-! 🎉 这个手册涵盖了 Lean 4 中最常用的策略，每个策略都配有实际例子。
    通过系统学习这些策略，你将能够高效地进行数学证明。

    💡 **使用提示**：
    - 从基础策略开始，逐步掌握高级策略
    - 多练习常用证明模式
    - 善用组合策略提高效率
    - 遇到问题时查阅相应章节

    📖 **进一步学习**：
    - Mathematics in Lean 教程
    - Lean 4 官方文档
    - Mathlib 文档和源码
-/
