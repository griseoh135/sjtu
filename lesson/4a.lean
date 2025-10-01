import Mathlib

-- ================================================================
-- Part 1: Introduction - 数论中的数系基础
-- ================================================================

-- ============ 1.1 数论特有的数系及扩展 ============

-- 数论中自然数的重要子集
#check ℕ             -- 自然数 {0, 1, 2, 3, ...}
#check Nat
#check ℕ+
#check PNat         -- 正自然数 {1, 2, 3, ...}

/-
一般来说，不特别声明的情况下，LEAN会将一个variable自动infer为自然数，
这也体现了自然数在LEAN系统中十分fundamental的地位
-/
#check 1

-- 一些基本运算
example : 4 - 3 = 1 := by rfl --proof term 自反性
example : 5 - 6 = 0 := rfl -- 自然数减法，结果不能为负
example : 1 ≠ 0 := Nat.one_ne_zero
example : 7 * 4 = 28 := rfl

#check Nat.Prime    -- 质数（theorem形式）
#check Nat.Primes   -- 所有质数，这是一个type
#check Nat.prime_def-- 质数的定义，但是本质上这是一个theorem


#check ℤ            -- 整数
#check Int
#check GaussianInt  -- 高斯整数 ℤ[i]（代数数论）
#check ZMod         -- 模n整数环 ℤ/nℤ（同余理论核心）
#check Nat.ModEq    -- 同余关系/模等式：两个自然数 a 和 b 在模 n 下同余， a ≡ b (mod n)

-- 模运算数系的嵌套
example : ZMod 5 := 7  -- 7 ≡ 2 (mod 5)
example (a : Fin 5) : ZMod 5 := a

-- 有理数在数论中的应用
#check ℚ            -- 有理数域
#check Rat
#check ℚ≥0          -- 非负有理数
#check NNRat


section BasicDefinition

-- ============ 1.2 Lean4中的自然数的构造 ============

-- The natural numbers in LEAN4 are defined inductively using successor
#check Nat
-- inductive Nat where
-- | zero : Nat
-- | succ : Nat → Nat

-- Basic successor operations
#check Nat.succ     -- succ : ℕ → ℕ 如猫猫讲的，事实上这是一个映射，那么通过映射间的线性结构可以得到如下（Peano Axiom）
#eval Nat.succ 0    -- 1
#eval Nat.succ 1    -- 2
#eval Nat.succ 5    -- 6

/-- Numbers are nested applications of successor -/
example : (0 : ℕ) = Nat.zero := rfl
example : (1 : ℕ) = Nat.succ Nat.zero := rfl
example : (2 : ℕ) = Nat.succ (Nat.succ Nat.zero) := rfl
example : (3 : ℕ) = Nat.succ (Nat.succ (Nat.succ Nat.zero)) := rfl
example : Nat.succ (Nat.succ 4) = 6 := rfl

end BasicDefinition

section PeanoAxiom

-- Axiom 1: 0 is a natural number (built into the type)
#check (0 : ℕ)

-- Axiom 2: Every natural number has a successor
example (n : ℕ) : ℕ := Nat.succ n

-- Axiom 3: 0 is not the successor of any natural number
example (n : ℕ) : Nat.succ n ≠ 0 := by
  exact Nat.succ_ne_zero n
  -- apply?

-- Axiom 4: Successor is injective
example (n m : ℕ) : Nat.succ n = Nat.succ m → n = m := by
  apply Nat.succ_injective

example (m n : ℕ) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h

-- Axiom 5: Induction principle (built into the type structure)
#check @Nat.rec

end PeanoAxiom

section NaturalNumberGame

/-- Successor equals adding one -/
theorem succ_eq_add_one (n : ℕ) : Nat.succ n = n + 1 := by sorry

/-- Numbers as successor expressions -/
example : (2 : ℕ) = Nat.succ (Nat.succ 0) := by sorry
example : (3 : ℕ) = Nat.succ (Nat.succ (Nat.succ 0)) := sorry

/-- Basic arithmetic using successor properties -/
example : Nat.succ 2 = 3 := sorry
example (n : ℕ) : Nat.succ n ≠ n := sorry

/-- Induction principle demonstration -/
theorem all_nats_geq_zero (n : ℕ) : 0 ≤ n := by
  sorry

end NaturalNumberGame

section SuccessorProperties

/-- Property 1: Injectivity - successor is injective -/
theorem succ_injective {a b : ℕ} : Nat.succ a = Nat.succ b → a = b := by
 intro h
 injection h

/-- Alternative proof using cases -/
theorem succ_injective' (a b : ℕ) (h : Nat.succ a = Nat.succ b) : a = b := by
 cases h
 rfl

/-- Property 2: Non-zero successor is never zero -/
theorem succ_ne_zero (n : ℕ) : Nat.succ n ≠ 0 := by
  intro h
  cases h

/-- Examples of non-zero property -/
example : (1 : ℕ) ≠ 0 := sorry
example : (42 : ℕ) ≠ 0 := sorry

/-- Property 3: Coverage - every non-zero number is a successor -/
theorem nat_zero_or_succ (n : ℕ) : n = 0 ∨ ∃ m, n = Nat.succ m := by
  -- rw [Nat.exists_eq_add_one]; exact Nat.eq_zero_or_pos n
  cases n with
  | zero => left; rfl
  | succ m => right; use m

end SuccessorProperties


-- ============ 1.3 递归定义与归纳证明 ============
/-
递归(Recursion)是定义函数或构造对象的方法：用自己来定义自己。
归纳(Induction)是证明命题的方法：证明某个性质对(所有自然数)都成立。-/
section RecursiveDefinitions

/-- 使用递归定义加法函数，
这是皮亚诺公理中自然数加法的标准定义 -/
def myAdd : ℕ → ℕ → ℕ
  -- 基础情况：任何数加0等于其本身
  | a, 0 => a
  -- 递归情况：a + (b+1) = (a + b) + 1
  | a, Nat.succ b => Nat.succ (myAdd a b)

/-- Basic properties of addition -/
example (n : ℕ) : myAdd n 0 = n := rfl
example (n m : ℕ) : myAdd n (Nat.succ m) = Nat.succ (myAdd n m) := rfl

/-- Multiplication defined recursively -/
def myMul : ℕ → ℕ → ℕ
| _, 0 => 0
| a, Nat.succ b => myAdd a (myMul a b)


-- Test multiplication
#eval myMul 3 2  -- 6
#eval myMul 4 0  -- 0

/-- Factorial defined recursively -/
def myFactorial : ℕ → ℕ
| 0 => 1
| Nat.succ n => myMul (Nat.succ n) (myFactorial n)

-- Test factorial
#eval myFactorial 0  -- 1
#eval myFactorial 1  -- 1
#eval myFactorial 5  -- 120

-- Fibonacci sequence using successor pattern
def fibonacci : ℕ → ℕ
| 0 => 0
| 1 => 1
| Nat.succ (Nat.succ n) => fibonacci n + fibonacci (Nat.succ n)

#eval fibonacci 10  -- 55

end RecursiveDefinitions


section MathematicalInduction

/-- 归纳法的基本原理 -/
theorem nat_induction (P : ℕ → Prop) :
  P 0 →                           -- Base case
  (∀ n, P n → P (Nat.succ n)) →   -- Inductive step
    ∀ n, P n :=                     -- Conclusion
  Nat.rec

/-- Example: Prove that myAdd is commutative -/
theorem myAdd_zero_right (n : ℕ) :
  myAdd n 0 = n := rfl

theorem myAdd_succ_right (n m : ℕ) :
  myAdd n (Nat.succ m) = Nat.succ (myAdd n m) := rfl

theorem myAdd_zero_left (n : ℕ) : myAdd 0 n = n := by
 induction n with
 | zero => rfl
 | succ n ih =>
   rw [myAdd_succ_right, ih]

theorem myAdd_succ_left (n m : ℕ) : myAdd (Nat.succ n) m = Nat.succ (myAdd n m) := by
 induction m with
 | zero => rfl
 | succ m ih =>
   rw [myAdd_succ_right, myAdd_succ_right, ih]

theorem myAdd_comm (a b : ℕ) : myAdd a b = myAdd b a := by
 induction b with
 | zero =>
   rw [myAdd_zero_right, myAdd_zero_left]
 | succ b ih =>
   rw [myAdd_succ_right, myAdd_succ_left, ih]

end MathematicalInduction

section PatternMatching
-- Section 5: Induction in Pattern Matching and Computational Aspects

/-- Even/odd using successor pattern matching -/
def isEven : ℕ → Bool
| 0 => true
| Nat.succ 0 => false
| Nat.succ (Nat.succ n) => isEven n

#eval isEven 0   -- true
#eval isEven 1   -- false
#eval isEven 4   -- true
#eval isEven 5   -- false

-- # 下面的例子感兴趣的可以下去看看，多观察编译器信息可以帮助你更快进步！
/-- Division by 2 using successor pattern -/
def divByTwo : ℕ → ℕ
| 0 => 0
| Nat.succ 0 => 0
| Nat.succ (Nat.succ n) => Nat.succ (divByTwo n)

#eval divByTwo 8   -- 4
#eval divByTwo 9   -- 4
#eval divByTwo 10  -- 5

/-- Predecessor function (with 0 case) -/
def pred : ℕ → ℕ
| 0 => 0
| Nat.succ n => n

#eval pred 0  -- 0
#eval pred 5  -- 4

/-- Maximum of two numbers using successor -/
def myMax : ℕ → ℕ → ℕ
| 0, m => m
| n, 0 => n
| Nat.succ n, Nat.succ m => Nat.succ (myMax n m)

#eval myMax 5 3  -- 5
#eval myMax 2 7  -- 7

end PatternMatching

section AdvancedProperties

/-- Well-founded recursion example -/
def ackermann : ℕ → ℕ → ℕ
| 0, n => n + 1
| Nat.succ m, 0 => ackermann m 1
| Nat.succ m, Nat.succ n => ackermann m (ackermann (Nat.succ m) n)

#eval ackermann 2 3

end AdvancedProperties


-- ================================================================
-- Part 2 基础数论概念
-- ================================================================

-- ============ 2.1 整除关系及其性质 ============
#check (· ∣ ·)  -- 整除关系的符号

#check Nat.dvd_iff_mod_eq_zero  -- a ∣ b ↔ b % a = 0
example (a b : ℕ) : a ∣ b ↔ b % a = 0 := Nat.dvd_iff_mod_eq_zero

-- 整除的基本例子
example : 3 ∣ 12 := by norm_num
example : 7 ∣ 21 := by norm_num
example : ¬(4 ∣ 15) := by norm_num
example : 12 % 3 = 0 := by norm_num
example : 15 % 4 = 3 := by norm_num

-- 相关定理
#check dvd_refl        -- 自反性：a ∣ a，任何数都整除自己
example (a : ℕ) : a ∣ a := by
  exact Nat.dvd_refl a
  -- exact dvd_rfl
  -- exact dvd_refl a

#check dvd_trans       -- 传递性：a ∣ b → b ∣ c → a ∣ c，整除关系可以传递
example (a b c : ℕ) : a ∣ b → b ∣ c → a ∣ c :=
  Nat.dvd_trans

#check dvd_zero        -- 任何数都整除0：a ∣ 0
example (a : ℕ) : a ∣ 0 := Nat.dvd_zero a

#check one_dvd         -- 1整除任何数：1 ∣ a
example (a : ℕ) : 1 ∣ a := Nat.one_dvd a

-- 整除在加法下封闭
#check dvd_add         -- a ∣ b → a ∣ c → a ∣ b + c
example (a b c : ℕ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c :=
  Nat.dvd_add h1 h2

-- 整除在乘法下封闭
#check dvd_mul_right   -- a ∣ b → a ∣ b * c
example (a b c : ℕ) (h : a ∣ b) : a ∣ b * c := by
  exact Nat.dvd_mul_right_of_dvd h c
example (a b c : ℕ) (h : a ∣ b) : a ∣ c * b := by
  exact Nat.dvd_mul_left_of_dvd h c

-- 整除的判定：使用余数判定整除
example (a b : ℕ) : a ∣ b ↔ b % a = 0 := Nat.dvd_iff_mod_eq_zero

-- 具体计算示例
example : 12 % 3 = 0 := by norm_num
example : 15 % 4 = 3 := by norm_num

-- 整除与因数的关系：如果a整除b且b≠0，则a ≤ b
example (a b : ℕ) (h : a ∣ b) (hb : 0 < b) : a ≤ b :=
  Nat.le_of_dvd hb h


-- ============ 2.2 质数与合数 ============
#check Nat.Prime    -- 质数（theorem形式）
#check Nat.Primes   -- 所有质数，这是一个type
#check Nat.prime_def-- 质数的标准定义，但是本质上这是一个theorem
/-
想要表达7是一个质数, 这样写是错误的
因为 ∈ 是用于集合成员关系的，而 Nat.Primes 是一个类型，不是集合。-/
-- example : 7 ∈ Nat.Primes := by sorry

/-
正确的是，这里是一个proposition
norm_num 是一个可以自动证明数值计算的策略-/
example : Nat.Prime 7 := by norm_num

example : Nat.Primes := ⟨7, by norm_num⟩ --这里用到了尖括号 ⟨⟩ ，是匿名构造器语法，等价于：

example : Nat.Primes := Subtype.mk 7 (by norm_num)

#check Subtype --这是一个structure
/-
mk 是 make 的缩写，是 Subtype 的构造器（constructor）。
本质上是在说："制作一个子类型的实例"，需要提供：
  1.值（val）
  2.证明（property）

同样的，这样也可以构造一个子类型，语法 { x : α // P x }
  1.α 是基础类型
  2.P x 是一个谓词（条件）
结果是满足条件 P x 的所有 x 组成的类型
-/

-- 所以更显式地
example : Nat.Primes := {
  val := 7,                 --这是子类型的值部分（val），类型为 ℕ
  property := by norm_num   --这是子类型的证明部分（property），证明了 Nat.Prime 7
}

#check Nat.prime_def_lt             -- 质数的标准定义
#check Nat.Prime.two_le             -- 质数 ≥ 2
#check Nat.Prime.eq_one_or_self_of_dvd  -- 质数只有平凡因数

-- 相关定理
#check Nat.prime_two              -- 2是质数
#check Nat.prime_three            -- 3是质数
#check Nat.not_prime_one          -- 1不是质数
#check Nat.Prime.dvd_mul          -- 质数整除乘积的性质
#check Nat.prime_def_le_sqrt      -- 质数的√n判定法

-- 质数判定示例

-- 小质数的直接证明
example : Nat.Prime 2 := Nat.prime_two
example : Nat.Prime 3 := Nat.prime_three
example : Nat.Prime 5 := by norm_num
example : Nat.Prime 17 := by decide
example : Nat.Prime 97 := by norm_num

-- 1不是质数
example : ¬Nat.Prime 1 := Nat.not_prime_one

-- ============ 质数的基本性质 ============

-- 质数至少为2
example (p : ℕ) (hp : Nat.Prime p) : p ≥ 2 := Nat.Prime.two_le hp

-- 质数只有两个正因数
example (p : ℕ) (hp : Nat.Prime p) (d : ℕ) (hd : d ∣ p) :
  d = 1 ∨ d = p := by exact (Nat.dvd_prime hp).mp hd

-- 质数整除乘积则整除其中一个因子
example (p a b : ℕ) (hp : Nat.Prime p) (h : p ∣ a * b) :
  p ∣ a ∨ p ∣ b := by exact (Nat.Prime.dvd_mul hp).mp h

-- 质数无限性定理
example : ∀ n, ∃ p, p ≥ n ∧ Nat.Prime p := Nat.exists_infinite_primes


-- 合数的例子
-- 4是合数（有因数2）
example : ¬Nat.Prime 4 := by norm_num

-- 展示合数的因数分解
example : 2 ∣ 4 ∧ 2 ≠ 1 ∧ 2 ≠ 4 := by norm_num
example : 3 ∣ 9 ∧ 3 ≠ 1 ∧ 3 ≠ 9 := by norm_num


-- ============ 2.3 素因子分解 ============
-- 最小素因子
example : Nat.minFac 12 = 2 :=rfl

-- 素因子列表（按递增顺序）
#eval Nat.primeFactorsList (2^32+1)

-- 素因子分解的理论基础
#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList

-- ============ 2.4 互质与最大公约数 ============

-- 互质的定义
example (a b : ℕ) : Nat.Coprime a b ↔ Nat.gcd a b = 1 := Iff.rfl

-- 相邻整数互质的几种证明方法
example (n : ℕ) : Nat.Coprime n (n + 1) := by sorry


-- 互质的具体例子
example : Nat.Coprime 9 16 := by norm_num
example : Nat.Coprime 15 28 := by norm_num
#check Nat.gcd                    -- 最大公约数函数
#check Nat.Coprime                -- 互质谓词
#check Nat.gcd_dvd_left           -- gcd整除左操作数
#check Nat.gcd_dvd_right          -- gcd整除右操作数
#check Nat.dvd_gcd                -- 公因数整除gcd

-- 相关定理检查
#check Nat.gcd_rec                -- 欧几里得算法递归
#check Nat.gcd_comm               -- gcd交换律
#check Nat.gcd_mul_lcm            -- gcd与lcm的关系
#check Nat.coprime_self_add_right -- n与n+1互质
#check Nat.coprime_iff_gcd_eq_one -- 互质当且仅当gcd=1
#check Nat.lcm_comm               -- lcm交换律

--基本计算示例
-- gcd计算
example : Nat.gcd 12 8 = 4 := by norm_num
example : Nat.gcd 15 10 = 5 := by norm_num
example : Nat.gcd 17 13 = 1 := by norm_num

-- lcm计算
example : Nat.lcm 6 4 = 12 := by norm_num
example : Nat.lcm 8 12 = 24 := by norm_num

-- 最大公约数的性质
-- gcd同时整除两个数
example (a b : ℕ) : Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b :=
  ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩

-- gcd的交换律
example (a b : ℕ) : Nat.gcd a b = Nat.gcd b a := Nat.gcd_comm a b


-- gcd与lcm的关系

-- 基本关系式
example (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b :=
  Nat.gcd_mul_lcm a b

-- lcm的交换律
example (a b : ℕ) : Nat.lcm a b = Nat.lcm b a := Nat.lcm_comm a b

-- 互质时的特殊情况
example (a b : ℕ) (h : Nat.Coprime a b) : Nat.lcm a b = a * b := by
  have : Nat.gcd a b = 1 := h
  rw [← Nat.gcd_mul_lcm, this, one_mul]

-- ================================================================
-- Part 3 同余与模运算
-- ================================================================

-- ============3.1 同余关系的定义和基本性质 ============
-- 同余符号 ≡ (输入 \==)
example : 5 ≡ 8 [MOD 3] := rfl

-- 模运算的基本性质
example : 27 % 4 = 3 := by norm_num
example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]


-- ============3.2 模运算的应用 ============
#check ZMod         -- 模n整数环 Z/nZ
#check Nat.ModEq    -- 自然数模等价关系

-- 自动模运算
example : ZMod 5 := 7  -- 7 ≡ 2 (mod 5)

-- 有限类型到模运算的转换
example (a : Fin 5) : ZMod 5 := a


-- ============ 4.1 平方根函数 ============
-- 整数平方根（向下取整）
#eval Nat.sqrt 1000047 -- 1000
#eval Nat.sqrt 1000000 -- 1000

example (a : ℕ) : Nat.sqrt (a * a) = a := Nat.sqrt_eq a
example (a b : ℕ) : Nat.sqrt a < b ↔ a < b * b := Nat.sqrt_lt

-- ============4.2 幂函数的性质 ============
#check Nat.pow  -- ℕ → ℕ → ℕ

-- 基础规则
example (a : ℕ) : a ^ 0 = 1 := by rfl
example (a : ℕ) : a ^ 1 = a := by rw [pow_one]
example (n : ℕ) : 1 ^ n = 1 := by rw [one_pow]

-- 重要定理
#check Nat.pow_add    -- a ^ (m + n) = a ^ m * a ^ n
#check Nat.mul_pow    -- (a * b) ^ n = a ^ n * b ^ n
#check Nat.mul_pos

-- 指数加法性质
example (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := Nat.pow_add a m n

-- 乘法分配律
example (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := Nat.mul_pow a b n

-- 零的幂
example (n : ℕ) (h : 0 < n) : 0 ^ n = 0 := by apply Nat.zero_pow h
example : 0 ^ 0 = 1 := by rfl

-- 平方
example (a : ℕ) : a ^ 2 = a * a := by rw [pow_two]

-- ============4.3 阶乘函数及其性质 ============
-- 阶乘的基本计算
example : Nat.factorial 4 = 24 := rfl

-- 阶乘的性质
example (a : ℕ) : Nat.factorial a > 0 := Nat.factorial_pos a

-- 从原始文档的阶乘定义
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

-- 阶乘的归纳证明
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction n with
  | zero => rw [fac]; exact zero_lt_one
  | succ n ih => rw [fac]; exact mul_pos n.succ_pos ih

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) :
  ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  sorry
