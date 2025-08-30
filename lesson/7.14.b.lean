import Mathlib
#check Add
#check 1
#check ℕ
#check Type
--1-ℕ-Type
#check rfl
universe u
#check  ∀ {α : Sort u} {a : α}, a = a
#check  Prop
--1-rfl-∀ -Prop-Type
def f ( a : Nat) : Nat :=a*a
def f1: Nat-> Nat :=fun a => a*a
#check f
#check f 1
#eval f 2
#eval f 3
def add (a :ℕ )(b :ℕ ) : ℕ  := a + b
#check add

def h := add_comm 1 2
#check h -- 1 + 2 = 2 + 1
def f2 { a } { b : ℕ } ( h : a + b = b + a ) : ℕ := b
#eval f2   h--双括号



#check pow_two_nonneg
#help tactic

def limq1 ( a_ : ℕ  → ℝ ) ( a : ℝ ) : Prop :=
∀ ε > 0 , ∃ N : ℕ , ∀ n > N, -ε < a_ n - a ∧ a_ n - a < ε
#check limq1 (fun n => 1 / n ) 0 -- Prop

theorem lim_uniq
{ a_ : ℕ → ℝ}
{ a b : ℝ}
( ha : limq1 a_ a )
( hb : limq1 a_ b )
: a = b
:= by
by_contra! this
apply lt_or_gt_of_ne at this
wlog h : a > b generalizing a b with wlog := by
    -- 对称情况处理
    apply this hb ha (Or.symm this)

  -- 主要证明：假设 a > b，推导矛盾
  unfold limq1 at ha hb

  -- 选择 ε = (a - b) / 2
  let ε := (a - b) / 2

  -- 证明 ε > 0
  have ε_pos : ε > 0 := by
    apply div_pos
    · exact sub_pos.mpr h  -- a > b 所以 a - b > 0
    · norm_num  -- 2 > 0

  -- 应用极限定义得到 N_a 和 N_b
  have ha_ε := ha ε ε_pos
  have hb_ε := hb ε ε_pos

  -- 解构存在量词
  rcases ha_ε with ⟨Na, ha_ε⟩
  rcases hb_ε with ⟨Nb, hb_ε⟩

  -- 选择足够大的 n
  let n := max Na Nb + 1

  -- 证明 n 满足条件
  have n_gt_Na : n > Na := by
    calc n = max Na Nb + 1 := rfl
         _ > max Na Nb := by norm_num
         _ ≥ Na := le_max_left Na Nb

  have n_gt_Nb : n > Nb := by
    calc n = max Na Nb + 1 := rfl
         _ > max Na Nb := by norm_num
         _ ≥ Nb := le_max_right Na Nb

  -- 应用极限条件
  have ha_n := ha_ε n n_gt_Na
  have hb_n := hb_ε n n_gt_Nb

  -- 关键矛盾：从两个极限条件推出不可能的不等式
  have h1 : a_ n - a < ε := ha_n.2
  have h2 : -ε < a_ n - b := hb_n.1

  -- 从这两个不等式推导矛盾
  have : a_ n < a + ε := by linarith [h1]
  have : a_ n > b - ε := by linarith [h2]
  have : b - ε < a + ε := by linarith

  -- 但是 ε = (a - b) / 2，所以这意味着 b - (a-b)/2 < a + (a-b)/2
  -- 化简得到 b < a（这我们已知），但更强的是会导致 b < a 的强度超出预期
  -- 实际的矛盾来自更精确的分析
  unfold ε at *
  linarith
-------------------------------------------7.14.c---------------------------

variable (p q : Prop)
theorem pq : p → q := by sorry
#check pq
theorem sth (hp : p) : q := pq p q hp  -- error

variable {p q r : Prop} {α : Type*} {P : α → Prop}

theorem th_name (p:Prop) : r := by
  have hp : p := by sorry
  #check hp         --  p
  sorry

-- Conjunction “∧”
-- Left rule:

theorem Conj_constructor (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  . exact hq

theorem Conj_refine (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩
  · exact hp
  . exact hq

-- Right rules:

theorem Conj_have1 (h : p ∧ q) : p := by
  have ⟨hp, hq⟩ := h
  exact hp

theorem Conj_have2 (h : p ∧ q) : p := by
  have hp : p := h.left
  have hq : q := h.right
  exact hp

theorem Conj_have3 (h : p ∧ q) : p := by
  have hp : p := h.1
  have hq : q := h.2
  exact hp

theorem Conj_rcases (h : p ∧ q) : p := by
  rcases h with ⟨hp, hq⟩
  exact hp

theorem Conj_obtain (h : p ∧ q) : p := by
  obtain ⟨hp, hq⟩ := h
  exact hp

-- Implication “→”
-- Right rule:

theorem Imp_intro (hq : q) : p → q := by
  intro hp
  exact hq
#check p→ q
theorem Imp_refine_left (hq : q) : p → q := by
  refine fun hp => ?_
  exact hq

-- Left rule:

theorem Imp_apply (hp : p) (h : p → q) : q := by
  apply h
  exact hp

theorem Imp_refine_right (hp : p) (h : p → q) : q := by
  refine h ?_
  exact hp

-- Disjunction “∨”
-- Right rule:

theorem Disj_left (hp : p) : p ∨ q := by
  left
  exact hp

theorem Disj_right (hq : q) : p ∨ q := by
  right
  exact hq

-- Left rule:

theorem Disj_obtain (h : p ∨ q) (pr : p → r) (qr : q → r) : r := by
  obtain hp | hq := h
  · exact pr hp
  · exact qr hq

theorem Disj_rcases (h : p ∨ q) (pr : p → r) (qr : q → r) : r := by
  rcases h with hp | hq
  · exact pr hp
  · exact qr hq

-- Universal quantifier “∀”
-- Right rule:

theorem Forall_intro : ∀ x, P x := by
  intro x       --  Goal: P x
  #check x      --  x : α
  sorry

theorem Forall_refine : ∀ x, P x := by
  refine fun x => ?_  -- Goal: P x
  #check x            -- x : α
  sorry

-- Left rule:

theorem Forall_sub (h : ∀ x, P x) (a : α) : p := by
  #check h a          -- P a
  sorry

theorem Forall_apply (h : ∀ x, P x) (x : α) : P x := by
  apply h

-- Existential quantifier “∃”
-- Right rule:

theorem Exists_use (a : α) : ∃ x, P x := by
  use a               -- Goal: P a
  sorry

theorem Exists_refine (a : α) : ∃ x, P x := by
  refine ⟨?_, ?_⟩
  · exact a           -- Goal: P a
  · sorry

theorem Exists_constructor (a : α) (h : P a) : ∃ x, P x := by
  constructor
  case w => exact a
  . sorry

-- Left rule:

theorem Exists_have (h : ∃ x, P x) : p := by
  have ⟨a, ha⟩ := h
  sorry

theorem Exists_obtain (h : ∃ x, P x) : p := by
  obtain ⟨a, ha⟩ := h
  sorry

theorem Exists_rcases (h : ∃ x, P x) : p := by
  rcases h with ⟨a, ha⟩
  sorry

-- Negation “¬”

theorem Not_intro : ¬p := by
  intro h
  sorry

theorem Not_contradiction (h1 : p) (h2 : ¬p) : q := by
  contradiction

theorem False_contradiction (h : False) : q := by
  contradiction

theorem By_contradiction1 (h1 : p) (h2 : ¬p) : q := by
  contrapose! h2
  exact h1

theorem By_contradiction3 : p := by
  by_contra h
  sorry

theorem By_cases {p : Prop} : q := by
  by_cases h : p
  · sorry
  · sorry

namespace EZAnalysis

def lim (a_ : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n > N, -ε < a_ n - a ∧ a_ n - a < ε

#check lim (fun n => 1 / n) 0

-- Theorem: Uniqueness of limits for sequences in ℝ.
-- If a sequence has two limits, then those limits are equal.
theorem lim_uniq
  {a_ : ℕ → ℝ}
  {a b : ℝ}
  (ha : lim a_ a)
  (hb : lim a_ b)
:
  a = b
:= by
  by_contra! hab
  apply lt_or_gt_of_ne at hab
  -- Without loss of generality, assume a > b (the other case is symmetric)
  wlog h : a > b generalizing a b with wlog
  · apply wlog hb ha
    · exact Or.symm hab
    · rcases hab with case1 | case2
      · exact case1
      · contradiction
  · unfold lim at *
    let ε := (a - b) / 2
    have ε_pos : ε > 0 := by
      apply div_pos
      · exact sub_pos_of_lt h
      · norm_num
    have ha := ha ε ε_pos
    have hb := hb ε ε_pos
    rcases ha with ⟨Na, ha⟩
    rcases hb with ⟨Nb, hb⟩
    let n := max Na Nb + 1
    have nga : n > Na := by
      calc
        n = max Na Nb + 1 := rfl
        _ > max Na Nb := by norm_num
        _ ≥ Na := le_max_left Na Nb
    have ngb : n > Nb := by
      calc
        n = max Na Nb + 1 := rfl
        _ > max Na Nb := by norm_num
        _ ≥ Nb := le_max_right Na Nb
    have ha := ha n nga
    have hb := hb n ngb
    unfold ε at *
    have ha := ha.1
    have hb := hb.2
    linarith

end EZAnalysis
