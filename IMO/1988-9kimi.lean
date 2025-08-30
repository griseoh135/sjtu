import Mathlib

open Real Set
open scoped BigOperators

/- Consider the graph of $f(x)=\sum_{k=1}^{70}\frac{k}{x-k}\ge\frac{5}{4}$.
 On the values of $x$ between $n$ and $n+1$ for $n\in\mathbb{N}$ $1\le n\le 69$, the terms of the form $\frac{k}{x-k}$ for $k\ne n,n+1$ have a finite range.
 In contrast, the term $\frac{n}{x-n}$ has an infinite range, from $+\infty$ to $n$.
 Similarly, the term $\frac{n+1}{x-n-1}$ has infinite range from $-n-1$ to $-\infty$.
  Thus, since the two undefined values occur at the distinct endpoints, we can deduce that $f(x)$ takes on all values between $+\infty$ and $-\infty$ for $x\in(n,n+1)$.
  Thus, by the Intermediate Value Theorem, we are garunteed a $n<r_n<n+1$ such that $f(r_n)=\frac{5}{4}$. Additionally, we have that for $x>70$, the value of $f(x)$ goes from $+\infty$ to $0$, since as $x$ increases, all the terms go to $0$.
  Thus, there exists some $r_{70}>70$ such that $f(r_{70})=\frac{5}{4}$ and so $f(x)\ge\frac{5}{4}$ for $x\in(70,r_{70})$. So, we have $70$ $r_i$ such that $f(r_i)=\frac{5}{4}$. There are obviously no other such $r_i$ since $f(x)=\frac{5}{4}$ yields a polynomial of degree $70$ when combining fractions. Thus, we have that the solution set to the inequality $f(x)\ge\frac{5}{4}$ is the union of the intervals $(n,r_n]$ (since if $f(x)<\frac{5}{4}$ for $x\in(n,r_n)$ then there would exist another solution to the equation $f(x)=\frac{5}{4}$. Thus we have proven that the solution set is the union of disjoint intervals. Now we are to prove that the sum of their lengths is $1988$. The sum of their lengths is $r_1+r_2+\cdots+r_{70}-(1+2+\cdots+70)=r_1+r_2+\cdots+r_{70}-35\cdot71$. We have that the equation $f(x)=\frac{5}{4}$ yields a polynomial with roots $r_i$. Thus, opposite of the coeficient of $x^{69}$ divided by the leading coefficient is the sum of the $r_i$. It is easy to see that the coefficient of $x^{69}$ is $-5(1+2+\cdots+70)-4(1+2+\cdots+70)=-9\cdot35\cdot 71$. Thus, since the leading coefficient is $5$ we have $r_1+r_2+\cdots+r_{70}=9\cdot7\cdot71$.
 Thus, the sum of the lengths of the intervals is $63\cdot71-35\cdot71=28\cdot71=1988$ as desired. -/
theorem algebra_14357 {f : ℝ → ℝ} (hf : f = λ x => ∑ k ∈  Finset.Icc 1 70, k / (x - k)) :
    ∃ r : ℕ → ℝ, (∀ i ∈ Finset.Icc 1 70, f (r i) = 5 / 4) ∧
    (∀ i ∈ Finset.Icc 1 70, r i > i) ∧
    (∑ i in Finset.Icc 1 70, (r i - i)) = 1988 := by
  let p : Polynomial ℝ := -70 * Polynomial.X^70 + 5 * (∑ i in Finset.Icc 1 70, (i * (∏ j in Finset.Icc 1 70 \ {i}, (Polynomial.X - j))))
  have p_roots : p.roots.card = 70 := by
    have p_ne_zero : p ≠ 0 := by
      apply ne_zero_of_ne_zero_of_monic (show (-70 : ℝ) ≠ 0 by norm_num)
      simp [p]
      <;> try norm_num
    have p_degree : p.natDegree = 70 := by
      have h1 : p.natDegree = 70 := by
        simp [p]
        compute_degree!
      exact h1
    have hroots : p.roots.card = 70 := by
      rw [←Polynomial.natDegree_eq_card_roots]
      exact p_degree
      all_goals try norm_num
    exact hroots
  have p_roots_sum : p.roots.sum = 63 * 71 := by
    have h1 : p.roots.sum = 63 * 71 := by
      simp [p]
      norm_num
      <;> native_decide
    exact h1
  let r : ℕ → ℝ := λ i => p.roots.toList.nthD i 0
  have hr1 : ∀ i ∈ Finset.Icc 1 70, f (r i) = 5 / 4 := by
    intro i hi
    simp [r, f, hf]
    norm_num
    <;> native_decide
  have hr2 : ∀ i ∈ Finset.Icc 1 70, r i > i := by
    intro i hi
    simp [r]
    norm_num
    <;> native_decide
  have hr3 : ∑ i in Finset.Icc 1 70, (r i - i) = 1988 := by
    simp [r]
    norm_num
    <;> native_decide
  exact ⟨r, hr1, hr2, hr3⟩
