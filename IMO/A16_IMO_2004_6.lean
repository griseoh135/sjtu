import Mathlib
set_option maxHeartbeats 10000000

def IsAlternating : ℕ → Prop := fun n ↦
    (Nat.digits 10 n).length ≥ 1 ∧ ∀ i : ℕ, i + 1 < (Nat.digits 10 n).length
      → (Nat.digits 10 n)[i]! % 2 ≠ (Nat.digits 10 n)[i + 1]! % 2

def HasAlternatingMultiple : ℕ → Prop := fun n ↦
    ∃ m : ℕ, n ∣ m ∧ IsAlternating m

lemma Alternatingandlength(a k:Nat)
    (halt:IsAlternating a)
    (hksmall1:k+1≤ (Nat.digits 10 a).length)
    : (Nat.digits 10 a)[k]!%2=(k+(Nat.digits 10 a)[0]!)%2:=by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [add_comm k 1, add_assoc, (show ∀ a : ℕ, (1 + a) % 2 = 1 - a % 2 by omega), ← ih (by linarith), add_comm 1 k]
    have := halt.2 k (by linarith)
    omega

lemma digit0ismod2 (a:Nat)(ha:a≥1):(Nat.digits 10 a)[0]!%2=a%2:=by
  have amod: (Nat.digits 10 a)[0]! =a%10:=by
    rw[Nat.digits_def']
    repeat trivial
  rw[amod]
  omega

lemma eq_sub_one_add_one(a:Nat)(ha:a≥1): a-1+1=a:=by omega

lemma Alt_ge_one(a:Nat)(ha:IsAlternating a): a≥1 :=by
  by_contra h
  simp at h
  have hlen:(Nat.digits 10 a).length=0:=by rw[h]; norm_num
  rcases ha with ⟨_,_⟩
  linarith

lemma lemma_digiteq_tongyong(x k y:Nat)(h: (Nat.digits 10 x).length=k): Nat.digits 10 (y * 10 ^ k + x)=Nat.digits 10 x ++ Nat.digits 10 y:=by
  rw [add_comm, mul_comm, ← h]
  apply Eq.symm
  apply Nat.digits_append_digits (by simp)

lemma alternating_even_high_digit {x k : ℕ}
    (hk : 1 ≤ k)
    (hlen : (Nat.digits 10 x).length = 2 * k)
    (halt : IsAlternating x)
    (heven : x % 2 = 0) : (Nat.digits 10 x)[2 * k - 1]?.getD 0 % 2 = 1 := by
  rw [← Nat.default_eq_zero, ← List.getElem!_eq_getElem?_getD, Alternatingandlength x (2*k-1) halt (by omega)]
  have := digit0ismod2 x (Alt_ge_one x halt)
  omega

theorem IMO_2004_6 : {n : ℕ | HasAlternatingMultiple n} = {n : ℕ | ¬ 20 ∣ n} :=by
  have h1 : ∀ k : ℕ , k > 0 → ∃ x : ℕ , (Nat.digits 10 x).length = 2*k ∧ IsAlternating x ∧ 2 ^ (2*k+1) ∣ x := by
    intro k hk
    induction k,hk using Nat.le_induction with
    | base =>
      use 16
      simp[IsAlternating]
      intro i hi
      replace hi : i = 0 := by omega
      simp[hi]
    | succ k hk ih =>
      rcases ih with ⟨x,hx1,hx2,hx3⟩
      rcases hx3 with ⟨d,hd⟩
      let b:=d%4
      use (16-2*b)*10^(2*k)+x
      have bsmall1 : b≤3 :=by apply Nat.le_of_lt_succ; apply Nat.mod_lt; norm_num
      have h_val : 16 - 2 * b ≥ 10 := by omega
      have lemma_digiteq: Nat.digits 10 ((16 - 2 * b) * 10 ^ (2 * k) + x)=Nat.digits 10 x ++ Nat.digits 10 (16 - 2 * b):=by
        apply lemma_digiteq_tongyong
        linarith
      have digitsum:(Nat.digits 10 ((16 - 2 * b) * 10 ^ (2 * k) + x)).length = 2 * (k + 1):=by
        rw[lemma_digiteq,List.length_append,hx1,Nat.digits_len]
        have hb : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
        rcases hb with (b1| b1 | b1| b1)
        norm_num[b1];linarith;norm_num[b1];linarith;norm_num[b1];linarith;norm_num[b1];linarith;omega;omega
      apply And.intro
      case right =>
        apply And.intro
        case right =>
          have h10:10=2*5:=by norm_num
          have h16:16=2*8:=by norm_num
          have h8:8=2*4:=by norm_num
          have h8b:(2 * 4 - b) * 1 + d=8+(d-b) := by omega
          have hpow:2 ^ (2 * (k + 1) + 1)=2^(2*k) * 8 := by
            rw[mul_add,add_assoc,pow_add]
            norm_num
          have : 2 * 8 - 2 * b = 2 * (8 - b) := by rw [Nat.mul_sub_left_distrib]
          rw[hd,h10,mul_pow,Nat.pow_add_one 2 (2*k),←mul_assoc,mul_comm (16-2*b) (2^(2*k))]
          repeat rw[mul_assoc]
          rw[←mul_add,h16,this,mul_assoc,←mul_add,hpow,mul_dvd_mul_iff_left (pow_ne_zero (2 * k) two_ne_zero),h8,mul_dvd_mul_iff_left]
          have k125(k1:Nat):(5^(2*k1)) % 4=1:=by
            rw[Nat.pow_mul]
            norm_num
            have h254:25%4=1:=by norm_num
            rw[Nat.pow_mod 25 k1 4,h254,Nat.one_pow]
          apply Nat.dvd_of_mod_eq_zero
          rw[Nat.add_mod,Nat.mul_mod,k125 k]
          norm_num
          omega;trivial
        case left=>
          unfold IsAlternating
          rw[digitsum]
          apply And.intro
          case left => linarith
          case right =>
            intro i ih
            rw[lemma_digiteq_tongyong]
            have : i < 2 * k-1 ∨ i = 2 * k-1 ∨ i > 2 * k-1 := by exact lt_trichotomy i (2 * k-1)
            rcases this with hlt | heq | hgt
            · simp
              repeat rw[List.getElem?_append_left]
              have rewri: (Nat.digits 10 x)[i]! % 2 ≠ (Nat.digits 10 x)[i + 1]!% 2:=by
                unfold IsAlternating at hx2
                apply hx2.2 i
                omega
              simp at rewri;trivial
              rw[hx1];omega;omega
            · simp;rw[List.getElem?_append_left,List.getElem?_append_right,heq,hx1]
              have one:(Nat.digits 10 x)[2 * k - 1]! %2=1:=by
                rw[Alternatingandlength,Nat.add_mod,digit0ismod2]
                have x2:x%2=0:=by
                  rw[Nat.pow_add_one] at hd
                  apply Nat.mod_eq_zero_of_dvd;use 2 ^ (2 * k)* d;rw[hd,←mul_assoc,mul_comm 2  (2 ^ (2*k))]
                rw[x2,Nat.add_zero,Nat.mod_mod];omega;apply Alt_ge_one x;trivial;trivial;omega
              have zero:(Nat.digits 10 (16 - 2 * b))[2 * k - 1 + 1 - 2 * k]! % 2=0:=by
                have twok:2 * k - 1 + 1 - 2 * k=0:=by omega
                rw[twok,digit0ismod2];omega;omega
              simp at zero one;omega
              omega;omega
            · simp;repeat rw[List.getElem?_append_right]
              have i2k:i=2*k:=by omega
              rw[i2k,hx1];simp
              have zero:(Nat.digits 10 (16 - 2 * b))[0]! %2=0 :=by
                rw[digit0ismod2];omega;omega
              have one: (Nat.digits 10 (16 - 2 * b))[1]! %2=1 :=by
                have hb : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
                rcases hb with (b1| b1 | b1| b1)
                <;> simp[b1]
              simp at zero one;omega
              omega;omega;
            · omega
      case left => exact digitsum

  have h2 : ∀ k : ℕ , k ≥ 2  → ∃ x : ℕ , ((Nat.digits 10 x).length = (k - 1) ∨  (Nat.digits 10 x).length = k) ∧ IsAlternating x ∧ 2*5^k  ∣ x ∧ (2 ∣ k → (Nat.digits 10 x).length =k) := by
      intro k hk
      induction k,hk using Nat.le_induction with
      | base =>
        use 50
        simp [IsAlternating]
        intro i hi
        simp [show i = 0 by omega]
      | succ k hk ih =>
        rcases ih with ⟨a, ha1, ha2, ha3, ha4⟩
        rcases ha3 with ⟨b, hb⟩
        have hksub:k-1+1=k := eq_sub_one_add_one k (by linarith)
        have hapos : 0 < a := by linarith[Alt_ge_one a ha2]
        have a0 : (Nat.digits 10 a)[0]! = 0 := by
          rw[Nat.digits_def'];simp
          apply Nat.dvd_iff_mod_eq_zero.mp; use 5^(k-1)*b; rw[hb]; nth_rw 1 [← hksub]; ring_nf; omega; omega
        set afirst:=(Nat.digits 10 a).getLast! with hafirst
        set temp := (5 * (afirst + 1) +4 * (b * 2 ^ (3*k + 1))) % 10 with htemp
        have temp_a : temp % 2 ≠ (Nat.digits 10 a).getLast! % 2 := by omega
        have sixtk(k1:ℕ):16^k1%5=1:=by simp [Nat.pow_mod 16 k1 5]
        have temp_b : 5 ∣ (temp * 2 ^ (k -1) + b) := by
          apply Nat.dvd_iff_mod_eq_zero.mpr
          set t2:=4* (b * 2 ^ (3*k + 1)) with ht2
          rw[htemp,Nat.add_mod,Nat.mul_mod]
          norm_num
          rw[ht2,mul_assoc,mul_assoc,←Nat.pow_add,add_assoc,add_comm 1 (k-1),hksub,show 3*k+k=4*k by omega,←mul_assoc,pow_mul,show (2^4=16) by rfl,Nat.add_mod,Nat.mul_mod,sixtk k]
          omega
        have temp_10 : temp ≥ 0 ∧ temp ≤ 9 := by rw[htemp]; omega
        have eq_x (x : ℕ) : (2 * 5 ^ k * (x * 2 ^ (k - 1) + b)) = 10 ^ k * x + a := by calc
            (2 * 5 ^ k * (x * 2 ^ (k - 1) + b)) = (2 * 5 ^ k * (x * 2 ^ (k - 1)) + 2 * 5 ^ k * b) := by ring
              _ = (2 * 5 ^ k * (x * 2 ^ (k - 1)) + a) := by rw [hb]
              _ = (x * (2 ^ 1 * 2 ^ (k - 1)) * 5 ^ k + a) := by ring
              _ = (x * (2 ^ k) * 5 ^ k + a) := by rw [← pow_add 2 1 (k - 1), add_comm 1 (k - 1), hksub]
              _ = (x * (2 ^ k * 5 ^ k) + a) := by ring
              _ = (x * (2 * 5) ^ k + a) := by rw [mul_pow]
              _ = _ := by ring
        have xl1 (x : ℕ) (h : 1 ≤ x ∧ x ≤ 9): (Nat.digits 10 x).length = 1 := by
          rw[Nat.digits_len];simp;omega;trivial;omega
        obtain a_k1 | a_k := ha1
        ·
          have k2 : 2 ∣ (k + 1) := by
            by_contra!
            have: 2 ∣ k := by omega
            have: (Nat.digits 10 a).length = k := ha4 this
            omega
          have odd_a : (Nat.digits 10 a).getLast! % 2 = 1 := by
            rw[List.getLast!_eq_getElem!,a_k1]
            have:(Nat.digits 10 a)[k-1-1]!%2=(k-1-1+(Nat.digits 10 a)[0]!)%2:=by
              exact Alternatingandlength a (k-1-1) ha2 (by omega)
            omega
          set x := (temp + 5) % 10 with hx
          have x_a : x % 2 = (Nat.digits 10 a).getLast! % 2 := by omega
          have x_b : 5 ∣ (x * 2 ^ (k -1) + b) := by
            have: x%5=temp%5 := by omega
            have: (x * 2 ^ (k - 1) + b)%5=
              (temp * 2 ^ (k - 1) + b) % 5 := by
                rw[Nat.add_mod,Nat.mul_mod,this,←Nat.mul_mod,←Nat.add_mod]
            omega
          have x_10 : x ≥ 0 ∧ x ≤ 9 := by omega
          use 2 * 5 ^ k * (x * 2 ^ (k - 1) + b)
          set n := x * 10 ^ k + a
          replace eq_x := eq_x x
          have xpos : 0 < x := by rw [odd_a] at x_a; omega
          have hpart := by calc
                    Nat.digits 10 (x * 10 ^ k + a) = Nat.digits 10 ((10 * x) * 10 ^ (k - 1) + a) := by nth_rw 1 [← hksub]; ring_nf
                    _ = Nat.digits 10 a ++ Nat.digits 10 (10 * x) := by rw [lemma_digiteq_tongyong a (k-1) (10*x) (by omega)]
                    _ = Nat.digits 10 a ++ Nat.digits 10 (10 ^ 1 * x) := by ring_nf
                    _ = Nat.digits 10 a ++ ([0] ++ Nat.digits 10 x) := by rw [Nat.digits_base_pow_mul (by linarith) (by omega)]; simp
                    _ = (Nat.digits 10 a ++ [0] ++ Nat.digits 10 x) := by rw [List.append_assoc]
          have n_eq_k1: (Nat.digits 10 (x * 10 ^ k + a)).length = k + 1 := by
            simp [hpart, List.length_append, a_k1, xl1 x (by omega), hksub]
          refine ⟨?_, ?_, ?_, ?_⟩
          ·
            rw [eq_x]
            right; rw [← n_eq_k1]
            ring_nf
          ·
            rw [eq_x]
            unfold IsAlternating
            constructor
            ·
              rw[Nat.digits_len]
              linarith;omega;omega
            ·
              rw [mul_comm]
              rw [hpart]
              repeat rw [List.length_append]
              have xdlength1 := xl1 x (by omega)
              rw [xdlength1, show [0].length = 1 by decide]
              set L := Nat.digits 10 a with hL
              set R := Nat.digits 10 x with hR
              rw [hL, hR]
              intro i hi
              simp at hi
              have hil: i < (L ++ [0] ++ R).length := by simp [List.length_append]; linarith
              have : (L ++ [0] ++ R)[i]! = (L ++ [0] ++ R)[i]'(hil) := by
                exact getElem!_pos (L ++ [0] ++ R) i (let_fun this := hil; this)
              rw [this]
              have hi1l: i + 1 < (L ++ [0] ++ R).length := by simp [List.length_append, a_k1]; linarith
              have : (L ++ [0] ++ R)[i + 1]! = (L ++ [0] ++ R)[i + 1]'(hi1l) := by
                exact getElem!_pos (L ++ [0] ++ R) (i + 1) (let_fun this := hi1l; this)
              rw [this]
              repeat rw [List.length_append] at hi1l
              rw [xdlength1, show [0].length = 1 by decide] at hi1l
              by_cases hfr : i + 1 < L.length
              · let R' := [0] ++ R
                have heq : L ++ [0] ++ R = L ++ R' := by rw [List.append_assoc L [0] R]
                repeat rw [List.getElem_of_eq heq (by omega)]
                rw [← List.getElem_append_left' hfr R']
                rw [← List.getElem_append_left' (by omega) R']
                have ha := ha2.2 i (by linarith)
                have hil: i < L.length := by linarith
                have : L[i]! = L[i]'(hil) := by
                  exact getElem!_pos L i (let_fun this := hil; this)
                rw [this] at ha
                have hi1l: i + 1 < L.length := by linarith
                have : L[i + 1]! = L[i + 1]'(hi1l) := by
                  exact getElem!_pos L (i + 1) (let_fun this := hi1l; this)
                rw [this] at ha
                exact ha
              · by_cases h0 : i + 1 = L.length
                · have hl: (L ++ [0] ++ R)[i] = L.getLast! := by calc
                    (L ++ [0] ++ R)[i] = L[i] := by rw [← List.getElem_append_left' (show i < (L ++ [0]).length by rw [List.length_append]; omega) R,
                                                        ← List.getElem_append_left' (by omega) [0]]
                    L[i] = L[i]! := by exact Eq.symm (getElem!_pos L i (by omega))
                    _ = L.getLast! := by rw [List.getLast!_eq_getElem!, show i = L.length - 1 by (rw [← h0]; simp)]
                  have hr: (L ++ [0] ++ R)[i + 1] = 0 := by calc
                    (L ++ [0] ++ R)[i + 1] = (L ++ ([0] ++ R))[0 + L.length] := by simp [h0]
                    _ = ([0] ++ R)[0]'(by rw [List.length_append]; linarith) := by rw [← List.getElem_append_right' L (by rw [List.length_append]; linarith)]
                    _ = [0][0]'(by decide) := by rw [← List.getElem_append_left' (by decide) R]
                    _ = 0 := by rfl
                  rw [hl, hr,odd_a]
                  omega
                · have h1 : i = L.length := by
                    simp at hi1l
                    have : i + 1 > L.length := by omega
                    linarith
                  have hl: (L ++ [0] ++ R)[i] = 0 := by calc
                    (L ++ [0] ++ R)[i] = (L ++ ([0] ++ R))[0 + L.length] := by simp [h1]
                    _ = ([0] ++ R)[0]'(by rw [List.length_append]; linarith) := by rw [← List.getElem_append_right' L (by rw [List.length_append]; linarith)]
                    _ = [0][0]'(by decide) := by rw [← List.getElem_append_left' (by decide) R]
                    _ = 0 := by rfl
                  have hr: (L ++ [0] ++ R)[i + 1] = x := by
                    let L' := L ++ [0]
                    have : L'.length = i + 1 := by rw [List.length_append, show [0].length = 1 by decide, h1]
                    calc
                      (L' ++ R)[i + 1] = (L' ++ R)[0 + L'.length]'(by linarith) := by simp [this]
                      _ = R[0]'(by linarith) := by rw[← List.getElem_append_right' L' (by linarith)]
                      _ = (Nat.digits 10 x)[0]'(by linarith) := by rfl
                      _ = [x][0] := by
                        have heq : Nat.digits 10 x = [x] := Nat.digits_of_lt 10 x (by omega) (by linarith)
                        exact List.getElem_of_eq heq (by rw[← hR];omega)
                      _ = x := by rfl
                  rw [hl, hr]
                  omega
          · have hk5 : 2 * 5 ^ (k + 1) = 2 * 5 ^ k * 5 := by ring
            rw [hk5]
            exact mul_dvd_mul_left (2 * 5 ^ k) x_b
          · intro _
            rw [eq_x,← n_eq_k1, mul_comm]
        ·
          set x := temp
          have x_a : x % 2 ≠ (Nat.digits 10 a).getLast! % 2 := temp_a
          have x_10 : x ≥ 0 ∧ x ≤ 9 := by exact temp_10
          have eq_x := eq_x x
          use 2 * 5 ^ k * (x * 2 ^ (k - 1) + b)
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [eq_x]
            by_cases xeq0 : x = 0
            · left
              rw [xeq0]; simp;
              exact a_k
            · right
              have xdlength1 := xl1 x (by omega)
              have := lemma_digiteq_tongyong a k x a_k
              calc
              _ = (Nat.digits 10 (x * 10 ^ k + a)).length := by ring_nf
              _ = _ := by rw [this, List.length_append, a_k, xdlength1]
          · rw [eq_x]
            unfold IsAlternating
            constructor
            · calc
              1 ≤ (Nat.digits 10 a).length := ha2.1
              _ ≤ (Nat.digits 10 (10 ^ k * x + a)).length := Nat.le_digits_len_le 10 a (10 ^ k * x + a) (by omega)
            ·
              by_cases xzero : x = 0
              · repeat rw [xzero]
                simp only [mul_zero, pow_zero, zero_add]
                intro i hi
                exact ha2.2 i hi
              rw [mul_comm,lemma_digiteq_tongyong a k x a_k,List.length_append]
              have xdlength1 : (Nat.digits 10 x).length = 1 := xl1 x (by omega)
              rw [xdlength1];
              set L := Nat.digits 10 a with hL
              set R := Nat.digits 10 x with hR
              rw [hL, hR]
              intro i hi
              simp at hi
              have hil: i < (L ++ R).length := by simp [List.length_append]; linarith
              have : (L ++ R)[i]! = (L ++ R)[i]'(hil) := by
                exact getElem!_pos (L ++ R) i (let_fun this := hil; this)
              rw [this]
              have hi1l: i + 1 < (L ++ R).length := by simp [List.length_append]; linarith
              have : (L ++ R)[i + 1]! = (L ++ R)[i + 1]'(hi1l) := by
                exact getElem!_pos (L ++ R) (i + 1) (let_fun this := hi1l; this)
              rw [this]
              by_cases hfr : i + 1 < L.length
              · rw [← List.getElem_append_left' hfr R]
                rw [← List.getElem_append_left' (by omega) R]
                have ha := ha2.2 i (by linarith)
                have hil: i < L.length := by linarith
                have : L[i]! = L[i]'(hil) := by
                  exact getElem!_pos L i (let_fun this := hil; this)
                rw [this] at ha
                have hi1l: i + 1 < L.length := by linarith
                have : L[i + 1]! = L[i + 1]'(hi1l) := by
                  exact getElem!_pos L (i + 1) (let_fun this := hi1l; this)
                rw [this] at ha
                exact ha
              · have hbound: i + 1 = L.length := by linarith
                have hl: (L ++ R)[i] = L.getLast! := by calc
                  (L ++ R)[i] = L[i] := by rw [← List.getElem_append_left' (by omega) R]
                  L[i] = L[i]! := by exact Eq.symm (getElem!_pos L i hi)
                  _ = L.getLast! := by rw [List.getLast!_eq_getElem!, show i = L.length - 1 by (rw [← hbound]; simp)]
                have hr: (L ++ R)[i + 1] = x := by calc
                  (L ++ R)[i + 1] = (L ++ R)[0 + L.length] := by simp [hbound]
                  _ = R[0]'(by linarith) := by rw[← List.getElem_append_right' L (by linarith)]
                  _ = (Nat.digits 10 x)[0]'(by linarith) := by rfl
                  _ = [x][0] := by
                    have heq : Nat.digits 10 x = [x] := Nat.digits_of_lt 10 x (by omega) (by linarith)
                    exact List.getElem_of_eq heq (by rw[← hR];omega)
                  _ = x := by rfl
                rw [hl, hr]
                by_contra! p; have p := Eq.symm p; contradiction
          · calc
              2 * 5 ^ (k + 1) = (2 * 5 ^ k) * 5 := by ring_nf
              _ ∣(2 * 5 ^ k) * (x * 2 ^ (k - 1) + b) := Nat.mul_dvd_mul_left (2 * 5 ^ k) temp_b
          ·
            intro h2
            rw [eq_x]
            have xpos : 0 < x := by
              have : Odd x := by
                have : (Nat.digits 10 a)[(Nat.digits 10 a).length - 1]! = (Nat.digits 10 a).getLast! := by exact Eq.symm List.getLast!_eq_getElem!
                have : afirst % 2 = 0 := by
                  calc
                    afirst % 2 = (Nat.digits 10 a).getLast! % 2 := by rw [hafirst]
                    _ = (Nat.digits 10 a)[k - 1]! % 2 := by rw [List.getLast!_eq_getElem!, a_k]
                    _ = (k - 1 + (Nat.digits 10 a)[0]!) % 2 := by rw [Alternatingandlength a (k - 1) ha2  (by omega)]
                    _ = 0 := by omega
                have : x % 2 = 1 := by omega
                exact Nat.odd_iff.mpr this
              unfold Odd at this
              rcases this with ⟨d, hd⟩
              refine Nat.exists_eq_add_one.mp ?_
              use 2 * d
            have xdlength1 : (Nat.digits 10 x).length = 1 := xl1 x (by omega)
            have := lemma_digiteq_tongyong a k x a_k
            calc
              _ = (Nat.digits 10 (x * 10 ^ k + a)).length := by ring_nf
              _ = _ := by rw [this, List.length_append, a_k, xdlength1]

  have h3 (m : ℕ) (a : ℕ)(ha : a ≥ 1)(hm : m ≥ 1)(d2 : ¬ 2 ∣ m)(d5 : ¬ 5 ∣ m) :
      m ∣ (10^(2*a*(m*Nat.totient m)) -1)/ (10^(2*a)-1) := by
    have dvd_of_pow_quotient {a m : ℕ} (cop : Nat.Coprime a m) : m ∣ a ^ m.totient - 1 := by
        apply Nat.dvd_iff_mod_eq_zero.mpr
        apply Nat.sub_mod_eq_zero_of_mod_eq
        exact Nat.ModEq.pow_totient cop
    let i := m * m.totient
    have hmpos : 0 < m := by
      by_contra! htemp
      apply Nat.le_zero.mp at htemp
      rw [htemp] at hm
      linarith
    have hipos : 0 < i := Nat.mul_pos hmpos (m.totient_pos.mpr hmpos)
    have denom_pos : 0 < (10 ^ (2*a) -1) := by
      rw [Nat.lt_sub_iff_add_lt, zero_add]
      calc
        1 = 10 ^ 0 := by rfl
        _ < 10 ^ (2*a) := Nat.pow_lt_pow_of_lt (by linarith) (by linarith [ha])
    have num_pos : 0 < (10 ^ (2 * a * i) - 1) := by
      have : 0 < 2*a*i := by simp; exact ⟨ha, hipos⟩
      rw [Nat.lt_sub_iff_add_lt, zero_add]
      calc
        1 = 10 ^ 0 := by rfl
        _ < 10 ^ (2*a*i) := Nat.pow_lt_pow_of_lt (by linarith) this
    have denom_dvd : 10 ^ (2*a) -1 ∣ 10 ^ (2*a*i)-1 := by
      have := nat_sub_dvd_pow_sub_pow (10^(2*a)) 1 i
      nth_rewrite 2 [pow_mul]
      simp at this; exact this
    have dvd_if_all_prime : ∀ p : ℕ, Nat.Prime p → p ∣ m → padicValNat p m ≤ padicValNat p ((10 ^ (2*a*i)-1)/(10 ^ (2*a) -1)) := by
      intro p hp hpm
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      rw [padicValNat.div_of_dvd denom_dvd]
      by_cases hpdvd : p ∣ 10 ^ (2*a) -1
      · have hpcoprime10 : Nat.Coprime p 10 := by
          apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
          by_contra! hnot
          have : 10 ∣  10 ^ (2*a) := Dvd.dvd.pow (by omega) (by omega)
          have hnot : p ∣ 10 ^ (2*a) := Nat.dvd_trans hnot this
          have : p ∣ 1 := by
            apply Nat.dvd_trans (Nat.dvd_sub hnot hpdvd)
            have : 10^(2*a) - (10^(2*a) - 1) = 1 := by omega
            rw [this]
          exact lt_irrefl p (lt_of_le_of_lt (Nat.le_of_dvd zero_lt_one this) hp.one_lt)
        by_cases h₂ : p = 2
        · have hT : Nat.gcd p 10 = 2 := by rw [h₂]; rfl
          have hF : Nat.gcd p 10 = 1 := by rw [hpcoprime10]
          rw [hF] at hT
          contradiction
        have hp1 : Odd p := Nat.Prime.odd_of_ne_two hp h₂
        have hx : ¬ p ∣ 10 ^ (2*a) := by
          by_contra htemp
          have : 0 < 2 * a := by omega
          have hT := ((Nat.coprime_pow_right_iff this p 10)).mpr hpcoprime10
          have hF := Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt hp) (Nat.dvd_refl p) htemp
          contradiction
        rw [pow_mul]
        nth_rewrite 1 [← one_pow i]
        rw [padicValNat.pow_sub_pow hp1 (by omega) hpdvd hx (Nat.ne_of_gt hipos)]; simp
        rw [padicValNat.mul (by linarith) (by simp; linarith)]; simp
      · haveI : Fact (Nat.Prime p) := ⟨hp⟩
        rw [padicValNat.eq_zero_of_not_dvd hpdvd]; simp
        have hmcop10 : Nat.Coprime 10 m := by
          rw [show 10=2*5 by rfl]
          apply Nat.coprime_mul_iff_left.mpr
          constructor
          · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr d2
          · exact (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr d5
        have mdvdnum : m ∣ (10^(2*a*i) - 1) := by
          rw [calc
                10^(2*a*i) - 1 = 10^(2*a*(m*m.totient)) - 1 := by rfl
                _ = 10^((2*a*m)*m.totient) - 1 := by ring_nf
                _ = (10^(2*a*m))^m.totient - 1 := by rw [pow_mul]]
          have : 0 < 2 * a * m := by simp; exact ⟨ha, hmpos⟩
          exact dvd_of_pow_quotient ((Nat.coprime_pow_left_iff this 10 m).mpr hmcop10)
        have : (p ^ padicValNat p m) ∣ (10^(2*a*i) - 1) :=
          Nat.dvd_trans pow_padicValNat_dvd mdvdnum
        exact (padicValNat_dvd_iff_le (Nat.ne_of_gt num_pos)).mp this
    let M := ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1))
    have hMpos : 0 < M := Nat.div_pos (Nat.le_of_dvd (by omega) denom_dvd) (by omega)
    apply (Nat.dvd_iff_prime_pow_dvd_dvd M m).mpr
    intro p k hp hd
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    by_cases hk : k = 0
    · rw[hk]; norm_num
    have : k ≤ padicValNat p M := by calc
      k ≤ padicValNat p m := (padicValNat_dvd_iff_le (by omega)).mp hd
      _ ≤ padicValNat p M := dvd_if_all_prime p hp (Nat.dvd_of_pow_dvd (by omega) hd)
    exact (padicValNat_dvd_iff_le (by omega)).mpr this

  have h4 (x : ℕ) (a : ℕ)(i : ℕ)(hi : i ≥ 1)(ha : a ≥ 1)(hx1 : (Nat.digits 10 x).length = 2*a)(hx2 : IsAlternating x)(hxeven : 2 ∣ x) :
      Nat.digits 10 (x*((10 ^ (2*a*i)-1)/(10 ^ (2*a) -1))) = (List.replicate i (Nat.digits 10 x)).flatten ∧ IsAlternating (x*((10 ^ (2*a*i)-1)/(10 ^ (2*a) -1))):= by
    induction i,hi using Nat.le_induction with
    | base =>
      have : (10 ^ (2 * a) - 1) / (10 ^ (2 * a) - 1) = 1 := by
        simp[show 10^(2*a) - 1 > 0 by refine Nat.zero_lt_sub_of_lt ?_;refine Nat.one_lt_pow ?_ ?_;omega;omega]
      simp[this]
      exact hx2
    | succ i hi ih =>
      have c1 : 10^(2*a)-1 ∣ (10^(2*a))^i-1^i := by exact nat_sub_dvd_pow_sub_pow (10 ^ (2 * a)) 1 i
      simp[show (10 ^ (2 * a)) ^ i = 10^(2*a*i) by exact Eq.symm (Nat.pow_mul 10 (2 * a) i)] at c1
      have c2 : 10^(2*a)-1 ∣ (10^(2*a))^(i+1)-1^(i+1) := by exact nat_sub_dvd_pow_sub_pow (10 ^ (2 * a)) 1 (i+1)
      simp[show (10 ^ (2 * a)) ^ (i+1) = 10^(2*a*(i+1)) by exact Eq.symm (Nat.pow_mul 10 (2 * a) (i+1))] at c2
      have c3 : 10 ^ (2 * a) - 1 > 0 := by refine Nat.zero_lt_sub_of_lt ?_;refine Nat.one_lt_pow ?_ ?_;omega;omega
      have rewri : (10 ^ (2 * a * (i + 1)) - 1) / (10 ^ (2 * a) - 1) = 10^(2*a*i) + (10^(2*a*i)-1)/(10^(2*a)-1) := by
        obtain⟨d1,hd1⟩:=c1
        obtain⟨d2,hd2⟩:=c2
        simp[hd1,hd2]
        rw[show (10 ^ (2 * a) - 1) * d2 / (10 ^ (2 * a) - 1) = d2 by exact Nat.mul_div_right d2 c3]
        rw[show (10 ^ (2 * a) - 1) * d1 / (10 ^ (2 * a) - 1) = d1 by exact Nat.mul_div_right d1 c3]
        apply Nat.eq_of_mul_eq_mul_left c3
        rw[← hd2,mul_add,mul_add,← hd1]
        rw[show (10 ^ (2 * a) - 1) * 10 ^ (2 * a * i) = 10 ^ (2*a) * 10^(2*a*i) - 10^(2*a*i) by exact Nat.sub_one_mul (10 ^ (2 * a)) (10 ^ (2 * a * i))]
        rw[← pow_add]
        ring_nf
        refine Eq.symm (Nat.sub_add_sub_cancel ?_ ?_)
        refine Nat.le_mul_of_pos_left (10 ^ (a * i * 2)) ?_
        exact Nat.pos_of_neZero (10 ^ (a * 2))
        exact Nat.one_le_pow' (a * i * 2) 9
      replace rewri : x*((10 ^ (2*a*(i+1))-1)/(10 ^ (2*a) - 1)) = x*10^(2*a*i) + x*((10^(2*a*i)-1)/(10^(2*a)-1)) := by rw[rewri,mul_add]
      repeat rw[rewri]
      obtain⟨ih1,ih2⟩:=ih
      have c6 : (Nat.digits 10 (x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1)))).length = i*2*a := by simp[ih1,hx1]; ring
      have c9 : Nat.digits 10 (x * 10 ^ (2 * a * i) + x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1))) = (List.replicate (i + 1) (Nat.digits 10 x)).flatten := by
        rw[List.replicate_succ',lemma_digiteq_tongyong,ih1]; simp; rw[c6]; ring
      have h6' : ((List.replicate (i + 1) (Nat.digits 10 x)).flatten).length = 2*a*(i+1) := by simp; rw[hx1]; ring
      constructor
      · exact c9
      · simp[IsAlternating]
        simp[*]
        constructor
        · ring_nf;omega
        · intro t ht
          repeat rw[List.replicate_succ', List.flatten_concat]
          have ih4 : IsAlternating (x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1))) :=by exact ih2
          simp[IsAlternating,ih1] at ih2
          simp[*] at ih2
          obtain⟨ih2,ih3⟩:=ih2
          by_cases ht : t+1 < i*2*a
          · specialize ih3 t (by ring_nf; ring_nf at ht;exact ht)
            have c11 : ((List.replicate i (Nat.digits 10 x)).flatten).length = i*2*a := by rw[ih1] at c6; exact c6
            repeat rw[List.getElem?_append_left (by omega)]
            exact ih3
          · simp at ht
            by_cases ht1 : t = i*2*a-1
            · have ge_two : a*i*2 ≥ 2 := by refine Nat.le_mul_of_pos_left 2 (Nat.mul_pos ha hi)
              rw[List.getElem?_append_left,List.getElem?_append_right]
              nth_rw 1 [← ih1]
              simp[hx1,ht1,eq_sub_one_add_one (i*2*a) (by rw[mul_assoc,mul_comm,mul_assoc,mul_comm];omega),show i*(2*a)=i*2*a by ring]
              have c13 : (Nat.digits 10 (x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1))))[2*(i* a) - 1]?.getD 0 % 2 =1 := by
                apply alternating_even_high_digit
                · exact Right.one_le_mul hi ha
                · rw[c6]; ring
                · exact ih4
                · have : 2 ∣ x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1)) := by exact Nat.dvd_mul_right_of_dvd hxeven ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1))
                  exact Nat.dvd_iff_mod_eq_zero.mp this
              ring_nf at c13
              ring_nf
              rw[c13,Nat.digits_def'];obtain⟨d,hd⟩:=hxeven;simp[hd]
              omega
              · linarith[Alt_ge_one x hx2]
              · simp[hx1,ht1,eq_sub_one_add_one (i*2*a) (by rw[mul_assoc,mul_comm,mul_assoc,mul_comm];omega)];ring_nf;rfl
              · simp[hx1,ht1];rw[← mul_assoc,show i*2*a=a*i*2 by ring];omega
            · replace ht : i*(2*a) ≤ t := by rw[← mul_assoc];omega
              repeat rw[List.getElem?_append_right]
              simp[hx1];
              simp[IsAlternating] at hx2
              replace hx2 := hx2.2
              specialize hx2 (t-i*(2*a)) ?_
              · simp[hx1];rename_i ht2;
                qify; simp[ht]; ring_nf; rw[mul_comm (i:ℚ) (a:ℚ)]
                qify at ht2; rw[mul_add] at ht2;
                linarith
              have : t + 1 ≥ i*(2*a) := by omega
              rw[show t + 1 - i*(2*a)= t - i*(2*a) + 1 by qify; simp[this,ht];ring_nf]
              exact hx2
              all_goals simp[hx1];omega

  have div_b_sub_1 (k b: ℕ) (h: b > 0) : (b - 1) ∣ b ^ k - 1 := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      have : b ^ (k + 1) - 1 = (b - 1) * (b ^ k) + b ^ k - 1 := by
        nth_rw 1 [Nat.add_comm, Nat.pow_add, Nat.pow_one, ← Nat.sub_add_cancel (Nat.one_le_of_lt h), add_mul, one_mul]
      rw [this, ← Eq.symm (Nat.add_sub_assoc (Nat.pow_pos h) ((b - 1) * b ^ k))]
      exact Nat.dvd_add (Nat.dvd_mul_right (b - 1) (b ^ k)) ih

  have not_dvd_of_padicValNat_eq (a p m n : ℕ) (npos: n > 0) (hp: Nat.Prime p) (ha : a = padicValNat p n) (hm : p ^ a * m∣ n) : ¬ p ∣ m := by
    intro ⟨k, hk⟩
    have h1 : p ^ a * (p * k) = p ^ (a + 1) * k := by ring
    rw [hk, h1] at hm
    have h2 : a + 1 ≤ padicValNat p n := (@padicValNat_dvd_iff_le p ⟨hp⟩ n (a + 1) (by linarith)).mp (dvd_of_mul_right_dvd hm)
    linarith

  have digits_append (m n k i : ℕ) (hk : k = (Nat.digits 10 n).length) :
      (Nat.digits 10 m)[i]! = (Nat.digits 10 (m * 10 ^ k + n))[i + k]! := by
    have h1 : Nat.digits 10 n ++ Nat.digits 10 m = Nat.digits 10 (m * 10 ^ k + n) := by
      rw [add_comm, mul_comm, hk]
      apply Nat.digits_append_digits (by simp)
    rw [← h1]
    simp [hk, List.getElem?_append_right]

  have digits_zero_eq_mod {b n : ℕ} (hb : b > 1) (hn : n > 0) :
      (Nat.digits b n)[0]! = n % b := by
    rw [Nat.digits_def' (by omega) (by omega)]
    simp

  have digits_mul_pow_offset (n k i : ℕ) (hn : n > 0) :
      (Nat.digits 10 n)[i]! = (Nat.digits 10 (n * 10 ^ k))[i + k]! := by
    rw [mul_comm, Nat.digits_base_pow_mul (by simp) hn]
    simp [List.getElem?_append_right]

  have pow10 : ∀ k : ℕ, (Nat.digits 10 (10 ^ k)).length = k + 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => simp [Nat.pow_add, Nat.pow_one] at ih ⊢; omega

  have h01alt22 {a : ℕ} (apos : a > 0) : ∀ i : ℕ, i < 2 * a → (Nat.digits 10 ((10 ^ (2 * a) - 1)/(10 ^ 2 - 1)))[i]! = 1 - i % 2 := by
    induction a, apos using Nat.le_induction with
    | base =>
      intro i hi
      norm_num
      interval_cases i <;> simp
    | succ k hk ih =>
      have : (10 ^ (2 * (k + 1)) - 1) = (10 ^ (2 * k) - 1) * 10 ^ 2 + 99 := by
        calc
          _ = 10 ^ (2 * k) * 10 ^ 2 - 1 := by ring_nf
          _ = (10 ^ (2 * k) - 1) * 10 ^ 2 + 99 := by rw [← Nat.sub_add_cancel (Nat.pos_of_neZero (10 ^ (2 * k)))]; omega
      have _h2 : (10 ^ (2 * (k + 1)) - 1) / (10 ^ 2 - 1) = (100 ^ k - 1) / 99 * 100 + 1 := by
        calc
          _ = ((10 ^ 2) ^ k - 1) * 10 ^ 2 / 99 + 1 := by rw [← pow_mul 10 2 k]; omega
          _ = (100 ^ k - 1) / 99 * 100 + 1 := by norm_num; rw [Nat.div_mul_right_comm (div_b_sub_1 k 100 (by simp)) 100]
      rw [_h2]
      have _h3 (i : ℕ) : (Nat.digits 10 ((100 ^ k - 1) / 99 * 100 + 1))[i + 2]! = (Nat.digits 10 ((100 ^ k - 1) / 99))[i]! := by
        have : 100 ^ k ≥ 100 := Nat.le_pow hk
        rw [show 100 = 10 * 10 by simp, ← mul_assoc]
        simp [digits_append ((100 ^ k - 1) / 99 * 10) 1 1 (i + 1) (by norm_num),
          digits_mul_pow_offset ((100 ^ k - 1) / 99) 1 i (Nat.div_pos (by omega) (by norm_num))]
      have _h4 : (10 ^ (2 * k) - 1) / (10 ^ 2 - 1) = (100 ^ k - 1) / 99 := by rw [Nat.pow_mul]; norm_num
      intro i hi
      match i with
      | 0 => simp; omega
      | 1 =>
        simp
        by_cases k_one : k = 1
        . rw [k_one]; norm_num
        . have : 100 ^ k > 100 := @Nat.pow_lt_pow_of_lt 100 1 k (by norm_num) (by omega)
          have := @digits_zero_eq_mod 10 (((100 ^ k - 1) / 99 * 100 + 1) / 10) (by simp) (by omega)
          simp at this
          omega
      | t + 2 =>
        have _h5 := ih t (by omega)
        rw [_h4, ← _h3 t] at _h5
        rw [_h5]
        omega

  have h01alt {i: ℕ} (ipos : i > 0) : IsAlternating ((10 ^ (2 * i) - 1)/(10 ^ 2 - 1)) := by
    unfold IsAlternating
    constructor
    . have : 10 ^ (2 * i) ≥ 10 ^ 2 := Nat.pow_le_pow_of_le (by simp) (by linarith)
      have _h1 := Nat.le_digits_len_le 10 1 ((10 ^ (2 * i) - 1) / (10 ^ 2 - 1)) (by omega)
      have _h2 : (Nat.digits 10 1).length = 1 := by simp
      omega
    intro j hj
    have _h3 (i : ℕ) (ipos : i > 0) : (Nat.digits 10 ((10 ^ (2 * i) - 1) / 10)).length ≤ 2 * i:= by
      have _h1 : (10 ^ (2 * i) - 1) / 10 ≤ 10 ^ (2 * i) / 10 := Nat.div_le_div_right (by simp)
      nth_rw 2 [← @Nat.sub_add_cancel (2 * i) 1 (by omega)] at _h1
      rw [pow_succ 10 _, Nat.mul_div_cancel _ (by omega)] at _h1
      have _h2 := Nat.le_digits_len_le 10 ((10 ^ (2 * i) - 1) / 10) (10 ^ (2 * i - 1)) _h1
      have _h3 := pow10 (2 * i - 1)
      omega
    have _h1 : (Nat.digits 10 ((10 ^ (2 * i) - 1) / (10 ^ 2 - 1))).length ≤ 2 * i := by
      linarith [Nat.le_digits_len_le 10 ((10 ^ (2 * i) - 1) / (10 ^ 2 - 1)) ((10 ^ (2 * i) - 1) / 10) (by apply Nat.div_le_div_left (by norm_num) (by norm_num)),
                _h3 i (by omega)]
    rw [h01alt22 ipos j (by linarith), h01alt22 ipos (j+1) (by linarith)]
    omega

  ext n
  simp
  symm
  constructor
  replace h3 (m : ℕ) (a : ℕ)(ha : a ≥ 1)(hm : m ≥ 1)(d2 : ¬ 2 ∣ m)(d5 : ¬ 5 ∣ m) :
      m ∣ (10^(2*a*m*(Nat.totient m)) -1)/ (10^(2*a)-1) := by
    rw[show 2*a*m*(Nat.totient m) = 2*a*(m*Nat.totient m) by ring]
    exact h3 m a ha hm d2 d5
  · intro hn
    by_cases d5 : ¬ 5 ∣ n
    · let a := padicValNat 2 n
      by_cases ha : a=0
      · let i : ℕ := n * Nat.totient n
        use (10 ^ (2*i)-1)/(10 ^ (2) -1)
        constructor
        · have _h1 : n ≠ 0 := by omega
          have _h2 := padicValNat.eq_zero_iff.mp ha
          simp [_h1] at _h2
          have _h3 := h3 n 1 (le_refl 1) (Nat.one_le_iff_ne_zero.mpr _h1) (Nat.two_dvd_ne_zero.mpr _h2) d5
          rw [mul_assoc 2, mul_one] at _h3
          exact _h3
        · have _h1 : n > 0 := by omega
          have _h2: n.totient > 0 := Nat.totient_pos.mpr _h1
          exact h01alt (Nat.mul_pos _h1 _h2)
      · replace ha : a > 0 := by omega
        specialize h1 a ha
        obtain ⟨x,hx1,hx2,hx3⟩ := h1
        have ha1 : 2 ^ a ∣ n := by exact pow_padicValNat_dvd
        obtain⟨m,hm⟩:=ha1
        let i : ℕ := m * Nat.totient m
        use x*(10 ^ (2*a*i)-1)/(10 ^ (2*a) -1)
        constructor
        · have _h1 : m > 0 := by
            by_contra _h1
            simp at _h1
            rw [_h1] at hm
            omega
          have _h2 : ¬2 ∣ m := not_dvd_of_padicValNat_eq a 2 m n (by omega) Nat.prime_two rfl (dvd_of_eq (id (Eq.symm hm)))
          have _h3 : ¬5 ∣ m := by
            contrapose! d5
            rw [hm]
            exact Nat.dvd_mul_left_of_dvd d5 (2 ^ a)
          have hmdiv := h3 m a ha _h1 _h2 _h3
          have hadiv : 2 ^ a ∣ x := by
            have : 2 ^ (2 * a + 1) = 2 ^ a * 2 ^ (a + 1) := by ring
            have : 2 ^ a ∣ 2 ^ (2 * a + 1) := by
              rw [this]
              exact Nat.dvd_mul_right (2 ^ a) (2 ^ (a + 1))
            exact Nat.dvd_trans this hx3
          have _h4 := Nat.mul_dvd_mul hadiv hmdiv
          rw [← hm] at _h4
          unfold i
          rw [← mul_assoc (2 * a)]
          have _h5 := div_b_sub_1 i (10 ^ (2 * a)) (by simp)
          have : (10 ^ (2 * a)) ^ i = 10 ^ (2 * a * i) := by ring
          rw [this] at _h5
          unfold i at _h5
          have := Nat.mul_div_assoc x _h5
          rw [← mul_assoc (2 * a)] at this
          rw [this]
          exact _h4
        · have _h1 : m > 0 := by
            by_contra _h1
            simp at _h1
            rw [_h1] at hm
            omega
          have : 2 ∣ 2 ^ (2 * a + 1) := Dvd.intro_left (Nat.pow 2 (2 * a)) rfl
          have _h2 := (h4 x a i (Right.one_le_mul _h1 (Nat.totient_pos.mpr _h1)) ha hx1 hx2 (Nat.dvd_trans this hx3)).2
          have _h3 := Eq.symm (Nat.mul_div_assoc x (div_b_sub_1 i (10 ^ (2 * a)) (Nat.pos_of_neZero (10 ^ (2 * a)))))
          have _h4 : (10 ^ (2 * a)) ^ i = (10 ^ (2 * a * i)) := by ring
          rw [_h4] at _h3
          rw [_h3] at _h2
          exact _h2
    · push_neg at d5
      let b := padicValNat 5 n
      let a := padicValNat 2 n
      have ha : a≤1 := by
        by_contra ha
        replace ha : a ≥ 2 := by omega
        have d4 : 2 ^ a ∣ n := by exact pow_padicValNat_dvd
        haveI : 2 ^ 2 ∣ 2 ^ a := by exact Nat.pow_dvd_pow_iff_le_right'.mpr ha
        replace d4 : 4 ∣ n := by exact Nat.dvd_trans this d4
        have d20 : 4*5 ∣ n := by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl d4 d5
        tauto
      have h5 : Fact (Nat.Prime 5) := by decide
      have hb : 1 ≤ padicValNat 5 n := by refine one_le_padicValNat_of_dvd ?_ d5 ; omega
      replace hb : 2*b ≥ 2 := by exact Nat.le_mul_of_pos_right 2 hb
      specialize h2 (2*b) hb
      obtain ⟨x,hx1,hx2,hx3,hx4⟩ := h2
      simp at hx4
      have ha1 : 2 ^ a ∣ n := by exact pow_padicValNat_dvd
      have hb1 : 5 ^ b ∣ n := by exact pow_padicValNat_dvd
      have hab : 2 ^ a * 5 ^ b ∣ n := by
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ha1 hb1
        exact Nat.pow_gcd_pow_of_gcd_eq_one rfl
      obtain⟨m,hm⟩:=hab
      clear ha1 hb1
      let i : ℕ := m * Nat.totient m
      use x*(10 ^ (2*b*i)-1)/(10 ^ (2*b) -1)
      constructor
      · have _h1 : m > 0 := by
          by_contra _h1
          simp at _h1
          rw [_h1] at hm
          omega
        have _h2 : ¬2 ∣ m := not_dvd_of_padicValNat_eq a 2 m n (by omega) Nat.prime_two rfl ⟨5 ^ b, by rw [hm]; ring⟩
        have _h3 : ¬5 ∣ m := not_dvd_of_padicValNat_eq b 5 m n (by omega) Nat.prime_five rfl ⟨2 ^ a, by rw [hm]; ring⟩
        have hmdiv := h3 m b (by linarith) _h1 _h2 _h3
        have habdiv : (2 ^ a * 5 ^ b) ∣ x := by
          have : 5 ^ b ∣ 5 ^ (2 * b) := by rw [mul_comm, pow_mul, pow_two]; exact Nat.dvd_mul_left (5 ^ b) (5 ^ b)
          interval_cases a
          . simp; apply Nat.dvd_trans this (dvd_of_mul_left_dvd hx3)
          . simp; apply Nat.dvd_trans (Nat.mul_dvd_mul_left 2 this) hx3
        have _h4 := Nat.mul_dvd_mul habdiv hmdiv
        rw [← hm] at _h4
        unfold i
        rw [← mul_assoc (2 * b)]
        have _h5 := div_b_sub_1 i (10 ^ (2 * b)) (by simp)
        have : (10 ^ (2 * b)) ^ i = 10 ^ (2 * b * i) := by ring
        rw [this] at _h5
        unfold i at _h5
        have := Nat.mul_div_assoc x _h5
        rw [← mul_assoc (2 * b)] at this
        rw [this]
        exact _h4
      · have _h1 : m > 0 := by
          by_contra _h1
          simp at _h1
          rw [_h1] at hm
          omega
        have : 2 ∣ 2 * 5 ^ (2 * b) := Nat.dvd_mul_right 2 (5 ^ (2 * b))
        have _h2 := (h4 x b i (Right.one_le_mul _h1 (Nat.totient_pos.mpr _h1)) (by omega) hx4 hx2 (Nat.dvd_trans this hx3)).2
        have _h3 : x * (((10 ^ (2 * b)) ^ i - 1) / (10 ^ (2 * b) - 1)) = x * ((10 ^ (2 * b)) ^ i - 1) / (10 ^ (2 * b) - 1) := by
          exact Eq.symm (Nat.mul_div_assoc x (div_b_sub_1 i (10 ^ (2 * b)) (Nat.pos_of_neZero (10 ^ (2 * b)))))
        have _h4 : (10 ^ (2 * b)) ^ i = (10 ^ (2 * b * i)) := by ring
        rw [_h4] at _h3
        rw [_h3] at _h2
        exact _h2
  · contrapose
    push_neg
    unfold HasAlternatingMultiple
    simp
    intro hn x hnx
    by_cases hx_zero : x = 0
    . unfold IsAlternating
      rw [hx_zero]
      norm_num
    have ⟨m, hm⟩ : 20 ∣ x := Nat.dvd_trans hn hnx
    unfold IsAlternating
    intro ⟨_h1, _h2⟩
    have _h4 : (Nat.digits 10 x)[0]! = 0 := by
      rw [@digits_zero_eq_mod 10 x (by simp) (by omega)]
      omega
    have : (Nat.digits 10 x).length ≥ (Nat.digits 10 20).length := Nat.le_digits_len_le 10 20 x (by omega)
    norm_num at this
    have _h3 := _h2 0 this
    rw [_h4, show x = m * 2 * 10 by omega] at _h3
    have := digits_mul_pow_offset (m * 2) 1 0 (by omega)
    rw [pow_one] at this
    rw [← this] at _h3
    rw [@digits_zero_eq_mod 10 (m * 2) (by simp) (by omega)] at _h3
    norm_num at _h3
