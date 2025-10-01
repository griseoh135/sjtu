import Mathlib
set_option maxHeartbeats 10000000

def IsAlternating : ℕ → Prop := fun n ↦
    (Nat.digits 10 n).length ≥ 1 ∧ ∀ i : ℕ, i + 1 < (Nat.digits 10 n).length → (Nat.digits 10 n)[i]! % 2 ≠ (Nat.digits 10 n)[i + 1]! % 2

def HasAlternatingMultiple : ℕ → Prop := fun n ↦
    ∃ m : ℕ, n ∣ m ∧ IsAlternating m

theorem IMO_2004_6 :
  {n : ℕ | HasAlternatingMultiple n} = {n : ℕ | ¬ 20 ∣ n} :=by
    have alternating_even_high_digit {x k : ℕ}
        (hk : 1 ≤ k)
        (hlen : (Nat.digits 10 x).length = 2 * k)
        (halt : IsAlternating x)
        (heven : x % 2 = 0) : (Nat.digits 10 x)[2 * k - 1]?.getD 0 % 2 = 1 := by
      have h0 : (Nat.digits 10 x)[0]?.getD 0 % 2 = 0 := by
        have : (Nat.digits 10 x)[0]?.getD 0 = x % 10 := by
          cases x with
          | zero => simp
          | succ n => rw [Nat.digits_eq_cons_digits_div (by norm_num) (by simp)]; simp
        rw [this]
        omega
      have h (i : ℕ) (hi : i < k) : (Nat.digits 10 x)[2 * i]?.getD 0 % 2 = 0 ∧ (Nat.digits 10 x)[2 * i + 1]?.getD 0 % 2 = 1 := by
        induction i with
        | zero =>
          constructor
          · exact h0
          · have := halt.2 0 (by rw [hlen]; omega)
            contrapose! this
            simp at *
            rw [h0]
            symm
            exact this
        | succ i ih =>
          have h1 := ih (by omega)
          have idx1 : 2 * (i + 1) < (Nat.digits 10 x).length := by simp [hlen]; omega
          have idx2 : 2 * (i + 1) + 1 < (Nat.digits 10 x).length := by simp [hlen]; omega
          have h2 : (Nat.digits 10 x)[2 * (i + 1)]?.getD 0 = (Nat.digits 10 x)[2 * (i + 1)]! := by simp
          have h3 : (Nat.digits 10 x)[2 * (i + 1) + 1]?.getD 0 = (Nat.digits 10 x)[2 * (i + 1) + 1]! := by simp
          rw [h2, h3]
          have alt1 := halt.2 (2 * i + 1) (by simp [hlen]; omega)
          have alt2 := halt.2 (2 * (i + 1)) (by simp [hlen]; omega)
          have two_mul_i_p1_p1_eq_two_mul_ip1 : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
          rw [two_mul_i_p1_p1_eq_two_mul_ip1] at alt1
          rcases h1 with ⟨_, h1_odd⟩
          simp at alt1 alt2 ⊢
          push_neg at alt1 alt2
          rw [h1_odd] at alt1
          have h_even' : (Nat.digits 10 x)[2 * (i + 1)]?.getD 0 % 2 = 0 := by omega
          rw [h_even'] at alt2
          have h_odd' : (Nat.digits 10 x)[2 * (i + 1) + 1]?.getD 0 % 2 = 1 := by omega
          omega
      have k_pos : k - 1 < k := by omega
      have ⟨_, last_odd⟩ := h (k - 1) k_pos
      have : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
      rw [this] at last_odd
      exact last_odd
    have dvd_of_pow_quotient {a m : ℕ} (cop : Nat.Coprime a m) : m ∣ a ^ m.totient - 1 := by
      apply Nat.dvd_iff_mod_eq_zero.mpr
      apply Nat.sub_mod_eq_zero_of_mod_eq
      exact Nat.ModEq.pow_totient cop
    have lemma_digiteq_tongyong(x k y:Nat)(h_big:y>0)(h: (Nat.digits 10 x).length=k): Nat.digits 10 (y * 10 ^ k + x)=Nat.digits 10 x ++ Nat.digits 10 y:=by
      let L:=Nat.digits 10 x++ Nat.digits 10 (y)
      have ofdigiteq: Nat.ofDigits 10 L= ((y) * 10 ^ ( k) + x) :=by
        unfold L
        nth_rw 1 [Nat.ofDigits_append]
        rw[h,Nat.ofDigits_digits,Nat.ofDigits_digits]
        rw[mul_comm]
        ring
      unfold L at ofdigiteq
      rw[ofdigiteq.symm]
      rw[Nat.digits_ofDigits]
      norm_num
      --digits_lt_base'
      have leftx: ∀ l1∈Nat.digits 10 x, l1 < 10 := by
        intro l1 hl1
        apply Nat.digits_lt_base
        norm_num
        apply hl1
      have leftb: ∀ l2∈Nat.digits 10 y, l2 < 10 := by
        intro l2 hl2
        apply Nat.digits_lt_base
        norm_num
        apply hl2
      intro l hl
      rw[List.mem_append] at hl
      apply Or.elim hl
      case left => exact leftx l
      case right => exact leftb l
      intro hnonempty
      have h_digits_ne_nil : Nat.digits 10 y ≠ [] :=by
        rw [Nat.digits_ne_nil_iff_ne_zero]
        apply Nat.ne_of_gt
        linarith [h_big]
      rw[List.getLast_append_of_ne_nil]
      apply Nat.getLast_digit_ne_zero
      apply Nat.ne_of_gt
      linarith [h_big]
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
        have bsmall : b<4 :=by apply Nat.mod_lt; norm_num
        have bsmall1:b≤3 :=by exact Nat.le_of_lt_succ bsmall
        have h_big : 10 ≤ 16 - 2 * b := by omega
        have h_val : 16 - 2 * b ≥ 10 := h_big
        have lemma_digiteq: Nat.digits 10 ((16 - 2 * b) * 10 ^ (2 * k) + x)=Nat.digits 10 x ++ Nat.digits 10 (16 - 2 * b):=by
          let L:=Nat.digits 10 x++ Nat.digits 10 (16 - 2 * b)
          have ofdigiteq: Nat.ofDigits 10 L= ((16 - 2 * b) * 10 ^ (2 * k) + x) :=by
            unfold L
            nth_rw 1 [Nat.ofDigits_append]
            rw[hx1,Nat.ofDigits_digits,Nat.ofDigits_digits]
            rw[mul_comm]
            ring
          unfold L at ofdigiteq
          rw[ofdigiteq.symm]
          rw[Nat.digits_ofDigits]
          norm_num
          --digits_lt_base'
          have leftx: ∀ l1∈Nat.digits 10 x, l1 < 10 := by exact fun l1 a => Nat.digits_lt_base' a
          have leftb: ∀ l2∈Nat.digits 10 (16 - 2 * b), l2 < 10 := by
            intro l2 hl2
            apply Nat.digits_lt_base
            norm_num
            apply hl2
          intro l hl
          rw[List.mem_append] at hl
          apply Or.elim hl
          case left => exact leftx l
          case right => exact leftb l
          intro hnonempty
          have h_digits_ne_nil : Nat.digits 10 (16 - 2 * b) ≠ [] :=by
            rw [Nat.digits_ne_nil_iff_ne_zero]
            apply Nat.ne_of_gt
            linarith [h_big]
          rw[List.getLast_append_of_ne_nil]
          apply Nat.getLast_digit_ne_zero
          apply Nat.ne_of_gt
          linarith [h_big]
        have digitsum:(Nat.digits 10 ((16 - 2 * b) * 10 ^ (2 * k) + x)).length = 2 * (k + 1):=by
          rw[lemma_digiteq,List.length_append,hx1]
          have digit2: (Nat.digits 10 (16-2*b)).length=2 :=by
            rw[Nat.digits_len]
            have logeq1:Nat.log 10 (16 - 2 * b)=1:=by
              rw[Nat.log_eq_iff]
              apply And.intro
              case left =>
                apply h_val
              case right =>
                have ten2:10^(1+1)=100:=by norm_num
                rw[ten2]
                apply Nat.lt_of_le_of_lt
                apply Nat.sub_le
                norm_num
              have one_not_eq_zero:1≠0:=by norm_num
              exact Or.inl one_not_eq_zero
            rw[logeq1]
            norm_num
            linarith[h_big]
          rw[digit2]
          linarith
        apply And.intro
        case right =>
          apply And.intro
          case right =>
            have h10:10=2*5:=by norm_num
            have h16:16=2*8:=by norm_num
            have h8:8=2*4:=by norm_num
            have h8b:(2 * 4 - b) * 1 + d=8+(d-b) := by
              rw[←h8,mul_one]
              rw[←Nat.mod_add_div d 4]
              nth_rw 4 [add_comm]
              unfold b
              rw[Nat.add_sub_cancel_right]
              have comm: 8+(d % 4 + 4 * (d / 4))-d % 4=8 - d % 4 + (d % 4 + 4 * (d / 4)):=by
                apply Nat.sub_add_comm
                apply le_of_lt
                apply lt_trans
                apply Nat.mod_lt
                all_goals norm_num
              rw[comm.symm]
              rw[Nat.add_sub_assoc]
              nth_rw 2 [add_comm]
              rw[Nat.add_sub_cancel_right]
              rw[add_comm]
              apply Nat.le_add_left
            have hpow:2 ^ (2 * (k + 1) + 1)=2^(2*k) * 8 := by
              rw[mul_add,add_assoc,pow_add]
              norm_num
            have : 2 * 8 - 2 * b = 2 * (8 - b) := by rw [Nat.mul_sub_left_distrib]
            rw[hd,h10,mul_pow,Nat.pow_add_one 2 (2*k),←mul_assoc,mul_comm (16-2*b) (2^(2*k))]
            repeat rw[mul_assoc]
            rw[←mul_add,h16,this,mul_assoc,←mul_add,hpow,mul_dvd_mul_iff_left (pow_ne_zero (2 * k) two_ne_zero),h8,mul_dvd_mul_iff_left]
            have dvd4:4∣(5^(2*k))-1 :=by
              apply Nat.dvd_of_mod_eq_zero
              rw[Nat.pow_mul]
              have eq25:5^2=25 := by norm_num
              rw[eq25]
              apply Nat.sub_mod_eq_zero_of_mod_eq
              have k125: ∀ k1:Nat,(25^k1) % 4=1:=by
                intro k1
                induction k1 with
                | zero => norm_num
                | succ d1 ih =>
                  rw[Nat.pow_add_one,Nat.mul_mod,ih]
              exact k125 k
            rcases dvd4 with ⟨c,hc⟩
            have dvd4beta: (5^(2*k))=4*c+1 := by
              rw[←hc]
              rw[Nat.sub_add_cancel]
              apply Nat.one_le_pow
              norm_num
            rw[dvd4beta,mul_add,add_assoc,h8b]
            apply dvd_add
            use (2*4-b)*c
            ring
            apply dvd_add
            norm_num
            unfold b
            exact Nat.dvd_sub_mod d
            norm_num
          case left=>
            simp[IsAlternating]
            apply And.intro
            case left => rw [digitsum]; linarith
            case right =>
              intro i irange
              rw [lemma_digiteq]
              have h_len_x : (Nat.digits 10 x).length = 2 * k := hx1
              have h_len_r : (Nat.digits 10 (16 - 2 * b)).length = 2 := by
              -- 16 - 2 * b 的值域是 {10,12,14}，都恰好是两位数
                interval_cases b <;> norm_num
              by_cases h_left : i < (Nat.digits 10 x).length
              case pos =>
                simp [List.getElem?_append_left h_left, h_len_x]
                by_cases h_left_left : i + 1 < (Nat.digits 10 x).length
                case pos =>
                  simp [List.getElem?_append_left h_left_left, h_len_x]
                  unfold IsAlternating at hx2
                  -- revert h_left_left
                  rcases hx2 with ⟨lenge1, h_alternating⟩
                  push_neg
                  have eq₁ : (Nat.digits 10 x)[i]?.getD 0 = (Nat.digits 10 x)[i]! :=by simp
                  have eq₂ : (Nat.digits 10 x)[i+1]?.getD 0 = (Nat.digits 10 x)[i+1]! :=by simp
                  simp only [eq₁, eq₂]
                  exact h_alternating i h_left_left
                case neg =>
                  let L := (Nat.digits 10 x).length
                  have exact_ip1 : i + 1 = L := by linarith [h_left, h_left_left]
                  have exact_i : i = L - 1 := by omega
                  simp [exact_i, h_len_x]
                  have L_m1_p1_eq_L : L - 1 + 1 = L := by omega
                  rw [L_m1_p1_eq_L]
                  have len_le_L : (Nat.digits 10 x).length ≤ L := by omega
                  simp only [List.getElem?_append_right len_le_L]
                  have L_eq_len : L = (Nat.digits 10 x).length := by omega
                  simp [L_eq_len]
                  have bdigitseq1 : (Nat.digits 10 (16 - 2 * b))[0]?.getD 0 % 2 = 0 := by
                    interval_cases b
                    simp; simp; simp; simp
                  rw [bdigitseq1]
                  -- have lemma_alternating_even_last_is_odd :
                  rw [Nat.succ_eq_add_one, zero_add] at hk
                  have xeven : x % 2 = 0 := by
                    rw [hd]
                    ring_nf
                    omega
                  rw [hx1, alternating_even_high_digit hk hx1 hx2 xeven]
                  trivial
              case neg =>
                push_neg at *
                have h_left_p1 : (Nat.digits 10 x).length ≤ i + 1 := by linarith [h_left, h_len_x]
                simp only [List.getElem?_append_right h_left]
                simp only [List.getElem?_append_right h_left_p1]
                have h_len_r : (Nat.digits 10 (16 - 2*b)).length = 2 := by
                  -- 16 - 2 * b 的值域是 {10,12,14,16}，都恰好是两位数
                  interval_cases b <;> norm_num
                have exact_i : i = (Nat.digits 10 x).length := by linarith [h_left, h_left_p1, h_len_r]
                simp [exact_i, h_len_x]
                interval_cases b
                simp; simp; simp; simp
        case left => exact digitsum
    have h2 : ∀ k : ℕ , k ≥ 2  → ∃ x : ℕ , ((Nat.digits 10 x).length = (k - 1) ∨  (Nat.digits 10 x).length = k) ∧ IsAlternating x ∧ 2*5^k  ∣ x ∧ (2 ∣ k → (Nat.digits 10 x).length =k) := by
      have Alternatingandlength(a k:Nat)
        (halt:IsAlternating a)
        (hksmall1:k+1≤ (Nat.digits 10 a).length)
        :(Nat.digits 10 a)[k]!%2=(k+(Nat.digits 10 a)[0]!)%2:=by
          have copy (halt:IsAlternating a)
          (hksmall:k+1≤ (Nat.digits 10 a).length)
          :(k+(Nat.digits 10 a)[0]!)%2=(Nat.digits 10 a)[k]!%2:=by
            induction k with
            | zero => norm_num
            | succ k1 ih =>
              unfold IsAlternating at halt
              rcases halt with ⟨hlen,haltern⟩
              have hk1:(k1 + (Nat.digits 10 a)[0]!) % 2 = (Nat.digits 10 a)[k1]! % 2:=by
                apply ih
                omega
                linarith[hksmall]
              have hk1alt:(Nat.digits 10 a)[k1]! % 2 ≠ (Nat.digits 10 a)[k1 + 1]! % 2:=by
                apply haltern
                omega
              rw[add_assoc,add_comm]
              have hk1altswitch:(Nat.digits 10 a)[k1+1]! % 2 =(1+(Nat.digits 10 a)[k1]!) % 2:=by
                have one_or_zerok1:(Nat.digits 10 a)[k1]! % 2=0 ∨ (Nat.digits 10 a)[k1]! % 2=1 :=by apply Nat.mod_two_eq_zero_or_one
                rcases one_or_zerok1 with (h1 | h2)
                case inl=>
                  rw[Nat.add_mod,h1]
                  rw[h1] at hk1alt
                  have hk1alt2:(Nat.digits 10 a)[k1 + 1]! % 2 ≠ 0:=by omega
                  rw[Nat.mod_two_ne_zero] at hk1alt2
                  omega
                rw[Nat.add_mod,h2]
                rw[h2] at hk1alt
                have hk1alt2:(Nat.digits 10 a)[k1 + 1]! % 2 ≠ 1:=by omega
                rw[Nat.mod_two_ne_one] at hk1alt2
                omega
              rw[hk1altswitch,add_assoc]
              rw[add_comm] at hk1
              rw[Nat.add_mod,hk1]
              omega
          rw[copy halt hksmall1]
      intro k hk
      induction k,hk using Nat.le_induction with
      | base =>
        use 50
        simp[IsAlternating]
        intro i hi
        replace hi : i = 0 := by omega
        simp[hi]
      | succ k hk ih =>
        rcases ih with ⟨a, ha1, ha2, ha3, ha4⟩
        rcases ha3 with ⟨b, hb⟩
        have h12: 1≤2:=by norm_num
        have hksub:k-1+1=k :=by apply Nat.sub_add_cancel; apply le_trans h12 hk
        have a0 : (Nat.digits 10 a)[0]! = 0 := by
          have : 10 ∣ 2 * 5 ^ k * b := by
            have h10: 10=2*5:=by norm_num
            use 5^(k-1)*b
            rw[←mul_assoc,h10,mul_assoc 2 5 (5^(k-1)),mul_comm 5 (5^(k-1)),←Nat.pow_add_one,hksub]
          rw[hb.symm] at this
          have gewei:Nat.digits 10 a=a % 10 :: Nat.digits 10 (a/ 10):=by
            apply Nat.digits_def'
            norm_num
            by_contra h
            have ale0:a=0:=by linarith[h]
            have adig0:Nat.digits 10 a=[]:=by
              subst ale0
              apply Nat.digits_zero 10
            rcases ha2 with ⟨hr1,hr2⟩
            have alen0: (Nat.digits 10 a).length=0:=by
              rw[List.length_eq_zero_iff]
              exact adig0
            linarith
          have amod10:a%10=0:=by by_contra h; omega
          rw[amod10] at gewei
          simp[gewei]
        set afirst:=(Nat.digits 10 a).getLast! with hafirst
        set temp := (5 * (afirst + 1) +4 * (b * 2 ^ (3*k + 1))) % 10 with htemp
        have temp_a : temp % 2 ≠ (Nat.digits 10 a).getLast! % 2 := by
            rw[hafirst.symm]
            have htemp_mod2 : temp % 2 = (afirst + 1) % 2 := by
                rw [htemp]
                rw [Nat.add_mod, Nat.mul_mod, Nat.mul_mod, Nat.mod_mod]
                norm_num -- simplifies 5 % 2 = 1, 4 % 2 = 0
                omega
            omega
        have sixtk(k1:ℕ):16^k1%5=1:=by
          induction k1 with
          | zero => norm_num
          | succ k1 ih =>
            rw[Nat.pow_add,Nat.pow_one,Nat.mul_mod]
            rw[ih]
        have temp_b : 5 ∣ (temp * 2 ^ (k -1) + b) := by
          apply Nat.dvd_iff_mod_eq_zero.mpr
          set t2:=4* (b * 2 ^ (3*k + 1)) with ht2
          rw[htemp,Nat.add_mod,Nat.mul_mod]
          norm_num
          have threekk: 3*k+k=4*k :=by omega
          have two4:2^4=16:=by norm_num
          rw[ht2,mul_assoc,mul_assoc,←Nat.pow_add,add_assoc,add_comm 1 (k-1),hksub,threekk,←mul_assoc,pow_mul,two4,Nat.add_mod,Nat.mul_mod,sixtk k]
          omega
        have temp_10 : temp ≥ 0 ∧ temp ≤ 9 := by
          rw[htemp]
          omega
        obtain a_k1 | a_k := ha1
        · have k2 : 2 ∣ (k + 1) := by
            by_contra kn2
            have k21 : 2 ∣ k := by omega
            have ak : (Nat.digits 10 a).length = k := by exact ha4 k21
            omega
          have odd_a : (Nat.digits 10 a).getLast! % 2 = 1 := by
            rw[List.getLast!_eq_getElem!,a_k1]
            have getlastid:(Nat.digits 10 a)[k-1-1]!%2=(k-1-1+(Nat.digits 10 a)[0]!)%2:=by
              apply Alternatingandlength
              exact ha2
              omega
            omega
          set x := (temp + 5) % 10 with hx
          have x_a : x % 2 = (Nat.digits 10 a).getLast! % 2 := by
            rw[odd_a]
            omega
          have x_b : 5 ∣ (x * 2 ^ (k -1) + b) := by
            have xandt: x%5=temp%5 := by omega
            have xandtv2: (x * 2 ^ (k - 1) + b)%5=
              (temp * 2 ^ (k - 1) + b) % 5 := by
                rw[Nat.add_mod,Nat.mul_mod,xandt,←Nat.mul_mod,←Nat.add_mod]
            omega
          have x_10 : x ≥ 0 ∧ x ≤ 9 := by omega
          use 2 * 5 ^ k * (x * 2 ^ (k - 1) + b)
          set n := x * 10 ^ k + a
          have eq_x : (2 * 5 ^ k * (x * 2 ^ (k - 1) + b)) = (10 ^ k * x + a) := by calc
            (2 * 5 ^ k * (x * 2 ^ (k - 1) + b)) = (2 * 5 ^ k * (x * 2 ^ (k - 1)) + 2 * 5 ^ k * b) := by ring
              _ = (2 * 5 ^ k * (x * 2 ^ (k - 1)) + a) := by rw [hb]
              _ = (x * (2 ^ 1 * 2 ^ (k - 1)) * 5 ^ k + a) := by ring
              _ = (x * (2 ^ k) * 5 ^ k + a) := by rw [← pow_add 2 1 (k - 1), add_comm 1 (k - 1), hksub]
              _ = (x * (2 ^ k * 5 ^ k) + a) := by ring
              _ = (x * (2 * 5) ^ k + a) := by rw [mul_pow]
              _ = (10 ^ k * x + a) := by ring
          refine ⟨?_, ?_, ?_, ?_⟩
          have n_eq_k1: (Nat.digits 10 (x * 10 ^ k + a)).length = k + 1:= by
              have tenksubone: 10^k-1+1=10^k:=by
                      apply Nat.sub_add_cancel
                      apply Nat.pow_pos
                      norm_num
              have loglx : x * 10 ^ k + a < 10 ^ (k + 1) := by
                rcases x_10 with ⟨_, hx2⟩
                apply Nat.lt_of_add_one_le
                have asmall: a≤10^k-1:=by
                  have tenklt0: 10 ^ k >0 := by norm_num
                  apply Nat.le_of_lt_add_one
                  rw[tenksubone]
                  apply Nat.lt_trans
                  apply Nat.lt_base_pow_length_digits
                  case a.h₁.b => exact 10
                  case a.h₁.hb => norm_num
                  case a.a=>
                    rw[a_k1]
                    apply Nat.pow_lt_pow_of_lt
                    repeat norm_num
                    apply lt_of_lt_of_le
                    case w.b=> exact 2
                    norm_num
                    exact hk
                calc
                  x * 10 ^ k + a + 1≤9*10^k+a+1:=by
                    repeat rw[add_assoc]
                    apply add_le_add_right
                    apply Nat.mul_le_mul_right
                    exact hx2
                  _≤ 9 * 10 ^ k + (10 ^ k-1) + 1 := by
                    rw[add_assoc,add_assoc]
                    apply add_le_add_left
                    apply add_le_add_right
                    exact asmall
                  _≤9 * 10 ^ k+10^k:=by
                    rw[add_assoc]
                    rw[tenksubone]
                  _=10^k*10:=by omega
              have loggx : x * 10 ^ k + a ≥ 10 ^ k := by
                rw[odd_a] at x_a
                have xbig:x≥1:=by omega
                apply Nat.le_add_right_of_le
                nth_rw 1 [←one_mul (10^k)]
                apply Nat.mul_le_mul_right
                exact xbig
              have base_gt_one : 1 < 10 := by norm_num
              have n_ge_one : n ≥ 1 := by omega
              have n_ne_one : n ≠ 0 := ne_of_gt (by linarith)
              rw [Nat.digits_len 10 n]
              rw [Nat.log_eq_of_pow_le_of_lt_pow loggx loglx]
              norm_num
              exact n_ne_one
          · rw [eq_x]
            right; rw [← n_eq_k1]
            ring_nf
          · have n_eq : n = 2 * 5 ^ k * (x * 2 ^ (k - 1) + b) := by rw [eq_x, mul_comm]
            have n_0true : (Nat.digits 10 n)[k-1]! = 0 := by
              have hn : n = x * 10 ^ k + a := rfl
              have newthang:x*10^k=(10*x)*10^(k-1):=by
                nth_rw 1 [←hksub]
                rw[Nat.pow_add_one]
                ring
              rw[hn,newthang]
              rw[lemma_digiteq_tongyong]
              · rw[List.getElem!_eq_getElem?_getD,List.getElem?_append_right,←List.getElem!_eq_getElem?_getD]
                rw[a_k1]
                simp
                rw[Nat.digits_of_two_le_of_pos]
                simp
                norm_num
                norm_num
                rw[odd_a] at x_a
                omega
                rw[a_k1]
              ·omega
              ·exact a_k1
            rw [eq_x]
            unfold IsAlternating
            constructor
            · calc
              1 ≤ (Nat.digits 10 a).length := ha2.1
              _ ≤ (Nat.digits 10 (10 ^ k * x + a)).length := Nat.le_digits_len_le 10 a (10 ^ k * x + a) (by omega)
            · by_cases xzero : x = 0
              · repeat rw [xzero];
                simp only [mul_zero, pow_zero, zero_add]
                intro i hi
                exact ha2.2 i hi
              rw [mul_comm]
              have hpart:
                    Nat.digits 10 (x * 10 ^ k + a) = (Nat.digits 10 a ++ [0] ++ Nat.digits 10 x) := by calc
                    Nat.digits 10 (x * 10 ^ k + a) = Nat.digits 10 ((10 * x) * 10 ^ (k - 1) + a) := by nth_rw 1 [← hksub]; ring_nf
                    _ = Nat.digits 10 a ++ Nat.digits 10 (10 * x) := by rw [lemma_digiteq_tongyong a (k - 1) (10 * x) (by omega) a_k1]
                    _ = Nat.digits 10 a ++ Nat.digits 10 (10 ^ 1 * x) := by ring_nf
                    _ = Nat.digits 10 a ++ ([0] ++ Nat.digits 10 x) := by rw [Nat.digits_base_pow_mul (by linarith) (by omega)]; simp
                    _ = (Nat.digits 10 a ++ [0] ++ Nat.digits 10 x) := by rw [List.append_assoc]
              repeat rw [hpart]
              -- rw [lemma_digiteq_tongyong a (k-1) x (by omega) a_k1]
              repeat rw [List.length_append]
              have xdlength1 : (Nat.digits 10 x).length = 1 := by
                apply Nat.le_antisymm
                · calc
                    (Nat.digits 10 x).length ≤ (Nat.digits 10 9).length := Nat.le_digits_len_le 10 x 9 x_10.right
                    _ = 1 := by simp
                · have : 1 ≤ x := by omega
                  calc
                    1 = (Nat.digits 10 1).length := by simp
                    _ ≤ (Nat.digits 10 x).length := Nat.le_digits_len_le 10 1 x this
              rw [xdlength1, show [0].length = 1 by decide]
              let L := Nat.digits 10 a
              have hL : L = Nat.digits 10 a := by rfl
              let R := Nat.digits 10 x
              have hR : R = Nat.digits 10 x := by rfl
              rw [← hL, ← hR]
              intro i hi
              simp at hi
              have hil: i < (L ++ [0] ++ R).length := by simp [List.length_append]; linarith
              have : (L ++ [0] ++ R)[i]! = (L ++ [0] ++ R)[i]'(hil) := by exact getElem!_pos (L ++ [0] ++ R) i (let_fun this := hil; this)
              rw [this]
              have hi1l: i + 1 < (L ++ [0] ++ R).length := by simp [List.length_append]; linarith
              have : (L ++ [0] ++ R)[i + 1]! = (L ++ [0] ++ R)[i + 1]'(hi1l) := by exact getElem!_pos (L ++ [0] ++ R) (i + 1) (let_fun this := hi1l; this)
              rw [this]
              repeat rw [List.length_append] at hi1l
              rw [xdlength1, show [0].length = 1 by decide] at hi1l
              -- ring_nf at hi1l
              by_cases hfr : i + 1 < L.length
              · let R' := [0] ++ R
                have heq : L ++ [0] ++ R = L ++ R' := by rw [List.append_assoc L [0] R]
                repeat rw [List.getElem_of_eq heq (by omega)]
                rw [← List.getElem_append_left' hfr R']
                rw [← List.getElem_append_left' (by omega) R']
                have ha := ha2.2 i (by linarith)
                have hil: i < L.length := by linarith
                have : L[i]! = L[i]'(hil) := by exact getElem!_pos L i (let_fun this := hil; this)
                rw [this] at ha
                have hi1l: i + 1 < L.length := by linarith
                have : L[i + 1]! = L[i + 1]'(hi1l) := by exact getElem!_pos L (i + 1) (let_fun this := hi1l; this)
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
                  rw [hl, hr]
                  rw [odd_a]
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
                        exact List.getElem_of_eq heq (by omega)
                      _ = x := by rfl
                  rw [hl, hr]
                  omega
          · have hk5 : 2 * 5 ^ (k + 1) = 2 * 5 ^ k * 5 := by ring
            rw [hk5]
            exact mul_dvd_mul_left (2 * 5 ^ k) x_b
          · intro _
            rw [eq_x]
            have xpos : 0 < x := by
              have : Odd x := by
                have : (Nat.digits 10 a)[(Nat.digits 10 a).length - 1]! = (Nat.digits 10 a).getLast! := by exact Eq.symm List.getLast!_eq_getElem!
                have : afirst % 2 = 1 := by
                  calc
                    afirst % 2 = (Nat.digits 10 a).getLast! % 2 := by rw [hafirst]
                    _ = (Nat.digits 10 a)[k - 2]! % 2 := by rw [List.getLast!_eq_getElem!, a_k1, show (k - 2 = k - 1 - 1) by omega]
                    _ = (k - 2 + (Nat.digits 10 a)[0]!) % 2 := by rw [Alternatingandlength a (k - 2) ha2  (by omega)]
                    _ = 1 := by omega
                have : x % 2 = 1 := by omega
                exact Nat.odd_iff.mpr this
              unfold Odd at this
              rcases this with ⟨d, hd⟩
              refine Nat.exists_eq_add_one.mp ?_
              use 2 * d
            have n_eq_k1: (Nat.digits 10 (x * 10 ^ k + a)).length = k + 1:= by
              have loglx : x * 10 ^ k + a < 10 ^ (k + 1) := by
                have : a < 10 ^ k := by calc
                  a < 10 ^ (Nat.digits 10 a).length := Nat.lt_base_pow_length_digits (by linarith)
                  _ = 10 ^ (k - 1) := by rw [a_k1]
                  _ < 10 ^ (k - 1 + 1) := by refine Nat.pow_lt_pow_succ (by linarith)
                  _ = 10 ^ k := by rw [hksub]
                calc
                  x * 10 ^ k + a < x * 10 ^ k + 10 ^ k := by linarith
                  _ ≤ 9 * 10 ^ k + 10 ^ k := by simp; exact x_10.2
                  _ = 10 ^ (k + 1) := by ring_nf
              have loggx : x * 10 ^ k + a ≥ 10 ^ k := by calc
                10 ^ k ≤ x * 10 ^ k := Nat.le_mul_of_pos_left (10 ^ k) xpos
                _ ≤ x * 10 ^ k + a := by linarith
              set n := x * 10 ^ k + a
              have base_gt_one : 1 < 10 := by norm_num
              have n_ge_one : n ≥ 1 := by
                have : 0 < x * 10 ^ k := by simp; linarith
                exact show 0 < n by calc
                  0 < x * 10 ^ k := this
                  _ ≤ x * 10 ^ k + a := by linarith
              have n_ne_one : n ≠ 0 := ne_of_gt (by linarith)
              rw [Nat.digits_len 10 n]
              rw [Nat.log_eq_of_pow_le_of_lt_pow loggx loglx]
              norm_num
              exact n_ne_one
            rw [← n_eq_k1, mul_comm]
        · set x := temp
          have x_a : x % 2 ≠ (Nat.digits 10 a).getLast! % 2 := temp_a
          have x_10 : x ≥ 0 ∧ x ≤ 9 := by exact temp_10
          have eq_x : (2 * 5 ^ k * (x * 2 ^ (k - 1) + b)) = (10 ^ k * x + a) := by calc
            (2 * 5 ^ k * (x * 2 ^ (k - 1) + b)) = (2 * 5 ^ k * (x * 2 ^ (k - 1)) + 2 * 5 ^ k * b) := by ring
              _ = (2 * 5 ^ k * (x * 2 ^ (k - 1)) + a) := by rw [hb]
              _ = (x * (2 ^ 1 * 2 ^ (k - 1)) * 5 ^ k + a) := by ring
              _ = (x * (2 ^ k) * 5 ^ k + a) := by rw [← pow_add 2 1 (k - 1), add_comm 1 (k - 1), hksub]
              _ = (x * (2 ^ k * 5 ^ k) + a) := by ring
              _ = (x * (2 * 5) ^ k + a) := by rw [mul_pow]
              _ = (10 ^ k * x + a) := by ring
          use 2 * 5 ^ k * (x * 2 ^ (k - 1) + b)
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [eq_x]
            by_cases xeq0 : x = 0
            · left
              rw [xeq0]; simp;
              exact a_k
            · right
              have xdlength1 : (Nat.digits 10 x).length = 1 := by
                apply Nat.le_antisymm
                · calc
                    (Nat.digits 10 x).length ≤ (Nat.digits 10 9).length := Nat.le_digits_len_le 10 x 9 temp_10.right
                    _ = 1 := by simp
                · have : 1 ≤ x := by omega
                  calc
                    1 = (Nat.digits 10 1).length := by simp
                    _ ≤ (Nat.digits 10 x).length := Nat.le_digits_len_le 10 1 x this
              have := lemma_digiteq_tongyong a k x (show 0 < x by omega) a_k
              calc
                (Nat.digits 10 (10 ^ k * x + a)).length = (Nat.digits 10 (x * 10 ^ k + a)).length := by ring_nf
                _ = (Nat.digits 10 a ++ Nat.digits 10 x).length := by rw [this]
                _ = (Nat.digits 10 a).length + (Nat.digits 10 x).length := List.length_append
                _ = k + 1 := by rw [a_k, xdlength1]
          · rw [eq_x]
            unfold IsAlternating
            constructor
            · calc
              1 ≤ (Nat.digits 10 a).length := ha2.1
              _ ≤ (Nat.digits 10 (10 ^ k * x + a)).length := Nat.le_digits_len_le 10 a (10 ^ k * x + a) (by omega)
            · by_cases xzero : x = 0
              · repeat rw [xzero];
                simp only [mul_zero, pow_zero, zero_add]
                intro i hi
                exact ha2.2 i hi
              rw [mul_comm]
              rw [lemma_digiteq_tongyong a k x (by omega) a_k]
              rw [List.length_append]
              have xdlength1 : (Nat.digits 10 x).length = 1 := by
                apply Nat.le_antisymm
                · calc
                    (Nat.digits 10 x).length ≤ (Nat.digits 10 9).length := Nat.le_digits_len_le 10 x 9 temp_10.right
                    _ = 1 := by simp
                · have : 1 ≤ x := by omega
                  calc
                    1 = (Nat.digits 10 1).length := by simp
                    _ ≤ (Nat.digits 10 x).length := Nat.le_digits_len_le 10 1 x this
              rw [xdlength1];
              let L := Nat.digits 10 a
              have hL : L = Nat.digits 10 a := by rfl
              let R := Nat.digits 10 x
              have hR : R = Nat.digits 10 x := by rfl
              rw [← hL, ← hR]
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
                have : L[i]! = L[i]'(hil) := by exact getElem!_pos L i (let_fun this := hil; this)
                rw [this] at ha
                have hi1l: i + 1 < L.length := by linarith
                have : L[i + 1]! = L[i + 1]'(hi1l) := by exact getElem!_pos L (i + 1) (let_fun this := hi1l; this)
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
                    exact List.getElem_of_eq heq (by omega)
                  _ = x := by rfl
                rw [hl, hr]
                by_contra! p; have p := Eq.symm p; contradiction
          · calc
              2 * 5 ^ (k + 1) = (2 * 5 ^ k) * 5 := by ring_nf
              _ ∣(2 * 5 ^ k) * (x * 2 ^ (k - 1) + b) := Nat.mul_dvd_mul_left (2 * 5 ^ k) temp_b
          · intro h2
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
            have xdlength1 : (Nat.digits 10 x).length = 1 := by
              apply Nat.le_antisymm
              · calc
                  (Nat.digits 10 x).length ≤ (Nat.digits 10 9).length := Nat.le_digits_len_le 10 x 9 temp_10.right
                  _ = 1 := by simp
              · have : 1 ≤ x := by omega
                calc
                  1 = (Nat.digits 10 1).length := by simp
                  _ ≤ (Nat.digits 10 x).length := Nat.le_digits_len_le 10 1 x this
            have := lemma_digiteq_tongyong a k x xpos a_k
            calc
              (Nat.digits 10 (10 ^ k * x + a)).length = (Nat.digits 10 (x * 10 ^ k + a)).length := by ring_nf
              _ = (Nat.digits 10 a ++ Nat.digits 10 x).length := by rw [this]
              _ = (Nat.digits 10 a).length + (Nat.digits 10 x).length := List.length_append
              _ = k + 1 := by rw [a_k, xdlength1]
    have h3 (m : ℕ) (a : ℕ)(ha : a ≥ 1)(hm : m ≥ 1)(d2 : ¬ 2 ∣ m)(d5 : ¬ 5 ∣ m) :
      m ∣ (10^(2*a*(m*Nat.totient m)) -1)/ (10^(2*a)-1) := by
      let i := m * m.totient
      have hmpos : 0 < m := by
        by_contra! htemp
        apply Nat.le_zero.mp at htemp
        rw [htemp] at hm
        linarith
      have hipos : 0 < i := Nat.mul_pos hmpos (Nat.totient_pos.mpr hmpos)
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
          have c4 : (10 ^ (2*a*(i+1)) - 10^(2*a*i)) / (10 ^ (2*a) - 1) = 10^(2*a*i) := by
            refine Nat.div_eq_of_eq_mul_right c3 ?_
            rw[show 10 ^ (2 * a * (i + 1)) = 10 ^ (2 * a * i) * 10 ^(2*a) by ring]
            rw[mul_comm]
            ring_nf
            exact Eq.symm (Nat.sub_one_mul (10 ^ (a * 2)) (10 ^ (a * i * 2)))
          have c5 : 10 ^ (2 * a*i) - 1 > 0 := by refine Nat.zero_lt_sub_of_lt ?_;refine Nat.one_lt_pow ?_ ?_; refine Nat.ne_zero_iff_zero_lt.mpr ?_;simp;omega;omega
          have rew : (10 ^ (2 * a * (i + 1)) - 1) / (10 ^ (2 * a) - 1) = 10^(2*a*i) + (10^(2*a*i)-1)/(10^(2*a)-1) := by
            obtain⟨d1,hd1⟩:=c1
            obtain⟨d2,hd2⟩:=c2
            simp[hd1,hd2]
            rw[show (10 ^ (2 * a) - 1) * d2 / (10 ^ (2 * a) - 1) = d2 by exact Nat.mul_div_right d2 c3]
            rw[show (10 ^ (2 * a) - 1) * d1 / (10 ^ (2 * a) - 1) = d1 by exact Nat.mul_div_right d1 c3]
            have : (10 ^ (2 * a) - 1) * d2 = (10 ^ (2 * a) - 1) * (10 ^ (2 * a * i) + d1) := by
              rw[← hd2]
              simp[mul_add]
              rw[← hd1]
              rw[show (10 ^ (2 * a) - 1) * 10 ^ (2 * a * i) = 10 ^ (2*a) * 10^(2*a*i) - 10^(2*a*i) by exact Nat.sub_one_mul (10 ^ (2 * a)) (10 ^ (2 * a * i))]
              rw[← pow_add]
              ring_nf
              refine Eq.symm (Nat.sub_add_sub_cancel ?_ ?_)
              refine Nat.le_mul_of_pos_left (10 ^ (a * i * 2)) ?_
              exact Nat.pos_of_neZero (10 ^ (a * 2))
              exact Nat.one_le_pow' (a * i * 2) 9
            exact Nat.eq_of_mul_eq_mul_left c3 this
          replace rew : x*((10 ^ (2*a*(i+1))-1)/(10 ^ (2*a) - 1)) = x*10^(2*a*i) + x*((10^(2*a*i)-1)/(10^(2*a)-1)) := by
            rw[rew]
            rw[mul_add]
          repeat rw[rew]
          obtain⟨ih1,ih2⟩:=ih
          have c6 : (Nat.digits 10 (x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1)))).length = i*2*a := by
            simp[ih1,hx1]; ring
          have c9 : Nat.digits 10 (x * 10 ^ (2 * a * i) + x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1))) = (List.replicate (i + 1) (Nat.digits 10 x)).flatten := by
            have c7 :  Nat.digits 10 (x * 10 ^ (2 * a * i) + x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1))) = (Nat.digits 10 (x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1)))) ++ Nat.digits 10 x := by
              apply lemma_digiteq_tongyong
              · by_contra hx0
                simp at hx0
                simp[hx0] at hx1
                omega
              · rw[c6]; ring
            rw[c7,ih1]
            have c8 : List.replicate (i + 1) (Nat.digits 10 x) = List.replicate i (Nat.digits 10 x) ++ [(Nat.digits 10 x)] := by
              exact List.replicate_succ'
            rw[c8]
            simp
          have h6' : ((List.replicate (i + 1) (Nat.digits 10 x)).flatten).length = 2*a*(i+1) := by simp; rw[hx1]; ring
          constructor
          · exact c9
          · simp[IsAlternating]
            simp[*]
            constructor
            · ring_nf;omega
            · intro t ht
              have c8 : List.replicate (i + 1) (Nat.digits 10 x) = List.replicate i (Nat.digits 10 x) ++ [(Nat.digits 10 x)] := by
                exact List.replicate_succ'
              repeat rw[c8]
              have c10 : (List.replicate i (Nat.digits 10 x) ++ [Nat.digits 10 x]).flatten = (List.replicate i (Nat.digits 10 x)).flatten ++ Nat.digits 10 x := by
                exact List.flatten_concat
              repeat rw[c10]
              have ih4 : IsAlternating (x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1))) :=by exact ih2
              simp[IsAlternating] at ih2
              simp[ih1] at ih2
              simp[*] at ih2
              obtain⟨ih2,ih3⟩:=ih2
              by_cases ht : t+1 < i*2*a
              · specialize ih3 t
                have ht': t+1 < i*(2*a) := by ring_nf; ring_nf at ht;exact ht
                apply ih3 at ht'
                have c11 : ((List.replicate i (Nat.digits 10 x)).flatten).length = i*2*a := by
                  rw[ih1] at c6; exact c6
                have c12 : (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x))[t]? = ((List.replicate i (Nat.digits 10 x)).flatten)[t]? := by
                  replace ht : t < (List.replicate i (Nat.digits 10 x)).flatten.length := by omega
                  have c13 : (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x))[t]? = (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x)).getI t := by
                    symm
                    let l : List ℕ := (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x))
                    have hl : l = (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x)) := by rfl
                    have c14 : l.getI t = l[t]? := by
                      have ht1 : t < l.length := by
                        rw[c8] at h6'
                        rw[c10] at h6'
                        rw[← hl] at h6'
                        rw[h6']
                        omega
                      rw[List.getI_eq_getElem l ht1]
                      exact (List.some_getElem_eq_getElem?_iff ht1).mpr trivial
                    rw[← hl]
                    exact c14
                  rw[c13]
                  have c14 : ((List.replicate i (Nat.digits 10 x)).flatten)[t]? = ((List.replicate i (Nat.digits 10 x)).flatten).getI t := by
                    symm
                    let l : List ℕ := (((List.replicate i (Nat.digits 10 x)).flatten))
                    have hl : l = (((List.replicate i (Nat.digits 10 x)).flatten)) := by rfl
                    have c14 : l.getI t = l[t]? := by
                      have ht1 : t < l.length := by
                        rw[hl]
                        simp
                        simp at ht
                        exact ht
                      rw[List.getI_eq_getElem l ht1]
                      exact (List.some_getElem_eq_getElem?_iff ht1).mpr trivial
                    rw[← hl]
                    exact c14
                  rw[c14]
                  let l : List ℕ := (((List.replicate i (Nat.digits 10 x)).flatten))
                  have hl : l = (((List.replicate i (Nat.digits 10 x)).flatten)) := by rfl
                  rw[← hl]
                  congr 1
                  exact List.getI_append l (Nat.digits 10 x) t ht
                rw[c12]
                have c12' : (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x))[t+1]? = ((List.replicate i (Nat.digits 10 x)).flatten)[t+1]? := by
                  replace ht : t+1 < (List.replicate i (Nat.digits 10 x)).flatten.length := by omega
                  have c13' : (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x))[t+1]? = (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x)).getI (t+1) := by
                    symm
                    let l : List ℕ := (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x))
                    have hl' : l = (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x)) := by rfl
                    have c14' : l.getI (t+1) = l[t+1]? := by
                      have ht1 : t+1 < l.length := by
                        rw[hl']
                        simp
                        simp at ht
                        omega
                      rw[List.getI_eq_getElem l ht1]
                      exact (List.some_getElem_eq_getElem?_iff ht1).mpr trivial
                    rw[← hl']
                    exact c14'
                  rw[c13']
                  have c14' : ((List.replicate i (Nat.digits 10 x)).flatten)[t+1]? = ((List.replicate i (Nat.digits 10 x)).flatten).getI (t+1) := by
                    symm
                    let l : List ℕ := (((List.replicate i (Nat.digits 10 x)).flatten))
                    have hl' : l = (((List.replicate i (Nat.digits 10 x)).flatten)) := by rfl
                    have c14' : l.getI (t+1) = l[t+1]? := by
                      have ht1 : t+1 < l.length := by
                        rw[hl']
                        simp
                        simp at ht
                        exact ht
                      rw[List.getI_eq_getElem l ht1]
                      exact (List.some_getElem_eq_getElem?_iff ht1).mpr trivial
                    rw[← hl']
                    exact c14'
                  rw[c14']
                  let l : List ℕ := (((List.replicate i (Nat.digits 10 x)).flatten))
                  have hl : l = (((List.replicate i (Nat.digits 10 x)).flatten)) := by rfl
                  rw[← hl]
                  congr 1
                  exact List.getI_append l (Nat.digits 10 x) (t+1) ht
                rw[c12']
                apply ih3
                ring_nf
                ring_nf at ht
                exact ht
              · simp at ht
                by_cases ht1 : t = i*2*a-1
                · have c12 : (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x))[t]? = ((List.replicate i (Nat.digits 10 x)).flatten)[t]? := by
                    replace ht : t < (List.replicate i (Nat.digits 10 x)).flatten.length := by simp;rw[hx1];rw[ht1];ring_nf;ring_nf at ih2;simp[ih2];omega
                    have c13 : (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x))[t]? = (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x)).getI t := by
                      symm
                      let l : List ℕ := (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x))
                      have hl : l = (((List.replicate i (Nat.digits 10 x)).flatten) ++ (Nat.digits 10 x)) := by rfl
                      have c14 : l.getI t = l[t]? := by
                        have ht1 : t < l.length := by
                          rw[c8] at h6'
                          rw[c10] at h6'
                          rw[← hl] at h6'
                          rw[h6']
                          omega
                        rw[List.getI_eq_getElem l ht1]
                        exact (List.some_getElem_eq_getElem?_iff ht1).mpr trivial
                      rw[← hl]
                      exact c14
                    rw[c13]
                    have c14 : ((List.replicate i (Nat.digits 10 x)).flatten)[t]? = ((List.replicate i (Nat.digits 10 x)).flatten).getI t := by
                      symm
                      let l : List ℕ := (((List.replicate i (Nat.digits 10 x)).flatten))
                      have hl : l = (((List.replicate i (Nat.digits 10 x)).flatten)) := by rfl
                      have c14 : l.getI t = l[t]? := by
                        have ht1 : t < l.length := by
                          rw[hl]
                          simp
                          simp at ht
                          exact ht
                        rw[List.getI_eq_getElem l ht1]
                        exact (List.some_getElem_eq_getElem?_iff ht1).mpr trivial
                      rw[← hl]
                      exact c14
                    rw[c14]
                    let l : List ℕ := (((List.replicate i (Nat.digits 10 x)).flatten))
                    have hl : l = (((List.replicate i (Nat.digits 10 x)).flatten)) := by rfl
                    rw[← hl]
                    congr 1
                    exact List.getI_append l (Nat.digits 10 x) t ht
                  rw[c12,ht1]
                  nth_rw 1 [← ih1]
                  have c13 : (Nat.digits 10 (x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1))))[2*(i* a) - 1]?.getD 0 % 2 =1 := by
                    apply alternating_even_high_digit
                    · exact Right.one_le_mul hi ha
                    · rw[c6]; ring
                    · exact ih4
                    · have : 2 ∣ x * ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1)) := by exact Nat.dvd_mul_right_of_dvd hxeven ((10 ^ (2 * a * i) - 1) / (10 ^ (2 * a) - 1))
                      exact Nat.dvd_iff_mod_eq_zero.mp this
                  ring_nf at c13
                  ring_nf
                  rw[c13]
                  have c14 : ((List.replicate i (Nat.digits 10 x)).flatten ++ Nat.digits 10 x)[a*i*2]? = (Nat.digits 10 x).getI 0 := by
                    let l:=(List.replicate i (Nat.digits 10 x)).flatten
                    have hl : l=(List.replicate i (Nat.digits 10 x)).flatten := by rfl
                    let l' := Nat.digits 10 x
                    have hl' : l' = Nat.digits 10 x := by rfl
                    have l_length : l.length = a*i*2 := by rw[hl];simp;rw[hx1];ring_nf
                    rw[← hl,← hl']
                    have l_add_l'_length : (l ++ l').length = 2*a*(i+1) := by simp[hl,hl',hx1];ring_nf
                    have c17 : a*i*2 < (l ++ l').length := by rw[l_add_l'_length] ; ring_nf;simp;omega
                    have c15 : (l ++ l').getI (a*i*2) = (l ++ l')[a * i * 2]? := by rw[List.getI_eq_getElem (l ++ l') c17];exact (List.some_getElem_eq_getElem?_iff c17).mpr trivial
                    have c16 : (l ++ l').getI (a*i*2) = l'.getI (a*i*2 - l.length) := by apply List.getI_append_right l l';rw[l_length]
                    rw[← c15,c16]
                    simp[l_length]
                  rw[show 1 + (a*i*2 -1) = a*i*2 by refine Nat.add_sub_of_le ?_;linarith]
                  rw[c14]
                  simp
                  have c15 : (Nat.digits 10 x).getI 0 = x % 10 := by
                    cases x with
                    | zero => simp
                    | succ n =>
                      rw [Nat.digits_eq_cons_digits_div (by norm_num) (by simp)]
                      simp
                  have c16 : 2 ∣ x % 10 := by omega
                  simp[c15,c16,show x%2 =0 by exact Nat.dvd_iff_mod_eq_zero.mp hxeven]
                · replace ht : a*i*2 ≤ t := by
                    ring_nf at ht ht1
                    ring_nf
                    contrapose! ht1
                    have htt : i*a*2-1 ≤ t := by omega
                    have httt : t < i*a * 2 :=by rw[show i*a=a*i by ring];exact ht1
                    omega
                  have c14 : ((List.replicate i (Nat.digits 10 x)).flatten ++ Nat.digits 10 x)[t]? = (Nat.digits 10 x).getI (t-a*i*2) := by
                    let l:=(List.replicate i (Nat.digits 10 x)).flatten
                    have hl : l=(List.replicate i (Nat.digits 10 x)).flatten := by rfl
                    let l' := Nat.digits 10 x
                    have hl' : l' = Nat.digits 10 x := by rfl
                    have l_length : l.length = a*i*2 := by rw[hl];simp;rw[hx1];ring_nf
                    rw[← hl,← hl']
                    have l_add_l'_length : (l ++ l').length = 2*a*(i+1) := by simp[hl,hl',hx1];ring_nf
                    have c17 : t < (l ++ l').length := by rw[l_add_l'_length] ; ring_nf;linarith
                    have c15 : (l ++ l').getI (t) = (l ++ l')[t]? := by rw[List.getI_eq_getElem (l ++ l') c17];exact (List.some_getElem_eq_getElem?_iff c17).mpr trivial
                    have c16 : (l ++ l').getI (t) = l'.getI (t - l.length) := by apply List.getI_append_right l l';rw[l_length];exact ht
                    rw[← c15,c16]
                    simp[l_length]
                  rw[c14]
                  have c14' : ((List.replicate i (Nat.digits 10 x)).flatten ++ Nat.digits 10 x)[t+1]? = (Nat.digits 10 x).getI (t+1-a*i*2) := by
                    let l:=(List.replicate i (Nat.digits 10 x)).flatten
                    have hl : l=(List.replicate i (Nat.digits 10 x)).flatten := by rfl
                    let l' := Nat.digits 10 x
                    have hl' : l' = Nat.digits 10 x := by rfl
                    have l_length : l.length = a*i*2 := by rw[hl];simp;rw[hx1];ring_nf
                    rw[← hl,← hl']
                    have l_add_l'_length : (l ++ l').length = 2*a*(i+1) := by simp[hl,hl',hx1];ring_nf
                    have c17 : t+1 < (l ++ l').length := by rw[l_add_l'_length] ; ring_nf;linarith
                    have c15 : (l ++ l').getI (t+1) = (l ++ l')[t+1]? := by rw[List.getI_eq_getElem (l ++ l') c17];exact (List.some_getElem_eq_getElem?_iff c17).mpr trivial
                    have c16 : (l ++ l').getI (t+1) = l'.getI (t+1 - l.length) := by apply List.getI_append_right l l';rw[l_length];omega
                    rw[← c15,c16]
                    simp[l_length]
                  rw[c14']
                  simp
                  simp[IsAlternating] at hx2
                  replace hx2 := hx2.2
                  specialize hx2 (t-a*i*2)
                  simp[*] at hx2
                  rename_i ht'
                  have c15 : t - a * i * 2 + 1 < 2 * a := by ring_nf at ht';omega
                  apply hx2 at c15
                  have ht2 : a * i * 2 ≤ t+1 :=by omega
                  rw[show t + 1 - a * i * 2 = t - a * i * 2 + 1 by qify; simp[ht2,ht];ring_nf]
                  exact c15
    have pow10 : ∀ k : ℕ, (Nat.digits 10 (10 ^ k)).length = k + 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        simp [Nat.pow_add, Nat.pow_one] at ih ⊢
        omega
    have digits_zero_eq_mod {b n : ℕ} (hb : b > 1) (hn : n > 0) :
        (Nat.digits b n)[0]! = n % b := by
      rw [Nat.digits_def' (by omega) (by omega)]; simp
    have div_b_sub_1 (k b: ℕ) (h: b > 0) : (b - 1) ∣ b ^ k - 1 := by
      induction k with
      | zero => norm_num
      | succ k ih =>
        have h1 : b ^ (k + 1) - 1 = (b - 1) * (b ^ k) + b ^ k - 1 := by
          calc
            _ = b * (b ^ k) - 1 := by ring_nf
            _ = (b - 1 + 1) * (b ^ k) - 1 := by rw [Nat.sub_add_cancel (Nat.one_le_of_lt h)]
            _ = (b - 1) * (b ^ k) + b ^ k - 1 := by ring_nf
        have : b ^ k > 0 := by apply Nat.pow_pos; linarith
        rw [h1, ← Eq.symm (Nat.add_sub_assoc this ((b - 1) * b ^ k))]
        have h2 : b - 1 ∣ (b - 1) * (b ^ k) := Nat.dvd_mul_right (b - 1) (b ^ k)
        exact Nat.dvd_add h2 ih
    have digits_append (m n k i : ℕ) (hk : k = (Nat.digits 10 n).length) :
        (Nat.digits 10 m)[i]! = (Nat.digits 10 (m * 10 ^ k + n))[i + k]! := by
      have h1 : Nat.digits 10 n ++ Nat.digits 10 m = Nat.digits 10 (m * 10 ^ k + n) := by
        rw [add_comm, mul_comm, hk]
        have : 10 > 0 := by simp
        apply Nat.digits_append_digits this
      rw[← h1]
      simp [hk, List.getElem!_eq_getElem?_getD, List.getElem?_append_right, List.length_replicate]
    have digits_append' (m n k i : ℕ) (hk : k = (Nat.digits 10 n).length) (hi : i < k) :
        (Nat.digits 10 n)[i]! = (Nat.digits 10 (m * 10 ^ k + n))[i]! := by
      have h1 : Nat.digits 10 (m * 10 ^ k + n) = Nat.digits 10 n ++ Nat.digits 10 m := by
        rw [add_comm, mul_comm, hk]
        have : 10 > 0 := by simp
        simp [Nat.digits_append_digits]
      rw [h1]
      have h2 : (Nat.digits 10 n ++ Nat.digits 10 m)[i]? = (Nat.digits 10 n)[i]? := by
        apply List.getElem?_append_left
        rw [hk] at hi
        exact hi
      simp [h2]
    have digits_mul_pow_offset (n k i : ℕ) (hn : n > 0) :
        (Nat.digits 10 n)[i]! = (Nat.digits 10 (n * 10 ^ k))[i + k]! := by
      have h1 : Nat.digits 10 (n * 10 ^ k) = List.replicate k 0 ++ Nat.digits 10 n := by
        rw [mul_comm]
        apply Nat.digits_base_pow_mul
        all_goals norm_num [hn]
      rw [h1]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right, List.length_replicate]
    have alternating_pos {x : ℕ} (hx : IsAlternating x) : x > 0 := by
      unfold IsAlternating at hx
      rcases hx with ⟨h1, h2⟩
      contrapose! h1
      simp at h1
      rw [h1]
      norm_num
    have h01alt22 {a : ℕ} (apos : a > 0) : ∀ i : ℕ, i < 2 * a → (Nat.digits 10 ((10 ^ (2 * a) - 1)/(10 ^ 2 - 1)))[i]! = 1 - i % 2 := by
      have number_theory_99 (k : ℕ) : 99 ∣ 100 ^ k - 1 := by
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          have h1 : 100 ^ (k + 1) - 1 = 100 * (100 ^ k) - 1 := by ring_nf
          rw [h1]
          omega
      induction a, apos using Nat.le_induction with
      | base =>
        intro i hi
        simp at hi
        norm_num
        interval_cases i <;> simp
      | succ k hk ih =>
        have _h1: (10 ^ (2 * (k + 1)) - 1) = (10 ^ (2 * k) - 1) * 10 ^ 2 + 99 := by
          calc
            10 ^ (2 * (k + 1)) - 1 = (10 ^ (2 * k + 2)) - 1 := by rw [mul_add]
            _ = 10 ^ (2 * k) * 10 ^ 2 - 1 := by rw [pow_add 10 (2 * k) 2]
            _ = (10 ^ (2 * k) - 1 + 1) * 10 ^ 2 - 1 := by
              have : 10 ^ (2 * k) > 0 := Nat.pos_of_neZero (10 ^ (2 * k))
              have : 10 ^ (2 * k) - 1 + 1 = 10 ^ (2 * k) := Nat.sub_add_cancel this
              rw [this]
            _ = (10 ^ (2 * k) - 1) * 10 ^ 2 + 10 ^ 2 - 1 := by rw [add_mul, one_mul]
            _ = (10 ^ (2 * k) - 1) * 10 ^ 2 + 99 := by norm_num
        have _h2 : (10 ^ (2 * (k + 1)) - 1) / (10 ^ 2 - 1) = (100 ^ k - 1) / 99 * 100 + 1 := by
          calc
            _ = (10 ^ (2 * (k + 1)) - 1) / 99 := by simp
            _ = (10 ^ (2 * k) - 1) * 10 ^ 2 / 99 + 1 := by omega
            _ = ((10 ^ 2) ^ k - 1) * 10 ^ 2 / 99 + 1 := by rw [← pow_mul 10 2 k]
            _ = (100 ^ k - 1) * 100 / 99 + 1 := by norm_num
            _ = (100 ^ k - 1) / 99 * 100 + 1 := by rw [Nat.div_mul_right_comm (number_theory_99 k) 100]
        rw [_h2]
        have _h3 (i : ℕ) : (Nat.digits 10 ((100 ^ k - 1) / 99 * 100 + 1))[i + 2]! = (Nat.digits 10 ((100 ^ k - 1) / 99))[i]! := by
          calc
            _ = (Nat.digits 10 ((100 ^ k - 1) / 99 * 10 * 10 + 1))[i + 2]! := by
              have : 100 = 10 * 10 := by norm_num
              rw [this, mul_assoc]
            _ = (Nat.digits 10 ((100 ^ k - 1) / 99 * 10 * 10 + 1))[i + 1 + 1]! := by
              have : 2 = 1 + 1 := by simp
              rw [this, add_assoc]
            _ = (Nat.digits 10 ((100 ^ k - 1) / 99 * 10))[i + 1]! := by
              have : 1 = (Nat.digits 10 1).length := by norm_num
              have __h1 := digits_append ((100 ^ k - 1) / 99 * 10) 1 1 (i + 1) this
              have : 10 ^ 1 = 10 := by simp
              rw [this] at __h1
              rw [__h1]
            _ = (Nat.digits 10 ((100 ^ k - 1) / 99))[i]! := by
              have : (100 ^ k - 1) / 99 > 0 := by
                have : 100 ^ k ≥ 100 := Nat.le_pow hk
                have __h2 : 100 ^ k - 1 ≥ 99 := Nat.sub_le_sub_right this 1
                apply Nat.div_pos __h2 (by norm_num)
              have := digits_mul_pow_offset ((100 ^ k - 1) / 99) 1 i this
              rw [this]
              simp
        have _h4 : (10 ^ (2 * k) - 1) / (10 ^ 2 - 1) = (100 ^ k - 1) / 99 := by
          calc
            _ = (10 ^ (2 * k) - 1) / 99 := by simp
            _ = (100 ^ k - 1) / 99 := by rw [Nat.pow_mul]
        intro i hi
        match i with
        | 0 => simp; omega
        | 1 =>
          have : 100 ∣ (100 ^ k - 1) / 99 * 100 := by omega
          simp
          by_cases k_one : k = 1
          . rw [k_one]
            norm_num
          have ⟨c, hc⟩ : 99 ∣ 100 ^ k - 1 := number_theory_99 k
          have kgt1 : k > 1 := by omega
          have : c > 1 := by
            have : 100 > 1 := by norm_num
            have : 100 ^ k > 100 := by exact (Nat.pow_lt_pow_iff_right this).mpr kgt1
            have _h5 : 100 ^ k - 1 > 99 := Nat.lt_sub_of_add_lt this
            rw [hc] at _h5
            omega
          have : ((100 ^ k - 1) / 99 * 100 + 1) / 10 > 0 := by
            rw [hc]
            omega
          have := @digits_zero_eq_mod 10 (((100 ^ k - 1) / 99 * 100 + 1) / 10) (by simp) this
          simp at this
          rw [this, hc]
          omega
        | t + 2 =>
          have ht : t < 2 * k := by omega
          have _h5 := ih t ht
          rw [_h4] at _h5
          rw [← _h3 t] at _h5
          rw [_h5]
          omega
    have h01alt {i: ℕ} (ipos : i > 0) : IsAlternating ((10 ^ (2 * i) - 1)/(10 ^ 2 - 1)) := by
      unfold IsAlternating
      constructor
      . have : 10 ^ (2 * i) ≥ 10 ^ 2 := by
          have _h1 : 10 > 1 := by simp
          have _h2 : 2 * i ≥ 2 := by linarith
          exact Nat.pow_le_pow_of_le _h1 _h2
        have : 10 ^ (2 * i) - 1 ≥ 10 ^ 2 - 1 := by omega
        have : (10 ^ (2 * i) - 1) / (10 ^ 2 - 1) > 0 := by omega
        have _h3 := Nat.le_digits_len_le 10 1 ((10 ^ (2 * i) - 1) / (10 ^ 2 - 1)) (this)
        have _h4 : (Nat.digits 10 1).length = 1 := by simp
        rw [_h4] at _h3
        exact _h3
      intro j hj
      have _h1 : (Nat.digits 10 ((10 ^ (2 * i) - 1) / (10 ^ 2 - 1))).length ≤ 2 * i := by
        have haha (i : ℕ) (ipos : i > 0) : (Nat.digits 10 ((10 ^ (2 * i) - 1) / 10)).length ≤ 2 * i:= by
          have : 10 ^ (2 * i) - 1 ≤ 10 ^ (2 * i) := by simp
          have _h1 : (10 ^ (2 * i) - 1) / 10 ≤ 10 ^ (2 * i) / 10 := by omega
          have : 10 ^ (2 * i) / 10 = 10 ^ (2 * i - 1) := by
            cases i with
            | zero => linarith -- 不会触发，因为 ipos : i > 0
            | succ i =>
              simp [Nat.pow_succ, Nat.pow_mul, Nat.mul_div_cancel]
              ring_nf
              have : 2 + i * 2 - 1 = i * 2 + 1 := by omega
              rw [this]
              have : 10 ^ (i * 2 + 1) = 10 ^ (i * 2) * 10 := by ring
              rw [this]
              have : 100 ^ i * 100 / 10 = 100 ^ i * 10 := by omega
              rw [this, mul_comm i 2]
              have : (10 ^ 2) ^ i = 10 ^ (2 * i) := Eq.symm (Nat.pow_mul 10 2 i)
              rw [← this]
              norm_num
          rw [this] at _h1
          have _h2 : (Nat.digits 10 ((10 ^ (2 * i) - 1) / 10)).length ≤ (Nat.digits 10 (10 ^ (2 * i - 1))).length := by
            exact Nat.le_digits_len_le 10 ((10 ^ (2 * i) - 1) / 10) (10 ^ (2 * i - 1)) _h1
          have := pow10 (2 * i - 1)
          rw [this] at _h2
          have : 2 * i - 1 + 1 = 2 * i := by omega
          rw [this] at _h2
          exact _h2
        have : (10 ^ (2 * i) - 1) / (10 ^ 2 - 1) ≤ (10 ^ (2 * i) - 1) / 10 := by
          have _h1_: 10 ^ 2 - 1 ≥ 10 := by norm_num
          have _h2_: 10 > 0 := by norm_num
          exact Nat.div_le_div_left _h1_ _h2_
        have := Nat.le_digits_len_le 10 ((10 ^ (2 * i)- 1) / (10 ^ 2 - 1)) ((10 ^ (2 * i) - 1) / 10) this
        have haha := haha i (by omega)
        linarith
      have hj : j + 1 < 2 * i := by linarith
      have _h2 := h01alt22 ipos
      rw [_h2 (j+1) hj]
      have _h3 : j < 2 * i := by linarith
      rw [_h2 j _h3]
      omega
    ext n
    simp
    symm
    replace h3 (m : ℕ) (a : ℕ)(ha : a ≥ 1)(hm : m ≥ 1)(d2 : ¬ 2 ∣ m)(d5 : ¬ 5 ∣ m) :
      m ∣ (10^(2*a*m*(Nat.totient m)) -1)/ (10^(2*a)-1) := by
        rw[show 2*a*m*(Nat.totient m) = 2*a*(m*Nat.totient m) by ring]
        exact h3 m a ha hm d2 d5
    constructor
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
            have _h3 : 2 * 1 = 2 := rfl
            have _h4 := h3 n 1 (le_refl 1) (Nat.one_le_iff_ne_zero.mpr _h1) (Nat.two_dvd_ne_zero.mpr _h2) d5
            rw [mul_assoc 2, _h3] at _h4
            exact _h4
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
            have _h2 : ¬2 ∣ m := by
              by_contra _h2
              have _h2_1 : padicValNat 2 m > 0 := by
                by_contra _h3
                simp at _h3
                omega
              have _h2_2 : padicValNat 2 n = a := by rfl
              have _h2_3 : padicValNat 2 (2 ^ a) = a := padicValNat.prime_pow a
              have _h2_4 : padicValNat 2 (2 ^ a * m) = padicValNat 2 (2 ^ a) + padicValNat 2 m :=
                padicValNat.mul (p := 2) (Ne.symm (NeZero.ne' (2 ^ a))) (Nat.ne_zero_of_lt _h1)
              rw [← hm, _h2_3, _h2_2] at _h2_4
              linarith
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
            have : x * (10 ^ (2 * a * (m * m.totient)) - 1) / (10 ^ (2 * a) - 1) = x * ((10 ^ (2 * a * (m * m.totient)) - 1) / (10 ^ (2 * a) - 1)) := by
              apply Nat.mul_div_assoc x _h5
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
            have _h3 : x * (((10 ^ (2 * a)) ^ i - 1) / (10 ^ (2 * a) - 1)) = x * ((10 ^ (2 * a)) ^ i - 1) / (10 ^ (2 * a) - 1) := by
              have : 10 ^ (2 * a) - 1 ∣ ((10 ^ (2 * a)) ^ i - 1)  := div_b_sub_1 i (10 ^ (2 * a)) (Nat.pos_of_neZero (10 ^ (2 * a)))
              exact Eq.symm (Nat.mul_div_assoc x this)
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
          have _h2 : ¬2 ∣ m := by
            by_contra _h2
            have _h2_1 : padicValNat 2 m > 0 := by
              by_contra _h3
              simp at _h3
              omega
            have _h2_2 : padicValNat 2 n = a := by rfl
            have _h2_3 : padicValNat 2 (2 ^ a) = a := padicValNat.prime_pow a
            have _h2_4 : padicValNat 2 (2 ^ a * m) = padicValNat 2 (2 ^ a) + padicValNat 2 m :=
              padicValNat.mul (p := 2) (Ne.symm (NeZero.ne' (2 ^ a))) (Nat.ne_zero_of_lt _h1)
            have _h2_5 : padicValNat 2 (5 ^ b) = 0 := by
              have : ¬ 2 ∣ 5 ^ b := by
                norm_num
                have h1 : 5 ^ b % 2 = 1 := by
                    have h : ∀ b : ℕ, 5 ^ b % 2 = 1 := by
                      intro b
                      induction b with
                      | zero => simp
                      | succ b ih => simp [Nat.pow_add, Nat.mul_mod, ih]
                    exact h b
                exact h1
              exact padicValNat.eq_zero_of_not_dvd this
            have _h2_6 : padicValNat 2 (2 ^ a * 5 ^ b) = padicValNat 2 (2 ^ a) + padicValNat 2 (5 ^ b) := by
              exact padicValNat.mul (p := 2) (Ne.symm (NeZero.ne' (2 ^ a))) (Ne.symm (NeZero.ne' (5 ^ b)))
            have _h2_7 : padicValNat 2 (2 ^ a * 5 ^ b * m) = padicValNat 2 (2 ^ a * 5 ^ b) + padicValNat 2 m := by
              exact padicValNat.mul (p := 2) (Ne.symm (NeZero.ne' (2 ^ a * 5 ^ b))) (Nat.ne_zero_of_lt _h1)
            rw [← hm, _h2_6, _h2_5, _h2_3, _h2_2] at _h2_7
            linarith
          have _h3 : ¬5 ∣ m := by
            by_contra _h2
            have _h2_1 : padicValNat 5 m > 0 := by
              by_contra _h3
              simp at _h3
              omega
            have _h2_2 : padicValNat 5 n = b := by rfl
            have _h2_3 : padicValNat 5 (5 ^ b) = b := padicValNat.prime_pow b
            have _h2_4 : padicValNat 5 (5 ^ b * m) = padicValNat 5 (5 ^ b) + padicValNat 5 m :=
              padicValNat.mul (p := 5) (Ne.symm (NeZero.ne' (5 ^ b))) (Nat.ne_zero_of_lt _h1)
            have _h2_5 : padicValNat 5 (2 ^ a) = 0 := by
              have : ¬ 5 ∣ 2 ^ a := by
                -- 先分情况讨论
                cases a with
                | zero =>
                  -- a = 0 时 2^0 = 1，显然 5 ∤ 1
                  norm_num
                | succ a =>
                  -- a ≥ 1，用归纳法证明 2^{a+1} % 5 ∈ {2,4,3,1}
                  have h : ∀ a : ℕ, 2 ^ (a + 1) % 5 = 2 ∨ 2 ^ (a + 1) % 5 = 4
                            ∨ 2 ^ (a + 1) % 5 = 3 ∨ 2 ^ (a + 1) % 5 = 1 := by
                    intro a
                    induction a with
                    | zero => norm_num
                    | succ a ih =>
                      have : 2 ^ (a + 1 + 1) % 5 = (2 * 2 ^ (a + 1)) % 5 := by ring_nf
                      rw [this, Nat.mul_mod]
                      rcases ih with (h | h | h | h) <;> simp [h]
                  -- 反证法
                  intro h5
                  have h' := h a
                  have : 2 ^ (a + 1) % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp h5
                  omega
              exact padicValNat.eq_zero_of_not_dvd this
            have _h2_6 : padicValNat 5 (5 ^ b * 2 ^ a) = padicValNat 5 (5 ^ b) + padicValNat 5 (2 ^ a) := by
              exact padicValNat.mul (p := 5) (Ne.symm (NeZero.ne' (5 ^ b))) (Ne.symm (NeZero.ne' (2 ^ a)))
            have _h2_7 : padicValNat 5 (5 ^ b * 2 ^ a * m) = padicValNat 5 (5 ^ b * 2 ^ a) + padicValNat 5 m := by
              exact padicValNat.mul (p := 5) (Ne.symm (NeZero.ne' (5 ^ b * 2 ^ a))) (Nat.ne_zero_of_lt _h1)
            rw [mul_comm (5 ^ b), ← hm, mul_comm (2 ^ a), _h2_6, _h2_5, _h2_3, _h2_2] at _h2_7
            linarith
          have hmdiv := h3 m b (by linarith) _h1 _h2 _h3
          have habdiv : (2 ^ a * 5 ^ b) ∣ x := by
            have : 2 ^ a ≤ 2 := Nat.pow_le_pow_of_le Nat.one_lt_two ha
            have : 2 ^ a > 0 := Nat.two_pow_pos a
            have _hab_1 : 2 ^ a ∣ 2 := by
              by_cases h : a = 0
              . rw [h]
                simp
              . have : a ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
                have : a = 1 := Eq.symm (Nat.le_antisymm this ha)
                rw [this]
                simp
            have : 5 ^ (2 * b) = 5 ^ b * 5 ^ b := by ring
            have _hab_2: 5 ^ b ∣ 5 ^ b * 5 ^ b := Nat.dvd_mul_left (5 ^ b) (5 ^ b)
            rw [← this] at _hab_2
            have := Nat.mul_dvd_mul _hab_1 _hab_2
            exact Nat.dvd_trans this hx3
          have _h4 := Nat.mul_dvd_mul habdiv hmdiv
          have : i = m * m.totient := rfl
          rw [← hm] at _h4
          unfold i
          rw [← mul_assoc (2 * b)]
          have _h5 := div_b_sub_1 i (10 ^ (2 * b)) (by simp)
          have : (10 ^ (2 * b)) ^ i = 10 ^ (2 * b * i) := by ring
          rw [this] at _h5
          unfold i at _h5
          have : x * (10 ^ (2 * b * (m * m.totient)) - 1) / (10 ^ (2 * b) - 1) = x * ((10 ^ (2 * b * (m * m.totient)) - 1) / (10 ^ (2 * b) - 1)) := by
            apply Nat.mul_div_assoc x _h5
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
            have : 10 ^ (2 * b) - 1 ∣ ((10 ^ (2 * b)) ^ i - 1)  := div_b_sub_1 i (10 ^ (2 * b)) (Nat.pos_of_neZero (10 ^ (2 * b)))
            exact Eq.symm (Nat.mul_div_assoc x this)
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
      have _h3 := _h2 0
      simp at _h3
      have digits_zero_eq_mod {b n : ℕ} (hb : b > 1) (hn : n > 0) :
          (Nat.digits b n)[0]! = n % b := by
        rw [Nat.digits_def' (by omega) (by omega)]
        simp
      have _h4 : (Nat.digits 10 x)[0]! = 0 := by
        simp
        have _h3 : 10 > 1 := by simp
        have _h4 : x > 0 := by
          by_contra _h4
          simp at _h4
          rw [_h4] at _h1
          simp at _h1
        have _h5 := digits_zero_eq_mod _h3 _h4
        have _h6 : x % 10 = 0 := by omega
        rw [_h6] at _h5
        simp at _h5
        exact _h5
      have mpos : m > 0 := by
        by_contra mzero
        simp at mzero
        rw [mzero] at hm
        contradiction
      have xge20 : x ≥ 20 := by omega
      have : (Nat.digits 10 x).length ≥ (Nat.digits 10 20).length := Nat.le_digits_len_le 10 20 x xge20
      simp at this
      have _h3 := _h3 this
      simp at _h4
      rw [_h4] at _h3
      norm_num at _h3
      have : x = m * 2 * 10 := by omega
      rw [this] at _h3
      have := digits_mul_pow_offset (m * 2) 1 0 (by omega)
      simp at this
      rw [← this] at _h3
      have := @digits_zero_eq_mod 10 (m * 2) (by simp) (by omega)
      simp at this
      rw [this] at _h3
      norm_num at _h3
