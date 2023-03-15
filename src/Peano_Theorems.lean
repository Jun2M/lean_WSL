import tactic.nth_rewrite.default
import tactic.ring


-- Define a custom type N of natural numbers
inductive N : Type
| Z : N
| S : N → N

reserve infix `+`:75
reserve infix `*`:76
reserve infix `ㅅ`:100

notation `Z` := N.Z
notation `S` := N.S
def N.mul : N → N → N := sorry
def N.add : N → N → N := sorry


notation (name := N.add) a `+` b := N.add a b
notation (name := N.mul) a `*` b := N.mul a b


theorem apply_to_both_side_of_eq {α : Type} {a b : α} (h : a = b) (f : α → α) : f a = f b :=
begin
    rw h,
end

notation (name := apply_to_both_side_of_eq) a `ㅅ` b := apply_to_both_side_of_eq a b

theorem iff_imp_false_imp_false (a b : Prop) (h : a ↔ b) : (a → false) → (b → false) :=
begin
    exact (iff.not h).mp,
end


-- Start of the proof

axioms 
    (PA1 : ∀ n : N  ,      Z ≠ S n) 
    (PA2 : ∀ m n : N,      S m = S n → m = n)
    (PA3 : ∀ n : N,        n + Z = n)
    (PA4 : ∀ m n : N,      m + S n = S (m + n))
    (PA5 : ∀ n : N,        n * Z = Z)
    (PA6 : ∀ m n : N,      m * S n = (m * n) + m)
    (PA7 : ∀ h : N → bool, (h(Z) ∧ ∀ n : N, h(n) → h(S n)) → ∀ n : N, h(n))


lemma S_iff_both_sides : ∀ m n : N, S m = S n ↔ m = n :=
begin
    intros m n,
    split,
    exact PA2 m n,
    intro h,
    rw h,
end
  
theorem PT8 : ∀ x : N, Z + x = x :=
begin
    intro x,
    induction x with n IH,
    exact PA3 Z,
    calc Z + S n = S (Z + n) : by rw PA4
             ... = S n       : by rw IH,
end

theorem Z_left_identity_add : ∀ x : N, Z + x = x := PT8

theorem PT9 : ∀ x y : N, S x + y = S (x + y) :=
begin
    intros x y,
    induction y with n IH,

    calc S x + Z = S x              : by rw PA3
             ... = S (x + Z)        : by rw PA3,

    calc S x + S n = S (S x + n)    : by rw PA4
               ... = S (S (x + n))  : by rw IH
               ... = S (x + S n)    : by rw PA4,
end

theorem S_left_associative : ∀ x y : N, S x + y = S (x + y) := PT9

theorem PT10 : ∀ x y : N, x + y = y + x :=
begin
    intros x y,
    induction y with n IH,

    calc x + Z = x              : by rw PA3
           ... = Z + x          : by rw PT8,

    calc x + S n = S (x + n)    : by rw PA4
             ... = S (n + x)    : by rw IH
             ... = S n + x      : by rw PT9,
end

theorem commutative_add : ∀ x y : N, x + y = y + x := PT10

theorem PT11 : ∀ x y z : N, (x + y) + z = x + (y + z) :=
begin
    intros x y z,
    induction z with n IH,

    calc (x + y) + Z = x + y                : by rw PA3
                 ... = x + (y + Z)          : by rw PA3,

    calc (x + y) + S n = S ((x + y) + n)    : by rw PA4
                   ... = S (x + (y + n))    : by rw IH
                   ... = x + S (y + n)      : by rw ← PA4
                   ... = x + (y + S n)      : by rw ← PA4,
end

theorem associative_add : ∀ x y z : N, (x + y) + z = x + (y + z) := PT11

theorem PT12 : ∀ x : N, Z * x = Z :=
begin
    intro x,
    induction x with n IH,

    exact PA5 Z,

    calc Z * S n = (Z * n) + Z  : by rw PA6
             ... = Z + Z        : by rw IH
             ... = Z            : by rw PA3,
end

theorem Z_left_sink_mul : ∀ x : N, Z * x = Z := PT12

lemma swap_s_add : ∀ x y : N, (S x) + y = x + (S y) :=
begin
    intros x y,
    calc (S x) + y = S (x + y)  : by rw PT9
               ... = x + (S y)  : by rw PA4,
end

theorem PT13 : ∀ x y : N, (S x) * y = (x * y) + y :=
begin
    intros x y,
    induction y with n IH,

    calc (S x) * Z = Z              : by rw PA5
               ... = Z + Z          : by rw PA3
               ... = (x * Z) + Z    : by rw PA5,

    calc (S x) * (S n) = ((S x) * n) + (S x)   : by rw PA6
                   ... = x * n + n + (S x)     : by rw IH
                   ... = x * n + (n + (S x))   : by rw PT11
                   ... = x * n + (S n + x)     : by rw swap_s_add
                   ... = x * n + (x + S n)     : by nth_rewrite 1 PT10
                   ... = x * n + x + S(n)      : by rw ← PT11
                   ... = x * (S n) + (S n)     : by rw PA6,
end

theorem S_left_distribute : ∀ x y : N, (S x) * y = (x * y) + y := PT13

theorem PT14 : ∀ x y : N, x * y = y * x :=
begin
    intros x y,
    induction y with n IH,

    calc x * Z = Z              : by rw PA5
           ... = Z * x          : by rw PT12,

    calc x * S n = x * n + x    : by rw PA6
             ... = n * x + x    : by rw IH
             ... = S n * x      : by rw PT13,
end

theorem commutative_mul : ∀ x y : N, x * y = y * x := PT14

theorem PT15 : ∀ x y z : N, x * (y + z) = x * y + x * z :=
begin
    intros x y z,
    induction z with n IH,

    calc x * (y + Z) = x * y            : by rw PA3
                 ... = x * y + Z        : by rw PA3
                 ... = x * y + x * Z    : by sorry, -- rw ← PA5 x,

    calc x * (y + S n) = x * (S y + n)                  : by rw swap_s_add
                   ... = x * (S (y + n))                : by rw PT9
                   ... = x * (y + n) + x                : by rw PA6
                   ... = x * y + x * n + x              : by rw IH
                   ... = x * y + (x * n + x)            : by rw PT11 (x * y) (x * n) x
                   ... = x * y + x * S n                : by rw ← PA6,
end

theorem left_distribute_mul : ∀ x y z : N, x * (y + z) = x * y + x * z := PT15

theorem PT16 : ∀ x y z : N, (x + y) * z = x * z + y * z :=
begin
    intros x y z,
    induction z with n IH,

    calc (x + y) * Z = Z                               : by rw PA5
                 ... = Z + Z                           : by rw PA3
                 ... = x * Z + Z                       : by rw PA5
                 ... = x * Z + y * Z                   : by sorry, -- rw ← PA5 x,

    calc (x + y) * S n = (x + y) * n + (x + y)         : by rw PA6
                   ... = (x * n + y * n) + (x + y)     : by rw ← IH
                   ... = x * n + y * n + x + y         : by rw ← PT11
                   ... = x * n + (y * n + x) + y       : by rw PT11 (x * n) (y * n) x
                   ... = x * n + (x + y * n) + y       : by rw PT10 x (y * n)
                   ... = (x * n + x) + (y * n + y)     : by rw [PT11 (x * n) (x + (y * n)) y, PT11 x (y * n) y, PT11 (x * n) x ((y * n) + y)]
                   ... = (x * S n) + (y * S n)         : by rw [← PA6 x , ← PA6 y],
end

theorem right_distribute_mul : ∀ x y z : N, (x + y) * z = x * z + y * z := PT16

theorem PT17 : ∀ x y z : N, x * (y * z) = (x * y) * z :=
begin
    intros x y z,
    induction z with n IH,

    calc x * (y * Z) = Z            : by rw [PA5, PA5]
                 ... = (x * y) * Z  : by rw PA5,

    calc x * (y * S n) = x * (y * n + y)        : by rw PA6
                   ... = x * (y * n) + x * y    : by rw PT15
                   ... = (x * y) * n + x * y    : by rw IH
                   ... = (x * y) * S n          : by rw PA6,
end

theorem associative_mul : ∀ x y z : N, x * (y * z) = (x * y) * z := PT17

theorem PT18 : ∀ x y z : N, x + z = y + z → x = y :=
begin
    intros x y z H,
    induction z with n IH,
    
    rw [PA3 x, PA3 y] at H,
    exact H,

    apply IH,
    rw [PA4, PA4] at H,
    exact PA2 (x + n) (y + n) H,
end

theorem right_cancel_add : ∀ x y z : N, x + z = y + z → x = y := PT18

lemma left_cancel_add : ∀ x y z : N, x + y = x + z → y = z :=
begin
    intros x y z H,
    rw [PT10 x y, PT10 x z] at H,
    exact PT18 y z x H,
end


theorem PT19 : ∀ x : N, x + S Z = S x :=
begin
    intro x,
    rw [PA4, PA3],
end

theorem add_one : ∀ x : N, x + S Z = S x := PT19

theorem PT20 : ∀ x : N, x * S Z = x :=
begin
    intro x,
    rw [PA6, PA5, PT8],
end

theorem mul_one_N : ∀ x : N, x * S Z = x := PT20

theorem PT21 : ∀ x : N, x * S (S Z) = x + x :=
begin
    intro x,
    rw [PA6, PT20],
end

theorem mul_two_N : ∀ x : N, x * S (S Z) = x + x := PT21

theorem PT22 : ∀ x y : N, x + y = Z → (x = Z ∧ y = Z) :=
begin
    intros x y H,
    induction x with n IH,

        split,
            refl,

            rw PT8 at H,
            exact H,

        rw [PT9] at H,
        exfalso,
        apply PA1 (n + y),
        rw H,
end

theorem add_to_zero : ∀ x y : N, x + y = Z → (x = Z ∧ y = Z) := PT22

theorem PT23 : ∀ x y : N, x ≠ Z → (x * y = Z → y = Z) :=
begin
    intros x y H H1,
    induction y with n IH,

        refl,

        rw [PA6] at H1,
        exfalso,
        apply H,
        exact (PT22 (x * n) x H1).2,
end

theorem mul_to_zero : ∀ x y : N, x ≠ Z → (x * y = Z → y = Z) := PT23

theorem PT24 : ∀ x y : N, x + y = S Z → (x = Z ∧ y = S Z) ∨ (x = S Z ∧ y = Z) :=
begin
    intros x y H,
    induction x with n IH,

        rw [PT8] at H,
        left,
        split,
            refl,

            exact H,

        rw [PT9] at H,
        have n_y_Z := PT22 _ _ (PA2 _ _ H),
        right,
        split,
            rw n_y_Z.1,

            exact n_y_Z.2,
end

theorem add_to_one : ∀ x y : N, x + y = S Z → (x = Z ∧ y = S Z) ∨ (x = S Z ∧ y = Z) := PT24

theorem PT25 : ∀ x y : N, x * y = S Z → x = S Z ∧ y = S Z :=
begin
    intros x y H,
    induction x with n IH,

        exfalso,
        rw PT12 y at H,
        apply PA1 Z,
        exact H,

        clear IH,
        rw [PT13] at H,
        cases (PT24 _ _ H) with H1 H1;
        cases H1 with a b;
        clear H,
        {
            rw [PT14] at a,
            have y_nonzero := PA1 Z,
            rw ← b at y_nonzero,
            have n_zero := PT23 y n (y_nonzero.symm) a,
            refine ⟨ n_zero ㅅ S, b ⟩,
        },
        {
            exfalso,
            rw b at a,
            apply PA1 Z,
            rw PA5 at a,
            exact a,
        },
end

theorem mul_to_one : ∀ x y : N, x * y = S Z → x = S Z ∧ y = S Z := PT25

theorem PT26 : ∀ x : N, x ≠ Z → ∃ y : N, x = S y :=
begin
    intros x H,
    induction x with n IH,

        exfalso,
        apply H,
        refl,

        exact ⟨ n, rfl ⟩,
end

theorem exists_pred : ∀ x : N, x ≠ Z → ∃ y : N, x = S y := PT26

theorem PT27 : ∀ x y z : N, z ≠ Z → (x * z = y * z → x = y) :=
begin
    intros x y z H H1,
    sorry,
        
end

theorem right_cancel_mul : ∀ x y z : N, z ≠ Z → (x * z = y * z → x = y) := PT27

theorem PT28 : ∀ x : N, x ≠ Z ∧ x ≠ S Z → ∃ y : N, x = S (S y) :=
begin
    intros x H,
    induction x with n IH,

        exfalso,
        apply H.1,
        refl,

        cases em (n = S Z) with a b,
            
            use Z,
            rw a,

            have H2 := (iff.not (S_iff_both_sides n Z)).mp H.2,
            clear H,
            cases IH ⟨ H2, b ⟩ with x hx,
            use (S x),
            rw hx,
end

lemma Z_only_right_identity_add : ∀ x y : N, x + y = x → y = Z :=
begin
    intros x y H,
    induction x with n IH,

        rw [PT8] at H,
        exact H,

        rw [PT9] at H,
        exact IH (PA2 _ _ H),
end

lemma Z_only_left_identity_add : ∀ x y : N, x + y = y → x = Z :=
begin
    intros x y H,
    induction y with n IH,

        rw [PA3] at H,
        exact H,

        rw [PA4] at H,
        exact IH (PA2 _ _ H),
end

lemma SZ_only_left_identity_mul : ∀ x y : N, y ≠ Z → x * y = y → x = S Z :=
begin
    intros x y H H1,
    nth_rewrite 1 ← PT20 y at H1,
    nth_rewrite 1 [PT14] at H1,
    exact PT27 _ _ _ H H1,
end

lemma SZ_only_right_identity_mul : ∀ x y : N, x ≠ Z → x * y = x → y = S Z :=
begin
    intros x y H H1,
    nth_rewrite 1 ← PT20 x at H1,
    nth_rewrite 1 [PT14] at H1,
    rw [PT14] at H1,
    exact PT27 _ _ _ H H1,
end

-- theorem PT29 : ∀ n m : ℕ, n ≠ m → n' ≠ m'
-- theorem PT30 : ∀ n m : ℕ, n' + m' = (n + m)' ∧ n' * m' = (n * m)'

reserve infix `<`:50
reserve infix `≤`:50

notation (name := le) x ` ≤ ` y := ∃ z : N, x + z = y
notation (name := lt) x ` < ` y := ∃ z : N, x + z = y ∧ z ≠ Z


theorem PT31 : ∀ x : N, x < x → false :=
begin
    intros x H,
    cases H with z H,
    apply H.2,
    exact (Z_only_right_identity_add x z H.1),
end

theorem irrefl_lt : ∀ x : N, x < x → false := PT31

theorem PT32 : ∀ x y z : N, x < y ∧ y < z → x < z :=
begin
    intros x y z H,
    rcases H with ⟨ a, b, hb, b_nonzero ⟩,
    rcases a with ⟨ a, ha, a_nonzero ⟩,

    use (a + b),
    split,
        rw [← associative_add x a b, ha, hb],
        
        intro H3,
        have := add_to_zero _ _ H3,
        exact a_nonzero this.1,
end

theorem trans_lt : ∀ x y z : N, x < y ∧ y < z → x < z := PT32

theorem PT33 : ∀ x y : N, x < y → y < x → false :=
begin
    intros x y H1 H2,
    cases H1 with a H1,
    cases H1 with H1 a_nonzero,
    cases H2 with b H2,
    cases H2 with H2 b_nonzero,

    rw ← H1 at H2,
    rw associative_add at H2,
    have := Z_only_right_identity_add _ _ H2,
    have := add_to_zero _ _ this,
    exact a_nonzero this.1,
end

theorem nonsym_lt : ∀ x y : N, x < y → y < x → false := PT33

theorem PT34 : ∀ x y z : N, x < y → x + z < y + z :=
begin
    intros x y z H,
    cases H with a H,
    cases H with H a_nonzero,
    use a,
    split,
        rw [associative_add, commutative_add z a, ← associative_add, H],
        exact a_nonzero,
end

theorem right_add_lt : ∀ x y z : N, x < y → x + z < y + z := PT34

theorem PT35 : ∀ x : N, x ≤ x :=
begin
    intro x,
    use Z,
    exact PA3 _,
end

theorem refl_le : ∀ x : N, x ≤ x := PT35

theorem PT36 : ∀ x y z : N, x ≤ y ∧ y ≤ z → x ≤ z :=
begin
    intros x y z H,
    cases H with a b,
    cases a with a ha,
    cases b with b hb,
    use (a + b),
    rw [← associative_add x a b, ha, hb],
end

theorem trans_le : ∀ x y z : N, x ≤ y ∧ y ≤ z → x ≤ z := PT36

theorem PT37 : ∀ x y z : N, x ≤ y → x + z ≤ y + z :=
begin
    intros x y z H,
    cases H with a ha,
    use a,
    rw [associative_add x z a, commutative_add z a, ← associative_add x a z, ha],
end

theorem right_add_le : ∀ x y z : N, x ≤ y → x + z ≤ y + z := PT37

theorem PT38 : ∀ x y z : N, x ≤ y ∧ y < z → x < z :=
begin
    intros x y z H,
    cases H with a b,
    cases a with a ha,
    cases b with b hb,
    cases hb with hb b_nonzero,

    use (a+b),
    split,
        rw [← associative_add x a b, ha, hb],
        intro ab_nonzero,
        apply b_nonzero,
        have := add_to_zero _ _ ab_nonzero,
        exact this.2,
end

theorem PT39 : ∀ x : N, Z ≤ x :=
begin
    intro x,
    use x,
    exact PT8 _,
end

theorem Zero_le : ∀ x : N, Z ≤ x := PT39

theorem PT40 : ∀ x : N, Z < S x :=
begin
    intro x,
    use S x,
    split,
        rw PT8,
        exact (PA1 x).symm,
end

theorem Zero_lt : ∀ x : N, Z < S x := PT40

theorem PT41 : ∀ x y : N, x < y ↔ S x ≤ y :=
begin
    intros x y,
    split;
    intro H;
    cases H with a H,
        cases H with H a_nonzero,
        cases exists_pred a a_nonzero with b hb,
        use b,
        rw [← H, hb],
        exact swap_s_add x b,

        use S a,
        split,
            rw swap_s_add x a at H,
            exact H,
            exact (PA1 a).symm,
end

theorem lt_iff_S_le : ∀ x y : N, x < y ↔ S x ≤ y := PT41

theorem PT42 : ∀ x y : N, x ≤ y ↔ x < S y :=
begin
    intros x y,
    split;
    intro H;
    cases H with a H,
        use S a,
        split,
            rw [PA4, S_iff_both_sides, H],

            exact (PA1 a).symm,

        cases exists_pred a H.2 with b hb,
        use b,
        rw [← S_iff_both_sides, ← H.1, hb, PA4],
end

theorem le_iff_S_lt : ∀ x y : N, x ≤ y ↔ x < S y := PT42

theorem PT43 : ∀ x : N, x < S x :=
begin
    intro x,
    use S Z,
    split,
        exact add_one x,
        exact (PA1 Z).symm,
end

theorem lt_Self : ∀ x : N, x < S x := PT43

-- theorem PT44 : ∀ n : ℕ, n' < (n + 1)'

theorem PT45 : ∀ x y : N, x ≠ y → x < y ∨ y < x :=
begin
    intros x y H,
    sorry,
end

theorem lt_or_gt : ∀ x y : N, x ≠ y → x < y ∨ y < x := PT45

