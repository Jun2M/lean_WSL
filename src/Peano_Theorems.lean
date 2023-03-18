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

def add : N → N → N := 
begin
    intros a b,
    induction a with n IH,
        exact b,

        exact S (IH),
end
notation (name := N.add) a `+` b := add a b


def mul : N → N → N := 
begin
    intros a b,
    induction a with n IH,
        exact Z,

        exact (b + IH),
end
notation (name := N.mul) a `*` b := mul a b


theorem apply_to_both_side_of_eq {α : Type} {a b : α} (h : a = b) (f : α → α) : f a = f b :=
begin
    rw h,
end

notation (name := apply_to_both_side_of_eq) a `ㅅ` b := apply_to_both_side_of_eq a b


theorem not_to_not {α : Type} {a b c d : α} (h : a = b ↔ c = d) : a ≠ b ↔ c ≠ d :=
begin
    split,
        intros h1 h2,
        apply h1,
        rw ← h at h2,
        exact h2,

        intros h1 h2,
        apply h1,
        rw h at h2,
        exact h2,
end


-- Start of the proof

axioms 
    (PA1 : ∀ n : N  ,      Z ≠ S n) 
    (PA2 : ∀ m n : N,      S m = S n → m = n)
    (PA3 : ∀ n : N,        n + Z = n)
    (PA4 : ∀ m n : N,      m + S n = S (m + n))
    (PA5 : ∀ n : N,        n * Z = Z)
    (PA6 : ∀ m n : N,      m * S n = (m * n) + m)
    (PA7 : ∀ h : N → Prop, (h(Z) ∧ ∀ n : N, h(n) → h(S n)) → ∀ n : N, h(n))


theorem S_nonzero : ∀ n : N, Z ≠ S n := PA1
theorem S_inj : ∀ m n : N, S m = S n → m = n := PA2
theorem right_identity_add_Z : ∀ x : N, x + Z = x := PA3
theorem S_right_associative : ∀ x y : N, x + S y = S (x + y) := PA4
theorem right_sink_mul_Z : ∀ x : N, x * Z = Z := PA5
theorem S_right_distributive : ∀ x y : N, x * S y = (x * y) + x := PA6
theorem S_induction : ∀ h : N → Prop, (h(Z) ∧ ∀ n : N, h(n) → h(S n)) → ∀ n : N, h(n) := PA7


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
    apply S_induction (λ n, Z + n = n),
    split,
        exact PA3 Z,

        intros n IH,
        calc Z + S n = S (Z + n) : by rw PA4
                 ... = S n       : by rw IH,
end
theorem left_identity_add_Z : ∀ x : N, Z + x = x := PT8


theorem PT9 : ∀ x y : N, S x + y = S (x + y) :=
begin
    intros x y,
    apply S_induction (λ n, S x + n = S (x + n)),
    split,
        calc S x + Z = S x              : by rw PA3
                ... = S (x + Z)         : by rw PA3,

        intros n IH,
        calc S x + S n = S (S x + n)    : by rw PA4
                ... = S (S (x + n))     : by rw IH
                ... = S (x + S n)       : by rw PA4,
end
theorem S_left_associative : ∀ x y : N, S x + y = S (x + y) := PT9


lemma swap_s_add : ∀ x y : N, (S x) + y = x + (S y) :=
begin
    intros x y,
    calc (S x) + y = S (x + y)  : by rw PT9
               ... = x + (S y)  : by rw PA4,
end


theorem PT10 : ∀ x y : N, x + y = y + x :=
begin
    intros x y,
    apply S_induction (λ n, x + n = n + x),
    split,
        calc x + Z = x              : by rw PA3
               ... = Z + x          : by rw PT8,

        intros n IH,
        calc x + S n = S (x + n)    : by rw PA4
                 ... = S (n + x)    : by rw IH
                 ... = S n + x      : by rw PT9,
end
theorem add_commutative : ∀ x y : N, x + y = y + x := PT10


theorem PT11 : ∀ x y z : N, (x + y) + z = x + (y + z) :=
begin
    intros x y z,
    apply S_induction (λ n, (x + y) + n = x + (y + n)),
    split,
        calc (x + y) + Z = x + y                : by rw PA3
                     ... = x + (y + Z)          : by rw PA3,

        intros n IH,
        calc (x + y) + S n = S ((x + y) + n)    : by rw PA4
                       ... = S (x + (y + n))    : by rw IH
                       ... = x + S (y + n)      : by rw ← PA4
                       ... = x + (y + S n)      : by rw ← PA4,
end
theorem add_associative : ∀ x y z : N, (x + y) + z = x + (y + z) := PT11


theorem PT12 : ∀ x : N, Z * x = Z :=
begin
    intro x,
    apply S_induction (λ n, Z * n = Z),
    split,
        exact PA5 Z,

        intros n IH,
        calc Z * S n = (Z * n) + Z  : by rw PA6
                 ... = Z + Z        : by rw IH
                 ... = Z            : by rw PA3,
end
theorem left_sink_mul_Z : ∀ x : N, Z * x = Z := PT12


theorem PT13 : ∀ x y : N, (S x) * y = (x * y) + y :=
begin
    intros x y,
    apply S_induction (λ n, (S x) * n = (x * n) + n),
    split,
        calc (S x) * Z = Z              : by rw PA5
                   ... = Z + Z          : by rw PA3
                   ... = (x * Z) + Z    : by rw PA5,

        intros n IH,
        calc (S x) * (S n) = (S x) * n + (S x)      : by rw PA6
                       ... = x * n + n + (S x)      : by rw IH
                       ... = x * n + (n + (S x))    : by rw PT11
                       ... = x * n + (S n + x)      : by rw swap_s_add
                       ... = x * n + (x + S n)      : by nth_rewrite 1 PT10
                       ... = x * n + x + S(n)       : by rw ← PT11
                       ... = x * (S n) + (S n)      : by rw PA6,
end
theorem S_left_distribute : ∀ x y : N, (S x) * y = (x * y) + y := PT13


theorem PT14 : ∀ x y : N, x * y = y * x :=
begin
    intros x y,
    apply S_induction (λ n, x * n = n * x),
    split,
        calc x * Z = Z                  : by rw PA5
               ... = Z * x              : by rw PT12,

        intros n IH,
        calc x * S n = x * n + x        : by rw PA6
                 ... = n * x + x        : by rw IH
                 ... = S n * x          : by rw PT13,
end
theorem mul_commutative : ∀ x y : N, x * y = y * x := PT14


theorem PT15 : ∀ x y z : N, x * (y + z) = x * y + x * z :=
begin
    intros x y z,
    apply S_induction (λ n, x * (y + n) = x * y + x * n),
    split,

        calc x * (y + Z) = x * y            : by rw PA3
                     ... = x * y + Z        : by rw PA3
                     ... = x * y + x * Z    : by rw PA5 x,

        intros n IH,
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
    apply S_induction (λ n, (x + y) * n = x * n + y * n),
    split,

        calc (x + y) * Z = Z                               : by rw PA5
                     ... = Z + Z                           : by rw PA3
                     ... = x * Z + Z                       : by rw PA5
                     ... = x * Z + y * Z                   : by rw [PA5, PA5],

        intros n IH,
        calc (x + y) * S n = (x + y) * n + (x + y)         : by rw PA6
                       ... = (x * n + y * n) + (x + y)     : by rw ← IH
                       ... = x * n + (y * n + x) + y       : by rw [← PT11, PT11 (x * n) (y * n) x]
                       ... = x * n + (x + y * n) + y       : by rw PT10 x (y * n)
                       ... = (x * n + x) + (y * n + y)     : by rw [PT11 (x * n) (x + (y * n)) y, PT11 x (y * n) y, PT11 (x * n) x ((y * n) + y)]
                       ... = (x * S n) + (y * S n)         : by rw [← PA6 x , ← PA6 y],
end
theorem right_distribute_mul : ∀ x y z : N, (x + y) * z = x * z + y * z := PT16


theorem PT17 : ∀ x y z : N, x * (y * z) = (x * y) * z :=
begin
    intros x y z,
    apply S_induction (λ n, x * (y * n) = (x * y) * n),
    split,

        calc x * (y * Z) = Z            : by rw [PA5, PA5]
                     ... = (x * y) * Z  : by rw PA5,

        intros n IH,
        calc x * (y * S n) = x * (y * n + y)        : by rw PA6
                       ... = x * (y * n) + x * y    : by rw PT15
                       ... = (x * y) * n + x * y    : by rw IH
                       ... = (x * y) * S n          : by rw PA6,
end
theorem mul_associative : ∀ x y z : N, x * (y * z) = (x * y) * z := PT17


theorem PT18 : ∀ x y z : N, x + z = y + z → x = y :=
begin
    intros x y z,
    apply S_induction (λ n, x + n = y + n → x = y),
    split,

        intro H,
        rw [PA3 x, PA3 y] at H,
        exact H,

        intros n IH H,
        apply IH,                       clear IH,
        rw [PA4, PA4] at H,
        exact PA2 (x + n) (y + n) H,
end


theorem right_cancel_add_iff : ∀ x y z : N, x + y = z + y ↔ x = z := 
begin
    intros x y z,
    split,
        exact PT18 x z y,
        intro H,
        rw H,
end

lemma left_cancel_add_iff : ∀ x y z : N, x + y = x + z ↔ y = z :=
begin
    intros x y z,
    split;
    intros H,
        rw [PT10 x y, PT10 x z] at H,
        exact PT18 y z x H,
        rw H,
end


theorem PT19 : ∀ x : N, x + S Z = S x :=
begin
    intro x,
    rw [PA4],
    rw [PA3],
end
theorem add_one : ∀ x : N, x + S Z = S x := PT19


theorem PT20 : ∀ x : N, x * S Z = x :=
begin
    intro x,
    rw [PA6], 
    rw [PA5], 
    rw [PT8],
end
theorem mul_one_ : ∀ x : N, x * S Z = x := PT20


theorem PT21 : ∀ x : N, x * S (S Z) = x + x :=
begin
    intro x,
    rw [PA6], 
    rw [PT20],
end
theorem mul_two_ : ∀ x : N, x * S (S Z) = x + x := PT21


theorem PT22 : ∀ x y : N, x + y = Z → (x = Z ∧ y = Z) :=
begin
    intros x y,
    apply S_induction (λ n, x + n = Z → (x = Z ∧ n = Z)),
    split,
        intros H,
        split,
            rw [PA3] at H,
            exact H,
            refl,

        intros a IH H,              clear IH,
        exfalso,
        rw [PA4] at H,
        have succ_nonzero := (PA1 (x + a)).symm,
        contradiction,
end
theorem add_to_zero : ∀ x y : N, x + y = Z → (x = Z ∧ y = Z) := PT22


theorem add_to_zero_iff : ∀ x y : N, x + y = Z ↔ (x = Z ∧ y = Z) := 
begin
    intros x y,
    split,
        exact PT22 x y,

        intro H,
        rcases H with ⟨ rfl, rfl ⟩,
        exact PA3 Z,
end


theorem PT23 : ∀ x y : N, x ≠ Z → (x * y = Z → y = Z) :=
begin
    intros x y,
    apply S_induction (λ n, x ≠ Z → (x * n = Z → n = Z)),
    split,
        intros x_nonzero H2,
        refl,

        intros n IH x_nonzero x_mul_zero,       clear IH,
        exfalso,
        apply x_nonzero,                        clear x_nonzero,
        rw [PA6] at x_mul_zero,
        exact (PT22 (x * n) x x_mul_zero).2,
end
theorem mul_to_zero : ∀ x y : N, x ≠ Z → (x * y = Z → y = Z) := PT23


theorem mul_to_zero_iff : ∀ x y : N, x ≠ Z → (x * y = Z ↔ y = Z) :=
begin
    intros x y x_nonzero,
    split;
    intro H,
        exact PT23 x y x_nonzero H,             clear x_nonzero,
        rw H,
        exact PA5 x,
end


lemma nonzero_nonzero_mul_nonzero : ∀ x y : N, x ≠ Z → y ≠ Z → x * y ≠ Z :=
begin
    intros x y H1 H2 H3,
    apply H2,
    exact mul_to_zero _ _ H1 H3,
end

theorem PT24 : ∀ x y : N, x + y = S Z → (x = Z ∧ y = S Z) ∨ (x = S Z ∧ y = Z) :=
begin
    intros x y,
    apply S_induction (λ n, n + y = S Z → (n = Z ∧ y = S Z) ∨ (n = S Z ∧ y = Z)),
    split,
    {
        intros H,
        left,
        split,
            refl,

            rw [PT8] at H,
            exact H,
    },
    {
        intros n IH H,                                  clear IH,
        right,
        rw [PT9] at H,
        have ny_zero := (PA2 _ _ H),                    clear H,
        cases PT22 _ _ ny_zero with n_zero y_zero,      clear ny_zero,
        exact ⟨by rw n_zero, y_zero⟩,
    },
end
theorem add_to_one : ∀ x y : N, x + y = S Z → (x = Z ∧ y = S Z) ∨ (x = S Z ∧ y = Z) := PT24


theorem PT25 : ∀ x y : N, x * y = S Z → x = S Z ∧ y = S Z :=
begin
    intros x y,
    apply S_induction (λ n, n * y = S Z → n = S Z ∧ y = S Z),
    split,
    {
        intros H,
        exfalso,
        apply PA1 Z,
        rw [PT12 _] at H,
        exact H,
    },
    {
        intros n IH H,
        rw [PT13] at H,
        cases (PT24 _ _ H) with H1 H1;
        cases H1 with ny_zero y_1;                              clear H IH,
        {   
            refine ⟨ _, y_1 ⟩, 
            rw [S_iff_both_sides],
            rw [y_1] at ny_zero,                                  clear y_1,
            rw [PT20] at ny_zero,
            exact ny_zero,
        },
        {
            exfalso,
            rw [y_1] at ny_zero,                                clear y_1,
            rw [PA5] at ny_zero,
            have one_nonzero := PA1 Z,
            contradiction,
        },
    },
end
theorem mul_to_one : ∀ x y : N, x * y = S Z → x = S Z ∧ y = S Z := PT25


theorem PT26 : ∀ x : N, x ≠ Z → ∃ y : N, x = S y :=
begin
    intros x,
    apply S_induction (λ n, n ≠ Z → ∃ y : N, n = S y),
    split,
    {
        intros H,
        exfalso,
        contradiction,
    },
    {
        intros n IH H,
        use n,
    },
end
theorem exists_pred : ∀ x : N, x ≠ Z → ∃ y : N, x = S y := PT26


theorem PT27 : ∀ x y z : N, z ≠ Z → (x * z = y * z → x = y) :=
begin
    intros x y z,
    revert x,
    apply S_induction (λ n, ∀ x : N, z ≠ Z → (x * z = n * z → x = n)),
    split,
    {
        intros x z_nonzero xz_zero,
        rw [PT12] at xz_zero,
        rw [mul_commutative] at xz_zero,
        rw [mul_to_zero_iff _ _ z_nonzero] at xz_zero,
        exact xz_zero,
    },
    {
        intros n IH x z_nonzero xz_Snz,
        by_cases x = Z,
        {
            exfalso,
            rw h at xz_Snz,                                     clear h IH,
            rw [PT12] at xz_Snz,
            have Snz_zero : S n * z = Z := xz_Snz.symm,         clear xz_Snz,
            have Sn_nonzero := (PA1 n).symm,
            rw [mul_to_zero_iff _ _ Sn_nonzero] at Snz_zero,
            contradiction,
        },
        {
            rcases (PT26 _ h) with ⟨ w, rfl ⟩,                    clear h,
            rw [PT13, PT13] at xz_Snz,
            rw [right_cancel_add_iff] at xz_Snz,
            specialize IH w z_nonzero xz_Snz,
            rw IH,
        },
    },
end
theorem right_cancel_mul : ∀ x y z : N, z ≠ Z → (x * z = y * z → x = y) := PT27


lemma right_cancel_mul_iff : ∀ x y z : N, z ≠ Z → (x * z = y * z ↔ x = y) :=
begin
    intros x y z z_nonzero,
    split,
    {
        exact right_cancel_mul x y z z_nonzero,
    },
    {
        intros H,
        rw H,
    },
end


lemma left_cancel_mul_iff : ∀ x y z : N, z ≠ Z → (z * x = z * y ↔ x = y) :=
begin
    intros x y z z_nonzero,
    rw [mul_commutative, mul_commutative z y],
    exact right_cancel_mul_iff x y z z_nonzero,
end


theorem PT28 : ∀ x : N, x ≠ Z ∧ x ≠ S Z → ∃ y : N, x = S (S y) :=
begin
    intros x,
    apply S_induction (λ n, n ≠ Z ∧ n ≠ S Z → ∃ y : N, n = S (S y)),
    split,
    {
        intros H,
        exfalso,
        cases H with Z_nonzero one_nonzero,                                         clear one_nonzero,
        contradiction,
    },
    {
        intros n IH H,
        cases H with Sn_nonzero Sn_not_one,                                         clear Sn_nonzero,
        by_cases (n = S Z),
            use Z,
            rw [h],

            rw [not_to_not (S_iff_both_sides _ _)] at Sn_not_one,
            rcases IH ⟨ Sn_not_one, h ⟩ with ⟨ z, rfl ⟩,                            clear IH h Sn_not_one,
            use (S z),
    },  
end

lemma Z_only_right_identity_add : ∀ x y : N, x + y = x → y = Z :=
begin
    intros x y H,
    nth_rewrite 1 [← right_identity_add_Z x] at H,
    rw [left_cancel_add_iff] at H,
    exact H,
end


lemma right_identity_add_iff_Z : ∀ x y : N, x + y = x ↔ y = Z :=
begin
    intros x y,
    split,
    {
        exact Z_only_right_identity_add x y,
    },
    {
        intros H,
        rw H,
        exact PA3 x,
    },
end


lemma x_add_y_add_z_eq_x_imp_y_and_z_zero : ∀ x y z : N, x + y + z = x → y = Z ∧ z = Z :=
begin
    intros x y z H,
    rw [add_associative] at H,
    rw [right_identity_add_iff_Z] at H,
    rw [add_to_zero_iff] at H,
    exact H,
end


-- theorem PT29 : ∀ n m : ℕ, n ≠ m → n' ≠ m'
-- theorem PT30 : ∀ n m : ℕ, n' + m' = (n + m)' ∧ n' * m' = (n * m)'

reserve infix `<`:50
reserve infix `≤`:50

def le (x y : N) := ∃ z : N, x + z = y
def lt (x y : N) := ∃ z : N, x + z = y ∧ z ≠ Z

notation (name := le) x ` ≤ ` y := le x y
notation (name := lt) x ` < ` y := lt x y


lemma eq_imp_le : ∀ x y : N, x = y → x ≤ y :=
begin
    intros x y H,
    use Z,
    rw H,
    rw PA3,
end

lemma lt_imp_le : ∀ x y : N, x < y → x ≤ y :=
begin
    intros x y H,
    rcases H with ⟨ z, H1, H2 ⟩,
    use z,
    exact H1,
end


lemma le_imp_nlt : ∀ x y : N, x ≤ y → ¬ y < x :=
begin
    intros x y,
    apply S_induction (λ n, n ≤ y → ¬ y < n),
    split,
    {
        intros H H1,
        rcases H1 with ⟨ a, Ha, a_nonzero ⟩, clear H,
        cases add_to_zero y a Ha with y_zero a_zero, clear Ha,
        exact a_nonzero a_zero,
    },
    {
        intros n IH Sn_le_y y_lt_Sn, clear IH,
        rcases y_lt_Sn with ⟨ a, Ha, a_nonzero ⟩,
        rw ← Ha at Sn_le_y, clear Ha,
        cases Sn_le_y with b hb,
        cases x_add_y_add_z_eq_x_imp_y_and_z_zero _ _ _ hb with a_zero b_zero, clear hb,
        exact a_nonzero a_zero
    },
end


lemma le_Z_iff_eq_Z : ∀ x : N, x ≤ Z ↔ x = Z :=
begin
    intros x,
    split;
    intro H,
    {
        rcases H with ⟨ z, H1 ⟩,
        rw [add_to_zero_iff] at H1,
        exact H1.1,
    },
    {
        use Z,
        rw H,
        exact PA3 Z,
    },
end

-- proved here for convenience
theorem PT56 : ∀ x : N, ¬ x < Z :=
begin
    intros x x_lt_Z,
    rcases x_lt_Z with ⟨ a, ha, a_nonzero ⟩,
    cases add_to_zero _ _ ha with y_zero a_zero, clear ha,
    exact a_nonzero a_zero,
end
theorem nlt_Z : ∀ x : N, x < Z → false := PT56


lemma left_cancel_add_le_iff : ∀ x y z : N, x + y ≤ x + z ↔ y ≤ z :=
begin
    intros x y z,
    split,
    {
        intros H,
        rcases H with ⟨ a, Ha ⟩,
        use a,
        rw [add_associative] at Ha,
        rw left_cancel_add_iff x (y+a) z at Ha,
        exact Ha,
    },
    {
        intros H,
        rcases H with ⟨ a, Ha ⟩,
        use a,
        rw [add_associative],
        rw [Ha],
    },
end


lemma right_cancel_add_le_iff : ∀ x y z : N, x + y ≤ z + y ↔ x ≤ z :=
begin
    intros x y z,
    rw [add_commutative x y, add_commutative z y],
    exact left_cancel_add_le_iff _ _ _,
end


lemma left_cancel_add_lt_iff : ∀ x y z : N, x + y < x + z ↔ y < z :=
begin
    intros x y z,
    split,
    {
        intros H,
        rcases H with ⟨ a, Ha, a_nonzero ⟩,
        use a,
        split,
            rw [add_associative] at Ha,
            rw [left_cancel_add_iff x (y+a) z] at Ha,
            exact Ha,

            exact a_nonzero,
    },
    {
        intros H,
        rcases H with ⟨ a, Ha, a_nonzero ⟩,
        use a,
        split,
            rw [add_associative],
            rw [Ha],

            exact a_nonzero,
    },
end


lemma right_cancel_add_lt_iff : ∀ x y z : N, x + y < z + y ↔ x < z :=
begin
    intros x y z,
    rw [add_commutative x y, add_commutative z y],
    exact left_cancel_add_lt_iff _ _ _,
end


theorem PT31 : ∀ x : N, ¬  x < x :=
begin
    intros x H,
    rcases H with ⟨ a, ha, a_nonzero ⟩,
    rw [right_identity_add_iff_Z _ _] at ha,
    exact a_nonzero ha,
end
theorem lt_irreflexive : ∀ x : N, x < x → false := PT31


theorem PT32 : ∀ x y z : N, x < y ∧ y < z → x < z :=
begin
    intros x y z H,
    rcases H with ⟨ a, b, hb, b_nonzero ⟩,
    rcases a with ⟨ a, ha, a_nonzero ⟩,

    use (a + b),
    split,
        rw [← add_associative x a b, ha, hb],
        
        intro ab_zero,
        cases add_to_zero _ _ ab_zero with a_zero b_zero, clear ab_zero,
        exact a_nonzero a_zero,
end
theorem lt_transitive : ∀ x y z : N, x < y ∧ y < z → x < z := PT32


theorem PT33 : ∀ x y : N, x < y → ¬ y < x :=
begin
    intros x y H1 H2,
    rcases H1 with ⟨ a, ha, a_nonzero ⟩,
    rcases H2 with ⟨ b, hb, b_nonzero ⟩,

    rw [← ha] at hb,
    cases x_add_y_add_z_eq_x_imp_y_and_z_zero _ _ _ hb with a_zero b_zero,
    exact a_nonzero a_zero,
end
theorem lt_nonsym : ∀ x y : N, x < y → y < x → false := PT33


theorem PT34 : ∀ x y z : N, x < y → x + z < y + z :=
begin
    intros x y z,
    exact (right_cancel_add_lt_iff x z y).mpr,
end
theorem N_right_add_lt : ∀ x y z : N, x < y → x + z < y + z := PT34


theorem PT35 : ∀ x : N, x ≤ x :=
begin
    intro x,
    use Z,
    exact PA3 _,
end
theorem le_reflexive : ∀ x : N, x ≤ x := PT35


theorem PT36 : ∀ x y z : N, x ≤ y ∧ y ≤ z → x ≤ z :=
begin
    intros x y z H,
    rcases H with ⟨ ⟨ a, rfl ⟩, ⟨ b, rfl ⟩ ⟩,
    use (a + b),
    rw [← add_associative x a b],
end
theorem le_transitive : ∀ x y z : N, x ≤ y ∧ y ≤ z → x ≤ z := PT36


theorem PT37 : ∀ x y z : N, x ≤ y → x + z ≤ y + z :=
begin
    intros x y z,
    exact (right_cancel_add_le_iff x z y).mpr,
end
theorem N_right_add_le : ∀ x y z : N, x ≤ y → x + z ≤ y + z := PT37


theorem PT38 : ∀ x y z : N, x ≤ y ∧ y < z → x < z :=
begin
    intros x y z H,
    rcases H with ⟨ ⟨ a, rfl ⟩, ⟨ b, rfl, b_nonzero ⟩ ⟩,

    use (a+b),
    split,
        rw [← add_associative x a b],

        intro ab_nonzero,
        cases (add_to_zero _ _ ab_nonzero) with a_zero b_zero,
        exact b_nonzero b_zero,
end

theorem PT39 : ∀ x : N, Z ≤ x :=
begin
    intro x,
    use x,
    exact PT8 _,
end
theorem zero_le_ : ∀ x : N, Z ≤ x := PT39


theorem PT40 : ∀ x : N, Z < S x :=
begin
    intro x,
    use S x,
    split,
        rw [PT8],
        exact (PA1 x).symm,
end
theorem zero_lt_S : ∀ x : N, Z < S x := PT40


theorem PT41 : ∀ x y : N, x < y ↔ S x ≤ y :=
begin
    intros x y,
    split;
    intro H,
    {
        rcases H with ⟨ a, rfl, a_nonzero ⟩,
        rcases PT26 a a_nonzero with ⟨ b, rfl ⟩,    clear a_nonzero,
        use b,
        exact swap_s_add _ _,
    },
    {
        rcases H with ⟨ a, rfl ⟩,
        use S a,
        split,
            rw swap_s_add x a,

            exact (PA1 a).symm,
    }
        
end
theorem lt_iff_S_le : ∀ x y : N, x < y ↔ S x ≤ y := PT41


theorem PT42 : ∀ x y : N, x ≤ y ↔ x < S y :=
begin
    intros x y,
    split;
    intro H,
    {
        rcases H with ⟨ a, rfl ⟩,
        
        use S a,
        split,
            rw [PA4 x a],
            exact (PA1 a).symm,
    },
    {
        rcases H with ⟨ a, ha, a_nonzero ⟩,
        rcases PT26 a a_nonzero with ⟨ b, rfl ⟩,    clear a_nonzero,
        use b,
        rw [PA4] at ha,
        rw [S_iff_both_sides] at ha,
        exact ha,
    },
end
theorem le_iff_S_lt : ∀ x y : N, x ≤ y ↔ x < S y := PT42


theorem PT43 : ∀ x : N, x < S x :=
begin
    intro x,
    use S Z,
    split,
        exact PT19 x,
        exact (PA1 Z).symm,
end
theorem lt_S_self : ∀ x : N, x < S x := PT43


-- theorem PT44 : ∀ n : ℕ, n' < (n + 1)'

-- A copy of PT51 because I need it for PT45 and doesn't depend on anything but PT8.
theorem PT51 : ∀ x : N, x ≠ Z → Z < x :=
begin
    intros x H,
    use x,
    split,
        exact PT8 _,
        exact H,
end
theorem nonzero_imp_lt : ∀ x : N, x ≠ Z → Z < x := PT51


lemma lt_Sneq_imp_Slt : ∀ x y : N, x < y → S x ≠ y → S x < y :=
begin
    intros x y x_lt_y Sx_neq_y,
    rcases x_lt_y with ⟨ a, rfl, a_nonzero ⟩,
    rcases PT26 a a_nonzero with ⟨ a', rfl ⟩,
    rw [← PT19] at Sx_neq_y,
    rw [not_to_not (left_cancel_add_iff _ _ _)] at Sx_neq_y,
    rw [not_to_not (S_iff_both_sides _ _)] at Sx_neq_y,
    use a',
    split,
        rw swap_s_add,
        exact Sx_neq_y.symm,
end


theorem PT45 : ∀ x y : N, x ≠ y → x < y ∨ y < x :=
begin
    intros x y, revert x,
    apply PA7 (λ n, ∀ x : N, x ≠ n → x < n ∨ n < x),
    split,
    {
        intros x x_nonzero,
        right,
        exact PT51 x x_nonzero,
    },
    {
        intros n IH x x_neq_Sn,
        by_cases x_eq_n : x = n,
        {
            left,                                               clear IH x_neq_Sn y,
            rw x_eq_n,                                          clear x_eq_n,
            exact PT43 n,
        },
        {   
            specialize IH x x_eq_n,                     clear x_eq_n,
            cases IH,
            {
                rcases IH with ⟨ a, rfl, a_nonzero ⟩,
                left,
                use S a,
                refine ⟨ _, (PA1 a).symm ⟩,
                rw [PA4],
            },
            {
                right,
                exact lt_Sneq_imp_Slt n x IH x_neq_Sn.symm,
            },
        },
    },
end
theorem N_lt_or_gt : ∀ x y : N, x ≠ y → x < y ∨ y < x := PT45


theorem PT46 : ∀ x y : N, x < y ∨ x = y ∨ y < x :=
begin
    intros x y,
    by_cases H : x = y,
        right,
        left,
        exact H,

        cases (N_lt_or_gt x y H),
            left,
            exact h,

            right,
            right,
            exact h,
end
theorem lt_or_eq_or_gt : ∀ x y : N, x < y ∨ x = y ∨ y < x := PT46


theorem PT47 : ∀ x y : N, x ≤ y ∨ y ≤ x :=
begin
    intros x y,
    by_cases H : x = y,
    {
        left,
        rw H,
        exact le_reflexive _,
    },
    {
        cases N_lt_or_gt x y H,
        {
            left,
            exact lt_imp_le _ _ h,
        },
        {
            right,
            exact lt_imp_le _ _ h,
        },
    },
end
theorem le_or_le : ∀ x y : N, x ≤ y ∨ y ≤ x := PT47


theorem PT48 : ∀ x y : N, x ≤ x + y :=
begin
    intros x y,
    use y,
end


theorem le_add_right_N : ∀ x y z : N, x ≤ y → x ≤ y + z := 
begin
    intros x y z H,
    rcases H with ⟨ a, rfl ⟩,
    use a + z,
    rw [add_associative],
end


lemma le_add_left_N : ∀ x y z : N, x ≤ y → x ≤ z + y :=
begin
    intros x y z H,
    rcases H with ⟨ a, rfl ⟩,
    use z + a,
    rw [← add_associative, ← add_associative, add_commutative x z],
end


theorem PT49 : ∀ x y : N, y ≠ Z → x < x + y :=
begin
    intros x y H,
    use y,
    split,
        refl,
        exact H,
end
theorem lt_add_right_N : ∀ x y : N, y ≠ Z → x < x + y := PT49


lemma lt_add_left_N : ∀ x y : N, y ≠ Z → x < y + x :=
begin
    intros x y H,
    use y,
    split,
        rw [add_commutative],
        exact H,
end


theorem PT50 : ∀ x y : N, y ≠ Z → x ≤ x * y :=
begin
    intros x y H,
    rcases PT26 y H with ⟨ a, rfl ⟩,
    use x * a,
    rw [PA6],
    exact PT10 x (x*a),
end
theorem N_mul_right_le : ∀ x y : N, y ≠ Z → x ≤ x * y := PT50


-- PT51 is defined above just before PT45.
-- theorem PT51 : ∀ x : N, x ≠ Z → Z < x :=
-- begin
--     intros x H,
--     use x,
--     split,
--         exact PT8 _,
--         exact H,
-- end
-- theorem nonzero_imp_lt : ∀ x : N, x ≠ Z → Z < x := PT51


lemma nonzero_iff_lt : ∀ x : N, x ≠ Z ↔ Z < x :=
begin
    intro x,
    split,
        exact PT51 x,

        intros H x_zero,
        rw x_zero at H,                     clear x_zero,
        exact lt_irreflexive _ H,
end


theorem PT52 : ∀ x y : N, Z < x ∧ Z < y → Z < x * y :=
begin
    intros x y H,
    rw [← nonzero_iff_lt, ← nonzero_iff_lt] at H,
    rw [← nonzero_iff_lt],
    rcases H with ⟨ a_nonzero, y_nonzero ⟩,
    exact nonzero_nonzero_mul_nonzero _ _ a_nonzero y_nonzero,
end
theorem N_pos_mul_pos : ∀ x y : N, Z < x ∧ Z < y → Z < x * y := PT52


theorem PT53 : ∀ x y : N, x ≠ Z ∧ S Z < y → x < x * y :=
begin
    intros x y H,
    rcases H with ⟨ x_nonzero, ⟨ b, rfl, b_nonzero ⟩ ⟩,
    rw [left_distribute_mul],
    rw [mul_one_],
    apply lt_add_right_N,
    exact nonzero_nonzero_mul_nonzero _ _ x_nonzero b_nonzero,
end
theorem N_nonzero_mul_pos : ∀ x y : N, x ≠ Z ∧ S Z < y → x < x * y := PT53


theorem PT54 : ∀ x y z : N, z ≠ Z → (x < y ↔ x * z < y * z) :=
begin
    intros x y z Sn_nonzero,
    split,
    {
        intro H,
        rcases H with ⟨ a, rfl, a_nonzero ⟩,
        rw [right_distribute_mul],
        apply lt_add_right_N,
        exact nonzero_nonzero_mul_nonzero _ _ a_nonzero Sn_nonzero,
    },
    {
        intro H,                                                                    clear Sn_nonzero,
        cases PT46 x y,
            {
                exact h,
            },
            exfalso,
            rcases h with ⟨ rfl, rfl ⟩,
            {
                exact PT31 (x * z) H,
            },
            {
                rcases H with ⟨ b, hb, b_nonzero ⟩,
                rcases h with ⟨ a, rfl, a_nonzero ⟩,                                clear a_nonzero,
                rw [ right_distribute_mul, add_associative] at hb,
                have azb_zero := Z_only_right_identity_add _ _ hb,                  clear hb,
                cases add_to_zero _ _ azb_zero with az_zero b_zero,                 clear azb_zero,
                exact b_nonzero b_zero,
            },
    },
end
theorem N_right_cancel_mul_lt : ∀ x y z : N, z ≠ Z → (x < y ↔ x * z < y * z) := PT54


theorem PT55 : ∀ x y z : N, z ≠ Z → (x ≤ y ↔ x * z ≤ y * z) :=
begin
    intros x y z Sn_nonzero,
    split,
    {
        intro x_le_y,
        rcases x_le_y with ⟨ a, rfl ⟩,
        rw [right_distribute_mul],
        apply PT48,
    },
    {
        intro H,
        cases PT47 x y,
            exact h,

            rcases h with ⟨ a, rfl ⟩,
            rw [(PA3 (y*z)).symm]       at H,
            rw [right_distribute_mul]   at H,
            rw [left_cancel_add_le_iff] at H,
            rw [le_Z_iff_eq_Z]          at H,
            rw [mul_commutative]        at H,
            have a_zero := mul_to_zero _ _ Sn_nonzero H,        clear Sn_nonzero H,
            rw a_zero,                                          clear a_zero,
            rw [PA3],
            exact (PT35 y),
    },
end
theorem N_right_cancel_mul_le : ∀ x y z : N, z ≠ Z → (x ≤ y ↔ x * z ≤ y * z) := PT55


-- Proved at the start of ≤ & < section.
-- theorem PT56 : ∀ x : N, x < Z → false :=
-- begin
--     intros x x_lt_Z,
--     rcases x_lt_Z with ⟨ a, ha, a_nonzero ⟩,
--     cases add_to_zero _ _ ha with y_zero a_zero, clear ha,
--     exact a_nonzero a_zero,
-- end
-- theorem nlt_Z : ∀ x : N, x < Z → false := PT56


theorem PT57 : ∀ x y : N, x ≤ y ∧ y ≤ x → x = y :=
begin
    intros x y H,
    rcases H with ⟨ ⟨ a, ha ⟩, ⟨ b, hb ⟩ ⟩,

    rw [← ha] at hb,
    rcases x_add_y_add_z_eq_x_imp_y_and_z_zero _ _ _ hb with ⟨ rfl, rfl ⟩ , clear hb,
    rw [PA3] at ha,
    exact ha,
end
theorem le_antisymmetric : ∀ x y : N, x ≤ y ∧ y ≤ x → x = y := PT57


-- theorem PT58 : ∀ n : ℕ, x = Z ∨ x = S Z ∨ x = S (S Z) ∨ ... ∨ x = n' ↔ x ≤ n'


---------------------------------------------------------------------------------------

reserve infix ` | ` : 50
def divisible (x y : N) := ∃ z : N, y = x * z
notation x ` | ` y := divisible x y


theorem PT59 : ∀ x : N, x | x :=
begin
    intro x,
    use S Z,
    rw [mul_one_],
end
theorem N_divides_self : ∀ x : N, x | x := PT59


theorem PT60 : ∀ x : N, S Z | x :=
begin
    intro x,
    use x,
    rw [mul_commutative],
    rw [mul_one_],
end
theorem N_one_divides : ∀ x : N, S Z | x := PT60


theorem PT61 : ∀ x : N, x | Z :=
begin
    intro x,
    use Z,
    rw [PA5],
end
theorem N_divides_zero : ∀ x : N, x | Z := PT61


theorem PT62 : ∀ x y z : N, x | y ∧ y | z → x | z :=
begin
    intros x y z H,
    rcases H with ⟨ ⟨ a, rfl ⟩, ⟨ b, rfl ⟩ ⟩,
    use a * b,
    rw [mul_associative],
end
theorem N_divides_trans : ∀ x y z : N, x | y ∧ y | z → x | z := PT62


theorem PT63 : ∀ x y : N, y ≠ Z ∧ x | y → x ≤ y :=
begin
    intros x y H,
    rcases H with ⟨ xa_nonzero, ⟨ a, rfl ⟩ ⟩,

    have a_nonzero : a ≠ Z,
    {
        intro a_zero,
        rw a_zero at xa_nonzero,    clear a_zero,
        rw [PA5] at xa_nonzero,
        contradiction,
    },

    exact PT50 x a a_nonzero,
end
theorem N_divides_imp_le : ∀ x y : N, y ≠ Z ∧ x | y → x ≤ y := PT63


theorem PT64 : ∀ x y : N, x | y ∧ y | x → x = y :=
begin
    intros x y H,
    rcases H with ⟨ ⟨ a, ha ⟩, ⟨ b, rfl ⟩ ⟩,
    rw [← mul_associative] at ha,
    by_cases y_zero : y = Z,
    {
        rw [y_zero],         clear y_zero ha,
        rw [PT12],
    },
    {
        nth_rewrite 0 [← mul_one_ y] at ha,
        rw [left_cancel_mul_iff _ _ _ y_zero] at ha,
        cases mul_to_one _ _ ha.symm with b_one a_one,                              clear ha a_one,
        rw [b_one],                                                                 clear b_one,
        exact PA3 y,
    },
end
theorem N_divides_antisymm : ∀ x y : N, x | y ∧ y | x → x = y := PT64


theorem PT65 : ∀ x y z : N, x | y → x | y*z :=
begin
    intros x y z H,
    rcases H with ⟨ a, rfl ⟩,
    use a * z,
    rw [mul_associative],
end
theorem N_divides_mul : ∀ x y z : N, x | y → x | y*z := PT65


theorem PT66 : ∀ x y z : N, x | y ∧ x | z → x | y + z :=
begin
    intros x y z H,
    rcases H with ⟨ ⟨ a, rfl ⟩, ⟨ b, rfl ⟩ ⟩,
    use a + b,
    rw [← left_distribute_mul],
end
theorem N_divides_add : ∀ x y z : N, x | y ∧ x | z → x | y + z := PT66


theorem PT67_induction_part : ∀ x y : N, y ≠ Z → (∃ u v : N, (x = y * u + v ∧ v < y)) :=
begin
    intros x y y_nonzero,
    revert x,
    apply S_induction (λ n : N, (∃ u v : N, (n = y * u + v ∧ v < y ))),
    split,
    {
        use Z,
        use Z,
        split,
            rw [PA5],
            rw [PA3],
            
            exact PT51 y y_nonzero,
    },
    {
        intros x IH,
        rcases IH with ⟨ u, v, H, v_lt_y  ⟩,
        have three_options := PT46 (S v) y,
        cases three_options,
        {
            use u,                                              clear v_lt_y y_nonzero,
            use S v,
            refine ⟨ _, three_options ⟩,                        clear three_options,
            rw [H],                                             clear H x,
            rw [← PA4],
        },
        cases three_options,
        {
            use S u,                                            clear v_lt_y,
            use Z,
            refine ⟨ _, (PT51 y y_nonzero) ⟩,
            rw [H],                                             clear H y_nonzero x,
            rw [PA6],
            rw [PA3],
            rw [← PA4],
            rw [three_options],
        },
        {
            exfalso,                                            clear y_nonzero H x u,
            rw [← PT42] at three_options,
            apply (le_imp_nlt y v three_options),               clear three_options,
            exact v_lt_y,
        },
    },
end


lemma PT67_uniqueness_part : ∀ x y : N, y ≠ Z → (∀ u v u1 v1 : N, (x = y * u + v ∧ v < y) → (x = y * u1 + v1 ∧ v1 < y) → (u = u1 ∧ v = v1)) :=
begin
    intros x y y_nonzero u v u1 v1 uv_qr' u1v1_qr',
    rcases uv_qr' with ⟨ uv_qr, v_lt_y ⟩,
    rcases u1v1_qr' with ⟨ u1v1_qr, v1_lt_y ⟩,
    rw u1v1_qr at uv_qr,                                                            clear u1v1_qr x,

    by_cases h' : u = u1,
    {
        refine ⟨ h', _ ⟩,
        rw [← h'] at uv_qr,
        rw [left_cancel_add_iff] at uv_qr,
        rw uv_qr,        
    },
    exfalso,                                                                        clear y_nonzero,
    cases (PT45 _ _ h') with h h;                                                   clear h';
    rcases h with ⟨ w, rfl, w_nonzero ⟩;
    rw [left_distribute_mul] at uv_qr;
    rw [add_associative] at uv_qr;
    rw [left_cancel_add_iff] at uv_qr;
    have y_le_yw : y ≤ y * w := PT50 y w w_nonzero;                                 clear w_nonzero,
    {
        have y_le_ywv1 : y ≤ y * w + v1 := le_add_right_N y (y * w) v1 y_le_yw,     clear y_le_yw v1_lt_y u,
        rw [uv_qr] at y_le_ywv1,                                                    clear uv_qr w v1,
        apply (le_imp_nlt y v y_le_ywv1),                                           clear y_le_ywv1,
        exact v_lt_y,
    },
    {
        have y_le_ywv : y ≤ y * w + v := le_add_right_N y (y * w) v y_le_yw,        clear y_le_yw v_lt_y u1,
        rw [← uv_qr] at y_le_ywv,                                                   clear uv_qr w v,
        apply (le_imp_nlt y v1 y_le_ywv),                                           clear y_le_ywv,
        exact v1_lt_y,
    },
end


theorem PT67 : ∀ x y : N, y ≠ Z → (∃ u v : N, (x = y * u + v ∧ v < y ∧ ∀ u1 v1 : N, (x = y * u1 + v1 ∧ v1 < y) → (u = u1 ∧ v = v1))) :=
begin
    intros x y y_nonzero,
    have H_induction := PT67_induction_part x y y_nonzero,
    rcases H_induction with ⟨ u, v, H, v_lt_y ⟩,
    use u,
    use v,
    refine ⟨ H, v_lt_y, _ ⟩,
    {
        intros u1 v1 H1,
        exact PT67_uniqueness_part x y y_nonzero u v u1 v1 (and.intro H v_lt_y) H1,
    },
end