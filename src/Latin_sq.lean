import algebra.group.basic algebra.group.defs
import logic.function.basic
import Latin_line
open function


-- define the latin square object
structure latin2 (len : ℕ) :=
(nonempty : len > 0)
(map : (fin len) → (fin len) → (fin len))
(is_inj : ∀ i : fin len, injective (map i) ∧ injective (λ j, map j i))


lemma latin2.ext {len : ℕ} {l1 l2 : latin2 len} (h : l1.map = l2.map) : l1 = l2 :=
begin
  cases l1, cases l2,
  congr,
  exact h,
end

lemma latin2.ext_iff {len : ℕ} {l1 l2 : latin2 len} : l1 = l2 ↔ l1.map = l2.map :=
begin
  split,
  { intro h, rw h },
  { intro h, apply latin2.ext, exact h },
end

lemma latin2_maps_to_self {len : ℕ} (L : latin2 len) : ∀ i : fin len, (finset.image (L.map i) finset.univ) = finset.univ :=
begin
  intro i,
  apply inj_maps_to_self,
  exact (L.is_inj i).1,
end

lemma surj_of_latin2 {len : ℕ} (f : latin2 len) : ∀ i : fin len, surjective (f.map i) :=
begin
  intro i,
  apply surj_of_inj,
  exact (f.is_inj i).1,
end

theorem bij_of_latin2 {len : ℕ} (f : latin2 len) : ∀ i : fin len, bijective (f.map i) :=
begin
  intro i,
  apply bij_of_inj,
  exact (f.is_inj i).1,
end


theorem transpose2 {len : ℕ} : ∀ f : latin2 len, ∃ g :latin2 len, ∀ i j : fin len, f.map i j = g.map j i :=
begin
  intros f,
  use { nonempty := f.nonempty, map := λ i j, f.map j i, is_inj := λ i, ⟨ (f.is_inj i).2, (f.is_inj i).1 ⟩ },
  intros i j,
  simp only [forall_2_true_iff],
end


theorem permi2 {len : ℕ} {g : (fin len) → (fin len)} (f : latin2 len) (g_inj : injective g) : 
  ∃ fg : latin2 len, fg.map = λ i j, f.map (g i) j :=
begin
  have : ∀ (i : fin len), injective (λ (j : fin len), f.map (g i) j) ∧ injective (λ (j : fin len), f.map (g j) i),
    intro i,
    refine ⟨ ((f.is_inj (g i)).1), _ ⟩,
    
    intros a b H,
    simp at H,
    cases transpose2 f with f_swap Hf_swap,
    rw (Hf_swap (g a) i) at H,
    rw (Hf_swap (g b) i) at H,
    exact g_inj ((f_swap.is_inj i).1 H),

  use { nonempty := f.nonempty, map := λ i j, f.map (g i) j, is_inj := this },
end


theorem perme2 {len : ℕ} {g : (fin len) → (fin len)} (f : latin2 len) (g_inj : injective g) : 
  ∃ gf : latin2 len, gf.map = λ i j, g (f.map i j) :=
begin
  have : ∀ (i : fin len), injective (λ (j : fin len), g (f.map i j)) ∧ injective (λ (j : fin len), g (f.map j i)),
    intro i,
    exact ⟨ injective.comp g_inj (f.is_inj i).1, injective.comp g_inj (f.is_inj i).2 ⟩,

  use { nonempty := f.nonempty, map := λ i j, g (f.map i j), is_inj := this },
end


lemma inv2 {len : ℕ} (f : latin2 len) :
    ∃ f' : latin2 len, ∀ i : fin len, right_inverse (f.map i) (f'.map i) ∧ left_inverse (f.map i) (f'.map i) :=
begin
  
  have partial_inverse1 : ∀ (i : fin len), ∃ g1 : fin len → fin len, right_inverse (f.map i) g1 ∧ left_inverse (f.map i) g1:=
    λ i, function.bijective_iff_has_inverse.1 (bij_of_latin2 f i),

  have h1 : ∀ (i : fin len), injective (partial_inverse1 i).some :=
    λ i, function.left_inverse.injective (classical.some_spec (partial_inverse1 i)).2,

  have h2' : ∀ (i : fin len), injective (λ (j : fin len), (partial_inverse1 j).some i),
    unfold injective,
    intros i x y H,
    apply ((f.is_inj ((partial_inverse1 x).some i)).2),
    unfold injective,
    nth_rewrite 1 H, clear H,

    have h : ∀ z : fin len, (f.map z ((partial_inverse1 z).some i)) = i,
      intro z,
      rw ← function.comp_apply (f.map z) ( (partial_inverse1 z).some ) i,
      rw function.right_inverse.id (classical.some_spec (partial_inverse1 z)).2,
      rw id.def,
    
    rw h x,
    rw h y,

  use { nonempty := f.nonempty, map := λ i, (partial_inverse1 i).some, is_inj := λ i, ⟨ h1 i, h2' i ⟩ },

  intro i,
  exact classical.some_spec (partial_inverse1 i),
end


def axis_rotate2 {len : ℕ} (f : latin2 len) : ∃ f' : latin2 len, ∀ i j : fin len, f'.map (f.map i j) i = j :=
begin
  cases inv2 f with f' hf',
  cases transpose2 f' with f'' hf'',
  use f'',
  intros i j,
  rw ← hf'' i,
  exact (hf' i).1 j,
end


-- because cycles (1 2 3) and (1 2) generates S3, rotate2 and transpose2 generates all possible permutations to and from indexes and entries of a latin square