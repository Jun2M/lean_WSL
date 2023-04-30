import algebra.group.basic algebra.group.defs
import logic.function.basic
import Latin_line
open function


-- define the latin square object
structure latin2 (len : ℕ) :=
(nonempty : len > 0)
(map : (fin len) → (fin len) → (fin len))
(is_inj : ∀ i : fin len, injective (map i) ∧ injective ((swap map) i))


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


structure latin2_hom (len : ℕ) : Type :=
  (to_fun : latin2 len → latin2 len)


lemma latin2_hom.ext {len : ℕ} (f g : latin2_hom len) : f.to_fun = g.to_fun → f = g :=
begin
  intros H,
  cases f,
  cases g,
  congr,
  exact H,
end

lemma latin2_hom.ext_iff {len : ℕ} (f g : latin2_hom len) : f = g ↔ f.to_fun = g.to_fun :=
begin
  split,
  { intro H, rw H },
  { intro H, apply latin2_hom.ext, exact H },
end


def permi_hom2 {len : ℕ} {g : (fin len) → (fin len)} (g_inj : injective g) : latin2_hom len :=
{
  to_fun := 
  begin
    intro f,
    refine ⟨ f.nonempty, _, _ ⟩,

      intro i,
      exact f.map (g i),
      
      intros i,
      refine ⟨ (f.is_inj (g i)).1, _ ⟩,
      have latinline_g : latin1 len := { nonempty := f.nonempty, map := g, is_inj := g_inj },
      have latinline_f : latin1 len := 
      { nonempty := f.nonempty, 
        map := (@swap (fin len) (fin len) f.map) i, is_inj := f.is_inj },
      have := (f.is_inj (g i)).2,
      sorry,
  end,
}


def perme_hom2 {len : ℕ} {g : (fin len) → (fin len)} (g_inj : injective g) : latin2_hom len :=
{
  to_fun := 
  begin
    intro f,
    refine ⟨ f.nonempty, _, _ ⟩,

      intros i j,
      exact g (f.map i j),
      
      intros i,
      split,
      {
        rw injective.of_comp_iff,
        exact (f.is_inj i).1,
        exact g_inj,
      },
      {
        intros a b H,
        apply (f.is_inj i).2,
        apply g_inj,
        exact H,
      },
  end,
}


def id_hom2 {len : ℕ} : latin2_hom len := permi_hom2 (injective_id)


noncomputable def transpose_hom2 {len : ℕ} : latin2_hom len :=
{
  to_fun := 
  begin
    intros f,
    refine ⟨ f.nonempty, _, _ ⟩,

      intro i,
      choose g hg using function.bijective_iff_has_inverse.1 (bij_of_latin2 f i),
      use g,

      intros i,
      split,
      {
          
      },
      {
          
      },
      have g_inj : injective g := left_inverse.injective (function.right_inverse.left_inverse hg.2),
      exact (permi_hom2 g_inj).to_fun f,
  end,
}

-- def perm_hom1 {len : ℕ} {g : (fin len) → (fin len)} (g_inj : injective g) : latin1_hom len :=
-- {
--   to_fun := 
--   begin
--     intro f,
--     refine ⟨ f.nonempty, (g ∘ f.map), _ ⟩,
    
--     rw injective.of_comp_iff,
--     exact f.is_inj,
--     exact g_inj,
--   end,
-- }

-- def id_hom1 {len : ℕ} : latin1_hom len := perm_hom1 (injective_id)


-- noncomputable def transpose_hom1 {len : ℕ} : latin1_hom len :=
-- {
--   to_fun := 
--   begin
--     intro f,
--     choose g hg using function.bijective_iff_has_inverse.1 (bij_of_latin1 f),
--     refine ⟨ f.nonempty, g, _ ⟩,

--     intros a b H,
--     rcases hg with ⟨ left_inverse, right_inverse ⟩,
--     have left_inverse_r := function.right_inverse.left_inverse right_inverse,
--     exact left_inverse_r.injective H,
--   end,
-- }


-- noncomputable def normalise_hom1 {len : ℕ} : latin1_hom len :=
-- begin
--   refine ⟨ λ f, _ ⟩,
--   choose g hg using function.bijective_iff_has_inverse.1 (bij_of_latin1 f),
--   have g_inj : injective g := left_inverse.injective (function.right_inverse.left_inverse hg.2),
--   exact (perm_hom1 g_inj).to_fun f,
-- end