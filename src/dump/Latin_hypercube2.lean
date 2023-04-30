import algebra.group.basic algebra.group.defs init.function
import data.set.image data.set.prod data.finset.card data.finset.basic data.set.function
import combinatorics.simple_graph.basic combinatorics.pigeonhole 
import Inverse_function logic.function.basic
open function set


-- Define latin square object
structure latin_square (len : ℕ):=
(nonempty : len > 0)
(map : (fin len) → (fin len) → (fin len))
(is_latin : ∀ i j k : fin len, j ≠ k →
                               map i j ≠ map i k ∧
                               map i j ≠ map k j)


theorem image_not_ssub_domain (n : ℕ) (L : latin_square n) (i : fin n) :
  ¬ (finset.image (L.map i) finset.univ) ⊂ finset.univ :=
begin
  intro image_ssub_domain,
  have sth : ∀ (a : fin n), a ∈ finset.univ → (L.map i a) ∈ finset.image (L.map i) finset.univ,
  {
    intros a ha,
    rw finset.mem_image,
    use a,
    split,
    exact ha,
    refl,
  },

  have card_image_ssub_domain := finset.card_lt_card image_ssub_domain,
  have := (finset.exists_ne_map_eq_of_card_lt_of_maps_to card_image_ssub_domain) sth,
  rcases this with ⟨ a, a_ext, b, b_ext, a_neq_b, H ⟩,
  have := L.is_latin i a b,
  cases L.is_latin i a b with H1 H2,
  exact H1 H,
end


theorem image_eq_domain (n : ℕ) (L : latin_square n) (i : fin n) :
  (finset.image (L.map i) finset.univ) = finset.univ :=
begin
  have image_sub_domain : (finset.image (L.map i) finset.univ) ⊆ finset.univ := (finset.image (L.map i) finset.univ).subset_univ,
  cases has_subset.subset.eq_or_ssubset image_sub_domain with image_eq_domain image_ssub_domain;
  clear image_sub_domain,
  exact image_eq_domain,

  exfalso,
  revert image_ssub_domain,
  exact image_not_ssub_domain n L i,
end


theorem col_of_latin_square_is_injective (n : ℕ) (L : latin_square n) (i : fin n) :
  function.injective (L.map i) :=
begin
  intros a b,
  by_contra,
  push_neg at h,
  cases h with same_output diff_input,
  have H := image_eq_domain n L i,
  
  have := finset.inj_on_of_card_image_eq,
  rotate,
  exact (fin n),
  exact (fin n),
  exact finset.univ,
  exact (L.map i),
  exact fin.decidable_eq n,
  have row_inj := this (by rw H),           clear H this,
  have consequence_of_inj := set.inj_on.eq_iff row_inj (finset.mem_univ a) (finset.mem_univ b),
  rw consequence_of_inj at same_output,
  exact diff_input same_output,
end


theorem col_of_latin_square_is_surjective (n : ℕ) (L : latin_square n) (i : fin n) : 
  function.surjective (L.map i) :=
begin
  intro j,
  by_contra,
  push_neg at h,
  apply image_not_ssub_domain n L i,
  
  rw finset.ssubset_def,
  split,
  {
    intro x,
    simp,
  },
  {
    intro H,
    specialize H (finset.mem_univ j),
    rw finset.mem_image at H,
    rcases H with ⟨ k, k_ext, hk ⟩,
    specialize h k,
    exact h hk,
  },
end


theorem col_of_latin_square_is_bijection (n : ℕ) (L : latin_square n) (i : fin n) :
  function.bijective (L.map i) :=
begin
  split,
  exact col_of_latin_square_is_injective n L i,
  exact col_of_latin_square_is_surjective n L i,
end


def col_inverse_latin_square (n : ℕ) (L : latin_square n) : latin_square n :=
{
  map := 
  begin
    intros i,
    have col_bij := col_of_latin_square_is_bijection n L i,
    have finn_nonempty := fin.pos_iff_nonempty.mp L.nonempty,
    choose f' hf' using (bijective_iff_has_inverse.mp col_bij),
    exact f',
  end,

  is_latin := begin
    intros i j k,
    split,
    {
      by_contra,

      intro H,
      have col_bij:= (col_of_latin_square_is_bijection n L i),
      choose f' hf' using (bijective_iff_has_inverse.mp col_bij),
      rw function.bijective_iff_exists_unique at col_bij,
      rcases col_bij j with ⟨ j', j'_j_inv, j'_unique ⟩,
      rcases col_bij k with ⟨ k', k'_k_inv, k'_unique ⟩,
      have hf'_custom : inverse (L.map i) f' := by exact hf',
      rw inv_symm at hf'_custom,
      have : L.map i ((λ (_x : left_inverse (L.map i) f' ∧ right_inverse (L.map i) f'), f') hf'_custom j) = j,
      {
        sorry,
      },
      rw this at H,

      cases col_bij k with k' Hk',

      
      have : (L.map i) j = (L.map i) k,
      {
        sorry,
      },
      -- have col_bij := col_of_latin_square_is_bijection n L i,
      -- choose f' hf' using (bijective_iff_has_inverse.mp col_bij),
      -- cases L.is_latin i j k,
      -- have : f' j ≠ f' k,
      -- {
      --   sorry,
      -- },
      -- exact this,
      
    },
    {
      intro H,
      have bijection := col_of_latin_square_is_bijection n L i,
      have H1 := bijection.1 H,
      exact H1,
    },
  end
}


-- Given a latin square, if we transpose the square (i.e. swap the row and column indices), it is still a latin square.
def transpose_latin_square (n : ℕ) (L : latin_square n) : latin_square n :=
{
  map := 
  begin
    intros i j,
    exact L.map j i,
  end,

  is_latin := begin
    intros i j k,
    split,
    {
      intro H,
      have H1 := L.is_latin j i k,
      exact H1.2 H,
    },
    {
      intro H,
      have H1 := L.is_latin j i k,
      exact H1.1 H,
    },
  end
}
-- hence any result about columns also holds for rows

def is_transpose (n : ℕ) (L1 L2 : latin_square n) : Prop :=
∀ i j : fin n, L1.map i j = L2.map j i


def is_roll (n : ℕ) (L1 L2 : latin_square n) : Prop :=
∀ i j k : fin n, L1.map i j = k ↔ L2.map k i = j
