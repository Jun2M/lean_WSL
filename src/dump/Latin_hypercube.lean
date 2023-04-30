import algebra.group.basic
import data.real.basic data.set.image
import combinatorics.simple_graph.basic data.matrix.basic combinatorics.pigeonhole data.finset.card data.finset.basic


-- Define latin square object
structure latin_square (n : ℕ) :=
(domain : fin n)
(square : matrix (fin n) (fin n) (fin n))
(is_latin : ∀ i j k : fin n, square i j ≠ square i k ∧
                             square j i ≠ square k i)


-- def specify (α β γ : Type) (f : α → β → γ) (a : α) : β → γ := f a


-- example (n : ℕ) (s : latin_square n) (i : fin n) : 
--   ∀ j : fin n, ∃ k : fin n, s.square j k = i :=


theorem all_entrys_appears_each_row (n : ℕ) (s : latin_square n) (i : fin n) : 
  ∀ j : fin n, ∃ k : fin n, s.square j k = i :=
begin
  intro j,
  by_contra,
  push_neg at h,
  -- have square_j := specify (fin n) (fin n) (fin n) s.square j,
  have image_ssub_domain : (finset.image (s.square j) finset.univ) ⊂ finset.univ,
  {
    rw finset.ssubset_def,
    split,
    {
      intro x,
      simp,
    },
    {
      intro H,
      specialize H (finset.mem_univ i),
      rw finset.mem_image at H,
      rcases H with ⟨ k, k_ext, hk ⟩,
      specialize h k,
      exact h hk,
    },
  },

  have card_image_ssub_domain := finset.card_lt_card image_ssub_domain,

  have sth : ∀ (a : fin n), a ∈ finset.univ → (s.square j a) ∈ finset.image (s.square j) finset.univ,
  {
    intros a ha,
    rw finset.mem_image,
    use a,
    split,
    exact ha,
    refl,
  },

  have := (finset.exists_ne_map_eq_of_card_lt_of_maps_to card_image_ssub_domain) sth,
  clear sth image_ssub_domain card_image_ssub_domain h,
  rcases this with ⟨ a, a_ext, b, b_ext, a_neq_b, H ⟩,
  cases s.is_latin j a b with H1 H2,
  exact H1 H,
end


-- Given a latin square, if we transpose the square (i.e. swap the row and column indices), it is still a latin square.
def transpose_latin_square (n : ℕ) (s : latin_square n) : latin_square n :=
{
  domain := s.domain,
  square := s.square.transpose,
  is_latin := begin
    intros i j k,
    split,
    {
      intro H,
      have H1 := s.is_latin i j k,
      rw matrix.transpose_apply at H,
      rw matrix.transpose_apply at H,
      exact H1.2 H,
    },
    {
      intro H,
      have H1 := s.is_latin i j k,
      rw matrix.transpose_apply at H,
      rw matrix.transpose_apply at H,
      exact H1.1 H,
    },
  end
}

