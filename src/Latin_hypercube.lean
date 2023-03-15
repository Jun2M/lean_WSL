import algebra.group.basic
import data.real.basic data.set.image
import combinatorics.simple_graph.basic data.matrix.basic combinatorics.pigeonhole data.finset.card data.finset.basic


/- Define latin square object-/
structure latin_square (n : ℕ) :=
(square : matrix (fin n) (fin n) (fin n))
(is_latin : ∀ i j k : fin n, square i j ≠ square i k ∧
                             square j i ≠ square k i)


def specify (α β γ : Type) (f : α → β → γ) (a : α) : β → γ := f a


-- example (n : ℕ) (s : latin_square n) (i : fin n) : 
--   ∀ j : fin n, ∃ k : fin n, s.square j k = i :=


theorem all_entrys_appears (n : ℕ) (s : latin_square n) (i : fin n) : 
  ∀ j : fin n, ∃ k : fin n, s.square j k = i :=
begin
  intro j,
  by_contra,
  push_neg at h,
  have square_j := specify (fin n) (fin n) (fin n) s.square j,
  have image_ssub_domain : (square_j '' set.univ) ⊂ set.univ,
  {
    rw set.ssubset_def,
    split,
    {
      rw set.subset_def,
      intro x,
      simp,
    },
    {
      rw set.subset_def,
      push_neg,
      use i,
      split,
      {
        simp,
      },
      {
        intro h1,
        -- hence there exist y st square j y = i
        rcases (set.mem_image square_j set.univ i).mp h1 with ⟨ x, xin_univ, hx ⟩,
        specialize h x,

      },
    },
  },
end
