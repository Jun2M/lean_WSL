import algebra.group.basic algebra.group.defs init.function
import data.set.image data.set.prod data.finset.card data.finset.basic data.set.function
import combinatorics.simple_graph.basic combinatorics.pigeonhole set_theory.cardinal.finite
import Inverse_function logic.function.basic
open set finset


-- Define latin square object
structure latin_square (len : ℕ):=
(nonempty : len > 0)
(map : ℕ → ℕ → ℕ)
(bound : ∀ i j : ℕ, i ∈ range len → j ∈ range len → map i j ∈ range len)
(is_latin : ∀ i j k : ℕ, i ∈ range len → j ∈ range len → k ∈ range len →
                          map i j ≠ map i k ∧
                          map j i ≠ map k i)


lemma finset_eq_iff_coe_set_eq {α : Type*} {s t : finset α} : s = t ↔ {x | x ∈ s} = {x | x ∈ t} :=
begin
  split,
  {
    intro H,
    rw H,
  },
  {
    intro H,
    rw finset.ext_iff,
    rw set.ext_iff at H,
    intros x,
    cases H x,
    split,
    {
      intro H1,
      exact mp H1,
    },
    {
      intro H1,
      exact mpr H1,
    },
  },
end


theorem col_of_latin_square_is_injective (n : ℕ) (L : latin_square n) (i : ℕ) (hi : i ∈ range n) :
  set.inj_on (L.map i) (finset.range n) :=
begin
  intros a ha,
  by_contra,
  push_neg at h,
  rcases h with ⟨ b, hb, H, anb ⟩,
  cases L.is_latin i a b hi ha hb with H1 H2,
  exact H1 H,
end


theorem col_of_latin_square_is_surjective (n : ℕ) (L : latin_square n) (i : ℕ) (hi : i ∈ range n) : 
  set.surj_on (L.map i) (finset.range n) (finset.range n) :=
begin
  have domain_image_eq_card: (finset.image (L.map i) (finset.range n)).card = (finset.range n).card,
  exact finset.card_image_of_inj_on (col_of_latin_square_is_injective n L ↑i hi),
  have image_sub_domain: (finset.image (L.map i) (finset.range n)) ⊆ (finset.range n),
  intros x hx,
  rw finset.mem_image at hx,
  rcases hx with ⟨ y, hy, H1 ⟩,
  rw ← H1,
  exact L.bound i y hi hy,
  
  have domain_card_le_image_card : (range n).card ≤ (finset.image (L.map i) (finset.range n)).card := eq.ge domain_image_eq_card,
  have domain_eq_image := finset.eq_of_superset_of_card_ge image_sub_domain domain_card_le_image_card,
  clear domain_image_eq_card image_sub_domain domain_card_le_image_card,
  have := set.surj_on_image (L.map i) (finset.range n),
  rw finset_eq_iff_coe_set_eq at domain_eq_image,
  rw finset.set_of_mem at domain_eq_image,
  rw finset.set_of_mem at domain_eq_image,
  rw domain_eq_image,
end


theorem col_of_latin_square_is_bijection (n : ℕ) (L : latin_square n) (i : range n) :
  set.bij_on (L.map i) set.univ set.univ :=
begin
  split,
  {
    
  },
  {
    exact col_of_latin_square_is_surjective n L i,
  },
end
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
      
      intro H,
      have col_bij := col_of_latin_square_is_bijection n L i,

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
