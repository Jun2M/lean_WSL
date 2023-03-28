import algebra.group.basic algebra.group.defs
import data.finset.card data.finset.basic data.set.function
import combinatorics.simple_graph.basic combinatorics.pigeonhole 
import logic.function.basic logic.equiv.basic logic.equiv.defs
open function


theorem ssub_by_non_mem {α : Type} {A B : finset α} {a : α}
: A ⊆ B → a ∉ A → a ∈ B → A ⊂ B :=
begin
  intros A_sub_B ainA not_ainB,
  rw ssubset_iff_subset_ne,
  refine ⟨ A_sub_B, _ ⟩,
  intro A_eq_B,
  rw A_eq_B at ainA,
  contradiction,
end


lemma surj_on_of_image_B {α β : Type} [decidable_eq β] {A : finset α} {B : finset β} {f : α → β}
: set.maps_to f A B → set.surj_on f A B → (finset.image f A) = B :=
begin
  intros f_AtoB f_surj,
  rw finset.ext_iff,
  intros b,
  split,
  {
    intro b_in_image,
    rw finset.mem_image at b_in_image,
    rcases b_in_image with ⟨ a, ainA, H ⟩,
    rw ← H,
    exact f_AtoB ainA,
  },
  {
    intro binB,
    rw finset.mem_image,
    rcases f_surj binB with ⟨ a, ainA, H ⟩,
    exact ⟨ a, ainA, H ⟩,
  },
end


lemma image_B_of_surj_on {α β : Type} [decidable_eq β] {A : finset α} {B : finset β} {f : α → β}
: set.maps_to f A B → (finset.image f A) = B → set.surj_on f A B :=
begin
  intros f_AtoB image_eq_B b binB,
  rw set.mem_image,
  rw finset.ext_iff at image_eq_B,
  rw finset.mem_coe at binB,
  have := finset.mem_image.mp ((image_eq_B b).mpr binB),
  rcases this with ⟨ a, ainA, H ⟩,
  exact ⟨ a, ainA, H ⟩,
end


theorem surj_on_iff_image_B {α β : Type} [decidable_eq β] {A : finset α} {B : finset β} {f : α → β}
: set.maps_to f A B → (set.surj_on f A B ↔ (finset.image f A) = B) :=
begin
  intros f_AtoB,
  exact ⟨ surj_on_of_image_B f_AtoB, image_B_of_surj_on f_AtoB ⟩,
end


theorem inj_on_of_le_card {α β : Type} [decidable_eq β] {A : finset α} {B : finset β} {f : α → β}
: set.maps_to f A B → set.inj_on f A → A.card ≤ B.card :=
begin
  intros f_AtoB f_inj,
  exact finset.card_le_card_of_inj_on f f_AtoB f_inj,
end


theorem surj_on_of_le_card {α β : Type} [decidable_eq β] {A : finset α} {B : finset β} {f : α → β} 
: set.maps_to f A B → set.surj_on f A B → B.card ≤ A.card :=
begin
  intros f_AtoB f_surj,
  rw ← surj_on_of_image_B f_AtoB f_surj,
  exact finset.card_image_le,
end


theorem bij_on_of_eq_card {α β : Type} [decidable_eq β] {A : finset α} {B : finset β} {f : α → β}
: set.bij_on f A B → A.card = B.card :=
begin
  intros H,
  rcases H with ⟨ f_AtoB, f_inj, f_surj ⟩,
  exact antisymm (inj_on_of_le_card f_AtoB f_inj) (surj_on_of_le_card f_AtoB f_surj),
end


lemma same_card_to_inj_surj {α β : Type}[decidable_eq β] {A : finset α} {B : finset β} {f : α → β}
: A.card = B.card → set.maps_to f A B → set.inj_on f A → set.surj_on f A B :=
begin
  intros same_card f_AtoB f_inj b binB,
  by_contra,
  have : finset.image f A ⊂ B,
  {
    apply ssub_by_non_mem (finset.image_subset_iff.mpr f_AtoB) _ binB,
    intro H,
    apply h,
    rw finset.mem_image at H,
    rcases H with ⟨ a, ainA, H ⟩,
    exact ⟨ a, ainA, H ⟩,
  },
  have card_lt := finset.card_lt_card this,
  rw finset.card_image_of_inj_on f_inj at card_lt,
  finish,
end


lemma same_card_to_surj_inj {α β : Type} [decidable_eq β] {A : finset α} {B : finset β} {f : α → β}
: A.card = B.card → set.maps_to f A B → set.surj_on f A B → set.inj_on f A :=
begin
  intros same_card f_AtoB f_surj,
  rw ← surj_on_of_image_B f_AtoB f_surj at same_card,
  exact finset.inj_on_of_card_image_eq same_card.symm,
end


theorem same_card_of_inj_iff_surj {α β : Type} [decidable_eq β] {A : finset α} {B : finset β} {f : α → β}
: A.card = B.card → set.maps_to f A B → (set.inj_on f A ↔ set.surj_on f A B) :=
begin
  intros same_card f_AtoB,
  split,
  exact same_card_to_inj_surj same_card f_AtoB,
  exact same_card_to_surj_inj same_card f_AtoB,
end


-- lemma smth {α : Type} [fintype α] {f : α → α}
-- : set.maps_to f (coe finset.univ) (coe (finset.image f finset.univ))


-------------------------------------------------------------------------------------------------
-- Define latin square object
structure latin_function (len : ℕ):=
(nonempty : len > 0)
(map : (fin len) → (fin len))
(is_inj : injective map)


theorem image_eq_domain (n : ℕ) (L : latin_function n) :
  (finset.image L.map finset.univ) = finset.univ :=
begin
  have image_sub_domain : (finset.image L.map finset.univ) ⊆ finset.univ := (finset.image L.map finset.univ).subset_univ,
  cases has_subset.subset.eq_or_ssubset image_sub_domain with image_eq_domain image_ssub_domain;
  clear image_sub_domain,
  exact image_eq_domain,

  exfalso,
  have maps_to : set.maps_to L.map (coe finset.univ) (coe (finset.image L.map finset.univ)),
  {
    intros a ha,
    rw finset.mem_coe at ha,
    rw finset.mem_coe,
    rw finset.mem_image,
    use a,
    exact ⟨ ha, rfl ⟩,
  },

  have card_image_ssub_domain := finset.card_lt_card image_ssub_domain,
  have := finset.exists_ne_map_eq_of_card_lt_of_maps_to card_image_ssub_domain maps_to,
  rcases this with ⟨ a, a_ext, b, b_ext, a_neq_b, H ⟩,
  exact a_neq_b (L.is_inj H),
end


lemma latin_function_injective (len : ℕ) (f : latin_function len) : injective f.map :=
begin
  intros i j h,
  exact f.is_inj h,
end


lemma latin_function_surjective (len : ℕ) (f : latin_function len) : surjective f.map :=
begin
  intros i,
  have i_in_image : i ∈ finset.univ := finset.mem_univ i,
  rw ← image_eq_domain len f at i_in_image,
  rw finset.mem_image at i_in_image,
  rcases i_in_image with ⟨ j, j_in_univ, j_maps_to_i ⟩,
  exact ⟨ j, j_maps_to_i ⟩,
end


theorem latin_function_bijective (len : ℕ) (f : latin_function len) : bijective f.map :=
begin
  split,
  exact latin_function_injective len f,
  exact latin_function_surjective len f,
end


def permute_index {len : ℕ} (f : latin_function len) {g : (fin len) → (fin len)} (g_inj : injective g) :
 latin_function len :=
begin
  refine ⟨ f.nonempty, (g ∘ f.map), _ ⟩,

  rw injective.of_comp_iff,
  exact f.is_inj,
  exact g_inj,
end


def latin_function_equiv (len : ℕ) (f : latin_function len) : equiv (fin len) (fin len) :=
begin
  refl,
end


noncomputable def transpose (len : ℕ) (f : latin_function len) : latin_function len :=
{
  map := 
  begin
    choose g hg using function.bijective_iff_has_inverse.1 (latin_function_bijective len f),
    exact g,
  end,

  is_inj :=
  begin
    intros a b H,
    have _x : left_inverse (classical.some _) f.map ∧ right_inverse (classical.some _) f.map := 
    classical.some_spec (function.bijective_iff_has_inverse.1 (latin_function_bijective len f)),
    rcases _x with ⟨ left_inverse, right_inverse ⟩,
    have left_inverse_r := function.right_inverse.left_inverse right_inverse,
    exact (function.left_inverse.injective left_inverse_r) H,
  end,

  nonempty := f.nonempty,
}


-- define hypercube object where each side has length len and takes dim number of inputs
structure hypercube_dim2 (len : ℕ) :=
(nonempty : len > 0)
(map : (fin len) → (fin len) → (fin len))
(is_inj : injective map)


structure hypercube_dim3 (len : ℕ) :=
(nonempty : len > 0)
(map : (fin len) → (fin len) → (fin len) → (fin len))
(is_inj : injective map)


structure hypercube_dim4 (len : ℕ) :=
(nonempty : len > 0)
(map : (fin len) → (fin len) → (fin len) → (fin len) → (fin len))
(is_inj : injective map)


