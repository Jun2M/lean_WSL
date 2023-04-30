import algebra.group.basic algebra.group.defs
import data.finset.card data.finset.basic data.set.function data.finset.fin
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


theorem inj_maps_to_self {len : ℕ} {f : (fin len) → (fin len)} (H : injective f) :
  (finset.image f finset.univ) = finset.univ :=
begin
  have image_sub_domain : (finset.image f finset.univ) ⊆ finset.univ := (finset.image f finset.univ).subset_univ,
  cases has_subset.subset.eq_or_ssubset image_sub_domain with image_eq_domain image_ssub_domain;
  clear image_sub_domain,
  exact image_eq_domain,

  exfalso,
  have maps_to : set.maps_to f (coe finset.univ) (coe (finset.image f finset.univ)),
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
  rcases this with ⟨ a, a_ext, b, b_ext, a_neq_b, H1 ⟩,
  exact a_neq_b (H H1),
end


lemma surj_of_inj {len : ℕ} {f : (fin len) → (fin len)} (H : injective f) : surjective f :=
begin
  intros i,
  have i_in_image : i ∈ finset.univ := finset.mem_univ i,

  rw ← inj_maps_to_self H at i_in_image,
  rw finset.mem_image at i_in_image,
  rcases i_in_image with ⟨ j, j_in_univ, j_maps_to_i ⟩,
  exact ⟨ j, j_maps_to_i ⟩,
end


theorem bij_of_inj {len : ℕ} {f : (fin len) → (fin len)} (H : injective f) : bijective f :=
⟨ H, surj_of_inj H ⟩

theorem inv_fun_of_inj {len : ℕ} {f : (fin len) → (fin len)} (H : injective f) :
 ∃ g : (fin len) → (fin len), right_inverse f g ∧ left_inverse f g :=
  function.bijective_iff_has_inverse.1 (bij_of_inj H)

-------------------------------------------------------------------------------------------------
-- Define latin square object
structure latin1M (len : ℕ):=
(nonempty : len > 0)
(map : (fin len) → (fin len))
(is_inj : injective map)


lemma latin1M.ext {len : ℕ} (L1 L2 : latin1M len) : L1.map = L2.map → L1 = L2 :=
begin
  intros H,
  cases L1,
  cases L2,
  congr,
  exact H,
end


lemma latin1M.ext_iff {len : ℕ} (L1 L2 : latin1M len) : L1 = L2 ↔ L1.map = L2.map :=
begin
  split,
    intro H,
    rw H,
    apply latin1M.ext,
end


theorem latin1M_maps_to_self {len : ℕ} (L : latin1M len) : (finset.image L.map finset.univ) = finset.univ := inj_maps_to_self L.is_inj

lemma surj_of_latin1M {len : ℕ} (f : latin1M len) : surjective f.map := surj_of_inj f.is_inj

theorem bij_of_latin1M {len : ℕ} (f : latin1M len) : bijective f.map := bij_of_inj f.is_inj

theorem inv_of_latin1M {len : ℕ} (f : latin1M len) : ∃ g : latin1M len, right_inverse f.map g.map ∧ left_inverse f.map g.map :=
begin
  have H := inv_fun_of_inj f.is_inj,
  cases H with gmap H,
  cases H with right_inv left_inv,
  have gmap_inj : injective gmap := left_inverse.injective left_inv,
  use { nonempty := f.nonempty, map := gmap, is_inj := gmap_inj },
  exact ⟨ right_inv, left_inv ⟩,
end

-------------------------------------------------------------------------------------------------

-- Define latin square object using finsets
structure latin1S (len : ℕ):=
(nonempty : len > 0)
(set : finset (fin len × fin len))
(unique_cover : ∀ i j : fin len, ∃! i1 j1 : fin len, (i1, j) ∈ set ∧ (i, j1) ∈ set)


lemma latin1S.ext {len : ℕ} (L1 L2 : latin1S len) : L1.set = L2.set → L1 = L2 :=
begin
  intros H,
  cases L1,
  cases L2,
  congr,
  exact H,
end


lemma latin1S.ext_iff {len : ℕ} (L1 L2 : latin1S len) : L1 = L2 ↔ L1.set = L2.set :=
begin
  split,
    intro H,
    rw H,
    apply latin1S.ext,
end


-------------------------------------------------------------------------------------------------

-- latin1M and latin1S are equivalent

def latin1M.S {len : ℕ} (L : latin1M len) : latin1S len :=
{
  nonempty := L.nonempty,
  set := finset.image (λ j : fin len, (j, L.map j)) finset.univ,
  unique_cover := 
  begin
    intros i j,
    choose g hg using function.bijective_iff_has_inverse.1 (bij_of_latin1M L),
    use g j,
    use L.map i,
    {
      split,
      {
        rw finset.mem_image,
        use g j,
        {
          refine ⟨ finset.mem_univ _, _ ⟩,
          rw hg.2,
        },
        {
          rw finset.mem_image,
          use i,
          exact ⟨ finset.mem_univ i, rfl ⟩,
        },
      },
      {
        intros j1 hj1,
        rcases hj1 with ⟨ hj1, hj2 ⟩,
        rw finset.mem_image at hj2,
        rcases hj2 with ⟨ j2, hj2, hj3 ⟩,
        cases hj3,
        refl,
      },
    },
    {
      intros a ha,
      rcases ha with ⟨  ⟩,
      
    }

      split;
      rw finset.mem_image,
        use g j,
        refine ⟨ finset.mem_univ _, _ ⟩,
        rw hg.2,

        use i,
        exact ⟨ finset.mem_univ i, rfl ⟩,
  end,
}


def latin1S.M {len : ℕ} (L : latin1S len) : latin1M len :=
{
  nonempty := L.nonempty,
  map := 
  begin
    intro i,
    have := L.covers i i,
    choose i1 H using this,
    choose j1 H using H,
    exact j1,
  end,
  is_inj := 
  begin
    intros i j H,
    
  end,
}


-- structure latin1_hom (len : ℕ) : Type :=
--   (to_fun : latin1 len → latin1 len)


-- lemma latin1_hom.ext {len : ℕ} (f g : latin1_hom len) : f.to_fun = g.to_fun → f = g :=
-- begin
--   intros H,
--   cases f,
--   cases g,
--   congr,
--   exact H,
-- end


-- lemma latin1_hom.ext_iff {len : ℕ} (f g : latin1_hom len) : f = g ↔ f.to_fun = g.to_fun :=
-- begin
--   split,
--     intro H,
--     rw H,
--     apply latin1_hom.ext,
-- end


-- def permi_hom1 {len : ℕ} {g : (fin len) → (fin len)} (g_inj : injective g) : latin1_hom len :=
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


-- def perme_hom1 {len : ℕ} {g : (fin len) → (fin len)} (g_inj : injective g) : latin1_hom len :=
-- {
--   to_fun := 
--   begin
--     intro f,
--     refine ⟨ f.nonempty, (f.map ∘ g), _ ⟩,
    
--     rw injective.of_comp_iff,
--     exact g_inj,
--     exact f.is_inj,
--   end,
-- }


-- def id_hom1 {len : ℕ} : latin1_hom len := permi_hom1 (injective_id)


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
--   exact (permi_hom1 g_inj).to_fun f,
-- end


-- def latin1_hom_comp {len : ℕ} (f g : latin1_hom len) : latin1_hom len :=
-- begin
--   refine ⟨ λ h, _ ⟩,
--   exact ((f.to_fun ∘ g.to_fun) h),
-- end


-- lemma id_hom1_id {len : ℕ} (f : latin1 len) : (id_hom1.to_fun f) = f :=
-- begin
--   apply latin1.ext,
--   unfold id_hom1,
--   unfold permi_hom1,
--   unfold latin1_hom.to_fun,
--   unfold latin1.map,
--   rw function.comp.left_id,
-- end


-- def latin1_equiv {len : ℕ} (f g : latin1 len) : Prop :=
--   ∃ hom : latin1_hom len, hom.to_fun f = hom.to_fun g


-- lemma latin1_equiv_refl {len : ℕ} (f : latin1 len) : latin1_equiv f f :=
-- begin
--   use id_hom1,
-- end


-- lemma latin1_equiv_symm {len : ℕ} (f g : latin1 len) : latin1_equiv f g → latin1_equiv g f :=
-- begin
--   intro H,
--   rcases H with ⟨ hom, H ⟩,
--   use hom,
--   exact H.symm,
-- end


-- lemma normalise_hom1_returns_id {len : ℕ} (f : latin1 len) : (normalise_hom1.to_fun f).map = id :=
-- begin
--   unfold normalise_hom1,
--   unfold permi_hom1,
--   apply function.left_inverse.id,
--   exact (classical.some_spec (function.bijective_iff_has_inverse.1 (bij_of_latin1 f))).1,
-- end


-- theorem all_latin1_equiv {len : ℕ} (f g : latin1 len) : latin1_equiv f g :=
-- begin
--   use normalise_hom1,
--   rw latin1.ext_iff,
--   rw normalise_hom1_returns_id,
--   rw normalise_hom1_returns_id,
-- end
