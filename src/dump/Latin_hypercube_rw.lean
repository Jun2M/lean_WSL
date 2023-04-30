import algebra.group.basic algebra.group.defs
import data.finset.card data.finset.basic data.set.function
import combinatorics.simple_graph.basic combinatorics.pigeonhole 
import logic.function.basic logic.equiv.basic logic.equiv.defs
import Latin_line
open function


def is_latin1 {len : ℕ} (f : (fin len) → (fin len)) : Prop := injective f

def is_normal1 {len : ℕ} (f : (fin len) → (fin len)) : Prop := f = id


theorem latin1_maps_to_self' {len : ℕ} {f : (fin len) → (fin len)} (H : is_latin1 f) :
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


lemma surj_of_latin1' {len : ℕ} {f : (fin len) → (fin len)} (H : is_latin1 f) : surjective f :=
begin
  intros i,
  have i_in_image : i ∈ finset.univ := finset.mem_univ i,
  rw ← latin1_maps_to_self' H at i_in_image,
  rw finset.mem_image at i_in_image,
  rcases i_in_image with ⟨ j, j_in_univ, j_maps_to_i ⟩,
  exact ⟨ j, j_maps_to_i ⟩,
end


theorem bij_of_latin1' {len : ℕ} {f : (fin len) → (fin len)} (H : is_latin1 f) : bijective f :=
⟨ H, surj_of_latin1' H ⟩


-----------------------------------------------------------------------------------------------------


structure latin1_hom' {len : ℕ} : Type :=
  (to_fun : ((fin len) → (fin len)) → ((fin len) → (fin len)))
  (map_latin1 {f : (fin len) → (fin len)} : is_latin1 f → is_latin1 (to_fun f))


def perm_hom_latin1' {len : ℕ} {g : (fin len) → (fin len)} (g_inj : injective g) : latin1_hom' :=
{
  to_fun := 
    begin
      intro f,
      exact g ∘ f,
    end,

  map_latin1 :=
    begin
      intros f f_inj,
      unfold is_latin1,
      rw injective.of_comp_iff,
      exact f_inj,
      exact g_inj,
    end,
}


noncomputable def transpose_hom_latin1 {len : ℕ} : latin1_hom :=
{
  to_fun := 
    begin
      intro f,
      
    end,
}


-- lemma latin1_canbe_permuted {len : ℕ} {f : (fin len) → (fin len)} (H : is_latin1 f) {g : (fin len) → (fin len)} (g_inj : injective g) :
--   is_latin1 (g ∘ f) :=
-- begin
--   unfold is_latin1,
--   rw injective.of_comp_iff,
--   exact H,
--   exact g_inj,
-- end


-- theorem latin1_iff_permuted {len : ℕ} {f : (fin len) → (fin len)} {g : (fin len) → (fin len)} (g_inj : injective g):
--   is_latin1 f ↔ is_latin1 (g ∘ f) :=
-- begin
--   split,

--   intro f_inj,
--   exact latin1_canbe_permuted f_inj g_inj,

--   intros gf_inj,
--   unfold is_latin1 at gf_inj,
--   rw injective.of_comp_iff g_inj f at gf_inj,
--   exact gf_inj,
-- end


-- theorem latin1_canbe_transposed {len : ℕ} {f : (fin len) → (fin len)} (H : is_latin1 f) :
-- ∃ g : (fin len) → (fin len), right_inverse g f ∧ left_inverse g f ∧ is_latin1 g :=
-- begin
--   choose g hg using function.bijective_iff_has_inverse.1 (bij_of_latin1 H),
--   use g,
--   refine ⟨ hg.2, hg.1, _ ⟩,
--   exact left_inverse.injective (function.right_inverse.left_inverse hg.2),
-- end


-- theorem latin1_iff_transposed {len : ℕ} {f : (fin len) → (fin len)} :
--   is_latin1 f ↔ ∃ g : (fin len) → (fin len), right_inverse g f ∧ left_inverse g f ∧ is_latin1 g :=
-- begin
--   split,
--   {
--     intro f_inj,
--     exact latin1_canbe_transposed f_inj,
--   },
--   {
--     intros gf_inj,
--     rcases gf_inj with ⟨ g, g_right_inv, g_left_inv, g_inj ⟩,
--     unfold is_latin1,
--     unfold is_latin1 at g_inj,
--     exact left_inverse.injective g_left_inv,
--   },
-- end



theorem latin1_canbe_normal1ised {len : ℕ} {f : (fin len) → (fin len)} (H : is_latin1 f) :
  ∃ g : (fin len) → (fin len), injective g ∧ is_latin1 (g ∘ f) ∧ is_normal1 (g ∘ f) :=
begin
  choose g hg using function.bijective_iff_has_inverse.1 (bij_of_latin1' H),
  use g,
  have g_inj : injective g := left_inverse.injective (function.right_inverse.left_inverse hg.2),
  refine ⟨ g_inj, (perm_hom_latin1' g_inj).map_latin1 H, left_inverse.id hg.1 ⟩,
end



