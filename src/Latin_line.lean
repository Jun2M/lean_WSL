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

theorem right_inv_ext {α β : Type} {f : α → β} {g : β → α} (H : right_inverse f g) (x : α) : g (f x) = x :=
  H x
  -- what!!! that is so good

-------------------------------------------------------------------------------------------------
-- Define latin square object
structure latin1 (len : ℕ):=
  (nonempty : len > 0)
  (map : (fin len) → (fin len))
  (is_inj : injective map)

-- nonempty from fin.pos


lemma latin1.ext {len : ℕ} (L1 L2 : latin1 len) : L1.map = L2.map → L1 = L2 :=
begin
  intros H,
  cases L1,
  cases L2,
  congr,
  exact H,
end


lemma latin1.ext_iff {len : ℕ} (L1 L2 : latin1 len) : L1 = L2 ↔ L1.map = L2.map :=
begin
  split,
    intro H,
    rw H,
    apply latin1.ext,
end


theorem latin1_maps_to_self {len : ℕ} (L : latin1 len) : (finset.image L.map finset.univ) = finset.univ := inj_maps_to_self L.is_inj

lemma surj_of_latin1 {len : ℕ} (f : latin1 len) : surjective f.map := surj_of_inj f.is_inj

theorem bij_of_latin1 {len : ℕ} (f : latin1 len) : bijective f.map := bij_of_inj f.is_inj

-- theorem inv_of_latin1 {len : ℕ} (f : latin1 len) : ∃ g : latin1 len, right_inverse f.map g.map ∧ left_inverse f.map g.map :=
-- begin
--   have fmap_bij := bij_of_latin1 f,
--   have : ∀ x : fin len, ∃ y : fin len, f.map y = x,
--   {
--     intro x,
--     have x_in_image : x ∈ finset.univ := finset.mem_univ x,
--     rw ← latin1_maps_to_self f at x_in_image,
--     rw finset.mem_image at x_in_image,
--     rcases x_in_image with ⟨ y, y_in_univ, y_maps_to_x ⟩,
--     exact ⟨ y, y_maps_to_x ⟩,
--   },

--   have to_nat := fin.fin_to_nat len,

--   -- define inverse of fmap as a function using nat.find
--   have exist_in_nat : ∀ x : fin len, ∃ y : ℕ, f.map (@fin.of_nat' len (ne_zero.of_pos f.nonempty) y) = x,
--   {
--     intro x,
--     have := this x,
--     rcases this with ⟨ y, y_maps_to_x ⟩,
--     use y.val,
--     rw ← y_maps_to_x,
--     simp only [fin.coe_coe_eq_self, fin.val_eq_coe, eq_self_iff_true, fin.of_nat'_eq_coe],
--   },

--   have fmap_inv : ∃ g : fin len → fin len, ∀ x : fin len, f.map (g x) = x ∧ g (f.map x) = x,
--   {
--     have g : fin len → fin len,
--     {
--       intro x,
--       cases exist_in_nat x,
--       have := nat.find (exist_in_nat x),
--       exact fin.of_nat' len (ne_zero.of_pos f.nonempty) this,
--     },
--     have := exist_in_nat x,
--   },

--   -- use ⟨ f.nonempty, fmap_inv, _ ⟩,

--   -- prove that fmap_inv is inverse of fmap
--   have fmap_inv_is_inv : right_inverse f.map fmap_inv ∧ left_inverse f.map fmap_inv,
--   {
--     split,
--     {
--       intro x,

--       rw ← (nat.find_spec (exist_in_nat x)),
--       simp only [fin.of_nat'_eq_coe],
--       exact nat.find_min (exist_in_nat x) (nat.find_spec (exist_in_nat x)),
--     },
--     {
--       intro x,
--       have := nat.find_spec (exist_in_nat x),
--       rw ← this,
--       simp only [fin.of_nat'_eq_coe, fin.coe_coe_eq_self, fin.val_eq_coe, eq_self_iff_true],
--       exact nat.find_min (exist_in_nat x) (nat.find_spec (exist_in_nat x)),
--     }
--   },
  
-- end

-------------------------------------------------------------------------------------------------


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


theorem permi1 {len : ℕ} {g : (fin len) → (fin len)} (f : latin1 len) (g_inj : injective g) : 
  ∃ fg : latin1 len, fg.map = g ∘ f.map :=
begin
  use { nonempty := f.nonempty, map := g ∘ f.map, is_inj := (injective.of_comp_iff g_inj f.map).mpr f.is_inj },
end

theorem perme1 {len : ℕ} {g : (fin len) → (fin len)} (f : latin1 len) (g_inj : injective g) : 
  ∃ gf : latin1 len, gf.map = f.map ∘ g :=
begin
  use { nonempty := f.nonempty, map := f.map ∘ g, is_inj := (injective.of_comp_iff f.is_inj g).mpr g_inj },
end

theorem push1 {len : ℕ} (f : latin1 len) : ∃ f' : latin1 len, left_inverse f'.map f.map ∧ right_inverse f'.map f.map :=
begin
  choose g hg using function.bijective_iff_has_inverse.1 (bij_of_latin1 f),
  have g_inj : injective g := left_inverse.injective (function.right_inverse.left_inverse hg.2),
  use { nonempty := f.nonempty, map := g, is_inj := g_inj },
  exact hg,
end

def is_normal1 {len : ℕ} (f : latin1 len) : Prop := f.map = id



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


-- structure latin1_isom (len : ℕ) : Type :=
--   (to_hom : latin1_hom len)
--   (inv : latin1_hom len)
--   (right_inv : to_hom.to_fun ∘ inv.to_fun = id )
--   (left_inv : inv.to_fun ∘ to_hom.to_fun = id )


-- lemma latin1_isom.ext {len : ℕ} (f g : latin1_isom len) : f.to_hom = g.to_hom → f = g :=
-- begin
--   intros H,
--   cases f,
--   cases g,
--   congr,
--   exact H,
--   sorry,
-- end


-- lemma latin1_isom.ext_iff {len : ℕ} (f g : latin1_isom len) : f = g ↔ f.to_hom = g.to_hom :=
-- begin
--   split,
--     intro H,
--     rw H,
--     apply latin1_isom.ext,
-- end


-- def perm_isom1 {len : ℕ} {g : (fin len) → (fin len)} (g_inj : injective g) : latin1_isom len :=
-- {
--   to_hom := permi_hom1 g_inj,
--   inv := 
--     {
--       to_fun := 
--       begin
--         intro f,
--         choose h hh using inv_fun_of_inj g_inj,
--         refine ⟨ f.nonempty, ( h ∘ f.map), _ ⟩,
        
--         rw injective.of_comp_iff,
--         exact f.is_inj,
--         exact left_inverse.injective (function.right_inverse.left_inverse hh.2),
--       end,
--     },
--   right_inv :=
--   begin
--     simp,
--     rw function.comp.left_id,
--   end,
-- }