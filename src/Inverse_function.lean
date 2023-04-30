import data.set.basic data.set.image
import logic.function.basic
open function set
variables {X Y : Type} {A E F U V : set X}


-- function.inv_fun is not good because it uses classical.some and it throws some weird errors
-- Haven't tried surj_inv yet
-- 


-- definition
def inverse {X Y : Type} (f : X → Y) (f' : Y → X) := 
function.left_inverse f' f ∧ function.right_inverse f' f



lemma inv_imp_bij {X' Y' : Type} (f : X' → Y') (f' : Y' → X'):
inverse f f' → function.bijective f:=
begin
  intro f'inv,
  refine function.bijective_iff_has_inverse.mpr _,
  use f',
  exact f'inv,
end


lemma linv_imp_rinv_swap {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : 
function.left_inverse f f' → function.right_inverse f' f :=
begin
  intros linv x,
  exact linv x,
end


lemma rinv_imp_linv_swap {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : 
function.right_inverse f f' → function.left_inverse f' f :=
begin
  intros rinv x,
  exact rinv x,
end


lemma rinv_iff_linv_swap {X' Y' : Type} (f : X' → Y') (f' : Y' → X') :
function.right_inverse f f' ↔ function.left_inverse f' f :=
begin
  split,
  exact rinv_imp_linv_swap f f',
  exact linv_imp_rinv_swap f' f,
end


lemma inv_swap {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : inverse f f' → inverse f' f :=
begin
  intros h,
  split,
  exact rinv_imp_linv_swap f' f h.right,
  exact linv_imp_rinv_swap f' f h.left,
end


lemma inv_symm {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : inverse f f' ↔ inverse f' f :=
begin
  split,
  have := inv_swap f f',
  exact this,
  have := inv_swap f' f,
  exact this,
end


lemma bij_inv_bij {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : inverse f f' →
(function.bijective f ↔ function.bijective f') :=
begin
  intros f'inv,
  split;
  intro fbij,
  rw inv_symm at f'inv,
  exact inv_imp_bij f' f f'inv,
  exact inv_imp_bij f f' f'inv,
end

lemma unique_preimage {X' Y' : Type} (f : X' → Y') (f' : Y' → X') : inverse f f' → 
∀ (s : set Y'), preimage f s = image f' s :=
begin
  intros f'inv s,
  have img_img:= left_inverse.image_image f'inv.right s,
  have := inv_imp_bij f f' f'inv,
  rw set.preimage_eq_iff_eq_image this,
  exact eq.symm img_img,
end
