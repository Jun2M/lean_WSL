import tactic
import field_theory.finite.basic
import field_theory.tower
import field_theory.subfield
import linear_algebra.finite_dimensional


universe u

variables {F0 F1 F2 : Type u} [F0_field: field F0] [F1_field: field F1] [F2_field: field F2]
variables [F1_in_F0: algebra F0 F1] [F2_in_F1: algebra F1 F2]



/- Prove F2 is a subfield of F0-/
lemma zero_in_F0_is_0_in_F2 : F2_field.one ∈ F2_field :=
begin
  sorry,
end

