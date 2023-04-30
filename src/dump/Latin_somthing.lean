import logic.equiv.basic

universes u_1 u_2 u_3

example (α : Type u_1) (β : Type u_2) (γ : Type u_3) :
  (α → β → γ) ≃ (β → α → γ) :=
begin
exact equiv.Pi_comm _,
end

