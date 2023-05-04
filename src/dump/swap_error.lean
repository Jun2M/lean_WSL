open function

variables {α : Type} {β : Type}

structure tiny_structure {α : Type} :=
  (something : α)

theorem function_on_the_structure {α : Type} (s : tiny_structure β) : tiny_structure β := s

