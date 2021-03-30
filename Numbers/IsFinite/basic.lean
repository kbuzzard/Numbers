import Numbers.Equiv.basic

inductive IsFinite : Type → Prop
| empty : IsFinite Empty
| option : IsFinite α → IsFinite (Option α)
| equiv : IsFinite α → (α ≃ β) → IsFinite β

attribute [class] IsFinite

open IsFinite

instance : IsFinite Empty := empty

instance : IsFinite Unit :=
equiv (option inferInstance) OptionEmptyEquivUnit

#check Subsingleton

instance (α : Type) [Subsingleton α] : IsFinite α :=
  by
  cases (SubsingletonEquivEmptyOrUnit α) with
  | inl h => exact equiv inferInstance h.1.symm;
  | inr h => exact equiv inferInstance h.1.symm;

-- how to do this in term mode?
instance (α : Type) [Subsingleton α] : IsFinite α :=
  by cases (SubsingletonEquivEmptyOrUnit α) with
  | _ h => exact equiv inferInstance h.1.symm;

instance (α β : Type) [IsFinite α] [IsFinite β] : IsFinite (Sum α β) :=
sorry


--class IsFinite (α : Type) :=
--(is_finite : ∃ L : List α, ∀ a : α, a ∈ L )

