/-

# Equivs

Two types α and β are equivalent, written α ≃ β, if there's
a bijection between them.

-/

structure Equiv (α β : Type) :=
(to_fun : α → β)
(inv_fun : β → α)
(left_inv : ∀ a, inv_fun (to_fun a) = a)
(right_inv : ∀ b, to_fun (inv_fun b) = b)

infix:25 " ≃ " => Equiv

def Equiv.symm {α β} (h : α ≃ β) : β ≃ α where
  to_fun := h.inv_fun
  inv_fun := h.to_fun
  left_inv := h.right_inv
  right_inv := h.left_inv

-- #check Option
-- #check Unit

-- #check Option.none
-- #check none

def OptionEmptyEquivUnit : Option Empty ≃ Unit where
  to_fun | none => Unit.unit
         | some a => Empty.rec (λ _ => _) a
  inv_fun := λ u => none 
  left_inv | none => rfl
           | some a => Empty.rec (λ _ => _) a
  right_inv := λ u => by
    cases u;
    rfl;

instance : Subsingleton Empty where
  allEq a := nomatch a -- (a : Empty) so no cases

def SubsingletonEquivEmptyOrUnit (α : Type) [Subsingleton α] :
  (∃ e : α ≃ Empty, True) ∨ (∃ e : α ≃ Unit, True) := by
  cases Classical.em (∃ a : α, True) with
    | inl h =>
    { apply Or.inr;
      let ⟨a, _⟩ := h;
      exact ⟨{
        to_fun := λ x => Unit.unit
        inv_fun := λ y => a
        left_inv := λ x => Subsingleton.elim _ _
        right_inv := λ y => Subsingleton.elim _ _
      }, True.intro⟩ }
    | inr h =>
    { apply Or.inl;
      exact ⟨{
        to_fun := λ x => False.elim $ h ⟨x, True.intro⟩
        inv_fun := λ y => by cases y;
        left_inv := λ x => Subsingleton.elim _ _
        right_inv := λ y => Subsingleton.elim _ _
      }, True.intro⟩ }

def SumEmptyEquiv (α : Type) : Sum Empty α ≃ α where
  to_fun 
  | Sum.inl a => nomatch a
  | Sum.inr a => a
  inv_fun b := Sum.inr b
  left_inv
  | Sum.inl a => nomatch a
  | Sum.inr a => rfl      
  right_inv b := rfl
