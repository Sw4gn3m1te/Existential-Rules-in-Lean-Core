import ExistentialRules.BasicTypes.Sets.Set


namespace Function

  def isInjective (f : α → β) (A : Set α) : Prop := ∀ x y, x ∈ A ∧ y ∈ A → (f x = f y → x = y)

  def isInjective' (f : α → β) (A : Set α) : Prop := ∀ x y, x ∈ A ∧ y ∈ A → (x ≠ y → f x ≠ f y)

  -- Mathlib.Tactic.Contrapose
  theorem isInjectiveIffisInjective' (f : α → β) (A : Set α) (B : Set β) : Function.isInjective f A ↔ Function.isInjective' f A := by
    unfold isInjective isInjective'
    constructor
    intro h x y ⟨x_in_A, y_in_A⟩ neq
    specialize h x y ⟨x_in_A, y_in_A⟩
    grind
    intro h x y ⟨x_in_A, y_in_A⟩ feq
    specialize h x y ⟨x_in_A, y_in_A⟩
    grind

  def isSurjective (f : α → β) (A : Set α) (B : Set β) : Prop := ∀ y, ∃ x, (y ∈ B ∧ x ∈ A) → (f x = y)

  def isBijective (f : α → β) (A : Set α) (B : Set β) : Prop := Function.isInjective f A ∧ Function.isSurjective f A B

end Function
