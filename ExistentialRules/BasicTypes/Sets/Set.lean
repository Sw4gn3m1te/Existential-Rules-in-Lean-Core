import BasicLeanDatastructures.Set.Basic

namespace Set

  def ssubset (X Y : Set α) : Prop := X ⊆ Y ∧ X ≠ Y
  infix:50 " ⊂ " => ssubset

  def singleton (a : α) : Set α := fun x => x = a

  def neg_element (e : α) (X : Set α) : Prop := ¬ X e
  infixr:75 " ∉ " => neg_element

  def diff (S1 S2 : Set α) : Set α := fun x => x ∈ S1 ∧ ¬ x ∈ S2


  @[simp, grind]
  theorem eq_empty_of_subset_empty {α : Type u} {X : Set α} : X ⊆ ∅ → X = ∅ := by
    intro subset
    apply Classical.byContradiction
    intro contra
    rw [← ne_eq] at contra
    have ex_elem : ∃ e, e ∈ X := by
      apply Set.not_empty_contains_element
      exact contra
    rcases ex_elem with ⟨e, e_in_X⟩
    exact subset e e_in_X

  @[grind]
  theorem empty_subset_of_each (X : Set α) : ∅ ⊆ X := by
    intro e e_in_empty
    contradiction

  @[grind]
  theorem subset_sym_eq (X Y : Set α) : X ⊆ Y ∧ Y ⊆ X ↔ X = Y := by
    constructor
    intro ⟨x_sub_y, y_sub_x⟩
    funext e
    exact Eq.propIntro (x_sub_y e) (y_sub_x e)
    intro eq
    rw [eq]
    simp only [and_self]
    apply Set.subset_refl

  @[simp, grind]
  theorem mem_singleton_iff_eq (e : α) : f ∈ (Set.singleton e) ↔ e = f := by
    unfold Set.singleton
    constructor
    intro h
    apply Classical.byContradiction
    intro contra
    exact Ne.elim (fun a => contra (id (Eq.symm a))) h
    intro h
    exact id (Eq.symm h)


  @[grind]
  theorem singleton_subset_iff_mem (X : Set α) (e : α) : e ∈ X ↔ Set.singleton e ⊆ X := by
    constructor
    intro e_in_x f f_in
    have eq : e = f := by
      rw [← mem_singleton_iff_eq]
      exact f_in
    rw [← eq]
    exact e_in_x
    intro sub
    exact sub e rfl

  @[simp, grind]
  theorem subset_trans_mem (X : Set α) : e ∈ X ∧ X ⊆ Y → e ∈ Y := by
    intro a
    obtain ⟨left, right⟩ := a
    apply right
    simp_all only

  @[grind]
  theorem union_iff (X Y : Set α) (e : α) : e ∈ (X ∪ Y) ↔ e ∈ X ∨ e ∈ Y := by
    exact Eq.to_iff rfl

  -- mathlib yoinks
  @[grind]
  theorem eq_subset {α} {s t : Set α} : s = t → s ⊆ t :=
    fun h₁ _ h₂ => by rw [← h₁]; exact h₂



end Set
