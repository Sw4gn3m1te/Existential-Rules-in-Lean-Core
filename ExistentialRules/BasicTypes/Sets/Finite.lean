import ExistentialRules.BasicTypes.Sets.Set
import ExistentialRules.BasicTypes.Functions.Function

namespace Set

  def finite' (S : Set α) : Prop := ∃ (n : Nat) (h : α → Nat), h.isBijective S (fun e => (e < n))

  --noncomputable def fin_size (S : Set α) (fin : S.finite') : Nat :=
  --  ite (¬ ∃ e, e ∈ S) (0) (1 + S.diff (by exists ∃ e, e ∈ S))
  -- We need to define empty function for that to work
  -- Note that ∅ → X ≠ ∅ → Y ↔ X ≠ Y


  theorem empty_if_finite' (S : Set α) : S = ∅ → S.finite' := by
    intro S_def
    exists 1, fun e => 0
    constructor
    intro x y ⟨x_in, y_in⟩ f_eq
    grind
    unfold Function.isSurjective
    intro n
    sorry


  theorem singleton_is_finite' (a : α) (S : Set α) : S = Set.singleton a → S.finite' := by
    intro S_def
    unfold Set.finite'
    exists 1, fun e => 0
    constructor
    intro x y ⟨x_in, y_in⟩ f_eq
    grind
    intro n
    exists a
    rintro ⟨h1, h2⟩
    simp
    simp at h1
    rw [h1]

  theorem finite'_union_is_finite' (A B : Set α) (a_fin : A.finite') (b_fin : B.finite') : (A ∪ B).finite' := by
    rcases a_fin with ⟨n1, f1, inj1, surj1⟩
    rcases b_fin with ⟨n2, f2, inj2, surj2⟩
    unfold union finite'
    let f : α → Nat := fun x =>
      have dec := Classical.propDecidable (x ∈ A)
      ite (x ∈ A) (f1 x) ((f2 x) + n1)
    exists (n1 + n2), f
    sorry

end Set
