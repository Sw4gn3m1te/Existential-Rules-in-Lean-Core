import ExistentialRules.Models.Cores


theorem contrapose (A B : Prop) : A → B ↔ ¬ B → ¬ A := by grind


namespace Function

  theorem id_is_injective (A : Set α) : Function.injective_for_domain_set id A := by
  intro a b a_in b_in eq
  simp at eq
  exact eq

theorem id_is_surjective (A : Set α) : Function.surjective_for_domain_and_image_set id A A := by
  intro a a_in
  exists a

end Function


namespace Option

  @[grind]
  theorem isSomeIffNeqNone (o : Option α) : o.isSome ↔ o ≠ none := by
    constructor
    grind
    intro h
    unfold Option.isSome
    split
    next => grind
    next => grind

  theorem NeqNoneIfIsSome (o : Option α) (a : α) : o = some a →  o ≠ none := by
    intro h
    exact (isSomeIffNeqNone o).mp (Option.isSome_of_mem h)

  @[simp, grind]
  def castToMemIfNotNone (o : Option α) (not_none : o ≠ none) : α :=
      match o with
        | some o => o
        | none => by contradiction

  @[simp, grind]
  def castToMemIfIsSome (o : Option α) (is_some : o.isSome) : α :=
    match o with
      | some o => o
      | none => by contradiction

  @[simp]
  def castisSomeIfEqSome (o : Option α) (a : α) : (o = some a) → o.isSome := by apply Option.isSome_of_mem

  @[simp, grind]
    theorem isNone_and_isSome_False (o : Option α) : o.isNone ∧ o.isSome → False := by
      simp_all

end Option


namespace Set

    @[grind]
  theorem subsetOfFiniteIsFinite [DecidableEq α] (A B : Set α) (b_fin : B.finite) (sub : A ⊆ B) : A.finite := by
    exact Set.finite_of_subset_finite b_fin sub

  @[grind]
  theorem unionOfFinteIsFinte [DecidableEq α] (A B : Set α) : A.finite ∧ B.finite ↔ (A ∪ B).finite := by
    constructor
    intro ⟨⟨al, al_nodup, al_eq⟩, ⟨bl, bl_nodup, bl_eq⟩⟩
    have dec := Classical.propDecidable
    exists (al ++ bl).eraseDupsKeepRight
    constructor
    exact List.nodup_eraseDupsKeepRight (al ++ bl)
    intro e
    rw [List.mem_eraseDupsKeepRight]
    constructor
    intro in_albl
    rw [List.mem_append] at in_albl
    rcases in_albl with in_a | in_b
    specialize al_eq e
    left
    rw [← al_eq]
    exact in_a
    specialize bl_eq e
    right
    rw [← bl_eq]
    exact in_b
    intro in_ab
    rw [@List.mem_append]
    rcases in_ab with in_a | in_b
    specialize al_eq e
    left
    rw [al_eq]
    exact in_a
    specialize bl_eq e
    right
    rw [bl_eq]
    exact in_b
    intro ab_fin
    have a_sub : A ⊆ (A ∪ B) := by exact Set.subset_union_of_subset_left fun e a => a
    have b_sub : B ⊆ (A ∪ B) := by exact Set.subset_union_of_subset_right B A B fun e a => a
    constructor
    exact subsetOfFiniteIsFinite A (A ∪ B) ab_fin a_sub
    exact subsetOfFiniteIsFinite B (A ∪ B) ab_fin b_sub

  @[grind]
  theorem union_iff (A B : Set α) (e : α) : e ∈ A ∪ B ↔ e ∈ A ∨ e ∈ B := by
    exact Eq.to_iff rfl

  @[grind]
  theorem unionSym (A B : Set α) : A ∪ B = B ∪ A := by
    apply Set.ext
    intro e
    grind

  @[grind]
  theorem exListOfSetIfFin (S : Set α) (fin : S.finite) : ∃ (l : List α), ∀ e, e ∈ l ↔ e ∈ S := by
    rcases fin with ⟨l, l_nodup, l_eq⟩
    exact Exists.intro l l_eq

end Set
