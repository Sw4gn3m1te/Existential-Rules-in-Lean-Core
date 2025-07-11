import ExistentialRules.Models.Basic
import ExistentialRules.ChaseSequence.Basic

namespace Set

  def ssubset (X Y : Set α) : Prop := X ⊆ Y ∧ X ≠ Y
  infix:50 " ⊂ " => ssubset

  theorem ext (X Y : Set α) : (∀ e, e ∈ X ↔ e ∈ Y) -> X = Y := by
    intro h
    apply funext
    intro e
    apply propext
    specialize h e
    exact h

  theorem ext_iff (X Y : Set α) : (∀ e, e ∈ X ↔ e ∈ Y) ↔ X = Y := by
    constructor
    . apply ext
    . intro h e; rw [h]

  def singleton (a : α) : Set α := fun x => x = a

  theorem not_empty_contains_element (X : Set α) : X ≠ ∅ -> ∃ e, e ∈ X := by
      intro neq
      apply Classical.byContradiction
      intro contra
      apply neq
      apply funext
      intro x
      apply propext
      simp only [not_exists] at contra
      unfold Set.empty
      specialize contra x
      unfold Set.element at contra
      simp only [iff_false]
      exact contra

  theorem eq_empty_of_subset_empty {α : Type u} {X : Set α} : X ⊆ ∅ → X = ∅ := by
    intro subset
    apply Classical.byContradiction
    intro contra
    rw [← ne_eq] at contra
    have ex_elem : ∃ e, e ∈ X := by
      apply Set.not_empty_contains_element
      exact contra
    rcases ex_elem with ⟨e, e_in_X⟩
    rw [Set.subset] at subset
    specialize subset e e_in_X
    contradiction

  theorem empty_subset_of_each (X : Set α) : ∅ ⊆ X := by
    unfold Set.subset
    intro e e_in_empty
    contradiction

  theorem subset_sym_eq (X Y : Set α) : X ⊆ Y ∧ Y ⊆ X ↔ X = Y := by
    constructor
    intro ⟨x_sub_y, y_sub_x⟩
    funext e
    exact Eq.propIntro (x_sub_y e) (y_sub_x e)
    intro eq
    rw [eq]
    simp only [and_self]
    apply Set.subset_refl

  theorem mem_singleton_iff_eq (e : α) : f ∈ (Set.singleton e) ↔ e = f := by
    unfold Set.singleton
    constructor
    intro h
    apply Classical.byContradiction
    intro contra
    exact Ne.elim (fun a => contra (id (Eq.symm a))) h
    intro h
    exact id (Eq.symm h)

  theorem subset_trans_mem (X : Set α) : e ∈ X ∧ X ⊆ Y → e ∈ Y := by
    intro a
    obtain ⟨left, right⟩ := a
    apply right
    simp_all only

  theorem union_iff (X Y : Set α) (e : α) : e ∈ (X ∪ Y) ↔ e ∈ X ∨ e ∈ Y := by
    exact Eq.to_iff rfl


-- mathlib yoinks
theorem Eq.subset {α} {s t : Set α} : s = t → s ⊆ t :=
  fun h₁ _ h₂ => by rw [← h₁]; exact h₂

end Set


namespace List

  def toSet' (l : List α) : α → Prop := fun x => x ∈ l

  theorem length_le_of_nodup_of_all_mem [DecidableEq α] (as bs : List α) (nodup : as.Nodup) (all_mem : ∀ e, e ∈ as -> e ∈ bs) : as.length ≤ bs.length := by
    induction as generalizing bs with
    | nil => simp
    | cons a as ih =>
      let bs_without_a := bs.erase a
      simp at nodup
      specialize ih
        bs_without_a
        nodup.right
        (by intro c c_mem; rw [List.mem_erase_of_ne]; apply all_mem; simp [c_mem]; intro contra; rw [contra] at c_mem; apply nodup.left; exact c_mem)
      rw [List.length_erase_of_mem (by apply all_mem; simp)] at ih
      rw [Nat.le_sub_one_iff_lt (by apply List.length_pos_of_mem; apply all_mem a; simp)] at ih
      apply Nat.succ_le_of_lt
      exact ih

  theorem equiv_of_nodup_of_length_eq_of_all_mem [DecidableEq α] (as bs : List α) (nodup : as.Nodup) (eq_length : as.length = bs.length) (all_mem : ∀ e, e ∈ as -> e ∈ bs) : ∀ e, e ∈ as ↔ e ∈ bs := by
    intro e
    constructor
    . apply all_mem
    . intro mem_bs
      induction as generalizing bs e with
      | nil => cases bs; simp at mem_bs; simp at eq_length
      | cons a as ih =>
        let bs_without_a := bs.erase a
        simp at nodup
        specialize ih
          bs_without_a
          nodup.right
          (by rw [List.length_erase_of_mem, ← eq_length]; simp; apply all_mem; simp)
          (by intro c c_mem; rw [List.mem_erase_of_ne]; apply all_mem; simp [c_mem]; intro contra; rw [contra] at c_mem; apply nodup.left; exact c_mem)
        cases Decidable.em (e = a) with
        | inl eq => simp [eq]
        | inr neq =>
          simp; apply Or.inr
          apply ih
          rw [List.mem_erase_of_ne]
          exact mem_bs
          exact neq


  theorem eq_empty_if_len_zero (l : List α) : l.length = 0 → l.toSet = ∅ := by
    simp only [List.length_eq_zero_iff]
    intro l_empty
    rw [l_empty]
    rfl

  theorem empty_eq_empty_set : @List.toSet α [] = ∅ := by
    rfl

  theorem empty_eq_empty_set' : @List.toSet' α [] = ∅ := by
    unfold List.toSet'
    funext a
    simp only [List.not_mem_nil]
    apply propext
    constructor
    intro contra
    contradiction
    intro contra
    contradiction

  theorem non_empty_has_length_gt_zero (l : List α) : l.length > 0 ↔ l ≠ [] := by
    constructor
    intro l_gt_zero l_empty
    unfold List.length at l_gt_zero
    cases l with
      | nil =>
        contradiction
      | cons hd tl =>
        contradiction
    intro l_empty
    cases l with
      | nil =>
        contradiction
      | cons hd tl =>
        simp

  theorem len_gt_one_not_empty (l : List α) : l.length ≥ 1 → ¬ l.isEmpty := by
    intro len_geq_1
    unfold List.length at len_geq_1
    cases l with
      | nil =>
        contradiction
      | cons hd tl =>
        simp

  theorem ex_elem_outside_prop_subset (l : List α) (subset_l : sub ⊆ l) (neq_l : ¬sub.toSet = l.toSet) : ∃ (e : α), e ∈ l ∧ ¬ e ∈ sub := by
    apply Classical.byContradiction
    intro contra
    simp only [not_exists, not_and, Classical.not_not] at contra
    apply neq_l
    funext a
    ext
    change a ∈ sub.toSet ↔ a ∈ l.toSet
    simp only [List.mem_toSet]
    exact ⟨fun h' => subset_l h', contra a⟩

  theorem mem_iff_toSet_mem (l : List α) (e : α) : e ∈ l ↔ e ∈ l.toSet := by
    induction l with
      | nil =>
        simp only [List.not_mem_nil, false_iff]
        exact id
      | cons hd tl ih =>
        unfold List.toSet
        simp only [List.mem_cons]
        constructor
        intro e_in_l
        change e ∈ fun e => e = hd ∨ e ∈ tl.toSet
        rcases e_in_l with e_hd | e_tl
        left
        exact e_hd
        right
        rw [← ih]
        exact e_tl
        intro e_tls
        change e ∈ fun e => e = hd ∨ e ∈ tl.toSet at e_tls
        rcases e_tls with e_hd | e_tl
        left
        exact e_hd
        right
        rw [ih]
        exact e_tl

  theorem toSet_iff_toSet' (l : List α) : l.toSet = l.toSet' := by
    cases l with
      | nil =>
        funext a
        apply propext
        rw [List.empty_eq_empty_set', List.empty_eq_empty_set]
      | cons hd tl =>
        funext a
        apply propext
        constructor
        intro h
        change a ∈ (hd :: tl)
        simp only [List.mem_cons]
        cases h with
          | inl h =>
            left
            apply h
          | inr h =>
            right
            exact (mem_iff_toSet_mem tl a).mpr h
        intro h
        unfold List.toSet
        change a ∈ (hd :: tl).toSet
        change a ∈ fun e => e = hd ∨ a ∈ tl.toSet
        rcases h with a_hs | ⟨a_tl, h⟩
        left
        rfl
        right
        exact (mem_iff_toSet_mem tl a).mp h

  theorem subset_mono [DecidableEq α] (l tl : List α) (hd : α) (subset : (hd :: tl) ⊆ l) : tl ⊆ l := by
    induction (hd :: tl) with
      | nil =>
        exact List.subset_of_cons_subset subset
      | cons hd2 tl2 ih =>
        exact ih

  theorem subset_if_sublist (l sub : List α) : sub ⊆ l → sub.toSet ⊆ l.toSet := by
    intro subset
    repeat rw [List.toSet_iff_toSet']
    apply subset

  theorem to_set_eq_if_eq (l1 l2 : List α) : l1 = l2 → l1.toSet = l2.toSet := by
    exact fun a => congrArg toSet a

  theorem length_lt_of_proper_subset [DecidableEq α] (l sub : List α) (sub_nodup : sub.Nodup) (subset : sub ⊆ l) (neq : sub.toSet ≠ l.toSet) : sub.length < l.length := by
    induction sub generalizing l with
      | nil =>
        exact List.length_lt_of_drop_ne_nil fun a => neq (congrArg List.toSet (id (Eq.symm a)))
      | cons hd tl ih =>
        have hd_in_l : hd ∈ l := by
          rw [mem_iff_toSet_mem]
          have subset' : (hd::tl).toSet ⊆ l.toSet := by
            exact subset_if_sublist l (hd :: tl) subset
          unfold Set.subset at subset'
          specialize subset' hd
          apply subset'
          unfold List.toSet
          left
          rfl
        have subset' : (hd :: tl).toSet ⊆ l.toSet := by
          exact subset_if_sublist l (hd :: tl) subset
        have hd_nin_tl : ¬ hd ∈ tl := by
          rw [List.nodup_cons] at sub_nodup
          exact sub_nodup.1
        have tl_nodup : tl.Nodup := by
          unfold List.Nodup
          exact List.Pairwise.of_cons sub_nodup
        have tl_sub_lerase : tl ⊆ (l.erase hd) := by
          intro e e_in_tl
          refine (List.mem_erase_of_ne ?_).mpr ?_
          have e_in_hdtl : e ∈ (hd :: tl) := by exact List.mem_cons_of_mem hd e_in_tl
          by_cases c : (e = hd)
          unfold List.Nodup at sub_nodup
          exact ne_of_mem_of_not_mem e_in_tl hd_nin_tl
          exact c
          have : e ∈ (hd :: tl) := by exact List.mem_cons_of_mem hd e_in_tl
          rw [mem_iff_toSet_mem] at this
          specialize subset' e this
          exact (mem_iff_toSet_mem l e).mpr subset'

        have lerase_len_lt : (l.erase hd).length = l.length - 1 := by
          exact List.length_erase_of_mem hd_in_l
        have tl_neq_lerase : tl.toSet ≠ (l.erase hd).toSet := by
          intro contra
          apply neq
          apply Set.ext
          intro e
          rw [List.mem_toSet]
          rw [List.mem_toSet]
          rw [← Set.ext_iff] at contra
          specialize contra e
          rw [List.mem_toSet] at contra
          rw [List.mem_toSet] at contra
          rw [List.mem_cons]
          constructor
          . intro e_mem
            cases e_mem with
            | inl e_mem => rw [e_mem]; exact hd_in_l
            | inr e_mem =>
              rw [← List.mem_erase_of_ne]
              . rw [← contra]; exact e_mem
              . intro contra
                apply hd_nin_tl
                rw [← contra]
                exact e_mem
          . intro e_mem
            cases Decidable.em (e = hd) with
            | inl e_eq_hd => apply Or.inl; exact e_eq_hd
            | inr e_neq_hd =>
              apply Or.inr
              rw [contra]
              rw [List.mem_erase_of_ne]
              . exact e_mem
              . exact e_neq_hd

        specialize ih (l.erase hd) tl_nodup tl_sub_lerase tl_neq_lerase
        have tl_len_eq_hdtl_len_lt : tl.length = (hd::tl).length -1 := by rfl
        rw [lerase_len_lt, tl_len_eq_hdtl_len_lt] at ih
        exact Nat.succ_lt_of_lt_pred ih

  theorem ex_elem_to_set_neq_empty (l : List α) (e : α) (e_in_l : e ∈ l) : l.toSet ≠ ∅ := by
    apply Classical.byContradiction
    intro contra
    simp only [ne_eq, Classical.not_not] at contra
    rw [List.mem_iff_toSet_mem] at e_in_l
    unfold Set.element at e_in_l
    rw [contra] at e_in_l
    contradiction

  theorem eq_mem_iff_eq_to_set (l1 l2 : List α) : (∀ e, e ∈ l1 ↔ e ∈ l2) ↔ l1.toSet = l2.toSet := by
    constructor
    intro e
    funext e'
    apply propext
    specialize e e'
    repeat rw [List.mem_iff_toSet_mem, Set.element] at e
    exact e
    intro h e
    repeat rw [List.mem_iff_toSet_mem]
    rw [h]

  theorem toSet_is_finite [DecidableEq α] (l : List α) : l.toSet.finite := by
    sorry


end List

namespace Function

  def image_set (f : α -> β) (A : Set α) : Set β := fun b => ∃ a, a ∈ A ∧ f a = b

  def injective_for_domain_set (f : α -> β) (domain : Set α) : Prop := ∀ a a', a ∈ domain -> a' ∈ domain -> f a = f a' -> a = a'
  def surjective_for_domain_and_image_set (f : α -> β) (domain : Set α) (image : Set β) : Prop := ∀ b, b ∈ image -> ∃ a, a ∈ domain ∧ f a = b

  theorem injective_of_injective_compose (f : α -> β) (g : β -> γ) (domain : Set α) :
      injective_for_domain_set (g ∘ f) domain -> injective_for_domain_set f domain := by
    intro inj a a' a_dom a'_dom image_eq
    apply inj a a' a_dom a'_dom
    simp [image_eq]

  theorem surjective_of_surjective_from_subset (f : α -> β) (domain : Set α) (image : Set β) :
      f.surjective_for_domain_and_image_set domain image ->
      ∀ domain', domain ⊆ domain' -> f.surjective_for_domain_and_image_set domain' image := by
    intro surj dom' dom'_sub b b_mem
    rcases surj b b_mem with ⟨a, a_mem, a_eq⟩
    exists a
    constructor
    . apply dom'_sub; exact a_mem
    . exact a_eq

  theorem surjective_of_surjective_compose (f : α -> β) (g : β -> γ) (domain : Set α) (image : Set γ) :
      surjective_for_domain_and_image_set (g ∘ f) domain image ->
      surjective_for_domain_and_image_set g (f.image_set domain) image := by
    intro surj b b_mem
    rcases surj b b_mem with ⟨a, a_mem, a_eq⟩
    exists f a
    constructor
    . exists a
    . exact a_eq

  def injective_for_domain_list (f : α -> β) (domain : List α) : Prop := ∀ a a', a ∈ domain -> a' ∈ domain -> f a = f a' -> a = a'
  def surjective_for_domain_and_image_list (f : α -> β) (domain : List α) (image : List β) : Prop := ∀ b, b ∈ image -> ∃ a, a ∈ domain ∧ f a = b

  theorem injective_set_list_equiv (f : α -> β) (domain_set : Set α) (domain_list : List α) (eq : ∀ e, e ∈ domain_list ↔ e ∈ domain_set) : f.injective_for_domain_set domain_set ↔ f.injective_for_domain_list domain_list := by
    constructor
    . intro h a a' a_mem a'_mem f_eq
      apply h
      . rw [← eq]; assumption
      . rw [← eq]; assumption
      . exact f_eq
    . intro h a a' a_mem a'_mem f_eq
      apply h
      . rw [eq]; assumption
      . rw [eq]; assumption
      . exact f_eq

  theorem surjective_set_list_equiv (f : α -> β)
      (domain_set : Set α) (domain_list : List α) (eq_domain : ∀ e, e ∈ domain_list ↔ e ∈ domain_set)
      (image_set : Set β) (image_list : List β) (eq_image : ∀ e, e ∈ image_list ↔ e ∈ image_set) :
      f.surjective_for_domain_and_image_set domain_set image_set ↔ f.surjective_for_domain_and_image_list domain_list image_list := by
    constructor
    . intro h b b_mem
      specialize h b (by rw [← eq_image]; exact b_mem)
      rcases h with ⟨a, a_mem, a_eq⟩
      exists a
      constructor
      . rw [eq_domain]; exact a_mem
      . exact a_eq
    . intro h b b_mem
      specialize h b (by rw [eq_image]; exact b_mem)
      rcases h with ⟨a, a_mem, a_eq⟩
      exists a
      constructor
      . rw [← eq_domain]; exact a_mem
      . exact a_eq

  theorem injective_for_domain_list_cons (f : α -> β) (hd : α) (tl : List α) : f.injective_for_domain_list (hd::tl) -> f.injective_for_domain_list tl := by
    intro h a a' a_mem a'_mem eq
    apply h
    . simp [a_mem]
    . simp [a'_mem]
    . exact eq

  def image [DecidableEq β] (f : α -> β) : List α -> List β
  | [] => []
  | hd::tl =>
    let tl_img := image f tl
    if f hd ∈ tl_img then tl_img else (f hd)::tl_img

  theorem mapping_mem_image_of_mem [DecidableEq β] (f : α -> β) (domain : List α) : ∀ a, a ∈ domain -> f a ∈ (image f domain) := by
    intro a a_mem
    induction domain with
    | nil => simp at a_mem
    | cons hd tl ih =>
      simp [image]
      cases Decidable.em (f hd ∈ image f tl) with
      | inl hd_mem => simp [image, hd_mem]; cases a_mem; exact hd_mem; apply ih; assumption
      | inr hd_not_mem => simp [image, hd_not_mem]; cases a_mem; apply Or.inl; rfl; apply Or.inr; apply ih; assumption

  theorem nodup_image [DecidableEq β] (f : α -> β) (domain : List α) : (image f domain).Nodup := by
    induction domain with
    | nil => simp [image]
    | cons hd tl ih =>
      cases Decidable.em (f hd ∈ image f tl) with
      | inl hd_mem => simp [image, hd_mem]; exact ih
      | inr hd_not_mem => simp [image, hd_not_mem]; exact ih

  theorem length_image [DecidableEq β] (f : α -> β) (domain : List α) : (image f domain).length ≤ domain.length := by
    induction domain with
    | nil => simp [image]
    | cons hd tl ih => simp [image]; split; apply Nat.le_trans; exact ih; simp; simp; exact ih

  theorem surjective_on_own_image [DecidableEq β] (f : α -> β) (domain : List α) : f.surjective_for_domain_and_image_list domain (image f domain) := by
    induction domain with
    | nil => simp [surjective_for_domain_and_image_list, image]
    | cons hd tl ih =>
      intro b b_mem
      cases Decidable.em (f hd ∈ image f tl) with
      | inl hd_mem => simp [image, hd_mem] at b_mem; rcases ih b b_mem with ⟨a, ha⟩; exists a; simp [ha]
      | inr hd_not_mem =>
        simp [image, hd_not_mem] at b_mem
        cases b_mem with
        | inr b_mem => rcases ih b b_mem with ⟨a, ha⟩; exists a; simp [ha]
        | inl b_mem => exists hd; simp [b_mem]

  theorem image_contained_of_closed [DecidableEq α] (f : α -> α) (domain : List α) (closed : ∀ e, e ∈ domain -> f e ∈ domain) : ∀ e, e ∈ image f domain -> e ∈ domain := by
    intro b b_mem
    rcases surjective_on_own_image f domain b b_mem with ⟨a, a_mem, a_eq⟩
    rw [← a_eq]
    apply closed
    exact a_mem

  theorem injective_iff_length_image_eq_of_nodup [DecidableEq β] (f : α -> β) (domain : List α) (nodup : domain.Nodup) : f.injective_for_domain_list domain ↔ (image f domain).length = domain.length := by
    constructor
    . intro inj
      induction domain with
      | nil => simp [image]
      | cons hd tl ih =>
        cases Decidable.em (f hd ∈ image f tl) with
        | inl hd_mem =>
          apply False.elim
          simp at nodup
          apply nodup.left
          rcases surjective_on_own_image f tl (f hd) hd_mem with ⟨a, a_mem, a_eq⟩
          specialize inj a hd (by simp [a_mem]) (by simp) a_eq
          rw [← inj]
          exact a_mem
        | inr hd_not_mem =>
          simp [image, hd_not_mem]
          apply ih
          . simp at nodup; exact nodup.right
          . apply injective_for_domain_list_cons; exact inj
    . intro length_eq
      induction domain with
      | nil => simp [injective_for_domain_list]
      | cons hd tl ih =>
        cases Decidable.em (f hd ∈ image f tl) with
        | inl hd_mem =>
          simp [image, hd_mem] at length_eq
          have contra := length_image f tl
          rw [length_eq] at contra
          simp [Nat.succ_le] at contra
        | inr hd_not_mem =>
          simp [image, hd_not_mem] at length_eq
          intro a a' a_mem a'_mem eq
          cases a_mem
          . cases a'_mem
            . rfl
            . apply False.elim
              apply hd_not_mem
              rw [eq]
              apply mapping_mem_image_of_mem
              assumption
          . cases a'_mem
            . apply False.elim
              apply hd_not_mem
              rw [← eq]
              apply mapping_mem_image_of_mem
              assumption
            . simp at nodup
              specialize ih nodup.right length_eq
              apply ih <;> assumption

  theorem surjective_on_target_iff_all_in_image [DecidableEq β] (f : α -> β) (domain : List α) (target_image : List β) : f.surjective_for_domain_and_image_list domain target_image ↔ ∀ b, b ∈ target_image -> b ∈ image f domain := by
    constructor
    . intro surj b b_mem
      specialize surj b b_mem
      rcases surj with ⟨a, a_mem, a_eq⟩
      rw [← a_eq]
      apply mapping_mem_image_of_mem
      exact a_mem
    . intro h b b_mem
      apply surjective_on_own_image
      apply h
      exact b_mem

  theorem injective_of_surjective_of_nodup [DecidableEq α] (f : α -> α) (l : List α) (nodup : l.Nodup) : f.surjective_for_domain_and_image_list l l -> f.injective_for_domain_list l := by
    intro surj
    rw [surjective_on_target_iff_all_in_image] at surj
    rw [injective_iff_length_image_eq_of_nodup _ _ nodup]
    rw [Nat.eq_iff_le_and_ge]
    constructor
    . exact length_image f l
    . exact List.length_le_of_nodup_of_all_mem l (image f l) nodup surj

  theorem injective_iff_surjective_of_nodup_of_closed [DecidableEq α] (f : α -> α) (l : List α) (nodup : l.Nodup) (closed : ∀ e, e ∈ l -> f e ∈ l) : f.injective_for_domain_list l ↔ f.surjective_for_domain_and_image_list l l := by
    constructor
    . intro inj

      have : ∀ e, e ∈ image f l ↔ e ∈ l := by
        apply List.equiv_of_nodup_of_length_eq_of_all_mem
        . apply nodup_image
        . rw [injective_iff_length_image_eq_of_nodup] at inj
          rw [inj]
          exact nodup
        . intro e e_mem
          apply image_contained_of_closed
          . exact closed
          . exact e_mem

      rw [surjective_on_target_iff_all_in_image]
      intro b
      apply (this b).mpr
    . apply injective_of_surjective_of_nodup; exact nodup

  theorem closed_of_injective_of_surjective_of_nodup [DecidableEq α] (f : α -> α) (l : List α) (nodup : l.Nodup) : f.injective_for_domain_list l -> f.surjective_for_domain_and_image_list l l -> ∀ e, e ∈ l -> f e ∈ l := by
    intro inj surj
    intro e e_mem
    rw [List.equiv_of_nodup_of_length_eq_of_all_mem l (image f l) nodup]
    . apply mapping_mem_image_of_mem; exact e_mem
    . rw [(injective_iff_length_image_eq_of_nodup f l nodup).mp inj]
    . exact (surjective_on_target_iff_all_in_image f l l).mp surj

  theorem image_eq_eraseDupsKeepRight_map [DecidableEq β] {f : α -> β} {l : List α} : image f l = (l.map f).eraseDupsKeepRight := by
    induction l with
    | nil => simp [image, List.eraseDupsKeepRight]
    | cons hd tl ih =>
      simp only [image, List.eraseDupsKeepRight, List.map_cons]
      simp only [ih, List.mem_eraseDupsKeepRight]

end Function

namespace GroundTermMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

  def strong (h : GroundTermMapping sig) (domain : Set (GroundTerm sig)) (A B : FactSet sig) : Prop :=
    ∀ (e : Fact sig), (∀ t, t ∈ e.terms -> t ∈ domain) -> ¬ e ∈ A -> ¬ (h.applyFact e) ∈ B

  theorem strong_of_compose_strong (g h : GroundTermMapping sig) (domain : Set (GroundTerm sig)) (A B C : FactSet sig) :
      h.isHomomorphism B C -> GroundTermMapping.strong (h ∘ g) domain A C -> g.strong domain A B := by
    intro h_hom compose_strong
    intro e e_dom e_not_mem_a e_mem_b
    apply compose_strong e
    . exact e_dom
    . exact e_not_mem_a
    . apply h_hom.right (GroundTermMapping.applyFact (h ∘ g) e)
      exists (g.applyFact e)
      constructor
      . exact e_mem_b
      . rw [applyFact_compose]
        simp

end GroundTermMapping


section HomomorphismRepetition

-- TODO: I think a lot of this can be generalized to arbitrary Functions

namespace GroundTermMapping

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

  def repeat_hom (h : GroundTermMapping sig) : Nat -> GroundTermMapping sig
  | .zero => id
  | .succ j => h ∘ (h.repeat_hom j)

  theorem repeat_hom_swap (h : GroundTermMapping sig) (i : Nat) : ∀ t, h (h.repeat_hom i t) = (h.repeat_hom i) (h t) := by
    intro t
    induction i with
    | zero => unfold repeat_hom; simp
    | succ i ih =>
      unfold repeat_hom
      simp
      rw [ih]

  theorem repeat_hom_add (h : GroundTermMapping sig) (n m : Nat) : ∀ t, h.repeat_hom (n + m) t = h.repeat_hom n (h.repeat_hom m t) := by
    intro t
    induction m with
    | zero => simp [repeat_hom]
    | succ m ih =>
      conv => left; unfold repeat_hom
      conv => right; right; unfold repeat_hom
      simp
      rw [ih]
      rw [h.repeat_hom_swap]

  theorem repeat_hom_cycle_mul (h : GroundTermMapping sig) (t : GroundTerm sig) (n : Nat) : h.repeat_hom n t = t -> ∀ m, h.repeat_hom (n * m) t = t := by
    intro cycle m
    induction m with
    | zero => simp [repeat_hom]
    | succ m ih =>
      rw [Nat.mul_add]
      rw [repeat_hom_add]
      simp
      rw [cycle, ih]

  theorem repeat_hom_move_cycle (h : GroundTermMapping sig) (t : GroundTerm sig) (n : Nat) : h.repeat_hom n t = t -> ∀ s m, h.repeat_hom m t = s -> h.repeat_hom n s = s := by
    intro cycle s m reaches_s
    induction m generalizing t with
    | zero => simp [repeat_hom] at reaches_s; rw [← reaches_s]; exact cycle
    | succ m ih =>
      apply ih (h t)
      . rw [← h.repeat_hom_swap]
        rw [cycle]
      . simp [repeat_hom] at reaches_s
        rw [h.repeat_hom_swap] at reaches_s
        exact reaches_s

  theorem repeat_each_reaches_self_of_each_reachable (h : GroundTermMapping sig) (ts : List (GroundTerm sig)) (each_reachable : ∀ t, t ∈ ts -> ∃ k, 1 ≤ k ∧ ∃ s, s ∈ ts ∧ (h.repeat_hom k) s = t) : (∀ s, s ∈ ts -> ∃ l, 1 ≤ l ∧ (h.repeat_hom l) s = s) := by
    induction ts with
    | nil => simp
    | cons hd tl ih =>
      specialize ih (by
        intro t t_mem
        have each_reachable_for_t := each_reachable t (by simp [t_mem])
        rcases each_reachable_for_t with ⟨k, k_le, s, s_mem, s_eq⟩
        simp at s_mem
        cases s_mem with
        | inr s_mem => exists k; constructor; exact k_le; exists s
        | inl s_mem =>
          have each_reachable_for_s := each_reachable s (by simp [s_mem])
          rcases each_reachable_for_s with ⟨l, l_le, u, u_mem, u_eq⟩
          simp at u_mem
          cases u_mem with
          | inl u_mem =>
            exists (((k / l) + 1) * l)
            constructor
            .
              rw [Nat.add_mul]
              apply Nat.le_trans
              . exact k_le
              . apply Nat.le_of_lt
                simp
                -- NOTE: taken from https://github.com/leanprover-community/mathlib4/blob/3f813de52d8cffaa73e27edd62364eec90eac633/Mathlib/Data/Nat/Defs.lean#L473-L474
                rw [← Nat.succ_mul, ← Nat.div_lt_iff_lt_mul (by apply Nat.lt_of_succ_le; exact l_le)]; exact Nat.lt_succ_self _
            . exists t
              constructor
              . exact t_mem
              . apply h.repeat_hom_move_cycle s
                . rw [Nat.mul_comm]
                  apply h.repeat_hom_cycle_mul
                  rw [u_mem, ← s_mem] at u_eq
                  exact u_eq
                . exact s_eq
          | inr u_mem =>
            exists (k + l)
            constructor
            . apply Nat.le_add_right_of_le; exact k_le
            . exists u
              constructor
              . exact u_mem
              . rw [GroundTermMapping.repeat_hom_add]
                rw [u_eq, s_eq]
      )

      intro s s_mem
      simp at s_mem
      cases s_mem with
      | inl s_mem =>
        specialize each_reachable s (by rw [s_mem]; simp)
        rcases each_reachable with ⟨k, k_le, t, t_mem, t_eq⟩
        simp at t_mem
        cases t_mem with
        | inl t_mem => exists k; constructor; exact k_le; rw [t_mem, ← s_mem] at t_eq; exact t_eq
        | inr t_mem =>
          specialize ih t t_mem
          rcases ih with ⟨l, l_le, ih⟩
          exists l
          constructor
          . exact l_le
          . apply h.repeat_hom_move_cycle t
            . exact ih
            . exact t_eq
      | inr s_mem =>
        apply ih
        exact s_mem

  theorem repeat_globally_of_each_repeats (h : GroundTermMapping sig) (ts : List (GroundTerm sig)) (each_repeats : ∀ s, s ∈ ts -> ∃ l, 1 ≤ l ∧ (h.repeat_hom l) s = s) :
      ∃ l, 1 ≤ l ∧ ∀ s, s ∈ ts -> (h.repeat_hom l) s = s := by
    induction ts with
    | nil => exists 1; simp
    | cons hd tl ih =>
      specialize ih (by intro s s_mem; apply each_repeats; simp [s_mem])
      rcases ih with ⟨l_ih, l_ih_le, ih⟩
      rcases each_repeats hd (by simp) with ⟨l_hd, l_hd_le, each_repeats⟩
      exists l_hd * l_ih
      constructor
      . apply Nat.le_trans; exact l_hd_le; apply Nat.le_mul_of_pos_right; apply Nat.lt_of_succ_le; exact l_ih_le
      . intro s s_mem
        simp at s_mem
        cases s_mem with
        | inl s_mem => rw [s_mem, h.repeat_hom_cycle_mul]; exact each_repeats
        | inr s_mem => specialize ih s s_mem; rw [Nat.mul_comm, h.repeat_hom_cycle_mul]; exact ih

  theorem exists_repetition_that_is_inverse_of_surj (h : GroundTermMapping sig) (ts : List (GroundTerm sig)) (surj : h.surjective_for_domain_and_image_list ts ts) : ∃ k, ∀ t, t ∈ ts -> (h.repeat_hom k) (h t) = t := by
    have each_repeats := h.repeat_each_reaches_self_of_each_reachable ts (by
      intro t t_mem
      exists 1
      constructor
      . simp
      . simp only [repeat_hom]
        apply surj t t_mem
    )
    have repeats_globally := h.repeat_globally_of_each_repeats ts each_repeats

    rcases repeats_globally with ⟨k, le, repeats_globally⟩

    exists k-1
    intro t t_mem
    have repeat_add := h.repeat_hom_add (k-1) 1 t
    conv at repeat_add => right; right; simp [repeat_hom]
    rw [← repeat_add]
    rw [Nat.sub_one_add_one]
    . apply repeats_globally; exact t_mem
    . apply Nat.ne_zero_of_lt; apply Nat.lt_of_succ_le; exact le

  theorem repeat_hom_id_on_const (h : GroundTermMapping sig) (idOnConst : h.isIdOnConstants) : ∀ i, (h.repeat_hom i).isIdOnConstants := by
    intro i
    induction i with
    | zero => unfold repeat_hom; unfold isIdOnConstants; intro t; split <;> simp
    | succ i ih =>
      intro t
      cases eq : t with
      | func _ _ => simp [GroundTerm.func]
      | const c =>
        simp only [GroundTerm.const]
        unfold repeat_hom
        rw [Function.comp_apply]
        have := GroundTermMapping.apply_constant_is_id_of_isIdOnConstants ih c
        unfold GroundTerm.const at this
        rw [this]
        have := GroundTermMapping.apply_constant_is_id_of_isIdOnConstants idOnConst c
        unfold GroundTerm.const at this
        rw [this]

  variable [DecidableEq sig.P]

  theorem repeat_hom_isHomomorphism (h : GroundTermMapping sig) (fs : FactSet sig) (hom : h.isHomomorphism fs fs) : ∀ i, (h.repeat_hom i).isHomomorphism fs fs := by
    intro i
    constructor
    . apply repeat_hom_id_on_const; exact hom.left
    . induction i with
      | zero =>
        simp [repeat_hom]
        intro f f_mem
        rcases f_mem with ⟨f', f'_mem, f_eq⟩
        have : f = f' := by
          unfold applyFact at f_eq
          . rw [← f_eq]; simp
        rw [this]
        exact f'_mem
      | succ i ih =>
        unfold repeat_hom
        rw [applyFactSet_compose]
        simp
        intro f f_mem
        apply hom.right
        have lifted_ih := h.applyFactSet_subset_of_subset _ _ ih
        apply lifted_ih
        exact f_mem

end GroundTermMapping

end HomomorphismRepetition


namespace FactSet

  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  def isWeakCore (fs : FactSet sig) : Prop :=
    ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs.terms fs fs ∧ h.injective_for_domain_set fs.terms

  def isStrongCore (fs : FactSet sig) : Prop :=
    ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs.terms fs fs ∧ h.injective_for_domain_set fs.terms ∧ h.surjective_for_domain_and_image_set fs.terms fs.terms

  def homSubset (c fs : FactSet sig) : Prop := c ⊆ fs ∧ (∃ (h : GroundTermMapping sig), h.isHomomorphism fs c)

  theorem hom_surjective_of_finite_of_injective (fs : FactSet sig) (finite : fs.finite) : ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.injective_for_domain_set fs.terms -> h.surjective_for_domain_and_image_set fs.terms fs.terms := by
    rcases finite with ⟨l, finite⟩
    intro h isHom inj

    let terms_list := (l.map Fact.terms).flatten.eraseDupsKeepRight
    have nodup_terms_list : terms_list.Nodup := by apply List.nodup_eraseDupsKeepRight
    have mem_terms_list : ∀ e, e ∈ terms_list ↔ e ∈ fs.terms := by
      simp only [terms_list]
      intro e
      rw [List.mem_eraseDupsKeepRight]
      unfold FactSet.terms
      simp
      constructor
      . intro h
        rcases h with ⟨ts, h, ts_mem⟩
        rcases h with ⟨f, f_mem, eq⟩
        exists f
        rw [eq]
        rw [← finite.right f]
        constructor <;> assumption
      . intro h
        rcases h with ⟨f, f_mem, e_mem⟩
        exists f.terms
        constructor
        . exists f; rw [finite.right f]; constructor; exact f_mem; rfl
        . exact e_mem
    have closed : ∀ e, e ∈ terms_list -> h e ∈ terms_list := by
      simp only [terms_list]
      intro e
      rw [List.mem_eraseDupsKeepRight]
      rw [List.mem_eraseDupsKeepRight]
      simp
      intro f f_mem e_in_f
      let f' := h.applyFact f
      have f'_mem : f' ∈ fs := by
        apply isHom.right
        unfold GroundTermMapping.applyFactSet
        exists f
        rw [← finite.right]
        constructor
        . exact f_mem
        . rfl
      exists f'.terms
      constructor
      . exists f'
        constructor
        . rw [finite.right]; exact f'_mem
        . rfl
      . simp only [f', GroundTermMapping.applyFact]
        rw [List.mem_map]
        exists e

    rw [Function.surjective_set_list_equiv h fs.terms terms_list mem_terms_list fs.terms terms_list mem_terms_list]
    rw [← Function.injective_iff_surjective_of_nodup_of_closed h terms_list nodup_terms_list closed]
    rw [← Function.injective_set_list_equiv h fs.terms terms_list mem_terms_list]
    exact inj

  theorem hom_strong_of_finite_of_injective (fs : FactSet sig) (finite : fs.finite) : ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.injective_for_domain_set fs.terms -> h.strong fs.terms fs fs := by
    intro h isHom inj

    intro f ts_mem f_not_mem apply_mem
    apply f_not_mem

    have surj := fs.hom_surjective_of_finite_of_injective finite h isHom inj

    have terms_finite := fs.terms_finite_of_finite finite
    rcases terms_finite with ⟨terms, nodup, equiv⟩

    rw [h.surjective_set_list_equiv fs.terms terms equiv fs.terms terms equiv] at surj
    have ex_inv := h.exists_repetition_that_is_inverse_of_surj terms surj
    rcases ex_inv with ⟨k, inv⟩
    have inv_hom : (h.repeat_hom k).isHomomorphism fs fs := h.repeat_hom_isHomomorphism fs isHom k

    have : f = (h.repeat_hom k).applyFact (h.applyFact f) := by
      rw [← Function.comp_apply (f := (h.repeat_hom k).applyFact)]
      rw [← GroundTermMapping.applyFact_compose]
      unfold GroundTermMapping.applyFact
      rw [Fact.mk.injEq]
      constructor
      . rfl
      . rw [List.map_id_of_id_on_all_mem]
        intro t t_mem
        rw [Function.comp_apply]
        apply inv
        rw [equiv]
        apply ts_mem
        exact t_mem
    rw [this]

    apply inv_hom.right
    apply GroundTermMapping.applyPreservesElement
    exact apply_mem

  theorem isStrongCore_of_isWeakCore_of_finite (fs : FactSet sig) (weakCore : fs.isWeakCore) (finite : fs.finite) : fs.isStrongCore := by
    rcases finite with ⟨l, finite⟩
    unfold isStrongCore
    intro h isHom
    specialize weakCore h isHom
    rcases weakCore with ⟨strong, injective⟩
    constructor
    . exact strong
    constructor
    . exact injective
    . apply hom_surjective_of_finite_of_injective
      . unfold Set.finite; exists l
      . exact isHom
      . exact injective

  theorem every_weakCore_isomorphic_to_strongCore_of_hom_both_ways
      (sc : FactSet sig) (sc_strong : sc.isStrongCore)
      (wc : FactSet sig) (wc_weak : wc.isWeakCore)
      (h_sc_wc h_wc_sc : GroundTermMapping sig) (h_sc_wc_hom : h_sc_wc.isHomomorphism sc wc) (h_wc_sc_hom : h_wc_sc.isHomomorphism wc sc) :
      ∃ (iso : GroundTermMapping sig), iso.isHomomorphism wc sc ∧ iso.strong wc.terms wc sc ∧ iso.injective_for_domain_set wc.terms ∧ iso.surjective_for_domain_and_image_set wc.terms sc.terms := by

    specialize wc_weak (h_sc_wc ∘ h_wc_sc) (by
      apply GroundTermMapping.isHomomorphism_compose
      . exact h_wc_sc_hom
      . exact h_sc_wc_hom
    )

    specialize sc_strong (h_wc_sc ∘ h_sc_wc) (by
      apply GroundTermMapping.isHomomorphism_compose
      . exact h_sc_wc_hom
      . exact h_wc_sc_hom
    )

    exists h_wc_sc
    constructor
    . exact h_wc_sc_hom
    constructor
    -- strong since h_sc_wc ∘ h_wc_sc is strong
    . apply GroundTermMapping.strong_of_compose_strong h_wc_sc h_sc_wc wc.terms wc sc wc h_sc_wc_hom
      exact wc_weak.left
    constructor
    -- injective since h_sc_wc ∘ h_wc_sc is injective
    . apply Function.injective_of_injective_compose h_wc_sc h_sc_wc
      exact wc_weak.right
    -- surjective since h_wc_sc ∘ h_sc_wc is surjective
    . apply Function.surjective_of_surjective_from_subset
      . apply Function.surjective_of_surjective_compose h_sc_wc h_wc_sc sc.terms
        exact sc_strong.right.right
      . intro t t_mem_image
        rcases t_mem_image with ⟨arg, arg_mem, arg_eq⟩
        rcases arg_mem with ⟨f, f_mem, f_eq⟩
        exists (h_sc_wc.applyFact f)
        constructor
        . apply h_sc_wc_hom.right
          exists f
        . unfold GroundTermMapping.applyFact
          rw [List.mem_map]
          exists arg

  theorem strongCore_unique_up_to_isomorphism_with_respect_to_weak_cores
      (fs : FactSet sig)
      (sc : FactSet sig) (sub_sc : sc.homSubset fs) (sc_strong : sc.isStrongCore)
      (wc : FactSet sig) (sub_wc : wc.homSubset fs) (wc_weak : wc.isWeakCore) :
      ∃ (iso : GroundTermMapping sig), iso.isHomomorphism wc sc ∧ iso.strong wc.terms wc sc ∧ iso.injective_for_domain_set wc.terms ∧ iso.surjective_for_domain_and_image_set wc.terms sc.terms := by

    rcases sub_sc with ⟨sub_sc, h_fs_sc, h_fs_sc_hom⟩
    rcases sub_wc with ⟨sub_wc, h_fs_wc, h_fs_wc_hom⟩

    have h_sc_wc_hom : h_fs_wc.isHomomorphism sc wc := by
      constructor
      . exact h_fs_wc_hom.left
      . apply Set.subset_trans (b := h_fs_wc.applyFactSet fs)
        . apply GroundTermMapping.applyFactSet_subset_of_subset
          exact sub_sc
        . exact h_fs_wc_hom.right

    have h_wc_sc_hom : h_fs_sc.isHomomorphism wc sc := by
      constructor
      . exact h_fs_sc_hom.left
      . apply Set.subset_trans (b := h_fs_sc.applyFactSet fs)
        . apply GroundTermMapping.applyFactSet_subset_of_subset
          exact sub_wc
        . exact h_fs_sc_hom.right

    exact every_weakCore_isomorphic_to_strongCore_of_hom_both_ways sc sc_strong wc wc_weak h_fs_wc h_fs_sc h_sc_wc_hom h_wc_sc_hom

  theorem every_universal_weakCore_isomorphic_to_universal_strongCore
      {kb : KnowledgeBase sig}
      (sc : FactSet sig) (sc_universal : sc.universallyModelsKb kb) (sc_strong : sc.isStrongCore)
      (wc : FactSet sig) (wc_universal : wc.universallyModelsKb kb) (wc_weak : wc.isWeakCore) :
      ∃ (iso : GroundTermMapping sig), iso.isHomomorphism wc sc ∧ iso.strong wc.terms wc sc ∧ iso.injective_for_domain_set wc.terms ∧ iso.surjective_for_domain_and_image_set wc.terms sc.terms := by

    rcases sc_universal.right wc wc_universal.left with ⟨h_sc_wc, h_sc_wc_hom⟩
    rcases wc_universal.right sc sc_universal.left with ⟨h_wc_sc, h_wc_sc_hom⟩

    exact every_weakCore_isomorphic_to_strongCore_of_hom_both_ways sc sc_strong wc wc_weak h_sc_wc h_wc_sc h_sc_wc_hom h_wc_sc_hom

  theorem strong_core_of_model_is_model
      {kb : KnowledgeBase sig}
      (fs : FactSet sig) (fs_model : fs.modelsKb kb)
      (sc : FactSet sig) (sc_sub : sc.homSubset fs) (sc_strong : sc.isStrongCore) :
      sc.modelsKb kb := by

    rcases sc_sub with ⟨sc_sub, h_fs_sc, h_fs_sc_hom⟩

    have h_fs_sc_endo_sc : h_fs_sc.isHomomorphism sc sc := by
      constructor
      . exact h_fs_sc_hom.left
      . apply Set.subset_trans (b := h_fs_sc.applyFactSet fs)
        . apply GroundTermMapping.applyFactSet_subset_of_subset
          exact sc_sub
        . exact h_fs_sc_hom.right

    specialize sc_strong h_fs_sc h_fs_sc_endo_sc

    -- TODO: extract this into a general result; check which properties we really need and want here
    have ex_inv : ∃ (inv : GroundTermMapping sig), (∀ t, t ∈ sc.terms -> (h_fs_sc (inv t)) = t) ∧ inv.isHomomorphism sc sc := by
      let inv : GroundTermMapping sig := fun t =>
        have dev := Classical.propDecidable (t ∈ sc.terms)
        if t_mem : t ∈ sc.terms
        then
          Classical.choose (sc_strong.right.right t t_mem)
        else
          t

      have inv_id : (∀ t, t ∈ sc.terms -> (h_fs_sc (inv t)) = t) := by
        intro t t_mem
        unfold inv
        simp [t_mem]
        have spec := Classical.choose_spec (sc_strong.right.right t t_mem)
        exact spec.right
      exists inv

      constructor
      . exact inv_id
      . constructor
        . intro t
          cases eq : t with
          | func _ _ => simp [GroundTerm.func]
          | const c =>
            simp only [GroundTerm.const]
            unfold inv
            cases Classical.em (GroundTerm.const c ∈ sc.terms) with
            | inr n_mem => unfold GroundTerm.const at n_mem; simp [n_mem]
            | inl mem =>
              unfold GroundTerm.const at mem
              simp [mem]
              have spec := Classical.choose_spec (sc_strong.right.right (GroundTerm.const c) mem)
              apply sc_strong.right.left
              . exact spec.left
              . exact mem
              . rw [spec.right]
                have := h_fs_sc_hom.left (GroundTerm.const c)
                simp only [GroundTerm.const] at this
                rw [this]
                simp [GroundTerm.const]
        . intro f f_mem
          rcases f_mem with ⟨f', f'_mem, f_eq⟩
          have strong := sc_strong.left
          unfold GroundTermMapping.strong at strong
          apply Classical.byContradiction
          intro contra
          apply strong f
          . intro t t_mem
            rw [← f_eq] at t_mem
            unfold GroundTermMapping.applyFact at t_mem
            rw [List.mem_map] at t_mem
            rcases t_mem with ⟨t', t'_mem, t_eq⟩
            have t'_mem : t' ∈ sc.terms := by exists f'
            have spec := Classical.choose_spec (sc_strong.right.right t' t'_mem)
            rw [← t_eq]
            unfold inv
            simp [t'_mem]
            exact spec.left
          . exact contra
          . rw [← f_eq]
            rw [← Function.comp_apply (f := h_fs_sc.applyFact), ← GroundTermMapping.applyFact_compose]
            have : f' = GroundTermMapping.applyFact (h_fs_sc ∘ inv) f' := by
              unfold GroundTermMapping.applyFact
              rw [Fact.mk.injEq]
              constructor
              . rfl
              . apply List.ext_getElem
                . rw [List.length_map]
                . intro n _ _
                  rw [List.getElem_map]
                  rw [Function.comp_apply]
                  rw [inv_id]
                  exists f'
                  constructor
                  . exact f'_mem
                  . apply List.getElem_mem
            rw [← this]
            exact f'_mem
    rcases ex_inv with ⟨inv, inv_id, inv_hom⟩

    constructor
    . intro f f_mem
      have : f = h_fs_sc.applyFact f := by
        have prop := kb.db.toFactSet.property.right
        unfold FactSet.isFunctionFree at prop
        unfold Fact.isFunctionFree at prop
        specialize prop f f_mem

        unfold GroundTermMapping.applyFact
        rw [Fact.mk.injEq]
        constructor
        . rfl
        . apply List.ext_getElem
          . rw [List.length_map]
          . intro n _ _
            rw [List.getElem_map]
            rcases (prop f.terms[n] (by apply List.getElem_mem)) with ⟨c, t_eq⟩
            rw [t_eq]
            rw [h_fs_sc_hom.left (GroundTerm.const c)]
      rw [this]
      apply h_fs_sc_hom.right
      apply GroundTermMapping.applyPreservesElement
      apply fs_model.left
      exact f_mem
    . intro r r_mem
      intro subs loaded

      have fs_models_rule := fs_model.right r r_mem (inv ∘ subs)
      specialize fs_models_rule (by
        apply Set.subset_trans (b := inv.applyFactSet sc)
        . intro f f_mem
          unfold GroundSubstitution.apply_function_free_conj at f_mem
          rw [List.mem_toSet, List.mem_map] at f_mem
          rcases f_mem with ⟨a, a_mem, f_eq⟩
          rw [GroundSubstitution.apply_function_free_atom_compose _ _ inv_hom.left] at f_eq
          rw [← f_eq]
          apply GroundTermMapping.applyPreservesElement
          apply loaded
          unfold GroundSubstitution.apply_function_free_conj
          rw [List.mem_toSet, List.mem_map]
          exists a
        . apply Set.subset_trans (b := sc)
          . exact inv_hom.right
          . exact sc_sub
      )
      rcases fs_models_rule with ⟨i, subs', frontier_mapping, sub_mapping⟩

      exists i
      exists (h_fs_sc ∘ subs')
      constructor
      . intro v v_mem
        rw [Function.comp_apply]
        rw [frontier_mapping v v_mem]
        rw [Function.comp_apply]
        rw [inv_id _ (by
          unfold Rule.frontier at v_mem
          rw [List.mem_filter] at v_mem
          have v_mem := v_mem.left
          unfold FunctionFreeConjunction.vars at v_mem
          rw [List.mem_flatMap] at v_mem
          rcases v_mem with ⟨a, a_mem, v_mem⟩
          exists subs.apply_function_free_atom a
          constructor
          . apply loaded
            unfold GroundSubstitution.apply_function_free_conj
            rw [List.mem_toSet, List.mem_map]
            exists a
          . unfold GroundSubstitution.apply_function_free_atom
            rw [List.mem_map]
            exists VarOrConst.var v
            constructor
            . unfold FunctionFreeAtom.variables at v_mem
              apply VarOrConst.filterVars_occur_in_original_list
              exact v_mem
            . rfl
        )]
      . apply Set.subset_trans (b := h_fs_sc.applyFactSet fs)
        . intro f f_mem
          unfold GroundSubstitution.apply_function_free_conj at f_mem
          rw [List.mem_toSet, List.mem_map] at f_mem
          rcases f_mem with ⟨a, a_mem, f_eq⟩
          rw [GroundSubstitution.apply_function_free_atom_compose _ _ h_fs_sc_hom.left] at f_eq
          rw [← f_eq]
          apply GroundTermMapping.applyPreservesElement
          apply sub_mapping
          unfold GroundSubstitution.apply_function_free_conj
          rw [List.mem_toSet, List.mem_map]
          exists a
        . exact h_fs_sc_hom.right

  theorem strong_core_of_universal_model_is_universal_model
      {kb : KnowledgeBase sig}
      (fs : FactSet sig) (fs_univ_model : fs.universallyModelsKb kb)
      (sc : FactSet sig) (sc_sub : sc.homSubset fs) (sc_strong : sc.isStrongCore) :
      sc.universallyModelsKb kb := by
    constructor
    . exact strong_core_of_model_is_model fs fs_univ_model.left sc sc_sub sc_strong
    . intro m m_model
      rcases fs_univ_model.right m m_model with ⟨h, h_hom⟩
      exists h
      constructor
      . exact h_hom.left
      . apply Set.subset_trans (b := h.applyFactSet fs)
        . apply GroundTermMapping.applyFactSet_subset_of_subset
          exact sc_sub.left
        . exact h_hom.right

  theorem every_stong_core_is_weak_core (fs : FactSet sig) : fs.isStrongCore → fs.isWeakCore := by
    unfold isStrongCore isWeakCore
    intro h1 h2 h3
    specialize h1 h2 h3
    exact ⟨h1.1, h1.2.1⟩

  theorem empty_set_is_weak_core (wc : FactSet sig) : wc = ∅ → wc.isWeakCore := by
    intro wc_empty
    rw [wc_empty]
    intro gtm ghom
    constructor
    intro _ _ contra _
    contradiction
    intro h1 h2 h3 h4 h5
    unfold FactSet.terms at h3
    rcases h3 with ⟨_, contra, _⟩
    contradiction

  theorem apply_fact_set_to_empty_is_empty (gtm : GroundTermMapping sig) (fs : FactSet sig) (fs_emtpy : fs = ∅) : gtm.applyFactSet fs ⊆ fs := by
    rw [Set.subset]
    rw [fs_emtpy]
    intro f fu
    have c : f ∈ gtm.applyFactSet ∅ → false := by
      intro ⟨f2, ⟨contra, g⟩⟩
      contradiction
    specialize c fu
    contradiction

  theorem hom_subset_of_empty (fs : FactSet sig) : fs = ∅ → homSubset fs fs := by
    unfold homSubset
    intro fs_empty
    rw [fs_empty]
    simp [Set.subset]
    exists (fun x => x)
    constructor
    unfold GroundTermMapping.isIdOnConstants
    intro gt
    cases eq : gt with
      | func f ts ar =>
        simp [GroundTerm.func]
      | const c =>
        simp [GroundTerm.const]
    · apply apply_fact_set_to_empty_is_empty
      rfl

  theorem id_is_hom (fs : FactSet sig) : GroundTermMapping.isHomomorphism id fs fs := by
    unfold GroundTermMapping.isHomomorphism
    constructor
    unfold GroundTermMapping.isIdOnConstants
    intro gt
    cases eq : gt with
      | func f ts ar =>
        simp [GroundTerm.func]
      | const c =>
        simp [GroundTerm.const]
    · unfold GroundTermMapping.applyFactSet
      intro f1 ⟨f2, f2_in_fs, af⟩
      rw [GroundTermMapping.applyFact] at af
      rw [Fact.mk.injEq] at af
      simp only [List.map_id_fun, id_eq] at af
      rcases af with ⟨lrs, rhs⟩
      have f1_eq_f2 : f1 = f2 := by rw [Fact.mk.injEq, lrs, rhs]; constructor <;> rfl
      rw [f1_eq_f2]
      exact f2_in_fs

  theorem Set.subset_mono' [DecidableEq α] (l tl : List α) (hd : α) (subset : (hd :: tl).toSet ⊆ l.toSet) : tl.toSet ⊆ l.toSet := by
    unfold Set.subset at subset
    unfold Set.subset
    intro  e
    specialize subset e
    intro h
    apply subset
    change e = hd ∨ e ∈ tl.toSet
    right
    exact h

  theorem every_set_has_subset_weakcore : ∀ (fs : FactSet sig), fs ≠ ∅ → ∃ (wc : FactSet sig), wc ⊆ fs ∧ wc.isWeakCore := by
    intro fs fs_nempty
    exists ∅
    constructor
    intro f f_in_empty
    contradiction
    apply empty_set_is_weak_core; rfl

  theorem apply_fact_set_monotone (f : GroundTermMapping sig) (A B : FactSet sig) (subset : A ⊆ B):
    f.applyFactSet B ⊆ A → f.applyFactSet B ⊆ B := by
      intro h
      unfold Set.subset
      intro e e_in_af_B
      unfold Set.subset at subset h
      specialize h e e_in_af_B
      specialize subset e h
      exact subset

  theorem length_eraseDupsKeepRight_eq_of_same_elements [DecidableEq α] (l1 l2 : List α) : (∀ e, e ∈ l1 ↔ e ∈ l2) -> l1.eraseDupsKeepRight.length = l2.eraseDupsKeepRight.length := by
    intro h1
    cases l1 with
      | nil =>
        cases l2 with
        | nil =>
          rfl
        | cons hd' tl' =>
          specialize h1 hd'
          simp_all only [List.not_mem_nil, List.mem_cons, true_or, iff_true]
      | cons hd tl =>
        cases l2 with
        | nil =>
          specialize h1 hd
          simp_all only [List.mem_cons, true_or, List.not_mem_nil, iff_false, not_true_eq_false]
        | cons hd' tl' =>
          simp only [List.mem_cons] at h1
          specialize h1 ?_
          exact hd
          rename_i h2
          specialize h2 hd'
          simp_all only [true_or, true_iff, iff_true]
          cases h1 with
          | inl h =>
            cases h2 with
            | inl h_1 =>
              subst h
              simp_all only
              sorry
            | inr h_2 =>
              subst h
              sorry
          | inr h_1 =>
            cases h2 with
            | inl h =>
              subst h
              sorry
            | inr h_2 =>
              sorry



  theorem s1 (l1 l2 : List α) : l1 ⊆ l2 ∧ l2 ⊆ l1 ↔ l1 = l2 := by
    unfold List.instHasSubset List.Subset
    simp_all only
    sorry

  theorem x (a b : Prop) : ¬ (a ∧ b) ↔ ¬ a ∨ ¬ b := by apply?

  theorem s3 (e f : Fact sig) (gtm : GroundTermMapping sig) : e ∈ gtm.applyFactSet (Set.singleton f) ↔ e = gtm.applyFact f := by
    constructor
    intro h
    unfold GroundTermMapping.applyFactSet at h
    rcases h with ⟨f', f'_single, gtm_f'_eq_e⟩
    rw [← gtm_f'_eq_e]
    have : f = f' := by
      rw [← Set.mem_singleton_iff_eq]
      exact f'_single
    rw [this]
    intro h
    unfold GroundTermMapping.applyFactSet
    rw [h]
    refine Set.subset_trans_mem ?_ ?_
    exact Set.singleton e
    apply Classical.byContradiction
    intro contra
    rw [Classical.not_and_iff_not_or_not] at contra
    rcases contra with lhs | rhs
    rw [h] at lhs
    contradiction
    sorry

  theorem s4 (l tl : List α) (l_def : l = hd :: tl) (e hd : α) : e ∈ (l).toSet ↔ e = hd ∨ e ∈ tl := by
    sorry

  theorem weak_core_of_nex_subset (l : List (Fact sig)):
    ¬ (∃ (sub : List (Fact sig)), sub ⊆ l ∧ sub.toSet ≠ l.toSet ∧ FactSet.homSubset sub.toSet l.toSet) -> (isWeakCore l.toSet) := by
      intro h
      simp only [not_exists] at h
      intro gtm gtm_hom
      simp only [not_and, ne_eq] at h
      have l_set_fin : l.toSet.finite := by exact List.toSet_is_finite l
      have inj_str := hom_strong_of_finite_of_injective l.toSet l_set_fin gtm gtm_hom
      specialize h (l.map gtm.applyFact)
      have gtm_hom' := gtm_hom
      have af_sub_l : List.map gtm.applyFact l ⊆ l := by
        unfold GroundTermMapping.isHomomorphism at gtm_hom
        unfold GroundTermMapping.strong at inj_str
        rcases gtm_hom with ⟨gtm_c, gtm_af⟩
        cases l with
          | nil =>
            exact fun _ a => a
          | cons hd tl =>
            intro e
            rw [List.mem_iff_toSet_mem]
            unfold List.map
            intro h2
            rw [List.mem_cons]
            sorry

      specialize h af_sub_l

      have hom_subset : homSubset (l.map gtm.applyFact).toSet l.toSet := by
        rcases gtm_hom with ⟨gtm_c, gtm_af⟩
        unfold homSubset
        have : gtm.applyFactSet l.toSet = (List.map gtm.applyFact l).toSet := by
          apply Set.ext
          intro e

          have lem1 : (List.map gtm.applyFact l).toSet ⊆ l.toSet := by
            exact List.subset_if_sublist l (List.map gtm.applyFact l) af_sub_l

          constructor
          intro h2
          induction l with
            | nil =>
              exact gtm_af e h2
            | cons hd tl ih =>
              have lem2 : e ∈ (List.map gtm.applyFact (hd :: tl)).toSet ↔ e = gtm.applyFact hd ∨ e ∈ List.map gtm.applyFact tl := by
                rw [← List.mem_iff_toSet_mem]
                simp_all only [List.map_cons, List.cons_subset, List.mem_cons, List.mem_map]
              have lem3 : e ∈ gtm.applyFactSet (hd :: tl).toSet ↔ e ∈ (gtm.applyFactSet (Set.singleton hd) ∪ gtm.applyFactSet tl.toSet) := by sorry
              rw [lem2]
              rw [lem3] at h2
              rcases h2 with lhs | rhs
              left
              exact (s3 e hd gtm).mp lhs
              right
              rw [List.mem_iff_toSet_mem]
              apply ih
              exact List.toSet_is_finite tl
              refine fun a => ?_
              repeat sorry

          intro h2
          induction l with
            | nil =>
              exact False.elim (lem1 e (lem1 e (lem1 e (lem1 e h2))))
            | cons hd tl ih =>
              have lem2 : e ∈ (List.map gtm.applyFact (hd :: tl)).toSet ↔ e = gtm.applyFact hd ∨ e ∈ List.map gtm.applyFact tl := by
                rw [← List.mem_iff_toSet_mem]
                simp_all only [List.map_cons, List.cons_subset, List.mem_cons, List.mem_map]
              have lem3 : e ∈ gtm.applyFactSet (hd :: tl).toSet ↔ e ∈ (gtm.applyFactSet (Set.singleton hd) ∪ gtm.applyFactSet tl.toSet) := by sorry
              rw [lem3, Set.union_iff]
              rw [lem2] at h2
              rcases h2 with lhs | rhs
              left
              exact (s3 e hd gtm).mpr lhs
              right
              apply ih
              exact List.toSet_is_finite tl
              refine fun a => ?_
              repeat sorry

        constructor
        rw [← this]
        exact gtm_af
        exists gtm
        exact ⟨gtm_c, Set.Eq.subset this⟩

      cases Decidable.em (l ⊆ l.map gtm.applyFact) with
      | inl l_sub_mapped =>
        have eq : (l.map gtm.applyFact).toSet = l.toSet := by
          funext e
          apply propext
          have : l = List.map gtm.applyFact l := by
            have : l ⊆ List.map gtm.applyFact l ∧ List.map gtm.applyFact l ⊆ l := by exact ⟨l_sub_mapped, af_sub_l⟩
            rw [← s1] -- by sorry
            exact this
          exact Eq.to_iff (congrFun (congrArg List.toSet (id (Eq.symm this))) e)

        rw [propext (and_iff_right_of_imp inj_str)]
        let terms_list := (l.map Fact.terms).flatten.eraseDupsKeepRight
        have nodup_terms_list : terms_list.Nodup := by
          apply List.nodup_eraseDupsKeepRight
        have mem_terms_list : ∀ e, e ∈ terms_list ↔ e ∈ (terms l.toSet) := by
          simp only [terms_list]
          intro e
          rw [List.mem_eraseDupsKeepRight]
          unfold FactSet.terms
          simp only [List.mem_flatten, List.mem_map]
          constructor
          intro h
          rcases h with ⟨ts, ⟨f, f_mem, eq⟩, ts_mem⟩
          exists f
          rw [← eq] at ts_mem
          rw [List.mem_iff_toSet_mem] at f_mem
          exact ⟨f_mem, ts_mem⟩
          intro h
          rcases h with ⟨f, f_mem, e_mem⟩
          exists f.terms
          constructor
          exists f
          rw [List.mem_iff_toSet_mem]
          exact ⟨f_mem, rfl⟩
          exact e_mem


        have closed : ∀ e, e ∈ terms_list -> gtm e ∈ terms_list := by
          simp only [terms_list]
          intro e
          repeat rw [List.mem_eraseDupsKeepRight]
          simp
          intro f f_mem e_in_f
          let f' := gtm.applyFact f
          have f'_mem : f' ∈ l.toSet := by
            repeat apply gtm_hom.right
            unfold GroundTermMapping.applyFactSet
            exists f
            constructor
            rw [← List.mem_iff_toSet_mem]
            exact f_mem
            rfl
          exists f'.terms
          constructor
          exists f'
          constructor
          rw [List.mem_iff_toSet_mem]
          exact f'_mem
          rfl
          simp only [f', GroundTermMapping.applyFact]
          rw [List.mem_map]
          exists e

        have closed' : ∀ e, e ∈ (List.map Fact.terms l).flatten → gtm e ∈ (List.map Fact.terms l).flatten := by
          sorry


        -- 1)

        /-
        rw [Function.injective_set_list_equiv gtm (terms l.toSet) terms_list mem_terms_list]
        rw [Function.injective_iff_surjective_of_nodup_of_closed gtm terms_list nodup_terms_list closed]
        refine (Function.surjective_on_target_iff_all_in_image gtm terms_list terms_list).mpr ?_
        intro b b_in
        rw [Function.image_eq_eraseDupsKeepRight_map]
        simp only [terms_list]
        sorry
        -/


        -- 2)

        rw [Function.injective_set_list_equiv gtm (terms l.toSet) terms_list mem_terms_list]
        rw [Function.injective_iff_length_image_eq_of_nodup]
        rw [Function.image_eq_eraseDupsKeepRight_map]
        apply length_eraseDupsKeepRight_eq_of_same_elements
        intro gt
        specialize mem_terms_list gt
        constructor
        intro gt_in_gtm_terms_list
        rw [← eq] at mem_terms_list
        apply Function.image_contained_of_closed gtm (List.map Fact.terms l).flatten closed' gt sorry
        intro h2
        sorry -- weil l nodup
        exact nodup_terms_list


      | inr l_not_sub_mapped =>
        have neq : (l.map gtm.applyFact).toSet ≠ l.toSet := by
          apply Classical.byContradiction
          intro c
          apply l_not_sub_mapped
          intro e e_in_l
          unfold homSubset at hom_subset
          rcases hom_subset with ⟨sub, gtm', gtm'_hom⟩
          refine List.mem_map.mpr ?_
          exists e
          constructor
          exact e_in_l
          sorry
        specialize h neq
        contradiction



  theorem t1 (gtm : GroundTermMapping sig) (fs sub : FactSet sig) (fs_nempty : fs ≠ ∅) : gtm.applyFactSet fs ⊆ sub ∧ sub ⊆ fs ∧ sub ≠ fs → gtm.applyFactSet fs ≠ fs := by
    intro ⟨gtm_af_sub, subset, neq⟩
    sorry

  theorem ex_subset_iff_not_weak_core (l : List (Fact sig)):
    (∃ (sub : List (Fact sig)), sub ⊆ l ∧ sub.toSet ≠ l.toSet ∧ FactSet.homSubset sub.toSet l.toSet) ↔ ¬ isWeakCore l.toSet := by
      constructor
      intro h
      rcases h with ⟨sub, subset, neq, subset', gtm_ls, gtm_ls_c, gtm_ls_af⟩
      unfold isWeakCore
      simp only [Classical.not_forall, not_imp, not_and]
      exists gtm_ls
      have gtm_ls_ll_hom : gtm_ls.isHomomorphism l.toSet l.toSet := by
        constructor
        exact gtm_ls_c
        apply apply_fact_set_monotone
        apply subset'
        exact gtm_ls_af
      exists gtm_ls_ll_hom
      intro gtm_ll
      rcases gtm_ls_ll_hom with ⟨gtm_ls_ll_c, gtm_ls_ll_af⟩
      have gtm_ll_ls_af_neq : gtm_ls.applyFactSet l.toSet ≠ l.toSet := by
        have ex_out : ∃ e, e ∈ l ∧ ¬ e ∈ sub := by
          apply List.ex_elem_outside_prop_subset
          exact subset
          exact neq
        rcases ex_out with ⟨e, e_in_l, e_nin_sub⟩
        apply t1 gtm_ls l.toSet sub.toSet
        exact List.ex_elem_to_set_neq_empty l e e_in_l
        constructor
        exact gtm_ls_af
        constructor
        exact subset'
        exact neq
      unfold Function.injective_for_domain_set
      simp only [Classical.not_forall, not_imp, exists_and_left]
      -- f(B) ⊆ A ⊂ B
      sorry
      intro n_wc
      have l_nempty : l.toSet ≠ ∅ := by
        apply Classical.byContradiction
        intro contra
        simp only [ne_eq, Classical.not_not] at contra
        have : isWeakCore l.toSet := by exact empty_set_is_weak_core l.toSet contra
        contradiction
      unfold isWeakCore at n_wc
      simp only [Classical.not_forall, not_imp, not_and] at n_wc
      have : ∃ e, e ∈ l.toSet := by exact Set.not_empty_contains_element l.toSet l_nempty
      rcases this with ⟨e, e_in_l⟩

      exists [e]
      constructor
      sorry
      constructor

      rcases n_wc with ⟨gtm, gtm_hom, gtm_ninj_if_str⟩
      sorry -- l.toSet hat min 2 elemente (da gtm nicht inj)
      constructor
      sorry
      exists id
      constructor
      sorry
      sorry

      /-- have : ∃ e, e ∈ l := by
        sorry
      rcases this with ⟨e, e_in_l⟩
      unfold Set.subset at rhs
      simp at rhs
      rcases rhs with ⟨f, gtm_af, f_nin_nempty⟩
      -/


    theorem weak_core_of_nex_subset (l : List (Fact sig)):
    ¬ (∃ (sub : List (Fact sig)), sub ⊆ l ∧ sub.toSet ≠ l.toSet ∧ FactSet.homSubset sub.toSet l.toSet) -> (isWeakCore l.toSet) := by
    intro h
    simp only [not_exists] at h
    intro g g_hom
    simp only [not_and, ne_eq] at h
    specialize h (l.map g.applyFact) sorry

    have hom_subset : homSubset (l.map g.applyFact).toSet l.toSet := by
      sorry

    cases Decidable.em (l ⊆ l.map g.applyFact) with
    | inl l_sub_mapped =>
      have eq : (l.map g.applyFact).toSet = l.toSet := by sorry
      constructor
      . sorry
      . sorry
    | inr l_not_sub_mapped =>
      have neq : (l.map g.applyFact).toSet ≠ l.toSet := by sorry
      specialize h neq
      contradiction



  theorem nex_subset_iff_weak_core (l : List (Fact sig)):
    ¬ (∃ (sub : List (Fact sig)), sub ⊆ l ∧ sub.toSet ≠ l.toSet ∧ FactSet.homSubset sub.toSet l.toSet) ↔ (isWeakCore l.toSet) := by
      rw [← Classical.not_iff]
      rw [ex_subset_iff_not_weak_core]
      simp

  theorem exists_weak_core_for_finite_set (length : Nat) (l : List (Fact sig)) (length_l : l.length = length):
    ∃ (wc : FactSet sig), wc.isWeakCore ∧ wc.homSubset l.toSet := by
      induction length using Nat.strongRecOn generalizing l with
        | ind n ih =>
          by_cases h : (∃ (sub : List (Fact sig)), sub ⊆ l ∧ sub.toSet ≠ l.toSet ∧ FactSet.homSubset sub.toSet l.toSet)
          . rcases h with ⟨sub', h2, h3, h4⟩
            let sub := sub'.eraseDupsKeepRight
            have sub_eq_sub' : sub.toSet = sub'.toSet := by
              apply funext
              intro e
              apply propext
              have := @List.mem_toSet _ sub' e
              unfold Set.element at this
              rw [this]
              have := @List.mem_toSet _ sub e
              unfold Set.element at this
              rw [this]
              apply List.mem_eraseDupsKeepRight
            specialize ih sub.length  -- m < n
            by_cases n_zero : (n = 0)
            . exists ∅
              constructor
              apply empty_set_is_weak_core; rfl
              rw [n_zero] at length_l
              rw [List.eq_empty_if_len_zero l length_l]
              apply hom_subset_of_empty; rfl
            . have x : _ := ih (by
                rw [← length_l]
                apply List.length_lt_of_proper_subset
                . apply List.nodup_eraseDupsKeepRight
                . intro e e_mem; apply h2; rw [List.mem_eraseDupsKeepRight] at e_mem; exact e_mem
                . intro contra
                  apply h3
                  rw [← contra]
                  rw [sub_eq_sub']
              ) sub rfl
              have y : _ := ex_subset_iff_not_weak_core sub
              rcases y with ⟨lhs, rhs⟩
              rcases x with ⟨fs, fs_wc, fs_hom_ss_tl⟩
              exists fs
              constructor
              . exact fs_wc
              . rw [sub_eq_sub'] at fs_hom_ss_tl
                rcases fs_hom_ss_tl with ⟨fs_ss_tl, ⟨gtm ,ghom⟩⟩
                rw [homSubset]
                constructor
                have h2' : sub'.toSet ⊆ l.toSet := by
                  apply List.subset_if_sublist; exact h2
                . apply Set.subset_trans fs_ss_tl h2'
                . rcases h4 with ⟨h4_sub, h4_hom, h4_hom_hom⟩
                  exists gtm ∘ h4_hom
                  apply GroundTermMapping.isHomomorphism_compose
                  . exact h4_hom_hom
                  . exact ghom
          -- l.toSet is wc
          · have x : FactSet.isWeakCore l.toSet := by
              rw [← nex_subset_iff_weak_core]

              exact h
            exists l.toSet
            constructor
            exact x
            rw [homSubset]
            constructor
            apply Set.subset_refl
            exists id
            apply id_is_hom

end FactSet
