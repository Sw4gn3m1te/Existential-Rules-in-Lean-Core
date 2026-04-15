import ExistentialRules.ChaseSequence.ChaseBranch

import ExistentialRules.Models.Basic
import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.Basic
import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms
import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Universality

import ExistentialRules.ChaseSequence.Deterministic

import ExistentialRules.ChaseSequence.CoreChase.Util

import BasicLeanDatastructures.List.EraseDupsKeepRight


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


namespace Fact

  def Fact.hom_mem (f : Fact sig) (fs : FactSet sig) :=
    ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism (fun x => x = f) fs ∧ (gtm.applyFact f) ∈ fs

  theorem applyFactIdEq (f g : Fact sig) : GroundTermMapping.applyFact id f = g → f = g := by
    intro h
    unfold GroundTermMapping.applyFact TermMapping.apply_generalized_atom at h
    simp only [List.map_id_fun, id_eq] at h
    rw [GeneralizedAtom.mk.injEq]
    exact ⟨congrArg GeneralizedAtom.predicate h, congrArg GeneralizedAtom.terms h⟩

  @[grind]
  theorem FactGeneralizedAtomEq (f : Fact sig) (ga : GeneralizedAtom sig (GroundTerm sig)) : f = ga ↔ f.predicate = ga.predicate ∧ f.terms = ga.terms := by
      constructor
      · intro eq
        rw [eq]
        exact ⟨rfl, rfl⟩
      · intro ⟨eq_p, eq_t⟩
        rw [GeneralizedAtom.mk.injEq]
        exact ⟨eq_p, eq_t⟩

end Fact

namespace GroundTermMapping

  def isIsomorphism (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
      h.isHomomorphism A B ∧ Function.injective_for_domain_set h A.terms ∧ Function.surjective_for_domain_and_image_set h A.terms B.terms ∧ h.strong A.terms A B


  @[simp, grind]
  theorem homApplyFactFunctionFreeId (fs1 fs2 : FactSet sig) (f : Fact sig) (f_is_ff : f.isFunctionFree) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism fs1 fs2) : gtm.applyFact f = f := by
      rw [GeneralizedAtom.mk.injEq]
      constructor
      · rfl
      · apply List.map_id_of_id_on_all_mem
        intro gt gt_in
        specialize f_is_ff gt gt_in
        rcases f_is_ff with ⟨c, c_eq⟩
        rw [c_eq]
        exact @gtm_hom.left c

  @[simp, grind]
  theorem homApplyFactSetFunctionFreeId (fs1 fs2 : FactSet sig) (fs1_is_ff : fs1.isFunctionFree) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism fs1 fs2) : gtm.applyFactSet fs1 = fs1 := by
    unfold GroundTermMapping.applyFactSet
    apply Set.ext
    intro f
    constructor
    · intro ⟨ff, ff_in, ff_eq⟩
      have := homApplyFactFunctionFreeId fs1 fs2 ff (fs1_is_ff ff ff_in) gtm gtm_hom
      grind
    · intro h
      exists f
      constructor
      exact h
      rw [← GroundTermMapping.applyFact.eq_def]
      rw [homApplyFactFunctionFreeId fs1 fs2 f (fs1_is_ff f h) gtm gtm_hom]


  @[grind]
  theorem hom_on_db_id (f : Fact sig) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism kb.db.toFactSet.val kb.db.toFactSet.val) (f_in_db : f ∈ kb.db.toFactSet.val) :
    gtm.applyFact f = f := by
      unfold GroundTermMapping.applyFact
      rw [GeneralizedAtom.mk.injEq]
      constructor
      · rfl
      · apply List.map_id_of_id_on_all_mem
        intro gt gt_in
        unfold GroundTermMapping.isHomomorphism at gtm_hom
        have db_funfree := kb.db.toFactSet.property.right
        unfold FactSet.isFunctionFree at db_funfree
        specialize db_funfree f f_in_db
        unfold Fact.isFunctionFree at db_funfree
        specialize db_funfree gt gt_in
        rcases db_funfree with ⟨c, c_eq⟩
        rcases f_in_db with ⟨ff, ff_in, ff_eq⟩
        unfold FunctionFreeFact.toFact at ff_eq
        rw [GeneralizedAtom.mk.injEq] at ff_eq
        rcases ff_eq with ⟨ff_pred_eq, ff_map_eq⟩
        rcases gtm_hom with ⟨gtm_c, gtm_sub⟩
        rw [c_eq]
        exact @gtm_c c

  @[grind]
  theorem hom_on_db_term_id (t : GroundTerm sig) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism kb.db.toFactSet.val kb.db.toFactSet.val) (t_in_db_terms : t ∈ kb.db.toFactSet.val.terms) :
    gtm t = t := by
      have db_funfree := kb.db.toFactSet.property.right
      have ex_fact : ∃ f, f ∈ kb.db.toFactSet.val ∧ t ∈ f.terms := t_in_db_terms
      rcases ex_fact with ⟨f, f_in, f_in_ter⟩
      unfold FactSet.isFunctionFree at db_funfree
      specialize db_funfree f f_in t f_in_ter
      rcases db_funfree with ⟨c, c_eq⟩
      rw [c_eq]
      exact @gtm_hom.left c


  @[grind]
  theorem memApplyFactSetIfMemApplyFactSetSubSet (h : GroundTermMapping sig) (fs1 fs2 : FactSet sig) (f : Fact sig) (f_af_in_f1 : f ∈ h.applyFactSet fs1) (sub : fs1 ⊆ fs2) :  f ∈ h.applyFactSet fs2 := by
    unfold GroundTermMapping.applyFactSet
    rcases f_af_in_f1 with ⟨f', f'_in, f'_af_eq⟩
    exists f'
    exact ⟨sub f' f'_in, f'_af_eq⟩


  theorem isHomIfEq (gtm1 gtm2 : GroundTermMapping sig) (A B : FactSet sig) : gtm1 = gtm2 → (gtm1.isHomomorphism A B ↔ gtm2.isHomomorphism A B) := fun a => Eq.to_iff (congrFun (congrFun (congrArg GroundTermMapping.isHomomorphism a) A) B)

  theorem gtm_rep_swap (gtm : GroundTermMapping sig) (rep : Nat) (A B : FactSet sig) : (gtm.repeat_hom (rep + 1)).isHomomorphism A B ↔ GroundTermMapping.isHomomorphism (gtm.repeat_hom rep ∘ gtm) A B := by
    have := isHomIfEq (gtm.repeat_hom rep ∘ gtm) (gtm.repeat_hom (rep + 1)) A B
    rw [this]
    have := GroundTermMapping.repeat_hom_add gtm rep 1
    funext t
    specialize this t
    exact id (Eq.symm this)

 @[grind]
  theorem subPreservesHom (A B C : FactSet sig) (sub : C ⊆ A) (h : GroundTermMapping sig) (h_hom : h.isHomomorphism  A B) : h.isHomomorphism C B := by
    rcases h_hom with ⟨idc, af⟩
    constructor
    · exact idc
    · intro f f_in_afc
      have f_in_afb := memApplyFactSetIfMemApplyFactSetSubSet h C A
      specialize f_in_afb f f_in_afc sub
      exact af f f_in_afb

  theorem id_is_hom {fs : FactSet sig} : GroundTermMapping.isHomomorphism id fs fs := by
    constructor
    · exact Subtype.ext rfl
    · intro f ⟨e, mem, eq⟩
      rw [TermMapping.apply_generalized_atom_eq_self_of_id_on_terms] at eq
      . grind
      . simp

end GroundTermMapping


namespace FactSet

  @[simp, grind =]
  theorem applyFactSetIdEq (fs : FactSet sig) : GroundTermMapping.applyFactSet id fs = fs := by
    unfold GroundTermMapping.applyFactSet TermMapping.apply_generalized_atom_set
    apply Set.ext
    intro f
    constructor
    · intro f_in_map
      rcases f_in_map with ⟨ga, ga_in, ga_eq⟩
      unfold TermMapping.apply_generalized_atom at ga_eq
      rw [GeneralizedAtom.mk.injEq] at ga_eq
      simp only [List.map_id_fun, id_eq] at ga_eq
      grind
    · intro f_in
      exists f
      exact ⟨f_in, Eq.symm (Fact.applyFactIdEq f (TermMapping.apply_generalized_atom id f) rfl)⟩

  @[grind]
  theorem exHomSubToSet (A B : FactSet sig) (sub : A ⊆ B) : ∃ (h : GroundTermMapping sig), h.isHomomorphism A B := by

    exists id
    constructor
    · intro gt
      simp only [id_eq]
    · intro f f_in
      grind

  theorem empty_set_is_weak_core : (∅ : FactSet sig).isWeakCore := by
    intro gtm ghom
    constructor
    · intro _ _ contra _
      contradiction
    · intro h1 h2 h3 h4 h5
      unfold FactSet.terms at h3
      rcases h3 with ⟨_, contra, _⟩
      contradiction

  theorem homSubset_refl (fs : FactSet sig) : fs.homSubset fs := by
    constructor
    . apply Set.subset_refl
    . exists id
      exact GroundTermMapping.id_is_hom

  theorem apply_fact_set_monotone (f : GroundTermMapping sig) (A B : FactSet sig) (subset : A ⊆ B):
    f.applyFactSet B ⊆ A → f.applyFactSet B ⊆ B := by
      intro h
      intro e e_in_af_B
      specialize h e e_in_af_B
      specialize subset e h
      exact subset

  @[grind =>]
  theorem weak_core_of_neq_subset (l : List (Fact sig)):
    ¬ (∃ (sub : List (Fact sig)), sub ⊆ l ∧ sub.toSet ≠ l.toSet ∧ FactSet.homSubset sub.toSet l.toSet) -> (isWeakCore l.toSet) := by
      intro h
      simp only [not_exists] at h
      intro gtm gtm_hom
      simp only [not_and, ne_eq] at h
      have l_set_fin : l.toSet.finite := by exact List.finite_toSet l
      have inj_str := hom_strong_of_finite_of_injective l.toSet l_set_fin gtm gtm_hom

      specialize h (l.map gtm.applyFact)

      have af_sub_l : List.map gtm.applyFact l ⊆ l := by
        rw [List.subset_def]
        intro f f_in_l
        rw [List.mem_map] at f_in_l
        rcases f_in_l with ⟨f', f'_in_l, f'_eq⟩
        rcases gtm_hom with ⟨gtm_c, gtm_af⟩

        specialize gtm_af f
        rw [← List.mem_toSet]
        apply gtm_af
        unfold GroundTermMapping.applyFactSet
        exists f'

      specialize h af_sub_l

      have hom_subset : homSubset (l.map gtm.applyFact).toSet l.toSet := by
        rcases gtm_hom with ⟨gtm_c, gtm_af⟩
        unfold homSubset
        have : gtm.applyFactSet l.toSet = (List.map gtm.applyFact l).toSet := by
          apply Set.ext
          intro e
          rw [List.mem_toSet, List.mem_map]
          unfold GroundTermMapping.applyFactSet
          constructor
          . intro h2
            rcases h2 with ⟨f, f_in, f_eq⟩
            exists f
          . intro h2
            rcases h2 with ⟨f, f_in, f_eq⟩
            exists f

        constructor
        · rw [← this]
          exact gtm_af
        · exists gtm
          constructor
          . exact gtm_c
          . rw [this]; apply Set.subset_refl

      cases Decidable.em (l ⊆ l.map gtm.applyFact) with
      | inl l_sub_mapped =>
        have eq : (l.map gtm.applyFact).toSet = l.toSet := by
          simp_all only [not_true_eq_false, imp_false, Classical.not_not]

        rw [propext (and_iff_right_of_imp inj_str)]
        let terms_list := (l.flatMap GeneralizedAtom.terms).eraseDupsKeepRight
        have nodup_terms_list : terms_list.Nodup := by
          apply List.nodup_eraseDupsKeepRight
        have mem_terms_list : ∀ e, e ∈ terms_list ↔ e ∈ (terms l.toSet) := by
          simp only [terms_list]
          intro e
          rw [List.mem_eraseDupsKeepRight]
          unfold FactSet.terms
          simp only [List.mem_flatMap]
          constructor
          . intro h
            rcases h with ⟨f, f_in_l, e_in_ft⟩
            exists f
          . intro h
            rcases h with ⟨f, f_in_l, e_in_ft⟩
            exists f


        rw [Function.injective_set_list_equiv gtm (terms l.toSet) terms_list mem_terms_list]
        rw [Function.injective_iff_length_image_eq_of_nodup]

        apply List.length_eraseDupsKeepRight_eq_of_same_elements
        intro gt
        specialize mem_terms_list gt

        unfold terms_list at mem_terms_list
        rw [List.mem_eraseDupsKeepRight] at mem_terms_list
        rw [mem_terms_list, ← eq]

        have eq2 : gt ∈ List.flatMap GeneralizedAtom.terms (List.map gtm.applyFact l) ↔ gt ∈ terms (List.map gtm.applyFact l).toSet := by grind

        rw [← eq2]
        unfold terms_list

        rw [← List.mem_map_iff_mem_map_eraseDupsKeepRight]
        rw [List.map_flatMap, List.flatMap_map]

        constructor
        · intro h2
          rw [List.mem_flatMap] at h2
          rcases h2 with ⟨f, f_in, f_eq⟩
          rw [List.mem_flatMap]
          exists f
        · intro h2
          rw [List.mem_flatMap]
          rw [List.mem_flatMap] at h2
          rcases h2 with ⟨f, f_in, f_eq⟩
          exists f

        exact nodup_terms_list

      | inr l_not_sub_mapped =>
        have neq : (l.map gtm.applyFact).toSet ≠ l.toSet := by
          intro contra
          apply l_not_sub_mapped
          intro f f_in_l
          rw [Set.ext_iff] at contra
          specialize contra f
          rw [← List.mem_toSet]
          rw [contra]
          rw [List.mem_toSet]
          exact f_in_l

        specialize h neq
        contradiction

  theorem exists_weak_core_for_list (l : List (Fact sig)) :
    ∃ (wc : FactSet sig), wc.isWeakCore ∧ wc.homSubset l.toSet := by
      induction d : l.length using Nat.strongRecOn generalizing l with
        | ind n ih =>
          by_cases h : (∃ (sub : List (Fact sig)), sub ⊆ l ∧ sub.toSet ≠ l.toSet ∧ FactSet.homSubset sub.toSet l.toSet)
          . rcases h with ⟨sub', h2, h3, h4⟩
            let sub := sub'.eraseDupsKeepRight
            have sub_eq_sub' : sub.toSet = sub'.toSet := by
              apply funext
              intro e
              apply propext
              change e ∈ sub.toSet ↔ e ∈ sub'.toSet
              have := @List.mem_toSet _ sub' e
              rw [this]
              have := @List.mem_toSet _ sub e
              rw [this]
              apply List.mem_eraseDupsKeepRight
            specialize ih sub.length  -- m < n
            by_cases n_zero : (n = 0)
            . exists ∅
              constructor
              . apply empty_set_is_weak_core
              . grind
            . have x : _ := ih (by
                have := List.length_lt_of_proper_subset l sub (List.nodup_eraseDupsKeepRight sub') (by grind) (by grind)
                exact Nat.lt_of_lt_of_eq this d

              ) sub rfl
              rcases x with ⟨fs, fs_wc, fs_hom_ss_tl⟩
              exists fs
              constructor
              . exact fs_wc
              . rw [sub_eq_sub'] at fs_hom_ss_tl
                rcases fs_hom_ss_tl with ⟨fs_ss_tl, ⟨gtm ,ghom⟩⟩
                rw [homSubset]
                constructor
                have h2' : sub'.toSet ⊆ l.toSet := Set.subset_trans h2 fun e a => a
                . apply Set.subset_trans fs_ss_tl h2'
                . rcases h4 with ⟨h4_sub, h4_hom, h4_hom_hom⟩
                  exists gtm ∘ h4_hom
                  apply GroundTermMapping.isHomomorphism_compose
                  . exact h4_hom_hom
                  . exact ghom
          -- l.toSet is wc
          · have x : FactSet.isWeakCore l.toSet := by
              apply weak_core_of_neq_subset
              exact h
            exists l.toSet
            constructor
            exact x
            rw [homSubset]
            constructor
            apply Set.subset_refl
            exists id
            exact GroundTermMapping.id_is_hom

  theorem exists_weak_core_for_finite_set (fs : FactSet sig) (fs_fin : fs.finite):
    ∃ (wc : FactSet sig), wc.isWeakCore ∧ wc.homSubset fs := by
      rcases fs_fin with ⟨l, nd, eq⟩
      have := exists_weak_core_for_list l
      rcases this with ⟨wc, wc_core, wc_sub⟩
      exists wc
      constructor
      · exact wc_core
      · have eq' : l.toSet = fs := by exact Set.ext l.toSet fs eq
        rw [eq'] at wc_sub
        exact wc_sub

end FactSet

namespace ChaseNode

  def ChaseNode.isWeakCore {obs : ObsolescenceCondition sig} (node : ChaseNode obs rules) :
    Prop := FactSet.isWeakCore node.facts

  def ChaseNode.isStrongCore {obs : ObsolescenceCondition sig} (node : ChaseNode obs rules) :
  Prop := FactSet.isStrongCore node.facts

end ChaseNode
