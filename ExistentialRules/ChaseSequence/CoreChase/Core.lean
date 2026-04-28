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

import ExistentialRules.ChaseSequence.CoreChase.Homomorphisms
import ExistentialRules.ChaseSequence.CoreChase.PseudoCoreChaseBranch
import ExistentialRules.ChaseSequence.CoreChase.Triggers
import ExistentialRules.ChaseSequence.CoreChase.Termination


--import ExistentialRules.BasicTypes.Sets.Set
--import ExistentialRules.BasicTypes.Sets.Finite
--import ExistentialRules.BasicTypes.Functions.Function


--import Aesop
-- import Canonical
-- import Mathlib.Combinatorics.Graph.Basic


-- set_option pp.proofs true
-- set_option diagnostics true

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}
--abbrev obs := RestrictedObsolescence sig


namespace CoreChaseBranch


  abbrev InductiveHomomorphismResultCore (cb : CoreChaseBranch kb) (m : FactSet sig) (depth : Nat) :=
    {gtm : GroundTermMapping sig // ∀ cn, cn ∈ cb.branch.get? depth → gtm.isHomomorphism cn.fs m}


  @[grind .]
  theorem kb_det_head_len_eq (kb_det : kb.isDeterministic): ∀ (r : Rule sig), r ∈ kb.rules.rules → r.head.length = 1 := by
    unfold KnowledgeBase.isDeterministic RuleSet.isDeterministic Rule.isDeterministic at kb_det
    intro r r_in
    specialize kb_det r r_in
    grind

  theorem func_term_not_mem_head {cb : CoreChaseBranch kb} {t : GroundTerm sig} (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) :
    ¬ t ∈ cb.head.fs.terms := by
      intro t_mem
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rcases kb.db.toFactSet.property.right f (by grind) t t_mem with ⟨c, t_eq⟩
      rcases t_is_func with ⟨_, _, _, t_eq'⟩
      rw [t_eq'] at t_eq
      simp [GroundTerm.func_neq_const] at t_eq


theorem ex_endo_hom  (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules)
    (disj_idx n : Nat) (trg: RTrigger obs.toLaxObsolescenceCondition kb.rules) (cn_eq : cn ∈ cb.branch.get? n)
    (t : GroundTerm sig ) (lt : disj_idx < trg.val.rule.head.length)
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) (t_mem_node : t ∈ cn.fs.terms) :
      ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet cn.core ∧
        gtm.isHomomorphism cn.core cn.core ∧ (Function.surjective_for_domain_and_image_set gtm cn.core.terms cn.core.terms) := by
          have : trg.val.satisfied_for_disj cn.fs ⟨disj_idx, Nat.lt_of_succ_le lt⟩ := by
            sorry
          sorry

  -- jeder surjektive endomorphisms auf endlichen mengen ist auch ein isomorphismus

  theorem triggerInactiveAfterApplication' (cb : CoreChaseBranch kb) (cn cn_succ : CoreChaseNode kb.rules) (n k : Nat)
    (cn_eq : cn ∈ cb.branch.infinite_list n) (cn_succ_eq : cn_succ ∈ cb.branch.infinite_list (n + k))
    (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (trg_act_cn : trg.val.active cn.core) :
      ¬ trg.val.active cn_succ.core := by sorry


  theorem apply_constant_is_id_of_isIdOnConstants {h : GroundTermMapping sig} (isId : h.isIdOnConstants) (c : sig.C) :
      h (GroundTerm.const c) = GroundTerm.const c := Subtype.ext (congrArg Subtype.val isId)



  --set_option trace.Meta.synthInstance true
  noncomputable def inductive_homomorphism_core_with_prev_node_and_trg_if_next_node_some (cb : CoreChaseBranch kb) (m : FactSet sig) (m_mod : m.modelsKb kb) (kb_det : kb.isDeterministic)
    (prev_depth : Nat) (prev_node : CoreChaseNode kb.rules) (prev_node_eq : prev_node ∈ cb.branch.get? prev_depth)
    (prev_gtm : GroundTermMapping sig) (prev_gtm_hom : prev_gtm.isHomomorphism prev_node.fs m) :
      ∀ next_node ∈ cb.branch.get? (prev_depth.succ), ∃ (next_gtm : GroundTermMapping sig), GroundTermMapping.isHomomorphism next_gtm next_node.fs m := by

        intro next_node next_node_eq

        have prev_core_eq : (cb.prev_node prev_depth (Option.isSome_of_mem next_node_eq)).core = prev_node.core := by grind

        have prev_gtm_hom_core : prev_gtm.isHomomorphism prev_node.core m := homFsToFsAlsoHomCoreToFs m prev_node prev_gtm prev_gtm_hom

        have trg_act := cb.triggers_active prev_depth prev_node prev_node_eq next_node next_node_eq

        let trg_on_prev_node := (Classical.choose trg_act).fst -- origin.fst
        let disj_on_prev_node := (Classical.choose trg_act).snd --origin.snd

        let fin_disj : Fin trg_on_prev_node.val.rule.head.length :=
            ⟨disj_on_prev_node.val, by
              rw [← PreTrigger.length_mapped_head]
              exact disj_on_prev_node.isLt
              ⟩

        let trg_active_prev_core := (Classical.choose_spec trg_act).right

        let next_node_origin_some := (Classical.choose_spec trg_act).left

        let next_node_origin := next_node.origin.get (origin_isSome cb prev_depth next_node_eq)


        let new_trg : PreTrigger sig := ⟨trg_on_prev_node.val.rule, (prev_gtm ∘ trg_on_prev_node.val.subs)⟩

        have new_trg_loaded : new_trg.loaded m := by
          apply Set.subset_trans _ prev_gtm_hom.right
          apply PreTrigger.term_mapping_preserves_loadedness
          . exact prev_gtm_hom.left
          . have trg_origin_act := (cb.origin_trg_is_active_prev_core prev_depth next_node next_node_eq ⟨trg_on_prev_node, disj_on_prev_node⟩ next_node_origin_some).left
            simp [prev_core_eq] at trg_origin_act
            have := trg_loaded_in_fs_if_loaded_in_core cb prev_depth prev_node prev_node_eq trg_on_prev_node.val trg_origin_act
            exact this


        have new_trg_satisfied : new_trg.satisfied_for_disj m ⟨fin_disj.val, fin_disj.isLt⟩ := by
          have modelsRule : m.modelsRule new_trg.rule := m_mod.right new_trg.rule trg_on_prev_node.property
          unfold FactSet.modelsRule at modelsRule
          specialize modelsRule new_trg.subs new_trg_loaded

          rcases modelsRule with ⟨i, s', s'_frontier, s'_contains⟩
          exists s'
          constructor
          . exact s'_frontier
          . have : i.val = fin_disj.val := by
              have isLt := i.isLt
              have := kb_det new_trg.rule trg_on_prev_node.property
              unfold Rule.isDeterministic at this
              rw [decide_eq_true_iff] at this
              simp only [this, Nat.lt_one_iff] at isLt
              have isLt' := fin_disj.isLt
              have := kb_det trg_on_prev_node.val.rule trg_on_prev_node.property
              unfold Rule.isDeterministic at this
              rw [decide_eq_true_iff] at this
              simp only [this, Nat.lt_one_iff] at isLt'
              rw [isLt, isLt']
            simp only [List.get_eq_getElem, this] at s'_contains
            exact s'_contains

        let subs := Classical.choose new_trg_satisfied
        have ⟨subs_frontier, subs_contained⟩ := Classical.choose_spec new_trg_satisfied

        -- build new hom
        let next_gtm : GroundTermMapping sig := fun t =>
          if t_mem : t ∈ (trg_on_prev_node.val.fresh_terms_for_head_disjunct ↑fin_disj fin_disj.isLt) then
            subs (trg_on_prev_node.val.existential_var_for_fresh_term ↑fin_disj fin_disj.isLt t t_mem)
          else
            prev_gtm t

        have next_gtm_is_id_on_const : next_gtm.isIdOnConstants := by
          intro c
          have : ¬ GroundTerm.const c ∈ trg_on_prev_node.val.fresh_terms_for_head_disjunct ↑fin_disj fin_disj.isLt := by
            apply PreTrigger.constant_not_mem_fresh_terms_for_head_disjunct
          simp_all
          simp only [next_gtm, this, ↓reduceDIte]
          exact prev_gtm_hom.left


        have next_gtm_is_subs_on_head_vars : ∀ v, v ∈ (trg_on_prev_node.val.rule.head[fin_disj.val]).vars -> (next_gtm (trg_on_prev_node.val.subs_for_mapped_head disj_on_prev_node v)) = subs v := by
          intro v v_mem
          simp only [PreTrigger.subs_for_mapped_head]
          cases Decidable.em (v ∈ trg_on_prev_node.val.rule.frontier) with
          | inl v_frontier =>
            rw [trg_on_prev_node.val.apply_to_var_or_const_frontier_var _ _ v_frontier]
            have : ¬ trg_on_prev_node.val.subs v ∈ trg_on_prev_node.val.fresh_terms_for_head_disjunct fin_disj.val fin_disj.isLt := by
              apply PreTrigger.frontier_term_not_mem_fresh_terms_for_head_disjunct
              apply List.mem_map_of_mem
              exact v_frontier
            simp only [next_gtm, this, ↓reduceDIte]
            simp only [subs, subs_frontier _ v_frontier]
            rfl
          | inr v_frontier =>
            rw [trg_on_prev_node.val.apply_to_var_or_const_non_frontier_var _ _ v_frontier]
            have v_exis : v ∈ trg_on_prev_node.val.rule.existential_vars_for_head_disjunct fin_disj.val fin_disj.isLt := by
              simp only [Rule.existential_vars_for_head_disjunct, List.mem_filter, decide_eq_true_iff]
              exact ⟨v_mem, v_frontier⟩
            have : trg_on_prev_node.val.functional_term_for_var disj_on_prev_node.val v ∈ trg_on_prev_node.val.fresh_terms_for_head_disjunct fin_disj.val fin_disj.isLt := by
              apply List.mem_map_of_mem; exact v_exis
            simp only [next_gtm, this, ↓reduceDIte]
            rw [PreTrigger.existential_var_for_fresh_term_after_functional_term_for_var]
            exact v_exis

        have next_gtm_eq_prev_gtm_on_terms_in_prev_node : ∀ t ∈ prev_node.core.terms, next_gtm t = prev_gtm t := by
          intro t t_mem
          have n_eq : (cb.prev_node prev_depth (Option.isSome_of_mem next_node_eq)) = prev_node := by grind

          have : ¬ t ∈ trg_on_prev_node.val.fresh_terms_for_head_disjunct fin_disj.val fin_disj.isLt := by
            intro contra
            apply trg_active_prev_core.right

            apply obs.contains_trg_result_implies_cond disj_on_prev_node

            intro f f_mem

            have ex_gtm := cb.result_of_trigger_introducing_functional_term_occurs_in_chase_core' prev_node disj_on_prev_node prev_depth (Classical.choose trg_act).fst
              (Option.mem_def.mpr prev_node_eq) t fin_disj.isLt (by grind) (CoreChaseNode.fs_terms_sub_core_terms prev_node t t_mem)

            have := CoreChaseBranch.functional_term_originates_from_some_trigger_or_database_core cb prev_depth prev_node prev_node_eq t
              (PreTrigger.term_functional_of_mem_fresh_terms t contra) (CoreChaseNode.fs_terms_sub_core_terms prev_node t t_mem)

            cases this with
              | inl from_db =>
                have := func_term_not_mem_head (PreTrigger.term_functional_of_mem_fresh_terms t contra) from_db
                contradiction
              | inr from_trg =>
                rcases ex_gtm with ⟨gtm, gtm_idc, gtm_af⟩

                have : f ∈ gtm.applyFactSet (Classical.choose trg_act).fst.val.mapped_head[↑disj_on_prev_node].toSet := by
                  unfold GroundTermMapping.applyFactSet
                  rw [GroundTermMapping.mem_applyFactSet]
                  exists f
                  constructor
                  exact List.mem_toSet.mpr f_mem
                  specialize gtm_af (gtm.applyFact f)
                    (TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set gtm f (Classical.choose trg_act).fst.val.mapped_head[↑disj_on_prev_node].toSet f_mem)
                  rcases from_trg with ⟨m, cm, cm_eq, cm_o, cm_o_eq, h⟩

                  have ex_endo := ex_endo_hom cb prev_node disj_on_prev_node prev_depth trg_on_prev_node prev_node_eq
                    t fin_disj.isLt (by grind) (CoreChaseNode.fs_terms_sub_core_terms prev_node t t_mem)

                  rcases ex_endo with ⟨gtm_endo, gtm_endo_hom, gtm_endo_endo, gtm_endo_surj⟩


                  have ex_eq_list : ∃ (tl : List (GroundTerm sig)), tl.toSet = prev_node.core.terms := by
                    have := Set.exListOfSetIfFin prev_node.core.terms (by
                      have := CoreChaseNode.all_core_finite prev_node
                      exact FactSet.terms_finite_of_finite prev_node.core this
                      )
                    rcases this with ⟨l, l_eq⟩
                    exists l
                    exact Set.ext l.toSet prev_node.core.terms l_eq

                  rcases ex_eq_list with ⟨tl, tl_eq⟩

                  have gtm_surj_list : Function.surjective_for_domain_and_image_list gtm_endo tl tl := by

                    unfold Function.surjective_for_domain_and_image_list
                    intro b b_in
                    exists b
                    constructor
                    exact b_in
                    have : b ∈ prev_node.core.terms := by grind
                    have : ∃ g, g ∈ prev_node.core ∧ b ∈ g.terms := Exists.imp (fun a a_1 => a_1) this
                    rcases this with ⟨g, g_in, g_term_in⟩
                    sorry

                  have ex_reps := gtm_endo.exists_repetition_that_is_inverse_of_surj tl gtm_surj_list

                  rcases ex_reps with ⟨k_rep, h_rep⟩
                  specialize h_rep t (by grind)


                  sorry

                specialize gtm_af f this
                exact gtm_af

          simp [next_gtm, this]

        exists next_gtm

        constructor
        · exact next_gtm_is_id_on_const
        · intro f'
          rw [GroundTermMapping.mem_applyFactSet]
          intro ⟨f, f_mem, f'_eq⟩
          rw [cb.origin_trg_result_yields_next_node_fs prev_depth next_node next_node_eq] at f_mem
          rw [f'_eq]
          cases f_mem with
            -- f comes from prev core
            | inl f_mem =>
              apply prev_gtm_hom.right
              rw [GroundTermMapping.mem_applyFactSet]
              exists f
              constructor
              · exact prev_node.core_sse.left f (by rw [prev_core_eq] at f_mem; exact f_mem)
              · apply TermMapping.apply_generalized_atom_congr_left
                intro t t_mem
                apply next_gtm_eq_prev_gtm_on_terms_in_prev_node
                exists f
                grind
            -- f comes from trg result
            | inr f_mem =>
              apply subs_contained
              have : (subs.apply_function_free_conj new_trg.rule.head[fin_disj.val]).toSet = next_gtm.applyFactSet trg_on_prev_node.val.mapped_head[↑fin_disj].toSet := by
                simp only [TermMapping.apply_generalized_atom_set_toSet]
                apply congrArg
                simp only [Fin.getElem_fin]
                rw [← PreTrigger.apply_subs_for_mapped_head_eq, ← GroundSubstitution.apply_function_free_conj_compose]
                . apply List.map_congr_left
                  intro a a_mem
                  apply TermMapping.apply_generalized_atom_congr_left
                  intro voc voc_mem
                  cases voc with
                  | const d => simp [GroundSubstitution.apply_var_or_const]
                  | var v =>
                    simp only [GroundSubstitution.apply_var_or_const, Function.comp_apply]
                    rw [next_gtm_is_subs_on_head_vars]
                    rw [FunctionFreeConjunction.mem_vars]
                    exists a
                . intros; exact next_gtm_is_id_on_const
              rw [this]
              apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
              simp [CoreChaseNode.origin_result] at f_mem
              have n_eq : (cb.prev_node prev_depth (Option.isSome_of_mem next_node_eq)) = prev_node := by grind
              have eq2 : (next_node.origin.get (origin_isSome cb prev_depth next_node_eq)).fst = trg_on_prev_node := by sorry
              have eq3 : (next_node.origin.get (origin_isSome cb prev_depth next_node_eq)).snd.val = disj_on_prev_node := by sorry
              simp only [eq2, eq3] at f_mem
              exact f_mem


  noncomputable def inductive_homomorphism_core (cb : CoreChaseBranch kb) (m : FactSet sig) (m_mod : m.modelsKb  kb) (kb_det : kb.isDeterministic) : (depth : Nat) → InductiveHomomorphismResultCore cb m depth
      | .zero => ⟨id, by
        intro cn cn_eq
        rw [cb.database_first] at cn_eq
        constructor
        · intro c; rfl
        · intro f f_in
          apply m_mod.left
          rw [Option.mem_some] at cn_eq
          simp only [FactSet.applyFactSetIdEq, ← cn_eq] at f_in
          exact f_in
      ⟩

      | .succ j =>
        let prev_gtm := (inductive_homomorphism_core cb m m_mod kb_det j).val
        let prev_gtm_hom := (inductive_homomorphism_core cb m m_mod kb_det j).property
        let prev_node := cb.branch.infinite_list j

        match prev_node_eq : prev_node with
          | .none => ⟨prev_gtm, by
            intro cn cn_eq
            rw [none_get_eq] at prev_node_eq
            have := @PossiblyInfiniteList.no_holes' _ cb.branch j prev_node_eq
            rw [Option.mem_def, this] at cn_eq
            contradiction
              ⟩
          | .some cn =>
            match c1 : Classical.propDecidable (∃ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), trg.val.active (prev_node.get (Option.isSome_of_mem prev_node_eq)).core) with
              | isTrue tr =>
                let trg := Classical.choose tr
                let trg_act := Classical.choose_spec tr
                have ex_next_node := exNextNodeIfExActiveTrigger cb j cn prev_node_eq trg (by grind)
                let next_node := Classical.choose ex_next_node
                let next_node_eq := Classical.choose_spec ex_next_node
                have := inductive_homomorphism_core_with_prev_node_and_trg_if_next_node_some
                  cb m m_mod kb_det j cn prev_node_eq prev_gtm (GroundTermMapping.subPreservesHom cn.fs m cn.fs (Set.subset_refl) prev_gtm (prev_gtm_hom cn prev_node_eq)) next_node next_node_eq
                let next_gtm := Classical.choose this
                have next_gtm_hom := Classical.choose_spec this
                ⟨next_gtm, by
                  intro cn' cn'_eq
                  have : cn' = next_node := mem_eq cb cn' next_node j.succ cn'_eq next_node_eq
                  subst next_gtm this
                  exact next_gtm_hom
                  ⟩
              | isFalse fa =>
                ⟨prev_gtm, by
                  intro cn' cn'_eq
                  have t := prev_gtm_hom cn prev_node_eq
                  simp only [not_exists] at fa
                  have next_none : (cb.branch.get? j.succ) = none := by
                    have := cb.no_succ_chase_node_if_not_exists_active_trigger_core cn j (Option.mem_def.mpr prev_node_eq) (by grind)
                    exact Option.isNone_iff_eq_none.mp this
                  rw [next_none] at cn'_eq
                  contradiction
                  ⟩



  theorem coreChaseResultIsUniversal (cb : CoreChaseBranch kb) (ter' : cb.terminates') (kb_det : kb.isDeterministic) : ∀ (m : FactSet sig), m.modelsKb kb → ∃ (h : GroundTermMapping sig), h.isHomomorphism (cb.result ter') m := by
    intro m m_mod
    let result : FactSet sig := cb.result ter'
    rcases ter' with ⟨n_ter, is_some, is_none⟩
    let h:= inductive_homomorphism_core cb m m_mod kb_det n_ter
    exists h
    have p := h.property
    unfold CoreChaseBranch.result
    have : ∃ cn_res, cb.branch.infinite_list n_ter = some cn_res := Option.ne_none_iff_exists'.mp is_some
    rcases this with ⟨cn_res, cn_res_eq⟩
    specialize p cn_res cn_res_eq
    have := homFsToFsAlsoHomCoreToFs m cn_res h.val p
    grind

  -- main theorem
  -- if cb.terminates → cb.result.universalmodels kb ∧ Set.finite cb.result
  -- ∃ fs, Set.finite fs ∧ fs.universalmodels kb → cb.terminates


  @[grind .]
  theorem cbDbInAllSucc_std (scb : ChaseBranch obs kb) (ccb : CoreChaseBranch kb) (n : Nat) (scn : ChaseNode obs kb.rules) (init : CoreChaseNode kb.rules) (init_eq : init ∈ ccb.branch.infinite_list 0) (scn_eq : scb.branch.infinite_list n = some scn):
    init.fs ⊆ scn.facts := by
      have db_funfree := kb.db.toFactSet.property.right
      have init_eq' : init.fs = kb.db.toFactSet.val := first_fs_eq ccb init init_eq
      have scb_dbf := scb.database_first
      unfold PossiblyInfiniteList.head InfiniteList.head InfiniteList.get at scb_dbf

      induction n generalizing scn with
        | zero =>
          intro f f_in
          rw [init_eq'] at f_in
          simp_all only [Option.some.injEq]
        | succ n ih =>
          have prev_cn_ex : ∃ prev_cn, scb.branch.infinite_list n = some prev_cn:= by
            exact ChaseBranch.ex_prev_node_at_each_leq_std scb (n + 1) (Option.isSome_of_mem scn_eq) n (Nat.le_add_right n 1)
          intro f f_in
          rcases prev_cn_ex with ⟨prev_cn, prev_cn_eq⟩
          specialize ih prev_cn (by grind) f f_in
          have := ChaseBranch.allFfInNextFsIfSome_std scb n prev_cn prev_cn_eq
          specialize this scn scn_eq f
          have f_in_prev_fs : f ∈ prev_cn.facts := ih
          apply this
          constructor
          exact f_in_prev_fs
          rw [init_eq'] at f_in
          exact db_funfree f f_in


  theorem allCoreChaseStepsHomSubsetOfAllStandardChaseSteps (scb : ChaseBranch obs kb) (n : Nat) (n_some : (scb.branch.infinite_list n).isSome) :
      ∀ (scn : ChaseNode obs kb.rules), scn ∈ scb.branch.get? n → ∃ (m : Nat) (ccb : CoreChaseBranch kb),
        ∀ (ccn : CoreChaseNode kb.rules), cnn ∈ ccb.branch.get? m → ccn.core.homSubset scn.facts := by sorry


  theorem allCoreChaseStepsHomSubsetOfFinalStandardChaseStep (scb : ChaseBranch obs kb) (ccb : CoreChaseBranch kb) (n_ter m : Nat)
    (ccb_m_some : (ccb.branch.infinite_list m).isSome) (last_scn : ChaseNode obs kb.rules) (scb_term : ((scb.branch.infinite_list n_ter) = some last_scn) ∧ (scb.branch.infinite_list (n_ter + 1) = none)):

      have scb_n_nter_some : (scb.branch.infinite_list n_ter).isSome = true := by
        rw [Option.isSome_iff_exists]
        exists last_scn
        exact scb_term.left

      let final_scn := (scb.branch.infinite_list n_ter).get scb_n_nter_some

      --FactSet.homSubset ((ccb.branch.infinite_list m).get (ccb_m_some)).core final_scn.facts.val := by
      ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism ((ccb.branch.infinite_list m).get (ccb_m_some)).core final_scn.facts := by
        have scb_n_nter_some : (scb.branch.infinite_list n_ter).isSome = true := by
          rw [Option.isSome_iff_exists]
          exists last_scn
          exact scb_term.left

        simp
        induction m with
          | zero =>
            exists id
            have := cbDbInAllSucc_std scb ccb n_ter ((scb.branch.infinite_list n_ter).get scb_n_nter_some) ((ccb.branch.infinite_list 0).get ccb_m_some) (Option.eq_some_of_isSome ccb_m_some) (Option.eq_some_of_isSome scb_n_nter_some)
            constructor
            exact @Function.comp ((fun a => id (GroundTerm.const a)) = GroundTerm.const)
              ((fun a => id (GroundTerm.const a)) = GroundTerm.const)
              (GroundTermMapping.isIdOnConstants id) congrFun (fun a => a) rfl
            sorry
            /-
            have eq := FactSet.applyFactSetIdEq kb.db.toFactSet.val
            rw [← eq]
            have eq' : kb.db.toFactSet.val = ((ccb.branch.infinite_list 0).get ccb_m_some).fs := by
              simp [ccb.database_first]
            grind
            -/
          | succ m ih =>
            rcases (Option.isSome_iff_exists.mp ccb_m_some) with ⟨cn_m, cn_m_eq⟩
            sorry
            /-
            grind
            have prev_some := prev_is_some_if_is_some' ccb (m + 1) cn_m cn_m_eq m (Nat.le_add_right m 1)
            specialize ih ((Option.isSomeIffNeqNone (ccb.branch.infinite_list m)).mpr prev_some)
            rcases ih with ⟨prev_hom, prev_hom_is_hom⟩

            have ex_step_hom := exHomCoreAllFollowingCore ccb m ((ccb.branch.infinite_list m).get ((Option.isSomeIffNeqNone (ccb.branch.infinite_list m)).mpr prev_some))
              (Option.eq_some_of_isSome ((Option.isSomeIffNeqNone (ccb.branch.infinite_list m)).mpr prev_some)) 1
            rw [Option.is_none_or_iff] at ex_step_hom
            specialize ex_step_hom ((ccb.branch.infinite_list (m + 1)).get ccb_m_some) (Option.eq_some_of_isSome ccb_m_some)
            rcases ex_step_hom with ⟨step_hom, step_hom_is_hom⟩

            have final_sub := finalChaseBranchNodeHomSubsetFinalCoreChaseBranchNode scb ccb n_ter n_ter last_scn cn_m scb_term

            exists (step_hom ∘ prev_hom)
            -- prev_hom : cbb.core @m → scb.fs @ n_ter
            -- step : cbb.core @m → cbb.core @ m+1
            have comp_hom_is_hom := GroundTermMapping.isHomomorphism_compose step_hom prev_hom ((ccb.branch.infinite_list m).get
              ((Option.isSomeIffNeqNone (ccb.branch.infinite_list m)).mpr prev_some)).core ((ccb.branch.infinite_list (m + 1)).get ccb_m_some).core ((scb.branch.infinite_list n_ter).get scb_n_nter_some).facts.val (step_hom_is_hom)

            -/



    -- wenn term dann gibt es eine node in der keine trigger mehr aktiv sind
    -- jedes .fs und .core @n aus der ccb ist homsubet der sbc @n

  theorem exLastNodeWithLastIndexIfTerminatesAndNoneAfter_std (scb : ChaseBranch obs kb) (ter : scb.terminates) :
    ∃ (last_cn : ChaseNode obs kb.rules) (n_ter : Nat), ((scb.branch.infinite_list n_ter) = some last_cn ∧ (scb.branch.infinite_list (n_ter + 1) = none)) := by
      sorry

  theorem exHomFromCoreIfExHomFromFs (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : (cb.branch.infinite_list n) = some cn) (fs : FactSet sig) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism cn.fs fs) :
    ∃ (gtm' : GroundTermMapping sig), gtm'.isHomomorphism cn.core fs := by
      rcases cn.core_sse.right with ⟨gtm2, gtm2_hom⟩
      sorry

  /-
    - trg_list: contains in order all the triggers used in the standard chase
    - n: to make it easier to track the last element of new_ccb (n should always be the length of new_ccb.branch.infinite_list - 1)
    - new_ccb: is used to carry the progress in between calls, final result will be then stored in new_ccb after recursion terminates

    SCB : DB → (t1) → SCN1 → (t2) → SCN2 → (t3) → SCN3 → (t4) → SCN4

    CCB : DB → (t1) → CCN1 → (t2) → CCN2 → (t3) → CCN3 → (t4) → CCN4

  -/

  -- maybe we dont want to use the list of triggers but only the list of used rules


  /-
    I need an example with the following characteristics:

      Given: A set Σ of rules and an initial instance I_0
      Goal: Construct a std. chase sequence (SCB) and a core chase sequence (CCB) on Σ and I_0 s.t.:

        - both terminate
        - the scb is longer than the ccb
        - some trigger (not the last one) used in the scb must become inapplicable in the ccb due to core computation


          I_0: A(c)

          σ_1: A(x) -> ∃z. R(x,z), R(x,x)
          σ_2: R(x,y) -> B(y)

          SC : {A(c)} + {R(c,n), R(c,c)} + {B(n)} + {B(c)}
          CC : {A(c)} + {R(c,c)} + {B(c)}

  -/

  theorem List.append_non_empty (l : List α) (e : α): (l.append [e] ≠ []) := by simp

  @[grind .]
  theorem get_origin_list_length_eq_term_n_scb (scb : ChaseBranch obs kb) (n : Nat) (term_at_n : (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone)
    (origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))
    (origin_list_eq : origin_list = ChaseBranch.get_origin_list scb n (List.range' 1 n) rfl term_at_n.left) :
      origin_list.length = n := by
        unfold ChaseBranch.get_origin_list at origin_list_eq
        simp_all

  def prev_node_std (cb : ChaseBranch obs kb) (n : Nat) (is_some : (cb.branch.get? (n+1)).isSome) : ChaseNode obs kb.rules := by
    exact (cb.branch.get? n).get (by grind)

  theorem origin_trg_is_active_prev_fs_std (cb : ChaseBranch obs kb) (n : Nat) (after : ChaseNode obs kb.rules) (after_eq : after ∈ cb.branch.get? (n+1)) :
    let prev_node : ChaseNode obs kb.rules := prev_node_std cb n (Option.isSome_of_mem after_eq)
    ∀ o, o ∈ after.origin → o.fst.val.active prev_node.facts := by
      let prev_node : ChaseNode obs kb.rules := prev_node_std cb n (Option.isSome_of_mem after_eq)
      have trg_ex := cb.triggers_exist n prev_node (sorry) after after_eq
      have trg_act := cb.triggers_active n prev_node (sorry) after after_eq
      sorry



  --@[grind .]
  theorem get_origin_list_length_eq_active_trigger_in_each_step (scb : ChaseBranch obs kb) (n m : Nat) (term_at_n : (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone)
    (origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length)) (lt : m < origin_list.length)
    (origin_list_eq : origin_list = ChaseBranch.get_origin_list scb n (List.range' 1 n) rfl term_at_n.left) :
      ∃ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), trg.val.active ((scb.branch.infinite_list m).get (by
      have len_eq : origin_list.length = n := get_origin_list_length_eq_term_n_scb scb n term_at_n origin_list origin_list_eq
      rw [len_eq] at lt
      exact ChaseBranch.all_prev_some_if_is_some_std scb n term_at_n.left m (Nat.le_of_succ_le lt)
      )).facts := by
        have len_eq : origin_list.length = n := get_origin_list_length_eq_term_n_scb scb n term_at_n origin_list origin_list_eq
        rw [len_eq] at lt
        let cm : ChaseNode obs kb.rules := ((scb.branch.infinite_list (m+1)).get (by
          by_cases c : (m + 1 = n)
          rw [c]
          exact term_at_n.left
          have c : m + 1 < n := by exact Nat.lt_of_le_of_ne lt c
          exact ChaseBranch.all_prev_some_if_is_some_std scb n term_at_n.left (m+1) (Nat.succ_le_of_lt lt)
          ))

        have := origin_trg_is_active_prev_fs_std scb (m) cm (by
          subst cm
          sorry
          )
        exists (cm.origin.get (by sorry)).fst
        sorry

  -- @[grind]
  theorem active_trigger_yields_next_chase_node_std (scb : ChaseBranch obs kb) (scn : ChaseNode obs kb.rules) (n : Nat) (scn_eq : scb.branch.infinite_list n = some scn) (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (trg_act : trg.val.active scn.facts) :
    ∃ (scn_succ : ChaseNode obs kb.rules), scb.branch.infinite_list (n+1) = some scn_succ := by
      have trg_ex := scb.triggers_exist n
      sorry
      /-
        Exists.intro
          {
            facts := ⟨scn.facts.val ∪ trg'.val.mapped_head[↑i].toSet,
            exists_trigger_opt_fs._proof_3 obs kb.rules scn trg' i⟩,
            origin := some ⟨trg', i⟩,
            facts_contain_origin_result := exists_trigger_opt_fs._proof_5 obs kb.rules scn trg' i
            } (id (Eq.symm h))
      -/

  @[grind .]
  theorem no_active_triggers_in_scb_if_empty_get_origin_list_empty (scb : ChaseBranch obs kb) (n : Nat) (term_at_n : (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone) :
    ChaseBranch.get_origin_list scb n (List.range' 1 n) rfl term_at_n.left = [] → ¬ ∃ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), trg.val.active ((scb.branch.infinite_list 0).get (by
      by_cases c : n = 0
      subst c
      exact term_at_n.left
      have gt : n > 0 := Nat.zero_lt_of_ne_zero c
      exact ChaseBranch.all_prev_some_if_is_some_std scb n term_at_n.left 0 (Nat.zero_le n)
    )).facts := by
      intro h
      apply Classical.byContradiction
      intro contra
      simp only [not_exists, Classical.not_forall, Classical.not_not] at contra
      rcases contra with ⟨trg, trg_loaded, trg_non_obs⟩
      unfold ChaseBranch.get_origin_list at h
      -- if we have an active trigger then we have a next node whose origin should be in the list but the list is empty thus we get a contradiction
      let init_scn := (scb.branch.infinite_list 0).get (by
        by_cases c : n = 0
        subst c
        exact term_at_n.left
        have gt : n > 0 := Nat.zero_lt_of_ne_zero c
        exact ChaseBranch.all_prev_some_if_is_some_std scb n term_at_n.left 0 (Nat.zero_le n)
      )
      have : ∃ (scn : ChaseNode obs kb.rules), (scb.branch.infinite_list 1) = some scn := by
        exact active_trigger_yields_next_chase_node_std scb init_scn 0 (by grind) trg ⟨trg_loaded, trg_non_obs⟩

      rcases this with ⟨scn, scn_eq⟩
      have : ChaseBranch.get_origin_list scb n (List.range' 1 n) rfl term_at_n.left ≠ [] := by
        unfold ChaseBranch.get_origin_list List.pmap
        grind
      contradiction


  -- wo ist der unterschied wenn ich anstelle von  (no_act_trg : ∀ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), ¬ trg.val.active scn.facts) als hyp
  -- statdessen (trg : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules)) und (not_active : ¬ trg.val.active scn.facts) nehme ?
  @[grind .]
  theorem no_succ_chase_node_if_not_exists_active_trigger (scb : ChaseBranch obs kb) (scn : ChaseNode obs kb.rules) (n m : Nat) (gt : m > n) (scn_eq : scb.branch.infinite_list n = some scn)
    (no_act_trg : ∀ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), ¬ trg.val.active scn.facts) : (scb.branch.infinite_list m).isNone := by
      apply Classical.byContradiction
      intro contra
      simp only [Option.isNone_iff_eq_none, ne_eq, ← Option.isSome_iff_ne_none] at contra
      have ex_cn_succ : ∃ (cn_succ : ChaseNode obs kb.rules), scb.branch.infinite_list (n+1) = some cn_succ := by
        exact ChaseBranch.ex_prev_node_at_each_leq_std scb m contra (n + 1) gt

      rcases ex_cn_succ with ⟨cn_succ, cn_succ_eq⟩
      have trg_act := scb.triggers_active n
      unfold PossiblyInfiniteList.drop InfiniteList.drop PossiblyInfiniteList.tail PossiblyInfiniteList.head InfiniteList.head InfiniteList.get InfiniteList.tail InfiniteList.get at trg_act
      simp only [Nat.succ_eq_add_one, Nat.zero_add] at trg_act
      specialize trg_act scn scn_eq cn_succ cn_succ_eq

      rcases trg_act with ⟨trg', trg'_in, trg'_act⟩
      specialize no_act_trg trg'.fst trg'_act
      contradiction



  theorem ex_list_for_set_if_finite (S : Set α) (S_fin : S.finite) : ∃ (l : List α), ∀ e, e ∈ l ↔ e ∈ S := by
    rcases S_fin with ⟨l, l_nd, l_eq⟩
    exists l

  noncomputable def generateNextCoreChaseBranchElement (o : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) (last_node : CoreChaseNode kb.rules) : CoreChaseNode kb.rules :=


    let trg_result : FactSet sig := (o.fst.val.mapped_head[o.snd]).toSet

    let trg_result_fin : trg_result.finite := List.finite_toSet o.fst.val.mapped_head[o.snd]

    let new_fs := last_node.core ∪ trg_result

    let new_fs_fin : new_fs.finite := by
      apply Set.union_finite_of_both_finite
      exact CoreChaseNode.all_core_finite last_node
      exact trg_result_fin

    let ex_new_fs_core := new_fs.exists_weak_core_for_finite_set new_fs_fin

    let new_fs_core := Classical.choose ex_new_fs_core
    let new_fs_core_prop := Classical.choose_spec ex_new_fs_core


    let next_ccn : CoreChaseNode kb.rules :=
    {
      fs := new_fs
      fs_fin := new_fs_fin
      core := new_fs_core
      is_core := new_fs_core_prop.left
      core_sse := new_fs_core_prop.right
      origin := o
      fs_contains_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
    }

    next_ccn


    -- generator from node to succ node

    noncomputable def generateNextCoreChaseBranchElement_usingTrigger (ccn : CoreChaseNode kb.rules) (o : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) : CoreChaseNode kb.rules :=

      let trg_result : FactSet sig := (o.fst.val.mapped_head[o.snd]).toSet

      let trg_result_fin : trg_result.finite := List.finite_toSet o.fst.val.mapped_head[o.snd]

      let new_fs := ccn.core ∪ trg_result
      let new_fs_fin : new_fs.finite := by
        apply Set.union_finite_of_both_finite
        exact CoreChaseNode.all_core_finite ccn
        exact trg_result_fin

    let ex_new_fs_core := new_fs.exists_weak_core_for_finite_set new_fs_fin

    let new_fs_core := Classical.choose ex_new_fs_core
    let new_fs_core_h := Classical.choose_spec ex_new_fs_core

    let ccn_succ : CoreChaseNode kb.rules := {
        fs := new_fs
        fs_fin := new_fs_fin
        core := new_fs_core
        is_core := new_fs_core_h.left
        core_sse := new_fs_core_h.right
        origin := o
        fs_contains_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
      }

    ccn_succ


  noncomputable def generateNextCoreChaseBranchElement_usingTrigger_only_active_opt (ccn : CoreChaseNode kb.rules) (o : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) : Option (CoreChaseNode kb.rules) :=
    match Classical.propDecidable (o.fst.val.active ccn.core) with
      | isTrue _ =>
        generateNextCoreChaseBranchElement_usingTrigger ccn o
      | isFalse _ =>
        none


  theorem exists_active_trigger_of_step [DecidableEq β] (origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))
    (init_ccn : CoreChaseNode kb.rules) (node_list : (List (CoreChaseNode kb.rules × Option ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))))
    (node_list_eq : node_list = foldl_save_hist_opt_nodup_trace origin_list init_ccn generateNextCoreChaseBranchElement_usingTrigger_only_active_opt)
    (n : Nat) (h : n + 1 < node_list.length) (before after : CoreChaseNode kb.rules)
    (before_eq : before = (node_list.get ⟨n, (Nat.lt_of_succ_lt h)⟩).fst) (after_eq : after = (node_list.get ⟨n+1, Nat.lt_of_succ_le h⟩).fst) (origin_some : after.origin ≠ none) :
      (after.origin.get (Option.isSome_iff_ne_none.mpr origin_some)).fst.val.active before.core := by
        --subst before_eq after_eq node_list_eq
        unfold foldl_save_hist_opt_nodup_trace at *

        have hstep : after ≠ before := by
          have := foldl_save_hist_opt_nodup_trace_adjacent_ne
            origin_list init_ccn generateNextCoreChaseBranchElement_usingTrigger_only_active_opt n
            (Nat.lt_of_lt_of_eq h (congrArg List.length node_list_eq))
          subst node_list_eq after_eq before_eq
          -- because nodup
          sorry

        have hex :
          ∃ o ∈ origin_list,
            generateNextCoreChaseBranchElement_usingTrigger_only_active_opt before o = some after := by sorry

        rcases hex with ⟨o, ho_mem, hgen⟩

        unfold generateNextCoreChaseBranchElement_usingTrigger_only_active_opt at hgen

        cases hdec :
          Classical.propDecidable ((after.origin.get (Option.isSome_iff_ne_none.mpr origin_some)).fst.val.active before.core) with
        | isTrue hactive =>
          exact hactive
        | isFalse hnot =>

          -- then result is none → contradiction
            simp_all
            sorry


  noncomputable def buildCoreChaseBranchFromChaseBranch (scb : ChaseBranch obs kb) (scb_term : scb.terminates) : CoreChaseBranch kb :=


    let origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) := by sorry

    let init_ccn : CoreChaseNode kb.rules := {
              fs := kb.db.toFactSet
              fs_fin := kb.db.toFactSet.property.left
              core := kb.db.toFactSet
              is_core := eachKbDbIsWeakCore kb
              core_sse := by
                constructor
                exact fun _ a => a
                exists id
                exact GroundTermMapping.id_is_hom
              origin := none,
              fs_contains_origin_result := by simp
              }

  /-
  computes node list

    origin_list = [o1, o2, o3]

    cn1 = generateNextCoreChaseBranchElement_usingTrigger init_ccn o1
    cn2 = generateNextCoreChaseBranchElement_usingTrigger cn1 o1
    cn3 = generateNextCoreChaseBranchElement_usingTrigger cn2 o1

    node_list = [init_ccn cn1, cn2, cn3]


  -/

  let node_list := foldl_save_hist_opt_nodup origin_list init_ccn generateNextCoreChaseBranchElement_usingTrigger_only_active_opt

    let new_ccb : CoreChaseBranch kb := {


      branch := PossiblyInfiniteList.from_list node_list
      database_first := by
        rw [PossiblyInfiniteList.get?_from_list, ← List.head?_eq_getElem?]
        exact foldl_save_hist_opt_nodup_head_eq
          origin_list init_ccn generateNextCoreChaseBranchElement_usingTrigger_only_active_opt

      triggers_active := by
        intro n before before_eq after after_eq
        have after_origin_some : after.origin ≠ none := by sorry -- weil nicht first
        exists (after.origin.get (Option.isSome_iff_ne_none.mpr after_origin_some))
        constructor
        exact Option.get_mem (Option.isSome_iff_ne_none.mpr after_origin_some)
        sorry

      triggers_exist := by
        simp only [PossiblyInfiniteList.get?_from_list]
        intro n before before_eq after after_eq
        have after_origin_some : after.origin ≠ none := by sorry -- weil nicht first


        let trg := (after.origin.get (Option.isSome_iff_ne_none.mpr after_origin_some)).fst
        let disj := (after.origin.get (Option.isSome_iff_ne_none.mpr after_origin_some)).snd
        let trg_result : FactSet sig := (trg.val.mapped_head[disj]).toSet
        let trg_result_fin : trg_result.finite := List.finite_toSet trg.val.mapped_head[disj]

        let new_fs := before.core ∪ trg_result
        let new_fs_fin : new_fs.finite := by
          apply Set.union_finite_of_both_finite
          exact CoreChaseNode.all_core_finite before
          exact trg_result_fin

        let ex_new_fs_core := new_fs.exists_weak_core_for_finite_set (Set.finite_of_subset_finite new_fs_fin fun e a => a)
        let core := Classical.choose ex_new_fs_core
        let core_wc := (Classical.choose_spec ex_new_fs_core).left
        let core_sub := (Classical.choose_spec ex_new_fs_core).right

        exists trg, disj, core, core_wc, core_sub
        -- benötig theorem wie n+1 aussieht wenn man n hat
        sorry


      fairness := sorry
    }

  new_ccb




  theorem buildCoreChaseBranchFromChaseBranch_terminates (scb : ChaseBranch obs kb) (scb_term : scb.terminates) :
    (buildCoreChaseBranchFromChaseBranch scb scb_term).terminates := by sorry



  /-## 1)
  -/
  noncomputable def buildCoreChaseFromPsc : true := sorry

  -- erst psc aus scb und dann ccb aus psc bauen
  noncomputable def buildCoreChaseFromStandardChase : true := sorry

  noncomputable def build_psc_from_scb_then_ccb_from_psc (scb : ChaseBranch obs kb) : CoreChaseBranch kb :=

    sorry

  --theorem exChaseBranchIfExCoreChaseBranch (ccb : CoreChaseBranch kb) : ∃ scb : ChaseBranch obs kb, True := by sorry



  theorem notExistsTerminatingChaseBranchIfNotExistsTerminatingCoreChaseBranch (ccb : CoreChaseBranch kb) (ccb_non_term : ¬ ccb.terminates) : ∃ (scb : ChaseBranch obs kb), ¬ scb.terminates := by

    sorry

  theorem existsNonTerminatingChaseBranchIfExistsNonTerminatingCoreChaseBranch (ccb : CoreChaseBranch kb) (ccb_term : ¬ ccb.terminates) : ∃ (scb : ChaseBranch obs kb), ¬ scb.terminates := by
    sorry


  -- zeigen dass ich aus der core chase eine psc und auch aus der standard chase eine psc bauen kann. Da in (10.) eine core

  -- aus psc eine core chase bauen, dann können wir aus der standard chase eine psc und aus der psc eine core chase bauen.

  -- a = b und c = b auch a = c


  theorem exTerminatingCoreChaseBranchIfExTerminatingChaseBranch (scb : ChaseBranch obs kb) (scb_term : scb.terminates) :
    ∃ (ccb : CoreChaseBranch kb), ccb.terminates' := by
      rcases scb.terminating_has_last_index_std.mp scb_term with ⟨n_ter, some_at, none_beyond⟩
      exists buildCoreChaseBranchFromChaseBranch scb scb_term
      have := buildCoreChaseBranchFromChaseBranch_terminates scb scb_term
      grind



  -- brauchen wir kb.det ?
  theorem main_lhs (ccb : CoreChaseBranch kb) (kb_det : kb.isDeterministic) : (∃ (fs : FactSet sig), fs.finite ∧ fs.universallyModelsKb kb) → ccb.terminates' := by

    -- 2.
    intro ⟨U, U_fin, U_umod⟩
    apply terminates'IfTerminatesAndNonEmpty
    have := ccb.database_first
    exists 0
    exact Option.isSome_of_mem this


    -- start of proof
    -- 1.
    apply Classical.byContradiction
    intro contra

    -- 3.
    have inf_scb := notExistsTerminatingChaseBranchIfNotExistsTerminatingCoreChaseBranch ccb contra
    rcases existsNonTerminatingChaseBranchIfExistsNonTerminatingCoreChaseBranch ccb contra with ⟨scb, scb_non_term⟩

    have scb_all_some : ∀ (n : Nat), (scb.branch.infinite_list n).isSome := by
      intro n
      apply Classical.byContradiction
      intro contra
      simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at contra
      unfold ChaseDerivation.terminates ChaseDerivationSkeleton.terminates PossiblyInfiniteList.finite at scb_non_term
      simp at scb_non_term
      specialize scb_non_term n
      contradiction


    -- 4.
    -- R = A_ω
    let R := scb.result

    have R_umod : R.universallyModelsKb kb := ChaseBranch.deterministicChaseBranchResultUniversallyModelsKb scb kb_det

    -- 5.
    have hom_U_R : ∃ (h : GroundTermMapping sig), h.isHomomorphism U R := by
      rcases U_umod with ⟨U_umod_l, U_umod_r⟩
      specialize U_umod_r R ChaseBranch.result_models_kb
      exact U_umod_r

    -- 6.
    have hom_R_U : ∃ (h : GroundTermMapping sig), h.isHomomorphism R U := by
      rcases R_umod with ⟨R_umod_l, R_umod_r⟩
      specialize R_umod_r U U_umod.left
      exact R_umod_r

    have monotonicity : ∀ (n : Nat), ((scb.branch.infinite_list (n)).get (scb_all_some (n))).facts ⊆ ((scb.branch.infinite_list (n+1)).get (scb_all_some (n+1))).facts := by
      intro n f f_in
      exact ChaseBranch.stepIsSubsetOfAllFollowing scb n 1 ((scb.branch.get? n).get (scb_all_some n)) ((scb.branch.get? (n+1)).get (scb_all_some (n+1)))
        (Option.get_mem (scb_all_some n)) (Option.get_mem (scb_all_some (n + 1))) f f_in

    -- 7.
    have f_first_somewhere : ∀ (f : Fact sig), f ∈ R → ∃ (n_min : Nat), f ∈ ((scb.branch.infinite_list (n_min)).get (scb_all_some (n_min))).facts ∧
      ∀ (m : Nat), m < n_min → ¬ f ∈ ((scb.branch.infinite_list (m)).get (scb_all_some (m))).facts := by

        intro f f_in_R
        simp only [R] at f_in_R
        unfold ChaseDerivationSkeleton.result at f_in_R

        rcases f_in_R with ⟨cn, cn_in1, cn_in2⟩
        have : ∃ n, cn ∈ scb.branch.get? n := InfiniteList.mem_iff.mp cn_in1
        rcases this with ⟨n, cn_eq⟩
        unfold PossiblyInfiniteList.get? at cn_eq
        -- the set of indices in the scb where f appears in scn.facts
        let Ix := fun (n : Nat) => f ∈ ((scb.branch.infinite_list n).get (scb_all_some n)).facts
        have Ix_non_empty : ∃ (n : Nat), Ix n := by
          simp only [Ix]
          exists n
          have eq : ((scb.branch.infinite_list n).get (scb_all_some n)) = cn := Option.get_of_eq_some (scb_all_some n) cn_eq
          rw [eq]
          exact Set.mem_of_subset_of_mem (fun e a => a) cn_in2

        -- well ordering principle
        have hmin := wop Ix Ix_non_empty
        rcases hmin with ⟨n_min, h1, h2⟩
        have t1 : f ∈ ((scb.branch.infinite_list n_min).get (scb_all_some n_min)).facts := h1
        have t2 : ∀ n, f ∈ ((scb.branch.infinite_list n).get (scb_all_some n)).facts → n_min ≤ n := h2

        have nin_before : ∀ (n : Nat), n < n_min → ¬ f ∈ ((scb.branch.infinite_list (n)).get (scb_all_some (n))).facts := by
          intro n lt contra
          have := h2 n contra
          grind

        exists n_min

    -- 8.

    have ex_hom_U_An : ∃ (n : Nat) (gtm : GroundTermMapping sig), gtm.isHomomorphism U ((scb.branch.get? n).get (scb_all_some n)).facts := by


      rcases hom_U_R with ⟨gtm_U_R, gtm_U_R_hom⟩

      -- the set of indices in the scb where f appears in scn.facts
      let Ix := fun (n : Nat) => U ⊆ ((scb.branch.get? n).get (scb_all_some n)).facts
      have Ix_non_empty : ∃ (n : Nat), Ix n := by
        simp only [Ix]
        apply Classical.byContradiction
        intro contra
        simp only [not_exists] at contra
        have : ∀ n, ((scb.branch.get? n).get (scb_all_some n)).facts ⊆ R := by sorry
        have sub : R ⊆ U := by sorry
        sorry

      have hmin := wop Ix Ix_non_empty
      rcases hmin with ⟨n_min, h1, h2⟩

      have t1 : U ⊆ ((scb.branch.infinite_list n_min).get (scb_all_some n_min)).facts := h1
      have t2 : ∀ n, U ⊆ ((scb.branch.infinite_list n).get (scb_all_some n)).facts → n_min ≤ n := h2

      exists n_min
      exact FactSet.exHomSubToSet U ((scb.branch.get? n_min).get (scb_all_some n_min)).facts h1


    -- 9.
    rcases ex_hom_U_An with ⟨n_max, ⟨gtm_U_An, gtm_U_An_hom⟩⟩

    let An := ((scb.branch.infinite_list n_max).get (scb_all_some n_max)).facts

    have ex_hom_An_U : ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism An U := by

      have sub : An ⊆ R := by
        have := ChaseBranch.stepIsSubsetOfResult scb n_max
        exact this ((scb.branch.infinite_list n_max).get (scb_all_some n_max)) (Option.eq_some_of_isSome (scb_all_some n_max))


      have ex_gtm_An_R : ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism An R := FactSet.exHomSubToSet An R sub
      rcases ex_gtm_An_R with ⟨gtm_An_R, gtm_An_R_hom⟩
      rcases hom_R_U with ⟨gtm_R_U, gtm_R_U_hom⟩
      exists (gtm_R_U ∘ gtm_An_R)
      apply GroundTermMapping.isHomomorphism_compose gtm_An_R gtm_R_U An R U gtm_An_R_hom gtm_R_U_hom


    -- 10. --> how even ?
    -- zeigen das psc eq ccb

    have An_fin : An.finite := by sorry

    have ex_An_core : ∃ (An_core : FactSet sig), An_core.isWeakCore ∧ An_core.homSubset An := An.exists_weak_core_for_finite_set An_fin



    have psc : PseudoCoreChaseBranch kb := {
      branch := PossiblyInfiniteList.from_list (scb.branch.prefixUpTo n_max)
      database_first := by
        have dbf := scb.database_first
        rw [PossiblyInfiniteList.head_eq] at dbf
        unfold PossiblyInfiniteList.get? InfiniteList.get at dbf
        unfold PossiblyInfiniteList.prefixUpTo List.filterMap
        simp only [PossiblyInfiniteList.get?_from_list]
        split
        next x heq =>
          rw [List.range_eq_nil] at heq
          contradiction
        next lst n1 n1l heq =>
          split
          next =>
            grind
          next opt cn cn_eq =>
            simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.some.injEq]
            have := List.range_head_eq (List.range (n_max + 1)) n_max (List.toList_toArray)
            have n1_eq : n1 = 0 := by grind
            subst n1
            rw [dbf, Option.some_inj] at cn_eq
            exact Eq.symm cn_eq

      triggers_active := by
        intro n before before_eq after after_eq

        have := scb.triggers_active n before sorry after sorry
        exact this

      triggers_exist := sorry
      fairness := sorry
      last_index := n_max
      terminates_at := by
        intro n gt
        constructor
        unfold PossiblyInfiniteList.prefixUpTo
        sorry
        sorry




      core_node := sorry
      core_node_eq := sorry

    }

    have ex_ccb_with_An_core : ∃ (ccb_with_An_core : CoreChaseBranch kb) (m : Nat), ((ccb_with_An_core.branch.infinite_list m).get sorry).core.homSubset An := by sorry

    -- 11.
    -- core calc only necc after fin steps

    -- für jeden step in der scb kann man einen core berechen
    have ex_core_of_scn_step (scb : ChaseBranch obs kb) (n : Nat) (scn : ChaseNode obs kb.rules) (scn_eq : scb.branch.infinite_list n = some scn) :
      ∃ (c : FactSet sig), c.isWeakCore ∧ c.homSubset scn.facts := by
        sorry
        /-
        rcases (scn.facts.property) with ⟨scn_fsl, scn_fsl_nodup, scn_fsl_eq⟩
        have ex_wc_sub := FactSet.exists_weak_core_for_finite_set scn_fsl.length scn_fsl rfl
        rcases ex_wc_sub with ⟨c, wc, sub, ⟨gtm, gtm_hom⟩⟩
        exists c
        constructor
        exact wc
        have eq : scn_fsl.toSet = scn.facts.val := Set.ext scn_fsl.toSet scn.facts.val scn_fsl_eq
        rw [← eq]
        exact ⟨sub, Exists.intro gtm gtm_hom⟩
        -/


    -- nehme den core den man aus der stelle n im scn berechnet hat
    rcases (ex_core_of_scn_step scb n_max ((scb.branch.infinite_list n_max).get (scb_all_some n_max)) (Option.eq_some_of_isSome (scb_all_some n_max))) with ⟨An_core, An_core_wc, An_core_homsub⟩

    -- es gibt eine stelle im ccb wo der core gleich (nur isomorph ?) zum scn_core (aus der zeile drüber) ist
    have : ∃ (n : Nat), ((ccb.branch.infinite_list n).get sorry).core = An_core := by sorry

    -- variante mit iso, ist iso def correct ?
    have scn_core_iso_some_ccb_core : ∃ (n : Nat) (iso : GroundTermMapping sig), iso.isIsomorphism An_core ((ccb.branch.infinite_list n).get sorry).core := by sorry


    -- 12.

    have ex_U_core : ∃ (c : FactSet sig), c.isWeakCore ∧ c.homSubset U := by
      --rcases U_fin with ⟨Ul, Ul_nodup, Ul_eq⟩
      have ex_wc_sub := FactSet.exists_weak_core_for_finite_set U U_fin
      rcases ex_wc_sub with ⟨c, wc, sub, ⟨gtm, gtm_hom⟩⟩
      exists c
      constructor
      exact wc
      exact ⟨sub, Exists.intro gtm gtm_hom⟩

    rcases ex_U_core with ⟨U_core, U_core_wc, U_core_homsub⟩

    have core_An_iso_core_U : ∃ (iso : GroundTermMapping sig), iso.isIsomorphism An_core U_core ∧ U_core.homSubset U := by sorry

    have An_umod : An_core.universallyModelsKb kb := by sorry

    rcases ex_ccb_with_An_core with ⟨constructed_ccb, location_of_homsub_of_An_in_constructed_ccb, is_homsub⟩

    have mod_term : ∀ (n : Nat), (((constructed_ccb.branch.infinite_list n).get sorry).core.universallyModelsKb kb) → constructed_ccb.terminates_at_step n := by sorry


    rcases An_umod with ⟨An_mod, An_univ⟩

    --specialize An_univ U U_umod.left

    specialize mod_term location_of_homsub_of_An_in_constructed_ccb sorry

    sorry



    -- contradiction



  /-
    CC : Core Chase, SC : Standard Chase

    Proof for "If there exists a finite universal model for I,Σ then there exists a CC sequecne that termiantes on I,Σ"

      Let U be an universal finite model for I,Σ
      Assume towards contradiction that every CC sequence does not terminate

      We know (proof needed) that the existence of a finite SC sequence would imply the existence of a finite CC sequence.
        -> Idea: Using same triggers in each step if applicable
      → Thus, every SC sequence is infinite.
      Since there exists at least one SC sequence (I guess this also needs to be proven as a very general result: Every KB admits a chase sequence.)
      we have an infinite SC sequence A = A_0, A_1, A_2, ...

      Define the Result of the SC as R = (⋃_i A_i)
      → We know that R is an universal model for I,Σ (proven result)

      As U and R are both universal models for I,Σ, we get U → R and R → U

      As each fact f in R is derived after some finite step i there is some A_i where f appears first
      → As U contains only finitely many facts and A_i ⊆ A_{i+1} there is some A_n where U → A_n holds

      → we also have A_n → U since A_n is a subset of R
      → Goal: find a CC seq which contains core(A_n)
            Idea: just take SC up to A_n and then compute the core once
                -> show that an equivalent CC seq exists that computes a core after each step
          Then we know that the CC seq reaches A_n.
          Since core(A_n) and core(U) are isomorphic, core(A_n) is a model and therefore the CC seq terminates once it reaches A_n. This contradicts our original assumption.


  -/


end CoreChaseBranch
