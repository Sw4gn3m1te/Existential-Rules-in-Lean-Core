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

  theorem notExActTrigInMod_std (scb : ChaseBranch obs kb) (m : ChaseNode obs kb.rules) (m_mod : m.facts.modelsKb kb) : ¬ ∃ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), trg.val.active m.facts := by
    apply Classical.byContradiction
    intro contra
    simp only [Classical.not_not] at contra
    rcases contra with ⟨trg, trg_act⟩
    rcases trg_act with ⟨trg_loaded, trg_not_obs⟩
    simp only [obs, RestrictedObsolescence] at *
    have ex_hom : ∃ (j : Fin trg.val.mapped_head.length) (gtm : GroundTermMapping sig), gtm.isHomomorphism (trg.val.mapped_head[↑j]'(j.isLt)).toSet m.facts := by sorry
    rcases ex_hom with ⟨j, gtm, gtm_hom⟩
    have trg_len_eq : trg.val.mapped_head.length = trg.val.rule.head.length := PreTrigger.length_mapped_head trg.val.toPreTrigger
    apply trg_not_obs
    exists (Fin.cast trg_len_eq j), (trg.val.subs_for_mapped_head j)
    constructor
    intro v v_in
    sorry
    intro e e_in
    unfold GroundSubstitution.apply_function_free_conj TermMapping.apply_generalized_atom_list at e_in
    rw [List.mem_toSet, List.mem_map] at e_in
    rcases e_in with ⟨a, ahl, ahr⟩
    rw [← GroundSubstitution.apply_function_free_atom.eq_def] at ahr
    rw [← ahr]
    apply gtm_hom.right
    sorry


  @[grind .]
  theorem fs_terms_sub_core_terms (cn : CoreChaseNode kb.rules) (t : GroundTerm sig) (t_in_core : t ∈ cn.core.terms) : t ∈ cn.fs.terms := by
      rcases t_in_core with ⟨f, f_c, f_t⟩
      have f_fs : f ∈ cn.fs := cn.core_sse.left f f_c
      exists f

  theorem func_term_not_mem_head {cb : CoreChaseBranch kb} {t : GroundTerm sig} (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) :
    ¬ t ∈ cb.head.fs.terms := by
      intro t_mem
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rcases kb.db.toFactSet.property.right f (by grind) t t_mem with ⟨c, t_eq⟩
      rcases t_is_func with ⟨_, _, _, t_eq'⟩
      rw [t_eq'] at t_eq
      simp [GroundTerm.func_neq_const] at t_eq


theorem ex_endo_hom  (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules)
    (disj_idx n : Nat) (trg: RTrigger obs.toLaxObsolescenceCondition kb.rules) (cn_eq : cb.branch.infinite_list n = some cn)
    (t : GroundTerm sig ) (lt : disj_idx < trg.val.rule.head.length)
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) (t_mem_node : t ∈ cn.fs.terms) :
      ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet cn.core ∧ gtm.isHomomorphism cn.core cn.core ∧ (Function.surjective_for_domain_and_image_set gtm cn.core.terms cn.core.terms) := by
        sorry

  -- jeder surjektive endomorphisms auf endlichen mengen ist auch ein isomorphismus

  theorem triggerInactiveAfterApplication' (cb : CoreChaseBranch kb) (cn cn_succ : CoreChaseNode kb.rules) (n k : Nat)
    (cn_eq : cn ∈ cb.branch.infinite_list n) (cn_succ_eq : cn_succ ∈ cb.branch.infinite_list (n + k))
    (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (trg_act_cn : trg.val.active cn.core) :
      ¬ trg.val.active cn_succ.core := by sorry

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

        have next_gtm_eq_prev_gtm_on_terms_in_node : ∀ t ∈ prev_node.core.terms, next_gtm t = prev_gtm t := by
          intro t t_mem
          have : ¬ t ∈ trg_on_prev_node.val.fresh_terms_for_head_disjunct fin_disj.val fin_disj.isLt := by
            intro contra
            apply trg_active_prev_core.right
            apply obs.contains_trg_result_implies_cond disj_on_prev_node
            have := cb.result_of_trigger_introducing_functional_term_occurs_in_chase_core' prev_node disj_on_prev_node prev_depth (Classical.choose trg_act).fst
              (Option.mem_def.mpr prev_node_eq) t fin_disj.isLt (by grind) (fs_terms_sub_core_terms prev_node t t_mem)
            rcases this with ⟨gtm, gtm_idc, gtm_af⟩
            intro f f_in
            specialize gtm_af f sorry -- ASK: overcooked ?
            exact gtm_af
          simp  [next_gtm, this]

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
                apply next_gtm_eq_prev_gtm_on_terms_in_node
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
              --have : ↑(next_node.origin.get (origin_isSome cb prev_depth next_node_eq)).snd = fin_disj.val:= by grind
              sorry -- ASK
              --exact f_mem


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
                    have := cb.no_succ_chase_node_if_not_exists_active_trigger cn j (Option.mem_def.mpr prev_node_eq) (by grind)
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


  theorem coreAndStandardChaseEqStart (scb : ChaseBranch obs kb) (ccb : CoreChaseBranch kb) (scn : ChaseNode obs kb.rules) (ccn : CoreChaseNode kb.rules) (scn_eq : scn ∈ scb.branch.get? 0) (ccn_eq : ccn ∈ ccb.branch.get? 0):
    scn.facts = ccn.fs := by
      have ccb_dbf := ccb.database_first
      have scb_dbf := scb.database_first
      unfold PossiblyInfiniteList.head InfiniteList.head InfiniteList.get at *
      have : scn.facts = kb.db.toFactSet.val := by sorry
      have : ccn.fs = kb.db.toFactSet.val := by sorry
      grind


  @[grind]
  theorem cbDbInAllSucc_std (scb : ChaseBranch obs kb) (ccb : CoreChaseBranch kb) (n : Nat) (scn : ChaseNode obs kb.rules) (init : CoreChaseNode kb.rules) (init_eq : ccb.branch.infinite_list 0 = some init) (scn_eq : scb.branch.infinite_list n = some scn):
    init.fs ⊆ scn.facts := by
      have db_funfree := kb.db.toFactSet.property.right
      have init_eq' : init.fs = kb.db.toFactSet.val := by sorry
      have scb_dbf := scb.database_first
      unfold PossiblyInfiniteList.head InfiniteList.head InfiniteList.get at scb_dbf

      induction n generalizing scn with
        | zero =>
          intro f f_in
          rw [init_eq'] at f_in
          simp_all only [Option.some.injEq]
        | succ n ih =>
          have prev_cn_ex : ∃ prev_cn, scb.branch.infinite_list n = some prev_cn:= by
            have := ChaseBranch.prev_is_some_if_is_some_std scb (n + 1) (Option.NeqNoneIfIsSome (scb.branch.infinite_list (n + 1)) scn scn_eq) n (Nat.lt_add_one n)
            exact Option.ne_none_iff_exists'.mp this
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


  theorem exHomFactorization (cb : CoreChaseBranch kb) (A B C : CoreChaseNode kb.rules) (n m : Nat) (gt : m > n + 1)
    (A_eq : cb.branch.infinite_list n = some A) (B_eq : cb.branch.infinite_list (n + 1) = some B) (C_eq : cb.branch.infinite_list m = some C)
    (gtm : GroundTermMapping sig) (gtm_eq : gtm.isHomomorphism A.core C.core) :
      ∃ (gtm' : GroundTermMapping sig), gtm'.isHomomorphism B.core C.core := by
        sorry

  theorem exHomFactorization_std (scb : ChaseBranch obs kb) (A B C : ChaseNode obs kb.rules) (n m : Nat) (gt : m > n + 1)
    (A_eq : scb.branch.infinite_list n = some A) (B_eq : scb.branch.infinite_list (n + 1) = some B) (C_eq : scb.branch.infinite_list m = some C)
    (gtm : GroundTermMapping sig) (gtm_eq : gtm.isHomomorphism A.facts C.facts) :
      ∃ (gtm' : GroundTermMapping sig), gtm'.isHomomorphism B.facts C.facts := by
        apply Classical.byContradiction
        intro contra

        let R := scb.result
        /-
        have R_umod : R.universallyModelsKb kb := by
          constructor
          exact ChaseBranch.result_models_kb scb
          have := deterministicChaseBranchResultUniversallyModelsKb scb sorry
          unfold FactSet.universallyModelsKb at this
          exact this.right
        -/
        have : R.universallyModelsKb kb → False := by sorry
        apply this
        apply Classical.byContradiction
        intro contra2

        have t1 : ∃ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), trg.val.active R := by
          apply Classical.byContradiction
          intro contra
          simp at contra
          unfold FactSet.universallyModelsKb at contra2
          simp only [Classical.not_and_iff_not_or_not] at contra2
          sorry

        sorry

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

  theorem finFactSetHasCore (fs : FactSet sig) (fin : fs.finite) : ∃ (c : FactSet sig), c.isWeakCore ∧ c.homSubset fs := by
    sorry

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

  noncomputable def buildCoreChaseBranchFromChaseBranch_rec (trg_list :  List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))
    (new_ccb_branch : List (CoreChaseNode kb.rules)) (non_empty : new_ccb_branch ≠ []) : List (CoreChaseNode kb.rules) :=
      match c : trg_list with
        -- there are no more triggers left to build into the new ccb
        -- wir müssen den ganzen origin mitnehmen
        | .nil => new_ccb_branch
        | .cons hd tl =>

          let trg := hd.fst
          let fin_i := hd.snd

          -- we need this to show new_ccb.isSome at n
          let prev_ccn : CoreChaseNode kb.rules := new_ccb_branch.getLast non_empty

          let trg_act_in_prev_core := Classical.propDecidable (trg.val.active prev_ccn.core)

          -- match if trg applicable in core chase env
          match trg_act_in_prev_core with

            -- if trigger is active on prev nodes core then we fire it, create the new resulting node and add it to new_ccb

            | Decidable.isTrue trg_act =>
              -- ist das die richtige idee an den index zu kommen ?

              let trg_result : FactSet sig := (trg.val.mapped_head[fin_i]).toSet

              let trg_result_fin : trg_result.finite := List.finite_toSet trg.val.mapped_head[fin_i]

              let new_fs := prev_ccn.core ∪ trg_result

              let new_fs_fin : new_fs.finite := by
                apply Set.union_finite_of_both_finite
                exact CoreChaseNode.all_core_finite prev_ccn
                exact trg_result_fin

              let ex_new_fs_core := finFactSetHasCore new_fs new_fs_fin

              let new_fs_core := Classical.choose ex_new_fs_core
              let new_fs_core_prop := Classical.choose_spec ex_new_fs_core


              let next_ccn : CoreChaseNode kb.rules :=
              {
                fs := new_fs
                fs_fin := new_fs_fin
                core := new_fs_core
                is_core := new_fs_core_prop.left
                core_sse := new_fs_core_prop.right
                origin := some ⟨trg, fin_i⟩
                fs_contains_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
              }

              let new_ccb_branch' : List (CoreChaseNode kb.rules) := (new_ccb_branch.append [next_ccn])

              buildCoreChaseBranchFromChaseBranch_rec tl new_ccb_branch' (List.append_non_empty new_ccb_branch next_ccn)

            | Decidable.isFalse _ =>
              buildCoreChaseBranchFromChaseBranch_rec tl new_ccb_branch (non_empty)



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
      have := ChaseBranch.prev_eq_is_some_if_is_some'_std scb n term_at_n.left m (by exact Nat.le_of_succ_le lt)
      exact Option.isSome_iff_ne_none.mpr this
      )).facts := by
        have len_eq : origin_list.length = n := get_origin_list_length_eq_term_n_scb scb n term_at_n origin_list origin_list_eq
        rw [len_eq] at lt
        let cm : ChaseNode obs kb.rules := ((scb.branch.infinite_list (m+1)).get (by
          by_cases c : (m + 1 = n)
          rw [c]
          exact term_at_n.left
          have c : m + 1 < n := by exact Nat.lt_of_le_of_ne lt c
          have := ChaseBranch.prev_eq_is_some_if_is_some'_std scb n term_at_n.left (m+1) lt
          exact Option.isSome_iff_ne_none.mpr this
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

  @[grind]
  theorem no_active_triggers_in_scb_if_empty_get_origin_list_empty (scb : ChaseBranch obs kb) (n : Nat) (term_at_n : (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone) :
    ChaseBranch.get_origin_list scb n (List.range' 1 n) rfl term_at_n.left = [] → ¬ ∃ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), trg.val.active ((scb.branch.infinite_list 0).get (by
      by_cases c : n = 0
      subst c
      exact term_at_n.left
      have gt : n > 0 := Nat.zero_lt_of_ne_zero c
      exact ChaseBranch.prev_is_some_if_is_some'_std scb n term_at_n.left 0 gt
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
        exact ChaseBranch.prev_is_some_if_is_some'_std scb n term_at_n.left 0 gt)
      have : ∃ (scn : ChaseNode obs kb.rules), (scb.branch.infinite_list 1) = some scn := by
        exact active_trigger_yields_next_chase_node_std scb init_scn 0 (by grind) trg ⟨trg_loaded, trg_non_obs⟩

      rcases this with ⟨scn, scn_eq⟩
      have : ChaseBranch.get_origin_list scb n (List.range' 1 n) rfl term_at_n.left ≠ [] := by
        unfold ChaseBranch.get_origin_list List.pmap
        split
        next => grind
        next => grind
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
        have := ChaseBranch.prev_eq_is_some_if_is_some'_std scb m contra (n + 1) gt
        exact Option.ne_none_iff_exists'.mp this
      rcases ex_cn_succ with ⟨cn_succ, cn_succ_eq⟩
      have trg_act := scb.triggers_active n
      unfold PossiblyInfiniteList.drop InfiniteList.drop PossiblyInfiniteList.tail PossiblyInfiniteList.head InfiniteList.head InfiniteList.get InfiniteList.tail InfiniteList.get at trg_act
      simp only [Nat.succ_eq_add_one, Nat.zero_add] at trg_act
      specialize trg_act scn scn_eq cn_succ cn_succ_eq

      rcases trg_act with ⟨trg', trg'_in, trg'_act⟩
      specialize no_act_trg trg'.fst trg'_act
      contradiction

  theorem buildCoreChaseBranchFromChaseBranch_rec_head' (origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))
    (hd : CoreChaseNode kb.rules) (tl : List (CoreChaseNode kb.rules)) :
      (buildCoreChaseBranchFromChaseBranch_rec origin_list (hd :: tl) (List.cons_ne_nil hd tl))[0]? = some hd := by

      unfold buildCoreChaseBranchFromChaseBranch_rec
      simp only [Fin.getElem_fin, List.append_eq, List.cons_append]
      cases c : origin_list with
          | nil => rfl
          | cons hd_o tl_o =>
            simp
            cases c2 : Classical.propDecidable (hd_o.fst.val.active ((hd :: tl).getLast (List.cons_ne_nil hd tl)).core) with
              | isTrue t =>
                simp
                exact buildCoreChaseBranchFromChaseBranch_rec_head' tl_o hd _
              | isFalse f =>
                simp
                exact buildCoreChaseBranchFromChaseBranch_rec_head' tl_o hd tl

  @[simp, grind =]
  theorem buildCoreChaseBranchFromChaseBranch_rec_nil (l : List (CoreChaseNode kb.rules)) (l_non_empty : l ≠ []) : buildCoreChaseBranchFromChaseBranch_rec [] l l_non_empty = l := by rfl

  theorem buildCoreChaseBranchFromChaseBranch_rec_cons_trg_act (hd : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length)
    (tl : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length)) (l : List (CoreChaseNode kb.rules)) (l_non_empty : l ≠ [])
    (trg_act : hd.fst.val.active (l.getLast l_non_empty).core) :
      ∃ (next_ccn : CoreChaseNode kb.rules), (buildCoreChaseBranchFromChaseBranch_rec (hd :: tl) l l_non_empty = buildCoreChaseBranchFromChaseBranch_rec tl (l ++ [next_ccn]) (List.concat_ne_nil next_ccn l)) := by
        have fs_fin : ((l.getLast l_non_empty).core ∪ hd.fst.val.mapped_head[↑hd.snd].toSet).finite := by
          apply Set.union_finite_of_both_finite
          exact CoreChaseNode.all_core_finite (l.getLast l_non_empty)
          exact List.finite_toSet hd.fst.val.mapped_head[hd.snd]

        have ex_wc : ∃ (wc: FactSet sig), wc.isWeakCore ∧ wc.homSubset ((l.getLast l_non_empty).core ∪ hd.fst.val.mapped_head[↑hd.snd].toSet) :=
          finFactSetHasCore ((l.getLast l_non_empty).core ∪ hd.fst.val.mapped_head[↑hd.snd].toSet) fs_fin

        let next_ccn : CoreChaseNode kb.rules := {
          fs := (l.getLast l_non_empty).core ∪ hd.fst.val.mapped_head[↑hd.snd].toSet
          fs_fin := fs_fin
          core := Classical.choose ex_wc
          is_core := (Classical.choose_spec ex_wc).left
          core_sse := (Classical.choose_spec ex_wc).right
          origin := some ⟨hd.fst, hd.snd⟩
          fs_contains_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
          }
        exists next_ccn
        conv => left; unfold buildCoreChaseBranchFromChaseBranch_rec;simp only [Fin.getElem_fin, List.append_eq]
        cases c : Classical.propDecidable (hd.fst.val.active (l.getLast l_non_empty).core) with
          | isTrue t =>
            grind
          | isFalse =>
            contradiction

  theorem buildCoreChaseBranchFromChaseBranch_rec_cons_trg_act' (hd : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length)
    (tl : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length)) (l : List (CoreChaseNode kb.rules)) (l_non_empty : l ≠ [])
    (trg_act : hd.fst.val.active (l.getLast l_non_empty).core) :
      ∃ (next_ccn : CoreChaseNode kb.rules), (buildCoreChaseBranchFromChaseBranch_rec (hd :: tl) l l_non_empty = buildCoreChaseBranchFromChaseBranch_rec tl (l ++ [next_ccn]) (List.concat_ne_nil next_ccn l) ∧

      have fs_fin : ((l.getLast l_non_empty).core ∪ hd.fst.val.mapped_head[↑hd.snd].toSet).finite := by
        apply Set.union_finite_of_both_finite
        exact CoreChaseNode.all_core_finite (l.getLast l_non_empty)
        exact List.finite_toSet hd.fst.val.mapped_head[hd.snd]

      have ex_wc : ∃ (wc: FactSet sig), wc.isWeakCore ∧ wc.homSubset ((l.getLast l_non_empty).core ∪ hd.fst.val.mapped_head[↑hd.snd].toSet) :=
        finFactSetHasCore ((l.getLast l_non_empty).core ∪ hd.fst.val.mapped_head[↑hd.snd].toSet) fs_fin
      next_ccn = {
        fs := (l.getLast l_non_empty).core ∪ hd.fst.val.mapped_head[↑hd.snd].toSet
        fs_fin := fs_fin
        core := Classical.choose ex_wc
        is_core := (Classical.choose_spec ex_wc).left
        core_sse := (Classical.choose_spec ex_wc).right
        origin := some ⟨hd.fst, hd.snd⟩
        fs_contains_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
      }
      ) := by
        have := buildCoreChaseBranchFromChaseBranch_rec_cons_trg_act hd tl l l_non_empty trg_act
        rcases this with ⟨next_ccn, next_ccn_eq⟩
        exists next_ccn
        constructor
        exact List.append_cancel_left (congrArg (HAppend.hAppend l) next_ccn_eq)
        simp
        sorry



  @[simp, grind =]
  theorem buildCoreChaseBranchFromChaseBranch_rec_cons_trg_not_act (hd : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length)
    (tl : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length)) (l : List (CoreChaseNode kb.rules)) (l_non_empty : l ≠ [])
    (trg_not_act : ¬ hd.fst.val.active (l.getLast l_non_empty).core) :
      buildCoreChaseBranchFromChaseBranch_rec (hd :: tl) l l_non_empty = buildCoreChaseBranchFromChaseBranch_rec tl l l_non_empty := by
        conv => left; unfold buildCoreChaseBranchFromChaseBranch_rec; simp only [Fin.getElem_fin, List.append_eq]
        cases c : Classical.propDecidable (hd.fst.val.active (l.getLast l_non_empty).core) with
          | isTrue t =>
            contradiction
          | isFalse f =>
            rfl

  @[simp, grind =]
  theorem buildCoreChaseBranchFromChaseBranch_rec_first_eq (l : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length)) (a : CoreChaseNode kb.rules) :
    (PossiblyInfiniteList.from_list (buildCoreChaseBranchFromChaseBranch_rec l [a] (List.cons_ne_nil a []))).infinite_list 0 = some a := by
      unfold buildCoreChaseBranchFromChaseBranch_rec
      simp only [List.getLast_singleton, Fin.getElem_fin, List.append_eq, List.cons_append, List.nil_append]
      cases l with
        | nil => rfl
        | cons hd tl =>
          simp_all
          cases c : (Classical.propDecidable (hd.fst.val.active a.core)) with
            | isTrue h' =>
              cases c2 : (Classical.propDecidable (hd.fst.val.active a.core)) with
                | isTrue h'' =>
                  simp
                  unfold PossiblyInfiniteList.from_list PossiblyInfiniteList.infinite_list
                  simp_all
                  rw [buildCoreChaseBranchFromChaseBranch_rec_head']
                | isFalse _ => contradiction
            | isFalse h' =>
              simp
              exact buildCoreChaseBranchFromChaseBranch_rec_first_eq tl a

  @[simp, grind]
  theorem buildCoreChaseBranchFromChaseBranch_rec_get_n (origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))
    (node_list : List (CoreChaseNode kb.rules)) (n : Nat) (node_list_non_empty : node_list.length ≥ n) (n_fin : n < node_list.length):
  (buildCoreChaseBranchFromChaseBranch_rec origin_list node_list (by grind))[n]? =  node_list.get ⟨n, n_fin⟩ := by
    unfold buildCoreChaseBranchFromChaseBranch_rec
    simp only [Fin.getElem_fin, List.append_eq]
    induction node_list with
      | nil =>
        contradiction
      | cons hd tl ih =>
        cases origin_list with
          | nil => exact (List.getElem_eq_iff n_fin).mp rfl
          | cons hd_o tl_o =>
            sorry

  @[simp, grind]
  theorem buildCoreChaseBranchFromChaseBranch_rec_succ_eq (origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length)) (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (i : Fin trg.val.mapped_head.length)
    (node_list : List (CoreChaseNode kb.rules)) (node_list_non_empty : node_list ≠ []) (origin_list_non_empty : origin_list ≠ []) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_origin : cn.origin = some ⟨trg, i⟩)
    (h1 : (buildCoreChaseBranchFromChaseBranch_rec origin_list node_list node_list_non_empty)[n]? = some cn) (h2 : trg.val.active (node_list.getLast node_list_non_empty).core) :

    let fs := (node_list.getLast node_list_non_empty).core ∪ (trg.val.mapped_head[i]).toSet
    let fs_fin := by
        apply Set.union_finite_of_both_finite
        exact CoreChaseNode.all_core_finite (node_list.getLast node_list_non_empty)
        exact List.finite_toSet trg.val.mapped_head[i]

    let ex_new_fs_core := finFactSetHasCore fs fs_fin
    let new_fs_core := Classical.choose ex_new_fs_core
    let new_fs_core_prop := Classical.choose_spec ex_new_fs_core

    (buildCoreChaseBranchFromChaseBranch_rec origin_list node_list node_list_non_empty)[n+1]? = some {
      fs := fs
      fs_fin := fs_fin
      core := new_fs_core
      is_core := new_fs_core_prop.left
      core_sse := new_fs_core_prop.right

      origin := some ⟨trg, i⟩
      fs_contains_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
    }
    := by sorry


  theorem ex_list_for_set_if_finite (S : Set α) (S_fin : S.finite) : ∃ (l : List α), ∀ e, e ∈ l ↔ e ∈ S := by
    rcases S_fin with ⟨l, l_nd, l_eq⟩
    exists l



  --set_option maxHeartbeats 500000
  noncomputable def buildCoreChaseBranchFromChaseBranch (scb : ChaseBranch obs kb) (scb_term : scb.terminates) : CoreChaseBranch kb :=

    have dbf := by
      have := scb.database_first
      unfold PossiblyInfiniteList.head InfiniteList.head InfiniteList.get at this
      exact this

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


    have : ∃ (n : Nat), (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone := by
      have := ChaseBranch.terminating_has_last_index_std scb
      rw [this] at scb_term
      rcases scb_term with ⟨n_ter, eq⟩
      exists n_ter
      grind


    let scb_term_n := Classical.choose this
    let scb_term_h := Classical.choose_spec this

    let scb_trg_list := ChaseBranch.get_origin_list scb scb_term_n (List.range' 1 scb_term_n) rfl scb_term_h.left

    let new_ccb_branch := PossiblyInfiniteList.from_list (buildCoreChaseBranchFromChaseBranch_rec scb_trg_list [init_ccn] (List.cons_ne_nil init_ccn []))

    let new_ccb : CoreChaseBranch kb :=
    {
      branch := new_ccb_branch
      database_first := buildCoreChaseBranchFromChaseBranch_rec_first_eq scb_trg_list init_ccn
      triggers_active := sorry
      triggers_exist := by

        have trg_from_ccb_active_αt_some_geq_in_scb (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (p1 : Nat)
          (ccn_p1 : CoreChaseNode kb.rules) (ccn_p1_eq : ccn_p1 ∈ new_ccb_branch.get? p1) (trg_act : trg.val.active ccn_p1.core) :
            (∃ (p2 : Nat) (scn_p2 : ChaseNode obs kb.rules), ((p2 ≥ p1) ∧ (scn_p2 ∈ scb.branch.get? p2)) → trg.val.active scn_p2.facts) := by sorry

        intro n cn cn_eq
        simp
        intro cn_succ cn_succ_eq

        induction n generalizing cn with
          | zero =>
            cases c1 : scb_trg_list with
              | nil =>
                simp_all
                have : new_ccb_branch.get? 1 = none := by
                  subst new_ccb_branch
                  rw [c1]
                  unfold buildCoreChaseBranchFromChaseBranch_rec
                  exact Option.isNone_iff_eq_none.mp rfl
                rw [this] at cn_succ_eq
                contradiction
              | cons hd tl =>

                cases c3 : Classical.propDecidable (hd.fst.val.active init_ccn.core) with
                  | isTrue t =>
                      have := buildCoreChaseBranchFromChaseBranch_rec_cons_trg_act' hd tl [init_ccn] (List.cons_ne_nil init_ccn []) (by grind)
                      rcases this with ⟨next_ccn, next_ccn_eq1, next_ccn_eq2⟩
                      simp at next_ccn_eq2

                      have t1 : new_ccb_branch.get? 1 = next_ccn := by sorry
                      have t2 : new_ccb_branch.get? 1 = cn_succ := Option.mem_def.mp cn_succ_eq
                      have eq : next_ccn = cn_succ := by grind
                      have eq2 : init_ccn = cn := by sorry

                      have eq3 : next_ccn.fs = cn.core ∪ hd.fst.val.mapped_head[↑hd.snd].toSet := by sorry
                      have := next_ccn.core_sse
                      rw [eq3] at this
                      exists hd.fst, hd.snd, next_ccn.core, next_ccn.is_core, this
                      rw [← eq]
                      sorry

                  | isFalse f =>
                    have := buildCoreChaseBranchFromChaseBranch_rec_cons_trg_not_act hd tl [init_ccn] (List.cons_ne_nil init_ccn []) (by grind)
                    -- contradiction weil wenn kein trigger active kann auch keine cn in buildCoreChaseBranchFromChaseBranch_rec[1] sein
                    sorry
            -- does an active trigger ex at pos 0 in the scb ?

            -- zwei Falluntershceidungen, gibt es den trigger aktiv in der SC und gibt es den trigger aktiv in der CC
            -- in beiden fällen falls ja, nehmen wir uns den index heraus wo der trigger vorkommt, exact dieser trigger ist dann jender der an der stelle n existiert
            -- in den beiden nein fällen muss man zeigen das die origin_list kleiner wird und dann termt der gen algo für CC auf leerer origin list und fügt nichts mehr in die infinite list ein thus alles none danach
            -- was ist mit ja nein fällen ?
            -- für jeden schritt n in der cc gibt es by contstuction einen schritt n+k in der sc welcher den gleichen trigger benutzt


          -- proceed here ---------------------
          | succ n ih =>
            have scb_trg_ex := scb.triggers_exist n

            sorry
            /-
            have scb_trg_ex := scb.triggers_exist n
            rw [Option.is_none_or_iff] at scb_trg_ex
            -- weil new_ccb_branch.infinite_list (n + 1) = some cn muss der scb auch mindestens n+1 lang sein (und damit auch scb_n_ter ≥ n + 1)
            have ex_scn_n : ∃ (scn_n : ChaseNode obs kb.rules), scb.branch.infinite_list n = some scn_n := by sorry
            -- stimmt nicht
            have ex_ccn_n : ∃ (ccn_n : CoreChaseNode kb.rules), new_ccb_branch.infinite_list n = some ccn_n := by sorry

            rcases ex_scn_n with ⟨scn_n, scn_n_eq⟩
            rcases ex_ccn_n with ⟨ccn_n, ccn_n_eq⟩
            specialize scb_trg_ex scn_n scn_n_eq

            cases scb_trg_ex with
              | inl trg_ex =>
                rcases trg_ex with ⟨trg, trg_act, i, eq1⟩
                have ex_ccn_with_scb_trg_at_leq_index := trg_from_scb_active_at_some_leq_in_ccb trg n
                rw [Option.is_some_and_iff] at ex_ccn_with_scb_trg_at_leq_index
                have n_some : (∃ a, scb.branch.infinite_list n = some a ∧ trg.val.active a.facts.val) := by grind
                specialize ex_ccn_with_scb_trg_at_leq_index n_some
                rcases ex_ccn_with_scb_trg_at_leq_index with ⟨p2, lt, h⟩
                rw [Option.is_some_and_iff] at h
                rcases h with ⟨ccn_with_scb_trg, ccn_with_scb_trg_eq, trg_act_in_ccn_with_scb_trg⟩
                specialize ih ccn_n ccn_n_eq
                cases ih with
                  | inl ex_ccb_trg_n =>
                    left
                    exists trg
                    constructor
                    sorry
                    have fin' : (cn.core ∪ trg.val.mapped_head[↑i].toSet).finite := Set.union_finite_of_both_finite (all_core_finite cn) (List.finite_toSet trg.val.mapped_head[i])
                    rcases fin' with ⟨l, l_nd, l_eq⟩
                    have ex_wc := FactSet.exists_weak_core_for_finite_set l.length l rfl
                    rcases ex_wc with ⟨wc, wc_core, wc_homsub⟩
                    exists wc, i
                    rw [Option.is_some_and_iff]

                    have ccn_succ : CoreChaseNode kb.rules := {
                      fs := sorry --(cn.core ∪ trg.val.mapped_head[↑i].toSet) (timeout for some reason)
                      fs_fin := by sorry
                      core := wc
                      is_core := wc_core
                      core_sse := by
                        have eq : l.toSet = (cn.core ∪ trg.val.mapped_head[↑i].toSet) := Set.ext l.toSet (cn.core ∪ trg.val.mapped_head[↑i].toSet) sorry
                        rw [eq] at wc_homsub
                        --exact wc_homsub
                        sorry
                      origin := some ⟨trg, i⟩
                      fs_contains_origin_result := by sorry
                    }
                    exists ccn_succ
                    sorry

                  | inr nex_ccb_trg_n =>
                    right
                    rcases nex_ccb_trg_n with ⟨not_trg_active, next_none⟩
                    constructor

                    sorry -- exact not_trg_active aber durch generalize jetzt mit ccn_n, was tun ?
                    exact new_ccb_branch.no_holes (n+1) next_none

              | inr trg_nex =>
                rcases trg_nex with ⟨trg_nex, is_none⟩
                -- ¬∃ trg, trg.val.active scn_n.facts.val thus no node at any >n thus no origins than can be added to origin list
                have scb_trg_list_len_n : scb_trg_list.length = n := by sorry
                -- new_ccb is constructed from origin_list this after n steps the list is depleated, thus there cannot be a node at position > n+1 (or is it only n ?)
                -- trg active in sc at p1 but skipped in cc becuase not loaded at the generation step
                right
                sorry
                -/


      fairness := sorry
    }

    new_ccb


  theorem notExistsTerminatingChaseBranchIfNotExistsTerminatingCoreChaseBranch (ccb : CoreChaseBranch kb) (ccb_non_term : ¬ ccb.terminates) (scb : ChaseBranch obs kb) : ¬ scb.terminates := by
    sorry

  theorem exChaseBranchIfExCoreChaseBranch (ccb : CoreChaseBranch kb) : ∃ scb : ChaseBranch obs kb, True := by sorry

  theorem min_le_of_mem_set (x : Nat) (S : Set Nat) (x_in : x ∈ S) : ∃ m : Nat, m ∈ S ∧ ∀ n : Nat, n ∈ S → m ≤ n := by

    let S' := (fun n => S (n + 1))

    induction x generalizing S with
    | zero =>
        exists 0, x_in
        intro n n_in
        exact Nat.zero_le n

    | succ x ih =>
        by_cases c : 0 ∈ S

        exists 0, c
        intro n n_in
        exact Nat.zero_le n

        have x_in' : S' x := by exact x_in

        rcases ih S' x_in' with ⟨m, hm, hmin⟩
        exists (m+1), hm
        intro n n_in
        cases n with
        | zero =>
            contradiction
        | succ n =>
            exact Nat.add_le_add_right (hmin n n_in) 1


  theorem wop (S : Set Nat) (S_non_empty : ∃ (n : Nat), n ∈ S) : ∃ (m : Nat), m ∈ S ∧ ∀ (n : Nat), n ∈ S → m ≤ n := by
    rcases S_non_empty with ⟨n, h⟩
    exact min_le_of_mem_set n S h

  def Set.fin_size (S : Set α) (fin : S.finite) : Nat := sorry


  theorem coreSizeLeqFactSetSize (fs c : FactSet sig) (fs_fin : fs.finite) (c_fin : c.finite) (is_core : c.isWeakCore) (hom_sub : c.homSubset fs) : Set.fin_size c c_fin ≤ Set.fin_size fs fs_fin := by
    sorry

  -- ∃ (ccb : CoreChaseBranch kb), ccb.terminates' := by oder cbb im header also assumption
  theorem exTerminatingCoreChaseBranchIfExTerminatingChaseBranch (scb : ChaseBranch obs kb) (kb_det : kb.isDeterministic) (scb_term : scb.terminates) :
    ∃ (ccb : CoreChaseBranch kb), ccb.terminates' := by

      rcases exLastNodeWithLastIndexIfTerminatesAndNoneAfter_std scb scb_term with ⟨final_scn, n_ter, n_ter_some, n_ter_succ_none⟩

      let ccb := buildCoreChaseBranchFromChaseBranch scb scb_term
      exists ccb
      sorry

      /-
      let R := scb.result

      have R_umod : R.universallyModelsKb kb := by
        constructor
        exact ChaseBranch.result_models_kb scb
        have := deterministicChaseBranchResultUniversallyModelsKb scb kb_det
        unfold FactSet.universallyModelsKb at this
        exact this.right

      have final_scn_eq : final_scn.facts = R := by
        subst R
        unfold ChaseBranch.result
        apply Set.ext
        intro f
        constructor
        intro f_in
        exists n_ter
        rw [Option.is_some_and_iff]
        exists final_scn
        intro ⟨n, h⟩
        rw [Option.is_some_and_iff] at h
        rcases h with ⟨h1, h2, h3⟩
        sorry


      have final_scn_umod : final_scn.facts.val.universallyModelsKb kb := by grind

      have sc_universal : ∀ (m : FactSet sig), m.modelsKb kb -> ∃ (h : GroundTermMapping sig), h.isHomomorphism scb.result m := R_umod.right

      have no_act_trg_on_final_scn := notExActTrigInMod_std scb final_scn final_scn_umod.left
      ------

      have final_scn_fin : final_scn.facts.val.finite := by sorry

      have ex_final_core : ∃ (c : FactSet sig), c.isWeakCore ∧ c.homSubset final_scn.facts := finFactSetHasCore final_scn.facts.val final_scn_fin

      rcases ex_final_core with ⟨final_core, final_core_wc, final_core_hs⟩

      have final_core_fin : final_core.finite := by
        unfold FactSet.homSubset at final_core_hs
        grind

      have final_core_size_leq : (Set.fin_size final_core sorry) ≤ (Set.fin_size final_scn.facts.val sorry):= coreSizeLeqFactSetSize final_scn.facts.val final_core final_scn_fin final_core_fin final_core_wc final_core_hs

      apply Classical.byContradiction
      intro contra
      unfold terminates' terminates_at_step at contra
      simp only [ne_eq, not_exists, Classical.not_and_iff_not_or_not, Classical.not_not] at contra

      ------
      have := allCoreChaseStepsHomSubsetOfAllStandardChaseSteps scb n_ter (Option.castisSomeIfEqSome (scb.branch.infinite_list n_ter) final_scn n_ter_some)
      rw [Option.is_some_and_iff] at this
      rcases this with ⟨scn, scn_eq, ⟨m, ⟨ccb, h⟩⟩⟩
      rw [Option.is_some_and_iff] at h
      rcases h with ⟨ccn, ccn_eq, cbn_hom⟩
      sorry

    -/


  -- brauchen wir kb.det ?
  theorem main_lhs (ccb : CoreChaseBranch kb) (kb_det : kb.isDeterministic) : (∃ (fs : FactSet sig), fs.finite ∧ fs.universallyModelsKb kb) → ccb.terminates' := by

    -- 2.
    intro ⟨U, U_fin, U_umod⟩
    apply terminates'IfTerminatesAndNonEmpty
    have := ccb.database_first
    sorry


    -- start of proof
    -- 1.
    apply Classical.byContradiction
    intro contra

    -- 3.
    have inf_scb := notExistsTerminatingChaseBranchIfNotExistsTerminatingCoreChaseBranch ccb contra
    rcases exChaseBranchIfExCoreChaseBranch ccb with ⟨scb, _⟩
    specialize inf_scb scb

    have scb_all_some : ∀ (n : Nat), (scb.branch.infinite_list n).isSome := by
      intro n
      apply Classical.byContradiction
      intro contra
      simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at contra

      unfold ChaseDerivation.terminates ChaseDerivationSkeleton.terminates PossiblyInfiniteList.finite PossiblyInfiniteList.get? at inf_scb
      simp only [not_exists, ne_eq] at inf_scb
      specialize inf_scb n
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


    /-

    have f_first_somewhere : ∀ (f : Fact sig), f ∈ R → ∃ (n_min : Nat), f ∈ ((scb.branch.infinite_list (n_min + 1)).get (scb_all_some (n_min + 1))).facts.val ∧
        ¬ f ∈ ((scb.branch.infinite_list (n_min)).get (scb_all_some (n_min))).facts.val := by

          have monotonicity : ∀ (n : Nat), ((scb.branch.infinite_list (n)).get (scb_all_some (n))).facts.val ⊆ ((scb.branch.infinite_list (n+1)).get (scb_all_some (n+1))).facts.val := by
            intro n f f_in
            have subsetAllFollowing := ChaseBranch.stepIsSubsetOfAllFollowing scb n ((scb.branch.infinite_list (n)).get (scb_all_some (n))) sorry (n+1)
            rw [Option.is_none_or_iff] at subsetAllFollowing
            specialize subsetAllFollowing ((scb.branch.infinite_list (n+1)).get (scb_all_some (n+1))) sorry
            exact subsetAllFollowing f f_in
    -/


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
    have monotonicity : ∀ (n : Nat), ((scb.branch.infinite_list (n)).get (scb_all_some (n))).facts ⊆ ((scb.branch.infinite_list (n+1)).get (scb_all_some (n+1))).facts := by
      intro n f f_in
      have ex_scn : ∃ (scn : ChaseNode obs kb.rules), scb.branch.infinite_list n = some scn := Option.isSome_iff_exists.mp (scb_all_some n)
      have ex_scn_succ : ∃ (scn : ChaseNode obs kb.rules), scb.branch.infinite_list (n + 1) = some scn := Option.isSome_iff_exists.mp (scb_all_some (n + 1))
      rcases ex_scn with ⟨scn, scn_eq⟩
      rcases ex_scn_succ with ⟨scn_succ, scn_succ_eq⟩
      /-
      have subsetAllFollowing := ChaseBranch.stepIsSubsetOfAllFollowing scb n scn scn_eq 1
      rw [Option.is_none_or_iff] at subsetAllFollowing
      specialize subsetAllFollowing scn_succ scn_succ_eq
      have : ((scb.branch.infinite_list n).get (scb_all_some n)) = scn := Option.get_of_eq_some (scb_all_some n) scn_eq
      rw [← this] at subsetAllFollowing
      specialize subsetAllFollowing f f_in
      grind
      -/
      sorry


    have ex_hom_U_An : ∃ (n : Nat) (gtm : GroundTermMapping sig), gtm.isHomomorphism U ((scb.branch.infinite_list n).get (scb_all_some n)).facts := by

      --1
      rcases hom_U_R with ⟨gtm_U_R, gtm_U_R_hom⟩

      --2
      have t1 : ∀ (f : Fact sig), f ∈ U → (gtm_U_R.applyFact f) ∈ R := by sorry

      have t2 : ∀ (f : Fact sig), f ∈ U → ∃ (n : Nat), (gtm_U_R.applyFact f) ∈ ((scb.branch.infinite_list n).get (scb_all_some n)).facts := by sorry
      sorry


    -- 9.
    rcases ex_hom_U_An with ⟨n_max, ⟨gtm_U_An, gtm_U_An_hom⟩⟩

    let An := ((scb.branch.infinite_list n_max).get (scb_all_some n_max)).facts

    have ex_hom_An_U : ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism An U := by

      have sub : An ⊆ R := by
        /-
        have := ChaseBranch.stepIsSubsetOfResult scb n_max
        rw [Option.is_none_or_iff] at this
        exact this ((scb.branch.infinite_list n_max).get (scb_all_some n_max)) (Option.eq_some_of_isSome (scb_all_some n_max))
        -/
        sorry

      have ex_gtm_An_R : ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism An R := FactSet.exHomSubToSet An R sub
      rcases ex_gtm_An_R with ⟨gtm_An_R, gtm_An_R_hom⟩
      rcases hom_R_U with ⟨gtm_R_U, gtm_R_U_hom⟩
      exists (gtm_R_U ∘ gtm_An_R)
      apply GroundTermMapping.isHomomorphism_compose gtm_An_R gtm_R_U An R U gtm_An_R_hom gtm_R_U_hom


    -- 10. --> how even ?
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


    --have every_trig : ∀ (n : Nat), exists_trigger_opt_fs_core obs kb.rules ((cb.branch.infinite_list n).get sorry) (cb.branch.infinite_list (n+1)) := by sorry


end CoreChaseBranch

/-

Open Problems:
  Factorizing homomorphism from n → ω to (n+1) → ω
  no active triggers in model.core
   ccb.branch.infinite_list (n_ter + 1) = none when sc term at n_ter + 1

Open Remarks:

  kb.rules.rules should maybe be kb.rules

-/
