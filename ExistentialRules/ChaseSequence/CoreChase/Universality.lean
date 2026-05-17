import ExistentialRules.ChaseSequence.ChaseBranch
import ExistentialRules.ChaseSequence.CoreChase.Homomorphisms
import ExistentialRules.ChaseSequence.CoreChase.Basic
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch
import ExistentialRules.ChaseSequence.CoreChase.Triggers
import ExistentialRules.ChaseSequence.CoreChase.Termination

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}

theorem ex_endo_hom  (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules)
      (disj_idx n : Nat) (trg: RTrigger obs.toLaxObsolescenceCondition kb.rules) (cn_eq : cn ∈ cb.branch.get? n)
      (t : GroundTerm sig ) (lt : disj_idx < trg.val.rule.head.length)
      (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) (t_mem_node : t ∈ cn.fs.terms) :
        ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet cn.core ∧
          gtm.isHomomorphism cn.core cn.core ∧ (Function.surjective_for_domain_and_image_set gtm cn.core.terms cn.core.terms) := by
            have : trg.val.satisfied_for_disj cn.fs ⟨disj_idx, Nat.lt_of_succ_le lt⟩ := by
              sorry
            sorry

  abbrev InductiveHomomorphismResultCore (cb : CoreChaseBranch kb) (m : FactSet sig) (depth : Nat) :=
    {gtm : GroundTermMapping sig // ∀ cn, cn ∈ cb.branch.get? depth → gtm.isHomomorphism cn.fs m}

  theorem disjoin_hom_is_hom (h1 h2 h3 : GroundTermMapping sig) (A B C : FactSet sig) [DecidablePred A.terms]
    (h1_hom : h1.isHomomorphism A C) (h2_hom : h2.isHomomorphism B C) (hdisj : ∀ x, x ∈ A → x ∈ B → False) :
      GroundTermMapping.isHomomorphism (fun t => if (t ∈ A.terms) then (h1 t) else (h2 t)) A B := by sorry

  noncomputable def inductive_homomorphism_core_with_prev_node_and_trg_if_next_node_some (cb : CoreChaseBranch kb) (m : FactSet sig) (m_mod : m.modelsKb kb) (kb_det : kb.isDeterministic)
    (prev_depth : Nat) (prev_node : CoreChaseNode kb.rules) (prev_node_eq : prev_node ∈ cb.branch.get? prev_depth)
    (prev_gtm : GroundTermMapping sig) (prev_gtm_hom : prev_gtm.isHomomorphism prev_node.fs m) :
      ∀ next_node ∈ cb.branch.get? (prev_depth.succ), ∃ (next_gtm : GroundTermMapping sig), GroundTermMapping.isHomomorphism next_gtm next_node.fs m := by

        intro next_node next_node_eq

        have prev_core_eq : (cb.prev_node prev_depth (Option.isSome_of_mem next_node_eq)).core = prev_node.core := by grind

        have prev_gtm_hom_core : prev_gtm.isHomomorphism prev_node.core m := CoreChaseBranch.homFsToFsAlsoHomCoreToFs m prev_node prev_gtm prev_gtm_hom

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

        let next_node_origin := next_node.origin.get (CoreChaseBranch.origin_isSome cb prev_depth next_node_eq)


        let new_trg : PreTrigger sig := ⟨trg_on_prev_node.val.rule, (prev_gtm ∘ trg_on_prev_node.val.subs)⟩

        have new_trg_loaded : new_trg.loaded m := by
          --have : new_trg.mapped_body.toSet ⊆ prev_gtm.applyFactSet prev_node.fs := by

          apply Set.subset_trans _ prev_gtm_hom.right
          apply PreTrigger.term_mapping_preserves_loadedness
          . exact prev_gtm_hom.left
          . have trg_origin_act := (cb.origin_trg_is_active_prev_core prev_depth next_node next_node_eq ⟨trg_on_prev_node, disj_on_prev_node⟩ next_node_origin_some).left
            simp [prev_core_eq] at trg_origin_act
            have := cb.trg_loaded_in_fs_if_loaded_in_core prev_depth prev_node prev_node_eq trg_on_prev_node.val trg_origin_act
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
            simp only [obs, RestrictedObsolescence]
            unfold PreTrigger.satisfied
            /-
              -- trigger_introducing_function_term_occurs_in_chase :
              knoten mit fresh term, dann gibt es knoten vorher dessen trigger equiv zu dem trigger der den fresh term erzeugen könnte
              this yields an equiv trigger trg2
              trg2 wurde angewand also trg nicht
              wenn trg2 sat dann trg sat
              wenn trg2 nicht loaded folgt nicht dass trg loaded ist (wir wissen trg loaded aus trg_active_prev_core.left)
              wir wisen dass trg2 loaded war weil er angewand wurde
              z.z. trg2 loade an der stelle wo trg loaded

              lemma, einmal sat trg bleibt sat (prop falsch)

              wenn ein trg angewendet wurde ist danach jeder equiv trigger nicht active
              A(c), A(x)→∃y, R(x,y), R(x,y)→ R(x,x) ∧ S(x,y) ∧ S(x,x)
              A(c), R(c,n), R(c,c), S(c,n), S(c,c)
              A(c), R(c,c), S(c,c)
          -/

            --apply trg_on_prev_node.sat
            --apply cb.triggerInactiveAfterApplication prev_node next_node prev_depth sorry sorry sorry

            apply obs.contains_trg_result_implies_cond disj_on_prev_node

            intro f f_mem

            have ex_gtm := cb.result_of_trigger_introducing_functional_term_occurs_in_chase_core' prev_node disj_on_prev_node prev_depth (Classical.choose trg_act).fst
              (Option.mem_def.mpr prev_node_eq) t fin_disj.isLt (by grind) (CoreChaseNode.fs_terms_sub_core_terms prev_node t t_mem)

            have := CoreChaseBranch.functional_term_originates_from_some_trigger_or_database_core cb prev_depth prev_node prev_node_eq t
              (PreTrigger.term_functional_of_mem_fresh_terms t contra) (CoreChaseNode.fs_terms_sub_core_terms prev_node t t_mem)

            cases this with
              | inl from_db =>
                have := CoreChaseBranch.func_term_not_mem_head (PreTrigger.term_functional_of_mem_fresh_terms t contra) from_db
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
              have eq1 : ⟨trg_on_prev_node, disj_on_prev_node⟩ ∈ next_node.origin := Option.mem_def.mpr next_node_origin_some
              have eq2 : (next_node.origin.get (cb.origin_isSome prev_depth next_node_eq)).fst = trg_on_prev_node := by simp_all
              have eq3 : (next_node.origin.get (cb.origin_isSome prev_depth next_node_eq)).snd.val = disj_on_prev_node := by simp_all; grind
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
            rw [cb.none_get_eq] at prev_node_eq
            have := @PossiblyInfiniteList.no_holes' _ cb.branch j prev_node_eq
            rw [Option.mem_def, this] at cn_eq
            contradiction
              ⟩
          | .some cn =>
            match c1 : Classical.propDecidable (∃ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), trg.val.active (prev_node.get (Option.isSome_of_mem prev_node_eq)).core) with
              | isTrue tr =>
                let trg := Classical.choose tr
                let trg_act := Classical.choose_spec tr
                have ex_next_node := cb.exNextNodeIfExActiveTrigger j cn prev_node_eq trg (by grind)
                let next_node := Classical.choose ex_next_node
                let next_node_eq := Classical.choose_spec ex_next_node
                have := inductive_homomorphism_core_with_prev_node_and_trg_if_next_node_some
                  cb m m_mod kb_det j cn prev_node_eq prev_gtm (GroundTermMapping.subPreservesHom cn.fs m cn.fs (Set.subset_refl) prev_gtm (prev_gtm_hom cn prev_node_eq)) next_node next_node_eq
                let next_gtm := Classical.choose this
                have next_gtm_hom := Classical.choose_spec this
                ⟨next_gtm, by
                  intro cn' cn'_eq
                  have : cn' = next_node := cb.mem_eq cn' next_node j.succ cn'_eq next_node_eq
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
    have := CoreChaseBranch.homFsToFsAlsoHomCoreToFs m cn_res h.val p
    grind
