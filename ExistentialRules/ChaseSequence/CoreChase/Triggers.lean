import ExistentialRules.ChaseSequence.ChaseBranch

import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch
import ExistentialRules.ChaseSequence.CoreChase.Homomorphisms


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


namespace CoreChaseBranch


  @[grind .]
  theorem functional_term_originates_from_some_trigger {cb : CoreChaseBranch kb} (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cn ∈ cb.branch.get? n) (t : GroundTerm sig)
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) (t_mem : t ∈ cn.fs.terms) :
      ∃ (m : Nat) (prev_cn : CoreChaseNode kb.rules), m ≤ n ∧ prev_cn ∈ cb.branch.get? m ∧ ∃ o ∈ cn.origin, t ∈ o.fst.val.fresh_terms_for_head_disjunct o.snd.val (by rw [← PreTrigger.length_mapped_head]; exact o.snd.isLt) := by sorry

  @[grind .]
  theorem ex_func_eq {disj_idx : Nat} {t : GroundTerm sig} {trg : RTrigger obs.toLaxObsolescenceCondition kb.rules} {lt : disj_idx < trg.val.rule.head.length} (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok := by
      cases cn_eq : t with
      | const _ =>
        rw [cn_eq] at t_mem_trg
        simp [PreTrigger.fresh_terms_for_head_disjunct, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem_trg
      | func func ts arity_ok => exists func, ts, arity_ok

  @[grind .]
  theorem trg_loaded_in_fs_if_loaded_in_core (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cn ∈ cb.branch.get? n) (trg : Trigger obs.toLaxObsolescenceCondition) :
    trg.loaded cn.core → trg.loaded cn.fs := by
      intro trg_loaded
      intro f f_in
      specialize trg_loaded f f_in
      exact cn.core_sse.left f trg_loaded

  @[grind .]
    theorem origin_trg_inactive_in_fs (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) (cn_origin_some : cn.origin.isSome) :
      ¬ (cn.origin.get cn_origin_some).fst.val.active cn.fs := by
          have trg_ex := cb.triggers_exist (n - 1)
          by_cases c_lt : n = 0
          subst c_lt
          have dbf := cb.database_first
          grind
          have c_lt := Nat.zero_lt_of_ne_zero c_lt
          have ex_prev_cn := ex_prev_cn_if_origin_some cb cn n cn_eq cn_origin_some
          rcases ex_prev_cn with ⟨prev_cn, prev_cn_eq⟩
          specialize trg_ex prev_cn prev_cn_eq cn (by grind)
          rcases trg_ex with ⟨trg, i, c, c_wc, c_sub, eq⟩
          intro contra
          rcases contra with ⟨loaded, non_obs⟩
          apply non_obs
          have len_eq : trg.val.mapped_head.length = trg.val.rule.head.length := by exact PreTrigger.length_mapped_head trg.val.toPreTrigger
          have lt : ↑i < (cn.origin.get cn_origin_some).fst.val.rule.head.length := by grind
          exists ⟨i, lt⟩
          rcases (exHomFsCore cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
          have := trg.val.term_mapping_preserves_loadedness cn.fs gtm gtm_hom.left (by grind)
          have := PreTrigger.satisfied_for_disj_of_mapped_head_contained (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn.fs ⟨↑i, by grind⟩
          apply this
          simp_all
          exact Set.subset_union_of_subset_right trg.val.mapped_head[↑i].toSet prev_cn.core trg.val.mapped_head[↑i].toSet fun e a => a

  -- muss fs loaded in core oder loaded in fs
    @[grind .]
    theorem trg_obs_in_core_if_obs_in_fs_and_loaded_in_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) (trg : Trigger obs.toLaxObsolescenceCondition) :
        (obs.cond trg.toPreTrigger cn.fs) ∧ (trg.loaded cn.core) → obs.cond trg.toPreTrigger cn.core := by
          simp only [obs, RestrictedObsolescence]
          intro ⟨trg_sat, trg_loaded⟩
          unfold PreTrigger.satisfied at *
          rcases trg_sat with ⟨i, gs, h1, h2⟩
          rcases (exHomFsCore cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
          have ex_eq_list : ∃ (tl : List (GroundTerm sig)), tl.toSet = cn.core.terms := by
            have := FactSet.terms_finite_of_finite cn.core cn.all_core_finite
            rcases this with ⟨tl, h1, h2⟩
            exists tl
            exact Set.ext tl.toSet cn.core.terms h2

          rcases ex_eq_list with ⟨tl, tl_eq⟩
          have gtm_surj := gtmFsCoreIsEndo cb cn n cn_eq gtm gtm_hom
          have gtm_surj_eq := gtm.surjective_set_list_equiv tl.toSet tl (fun e => Eq.to_iff rfl) tl.toSet tl (fun e => Eq.to_iff rfl)
          rw [tl_eq] at gtm_surj_eq
          rw [gtm_surj_eq] at gtm_surj

          have ex_reps := gtm.exists_repetition_that_is_inverse_of_surj tl gtm_surj
          rcases ex_reps with ⟨rep, h⟩

          let rep_hom := gtm.repeat_hom (rep + 1)
          have rep_hom_hom := gtm.repeat_hom_isHomomorphism cn.core (homFsToFsAlsoHomCoreToFs cn.core cn gtm gtm_hom) (rep + 1)
          have len_eq : trg.mapped_head.length = trg.rule.head.length := by exact PreTrigger.length_mapped_head trg.toPreTrigger
          have lt : ↑i < trg.mapped_head.length := by grind

          exists i, (rep_hom ∘ gs)

          constructor
          · intro v v_in
            have eq : trg.subs_for_mapped_head ⟨i, lt⟩ v = trg.subs v := by apply trg.apply_to_var_or_const_frontier_var i v v_in
            have one_more_eq : gtm.repeat_hom (rep + 1) (gs v) = gtm.repeat_hom rep (gtm (gs v)) := GroundTermMapping.repeat_hom_swap gtm rep (gs v)
            simp only [Function.comp_apply]
            specialize h1 v v_in
            rw [← h1]

            simp only [rep_hom]
            rw [one_more_eq]
            specialize h (gs v) (by
              rw [Set.ext_iff] at tl_eq
              specialize tl_eq (gs v)
              rw [← List.mem_toSet, tl_eq]
              rw [h1]
              have terms_sub := FactSet.terms_subset_of_subset cn.core_sse.left
              have ex_cnl : ∃ (cnl : List (Fact sig)), ∀ e, (e ∈ cnl ↔ e ∈ cn.core) := Set.exListOfSetIfFin cn.core cn.all_core_finite
              rcases ex_cnl with ⟨cn_core_l, cn_core_l_eq⟩
              have eq : cn_core_l.toSet = cn.core := Set.ext cn_core_l.toSet cn.core cn_core_l_eq
              have t1 := @FactSet.mem_terms_toSet _ _ _ _ cn_core_l (trg.subs v)
              rw [eq] at t1
              rw [t1]
              have t2 := PreTrigger.mem_terms_mapped_body_iff trg.toPreTrigger (trg.subs v)
              have sub : trg.mapped_body ⊆ cn_core_l := by
                intro e e_in
                specialize cn_core_l_eq e
                rw [cn_core_l_eq]
                exact trg_loaded e e_in
              have := @Rule.frontier_subset_vars_body _ _ _ _ trg.rule
              sorry --grind
              )
            exact h

          · intro f f_in
            have rep_hom_hom' : rep_hom.isHomomorphism cn.fs cn.core := by
              simp only [rep_hom]
              have g1 := gtm_hom

              have gtm_endo : gtm.isHomomorphism cn.core cn.core := homFsToFsAlsoHomCoreToFs cn.core cn gtm gtm_hom
              have : ∀ k, (gtm.repeat_hom k).isHomomorphism cn.core cn.core := by
                intro k
                induction k with
                  | zero => exact GroundTermMapping.repeat_hom_isHomomorphism gtm cn.core gtm_endo 0
                  | succ k ih =>
                    exact GroundTermMapping.repeat_hom_isHomomorphism gtm cn.core gtm_endo (k + 1)
              specialize this rep

              have g1_this_hom : GroundTermMapping.isHomomorphism ((gtm.repeat_hom rep) ∘ gtm) cn.fs cn.core := by
                have y := GroundTermMapping.isHomomorphism_compose gtm (gtm.repeat_hom rep) cn.fs cn.core cn.core g1 this
                exact y
              exact (GroundTermMapping.gtm_rep_swap gtm rep cn.fs cn.core).mpr g1_this_hom

            apply rep_hom_hom'.right

            unfold GroundSubstitution.apply_function_free_conj TermMapping.apply_generalized_atom_list at f_in
            rw [List.mem_toSet, List.mem_map] at f_in
            rcases f_in with ⟨a, ahl, ahr⟩
            rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants _ _ (rep_hom_hom'.left)] at ahr
            rw [← ahr]
            simp only [Function.comp_apply]
            unfold GroundTermMapping.applyFactSet GroundTermMapping.applyFact
            apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
            apply h2
            rw [List.mem_toSet]
            unfold GroundSubstitution.apply_function_free_conj TermMapping.apply_generalized_atom_list
            rw [List.mem_map]
            exists a

    @[grind .]
    theorem trg_obs_in_fs_if_obs_in_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) (trg : Trigger obs.toLaxObsolescenceCondition) :
      obs.cond trg.toPreTrigger cn.core → obs.cond trg.toPreTrigger cn.fs := by
        simp only [obs, RestrictedObsolescence]
        unfold PreTrigger.satisfied
        rcases (exHomFsCore cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
        intro ⟨i, gs, h1, h2⟩
        exists i, gs
        constructor
        intro v v_in
        exact h1 v v_in
        have sub := cn.core_sse.left
        apply Set.subset_trans h2 sub

    @[grind .]
    theorem trg_inactive_in_core_if_inactive_in_fs_and_loaded_in_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cb.branch.infinite_list n = some cn) (trg : Trigger obs.toLaxObsolescenceCondition) :
      (¬ trg.active cn.fs ∧ trg.loaded cn.core) → ¬ trg.active cn.core := by
        intro ⟨trg_not_active_fs, trg_loaded_core⟩
        unfold Trigger.active at *
        rw [Classical.not_and_iff_not_or_not, Classical.not_not] at *
        have : ¬trg.loaded cn.fs ∨ (trg.loaded cn.fs ∧ obs.cond trg.toPreTrigger cn.fs) := by grind
        rcases this with trg_not_loaded | ⟨trg_loaded, trg_obs⟩
        left
        intro contra
        apply trg_not_loaded
        intro e e_in
        specialize contra e e_in
        exact cn.core_sse.left e contra
        right
        exact trg_obs_in_core_if_obs_in_fs_and_loaded_in_core cb cn n cn_eq trg ⟨trg_obs, trg_loaded_core⟩

  @[grind .]
    theorem origin_trg_obs_and_loaded_in_fs (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cb.branch.infinite_list n = some cn) (cn_origin_some : cn.origin.isSome) :
      (cn.origin.get cn_origin_some).fst.val.loaded cn.fs ∧ obs.cond (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn.fs := by

        have n_gt : n > 0 := not_first_if_origin_some cb cn cn_origin_some n cn_eq
        have trg_active_origin := origin_trg_is_active_prev_core cb (n-1) cn (by rw [Nat.sub_add_cancel n_gt]; exact cn_eq)
          (cn.origin.get (Eq.symm (Bool.le_antisymm (fun a => cn_origin_some) (congrFun rfl))))
          (Option.get_mem (Eq.symm (Bool.le_antisymm (fun a => cn_origin_some) (congrFun rfl))))
        simp at trg_active_origin

        rcases trg_active_origin with ⟨trg_loaded, trg_non_obs⟩

        have ex_prev_node := ex_prev_cn_if_origin_some cb cn n cn_eq cn_origin_some
        rcases ex_prev_node with ⟨prev_cn, prev_cn_eq⟩
        have fs_eq := cbNextFsEq cb (n-1) prev_cn cn prev_cn_eq (by rw [Nat.sub_add_cancel n_gt]; exact cn_eq)
        have trg_loaded_cn_fs : (cn.origin.get cn_origin_some).fst.val.loaded cn.fs := by
          intro f f_in
          specialize trg_loaded f f_in
          grind
        constructor
        exact trg_loaded_cn_fs
        have := origin_trg_inactive_in_fs cb cn n cn_eq cn_origin_some
        unfold Trigger.active at this
        simp only [Classical.not_and_iff_not_or_not, Classical.not_not] at this
        rcases this with not_loaded | is_obs
        contradiction
        exact is_obs



  theorem trigger_introducing_functional_term_occurs_in_chase_core
    {cb : CoreChaseBranch kb} {cn : CoreChaseNode kb.rules}
    {disj_idx n : Nat}
    (cn_eq : cn ∈ cb.branch.get? n)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ cn.fs.terms)
    {trg : RTrigger obs.toLaxObsolescenceCondition kb.rules}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    ∃ (m : Nat) (prev_cn : CoreChaseNode kb.rules), m ≤ n ∧ prev_cn ∈ cb.branch.get? m → ∀ o, o ∈ prev_cn.origin → o.fst.equiv trg ∧ o.snd.val = disj_idx := by
      have := functional_term_originates_from_some_trigger n cn cn_eq t (ex_func_eq t_mem_trg) (Set.mem_of_subset_of_mem (fun e a => a) t_mem_node)
      rcases this with ⟨m, prev_cn, leq, prev_cn_eq, o, o_eq, t_mem⟩
      exists m, prev_cn
      intro h o' o'_in
      constructor
      sorry
      sorry

  theorem result_of_trigger_introducing_functional_term_occurs_in_chase_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules)
    (disj_idx n : Nat) (trg: RTrigger obs.toLaxObsolescenceCondition kb.rules) (cn_eq : cn ∈ cb.branch.get? n)
    (t : GroundTerm sig ) (lt : disj_idx < trg.val.rule.head.length)
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) (t_mem_node : t ∈ cn.fs.terms) :
      ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet cn.fs := by
        rcases trigger_introducing_functional_term_occurs_in_chase_core cn_eq t_mem_node t_mem_trg with ⟨n2, lt, h⟩
        sorry
        /-
        rcases h with ⟨cn2, cn2_eq, origin, origin_eq, equiv, index_eq⟩
        have ex_hom_following := exHomStepToAllFollowing cb n2 cn2 cn2_eq n lt
        simp only [cn_eq, Option.is_none_or] at ex_hom_following
        have := cn2.fs_contains_origin_result
        simp only [origin_eq, Option.is_none_or] at this
        simp only [← PreTrigger.result_eq_of_equiv equiv, ← index_eq]
        rcases ex_hom_following with ⟨gtm, h2⟩
        have := GroundTermMapping.subPreservesHom cn2.fs cn.fs origin.fst.val.mapped_head[↑origin.snd].toSet this gtm h2
        exact Exists.intro gtm this
        -/



  @[grind .]
  theorem result_of_trigger_introducing_functional_term_occurs_in_chase_core' (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules)
    (disj_idx n : Nat) (trg: RTrigger obs.toLaxObsolescenceCondition kb.rules) (cn_eq : cn ∈ cb.branch.get? n)
    (t : GroundTerm sig ) (lt : disj_idx < trg.val.rule.head.length)
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) (t_mem_node : t ∈ cn.fs.terms) :
      ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet cn.core := by
      rcases result_of_trigger_introducing_functional_term_occurs_in_chase_core cb cn disj_idx n trg cn_eq t lt t_mem_trg t_mem_node with ⟨gtm, gtm_hom⟩
      rcases exHomFsCore cb n cn cn_eq with ⟨gtm2, gtm2_hom⟩
      exists gtm2 ∘ gtm
      exact GroundTermMapping.isHomomorphism_compose gtm gtm2 (trg.val.mapped_head[disj_idx]'(by grind)).toSet cn.fs cn.core gtm_hom gtm2_hom


    -- ASK!: Macht dieses Resultat so noch sinn ? Wir müssen ja jetzt immer die nächste node angeben schon. Was ist wenn wir für einen beweis nur active trigger haben aber wir die nächste node nicht explizit haben ?
    -- isSome_next_iff_trg_ex
    @[grind .]
    -- exNextNodeIfExLoadedNonObsoleteTrigger
    theorem exNextNodeIfExActiveTrigger (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cn ∈ cb.branch.get? n)
      (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (trg_act : trg.val.active cn.core) :
          ∃ (cn' : CoreChaseNode kb.rules), cn' ∈ cb.branch.infinite_list (n+1) := by
            have trg_ex := cb.triggers_exist n cn cn_eq
            cases h : cb.branch.infinite_list (n+1) with
              | none =>
                apply Classical.byContradiction
                intro contra

                rcases (cb.fairness trg) with ⟨i, ⟨node, node_mem, not_active⟩, fair⟩
                apply not_active





                sorry
                /-
                have trg_ex := cb.triggers_exist n
                rw [h, Option.is_none_or_iff] at trg_ex
                specialize trg_ex cn cn_eq
                cases trg_ex with
                  | inl ex =>
                    unfold exists_trigger_opt_fs_core at ex
                    rcases ex with ⟨trg', trg'_act_c, ⟨i, c, c_eq⟩⟩
                    contradiction
                  | inr nex =>
                    unfold not_exists_trigger_opt_fs_core at nex
                    unfold Trigger.active at nex
                    simp only [not_exists, not_and, Classical.not_not, and_true] at nex
                    specialize nex trg trg_loaded
                    contradiction
                -/
              | some succ_cn =>
                exists succ_cn


  theorem triggerInactiveAfterApplication (cb : CoreChaseBranch kb) (cn cn_succ : CoreChaseNode kb.rules) (n k : Nat)
  (cn_eq : cb.branch.infinite_list n = some cn) (cn_succ_eq : cb.branch.infinite_list (n + k) = some cn_succ) (cn_origin_some : cn.origin.isSome) :

    ¬ (cn.origin.get cn_origin_some).fst.val.active cn_succ.core := by

      have ex_prev_node := ex_prev_cn_if_origin_some cb cn n cn_eq cn_origin_some
      rcases ex_prev_node with ⟨prev_cn, prev_cn_eq⟩

      induction k generalizing cn_succ with
        | zero =>
          have eq : cn = cn_succ := by grind
          subst eq
          have trg_inactive_fs := origin_trg_inactive_in_fs cb cn n cn_eq cn_origin_some
          by_cases c : (cn.origin.get cn_origin_some).fst.val.loaded cn.core
          have trg_inactive_core := trg_inactive_in_core_if_inactive_in_fs_and_loaded_in_core cb cn n cn_eq (cn.origin.get cn_origin_some).fst.val ⟨trg_inactive_fs, c⟩
          exact trg_inactive_core
          unfold Trigger.active
          rw [Classical.not_and_iff_not_or_not, Classical.not_not]
          left
          exact c

        | succ k ih =>

          have n_gt : n > 0 := not_first_if_origin_some cb cn cn_origin_some n cn_eq

          have trg_active_prev_cn_core : (cn.origin.get cn_origin_some).fst.val.active prev_cn.core := by
            have := origin_trg_is_active_prev_core cb (n-1) cn (by rw [Nat.sub_add_cancel n_gt]; exact cn_eq)
            sorry

          have trg_inactive_cn_core : ¬(cn.origin.get cn_origin_some).fst.val.active cn.core := by
              have trg_inactive_fs := origin_trg_inactive_in_fs cb cn n cn_eq cn_origin_some
              by_cases c : (cn.origin.get cn_origin_some).fst.val.loaded cn.core
              have trg_inactive_core := trg_inactive_in_core_if_inactive_in_fs_and_loaded_in_core cb cn n cn_eq (cn.origin.get cn_origin_some).fst.val ⟨trg_inactive_fs, c⟩
              exact trg_inactive_core
              unfold Trigger.active
              rw [Classical.not_and_iff_not_or_not, Classical.not_not]
              left
              exact c


          have ex_cn_k : ∃ (cn_k : CoreChaseNode kb.rules), cn_k ∈ cb.branch.infinite_list (n + k) :=
            cb.ex_prev_node_at_each_leq (n + k + 1) (Option.isSome_of_mem cn_succ_eq) (n + k) (Nat.le_add_right (n + k) 1)

          rcases ex_cn_k with ⟨cn_k, cn_k_eq⟩
          specialize ih cn_k cn_k_eq

          unfold Trigger.active at ih
          have ih' : ¬(cn.origin.get cn_origin_some).fst.val.loaded cn_k.core ∨ (obs.cond (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn_k.core ∧ (cn.origin.get cn_origin_some).fst.val.loaded cn_k.core) := by grind
          cases ih' with
            | inl trg_not_loaded_k =>

              intro ⟨trg_loaded_succ, trg_non_obs_succ⟩

              /-
              Hi, ich habe mich nochmal an das Theorem "ein angewendeter Trigger kann nie wieder aktiv werden" gesetzt.
              Dort machen wir eine Induktion über k. Induktionsanfang war schon fertig.
              Im Induktionsschritt wollen wir zeigen, dass der Trigger an der Stelle (n+k+1) nicht active ist.

              Die Situation ist also folgendermaßen:
              `prev_cn (n-1)` → `cn (n)` → `cn_k (n+k)` → `cn_succ (n+k+1)`

              Wir machen nun einen Wiederspruchsbeweis und nehemen an, dass der Trigger loaded auf cn_succ wäre

              und wir wissen damit:
                - trg active in prev_cn
                - trg loaded und obs in cn.fs
                - trg not loaded in cn_k.core
                - trg loaded auf cn_succ.fs
                - trg active auf cn_succ.core

                Des Weiteren wissen wir, dass es einen Fakt `f` geben muss, der im Trigger result (und damit auch in cn.fs) vorkommt aber nicht in cn_k.core
                Somit wissen wir auch, dass es eine weitere Node `cm` zwischen `prev_cn` und `cn_succ` geben muss s.d. f in `cm.fs` ist aber nicht in `cm.core`.

                Hier bin ich mir jetzt nicht sicher, ob ich eine Fallunterscheidung machen muss ob `cm=cn` und ob `cm=cn_k` ist?

                Hier bin ich mir dann auch nicht sicher wie genau es weiter geht.
                Ich glaube wir hatten mal gesagt, dass sich jetzt zeigen lassen sollte, dass es einen Term geben muss, s.d. `t ∈ prev_cn.core.terms ∧ ¬ t ∈ cm.core.terms ∧ t ∈ cn_succ.core.terms` gilt.
                Ist das richtig ?
                Das würde dann bedeuten, dass es auch einen Fakt gibt s.d. `f ∈ prev_cn.core ∧ ¬ f ∈ cm.core ∧ f ∈ cn_succ.core` richtig ?

                Jetzt weiß ich aber nicht mehr weiter, was wäre der Ansatz um hier weiter zu machen ?
                Wir hatten in der Vergangenheit mal eine Fallunterscheidung gemacht ob `t` eine Konstante ist oder nicht.
                Ich weiß aber nicht genau wie mich das hier weiter bringt.

                Hast du vlt. noch ein Paar Ratschläge wie ich hier weiter komme ?

                Danke im Voraus :)




              -/


              /-
                prev_cn →     cn →                 cn_k →              cn_succ
                (trg active)  trg in origin       (trg not loaded)    (show inactive here)
                .             thus inactive in fs
                .             loaded in fs
                .             maybe unloaded in core



                wir wissen dass nur in der core computation unloaded werden kann
                zudem wissen wir, dass ein trg in core obsolete ist, falls er in in fs obs ist und loaded auf dem core ist
              -/

              have trg_prev_cn_loaded := trg_active_prev_cn_core.left
              have trg_prev_cn_non_obs := trg_active_prev_cn_core.right

              have := origin_trg_obs_and_loaded_in_fs cb n cn cn_eq cn_origin_some
              have trg_obs_cn_fs := this.right
              have trg_loaded_cn_fs := this.left

              have l1 := trg_active_prev_cn_core.left
              have l2 := trg_inactive_cn_core
              have l3 := trg_not_loaded_k
              have l4 := trg_loaded_succ

              have trg_obs_cn_core := trg_obs_in_core_if_obs_in_fs_and_loaded_in_core cb cn n cn_eq (cn.origin.get cn_origin_some).fst.val ⟨trg_obs_cn_fs, sorry⟩

              unfold PreTrigger.loaded at l1 l2 l3

              have ex_f_nin : ∃ (f : Fact sig), f ∈ (cn.origin.get cn_origin_some).fst.val.mapped_body.toSet ∧ ¬ f ∈ cn_k.core := by
                unfold Subset instHasSubsetSet at l3
                simp at l3
                exact l3

              rcases ex_f_nin with ⟨f, f_in, f_nin⟩

              have eq : n - 1 + (k + 1) = n + k := by grind
              have ex_cm := exIntermeadiateCoreChaseNodeIfFactMissing cb prev_cn cn_k (n-1) (k+1) prev_cn_eq (by rw [eq]; exact cn_k_eq) f (trg_prev_cn_loaded f f_in) f_nin

              -- terms can only be removed during core calculation

              -- we know that as trg loaded in prev_cn but not in cn_k that some term either got removed in cn.fs → cn.core or in cn_k.fs → cn_k.core
              -- this term then got reintroduced as trg is loaded again in cn_succ

              -- loaded in cn.fs → unloaded between cn.core and cn_k.core

              rcases ex_cm with ⟨cm, cm_eq⟩
              -- cm can be (both including) between cn and cn_k

              have t_mem : ∃ (t : GroundTerm sig), t ∈ prev_cn.core.terms ∧ ¬ t ∈ cm.core.terms ∧ t ∈ cn_succ.core.terms := by

                have s1 := FactSet.terms_subset_of_subset cn.core_sse.left
                have s2 := FactSet.terms_subset_of_subset cn_k.core_sse.left
                have s3 := FactSet.terms_subset_of_subset cn_succ.core_sse.left
                sorry

              rcases t_mem with ⟨t, t_in_prev_cn, t_nin_cm, t_in_cn_succ⟩
              have t_in_cn_fs : t ∈ cn.fs.terms := by sorry -- weil cn.fs ⊆ prec_cn.core
              cases eq : t with
                | const c =>
                  -- es gibt einen zugehörigen fakt für den term
                  have ex_f : ∃ (f : Fact sig), f ∈ cn.fs ∧ t ∈ f.terms := t_in_cn_fs
                  rcases ex_f with ⟨f, f_in_cn_fs, t_in_f⟩

                  have := allFfInNextFsIfSome cb (n + k) cn_k cn_k_eq
                  specialize this cn_succ cn_succ_eq



                  have f_is_ff : f.isFunctionFree := by
                    unfold Fact.isFunctionFree
                    intro gt gt_in
                    exists c
                    sorry


                  specialize this f
                  have ff_in_all_succ := allFfInAllSuccIfSome cb n k cn cn_eq
                  specialize ff_in_all_succ cn_k cn_k_eq
                  have f_in_cn_k_fs : f ∈ cn_k.fs := by
                    apply ff_in_all_succ
                    exact ⟨f_in_cn_fs, f_is_ff⟩
                  have f_nin_cn_k_fs : ¬ f ∈ cn_k.fs := by
                    -- f enthält t von welchem wir wissen, dass es nicht in cn_k.fs ist daher kann t nicht in cn_k.fs.terms sein
                    sorry
                  contradiction

                | func func ts arity_ok =>
                  have ex_snd_trg : ∃ (m : Nat), m < n ∧ t ∈ FactSet.terms (((cb.branch.infinite_list m).get sorry).origin_result sorry).toSet := by sorry
                  rcases ex_snd_trg with ⟨m, lt, t_in⟩
                  sorry
                  /-
                  have some_prev_nk1 := prev_is_some_if_is_some'' cb (n + k + 1) (Option.castisSomeIfEqSome (cb.branch.infinite_list (n + k + 1)) cn_succ cn_succ_eq)
                  have lt' : m < n + k + 1 := Nat.lt_add_right (k + 1) lt
                  have lt'' : m + k < n + k + 1 := Nat.lt_succ_of_lt (Nat.add_lt_add_right lt k)

                  cases Decidable.em (m > 0) with
                    | inl gt =>
                      have m_origin_some : ((cb.branch.infinite_list m).get (some_prev_nk1 m lt')).origin.isSome := by
                        have := prev_is_some_if_is_some'' cb (n + k + 1) (Option.castisSomeIfEqSome (cb.branch.infinite_list (n + k + 1)) cn_succ cn_succ_eq) m lt'
                        have := @origin_isSome _ _ _ _ _ cb n ((cb.branch.infinite_list m).get (some_prev_nk1 m lt')) sorry
                        exact this
                      apply triggerInactiveAfterApplication cb ((cb.branch.infinite_list m).get (some_prev_nk1 m lt')) ((cb.branch.infinite_list (m + k)).get (some_prev_nk1 (m + k) lt''))
                        m k (Option.eq_some_of_isSome (some_prev_nk1 m lt')) (Option.eq_some_of_isSome (some_prev_nk1 (m + k) lt'')) m_origin_some ?_
                      sorry

                    | inr eq =>
                      have eq : m = 0 := Nat.eq_zero_of_not_pos eq
                      sorry
                      -/
                      -- m_origin_some not given, thus theorem not recurively applicable :c

            | inr trg_obs_loaded =>
              rcases trg_obs_loaded with ⟨trg_obs_k_core, trg_loaded_k_core⟩
              intro contra
              apply contra.right
              have trg_loaded_cn_succ_core := contra.left
              have trg_obs_succ_fs : obs.cond (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn_succ.fs := by
                have := before_core_sub_after_fs cb (n + k) cn_k cn_succ cn_k_eq cn_succ_eq
                exact obs.monotone this trg_obs_k_core
              have := trg_obs_in_core_if_obs_in_fs_and_loaded_in_core cb cn_succ (n + (k + 1)) cn_succ_eq ((cn.origin.get cn_origin_some).fst.val) ⟨trg_obs_succ_fs, trg_loaded_cn_succ_core⟩
              exact this


   @[grind .]
  theorem no_succ_chase_node_if_not_exists_active_trigger (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n)
    (no_act_trg : ∀ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), ¬ trg.val.active cn.core) : (cb.branch.get? (n+1)).isNone := by
      apply Classical.byContradiction
      intro contra
      simp only [Option.isNone_iff_eq_none, ne_eq] at contra
      have ex_cn_succ : ∃ (cn_succ : CoreChaseNode kb.rules), cn_succ ∈ cb.branch.get? (n+1) := Option.ne_none_iff_exists'.mp contra
      rcases ex_cn_succ with ⟨cn_succ, cn_succ_eq⟩
      have trg_act := cb.triggers_active n cn cn_eq cn_succ cn_succ_eq
      rcases trg_act with ⟨trg, trg_act, h⟩
      exact Ne.elim (fun a => no_act_trg trg.fst h) cn_eq

end CoreChaseBranch
