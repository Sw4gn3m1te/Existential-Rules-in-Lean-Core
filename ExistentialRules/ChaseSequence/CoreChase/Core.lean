import ExistentialRules.ChaseSequence.Basic
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
--abbrev obs := RestrictedObsoleteness sig



namespace CoreChaseBranch


  abbrev InductiveHomomorphismResultCore (cb : CoreChaseBranch kb) (m : FactSet sig) (depth : Nat) := {gtm : GroundTermMapping sig // (cb.branch.infinite_list depth).is_none_or (fun cn => gtm.isHomomorphism cn.fs m)}


  @[grind]
  theorem kb_det_head_len_eq (kb_det : kb.isDeterministic): ∀ (r : Rule sig), r ∈ kb.rules.rules → r.head.length = 1 := by
    unfold KnowledgeBase.isDeterministic RuleSet.isDeterministic Rule.isDeterministic at kb_det
    intro r r_in
    specialize kb_det r r_in
    grind

  theorem notExActTrigInMod_std (scb : ChaseBranch obs kb) (m : ChaseNode obs kb.rules) (m_mod : m.facts.val.modelsKb kb) : ¬ ∃ (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules), trg.val.active m.facts := by
    apply Classical.byContradiction
    intro contra
    simp only [Classical.not_not] at contra
    rcases contra with ⟨trg, trg_act⟩
    rcases trg_act with ⟨trg_loaded, trg_not_obs⟩
    simp only [obs, RestrictedObsoleteness] at *

    have ex_hom : ∃ (j : Fin trg.val.mapped_head.length) (gtm : GroundTermMapping sig), gtm.isHomomorphism (trg.val.mapped_head[↑j]'(j.isLt)).toSet m.facts.val := by sorry
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


  -- aus models rule
  --restrcited obs
  --ggf. kann es mod gebene was nicht im kontext der CC ist dann gilt das nicht
  theorem notExActTrigInMod (cb : CoreChaseBranch kb) (m : CoreChaseNode kb.rules) (m_mod : m.core.modelsKb kb) : ¬ ∃ (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules), trg.val.active m.core := by
    simp only [not_exists]
    intro trg
    unfold Trigger.active
    apply Classical.byContradiction
    simp only [Classical.not_not]
    intro ⟨trg_loaded, trg_not_obs⟩
    apply trg_not_obs
    simp only [obs, RestrictedObsoleteness] at *
    unfold PreTrigger.satisfied PreTrigger.satisfied_for_disj
    exists sorry, trg.val.subs
    constructor
    intro v v_in
    rfl
    intro e e_in
    sorry


  --@[grind]
  -- fs muss in cb vorkommen, fairness nutzen
  theorem act_trg_yields_some_node (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) (disj_idx : Nat) (fs : FactSet sig) (lt : disj_idx < trg.val.rule.head.length) (trg_act : trg.val.active fs)
    (cb : CoreChaseBranch kb) (fs_in : ∃ n, (cb.branch.infinite_list n).is_some_and (fun cn => fs = cn.fs)) :
    ∃ (cn : CoreChaseNode kb.rules), (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet ⊆ cn.fs := by
      rcases fs_in with ⟨n, fs_in⟩
      have fair := cb.fairness trg
      rcases fair with ⟨i, h⟩
      rw [Option.is_some_and_iff] at h
      rcases h with ⟨h1, h2⟩
      rcases h1 with ⟨cn2, cn2eq⟩
      exists cn2
      intro f f_in
      apply Classical.byContradiction
      intro h
      simp at h
      sorry
      -- sonnst haben wir chase term aber noch active trig d.h. kein mod

  @[grind]
  theorem fs_terms_sub_core_terms (cn : CoreChaseNode kb.rules) (t : GroundTerm sig) (t_in_core : t ∈ cn.core.terms) : t ∈ cn.fs.terms := by
      rcases t_in_core with ⟨f, f_c, f_t⟩
      have f_fs : f ∈ cn.fs := cn.core_sse.left f f_c
      exists f

  @[grind]
  theorem functional_term_originates_from_some_trigger_core (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules)
    (cn_eq : cb.branch.infinite_list n = some cn) (t : GroundTerm sig) (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) (t_mem : t ∈ cn.fs.terms) :
      ∃ (m : Nat), (cb.branch.infinite_list m).is_some_and (fun node2 => node2.origin.is_some_and (fun origin => t ∈ origin.fst.val.fresh_terms_for_head_disjunct origin.snd.val (by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt))) := by
        induction n generalizing cn with
          | zero =>
            rw [cb.database_first, Option.some.injEq] at cn_eq
            have func_free := kb.db.toFactSet.property.right
            unfold FactSet.isFunctionFree at func_free
            rcases t_mem with ⟨f, f_mem, t_mem⟩
            rw [← cn_eq] at f_mem
            specialize func_free f f_mem
            unfold Fact.isFunctionFree at func_free
            specialize func_free _ t_mem
            rcases func_free with ⟨_, func_free⟩
            rcases t_is_func with ⟨_, _, _, t_is_func⟩
            rw [t_is_func] at func_free
            simp [GroundTerm.func, GroundTerm.const] at func_free
          | succ n ih =>
            let prev_node := (cb.prev_node n (Option.isSome_of_mem cn_eq))
            cases Classical.em (t ∈ prev_node.core.terms) with
              | inl term_in_prev_node_core =>
                have term_in_prev_node_fs : t ∈ prev_node.fs.terms := fs_terms_sub_core_terms prev_node t term_in_prev_node_core
                specialize ih prev_node (prev_node_eq cb n (Option.isSome_of_mem cn_eq)) term_in_prev_node_fs
                rcases ih with ⟨m2, ih⟩
                exists m2
              | inr term_not_in_prev_node_core =>
                exists (n+1)
                rw [Option.is_some_and_iff]
                exists cn
                constructor
                exact cn_eq
                rw [Option.is_some_and_iff]
                let origin := cn.origin.get (origin_isSome cb n cn_eq)
                exists origin
                constructor
                exact Option.eq_some_of_isSome (origin_isSome cb n cn_eq)
                rcases t_mem with ⟨f, f_mem, t_mem⟩
                rw [cb.origin_trg_result_yields_next_node_fs n cn cn_eq] at f_mem
                change f ∈ (cb.prev_node n _).core ∨ f ∈ (cn.origin_result _).toSet at f_mem
                cases f_mem with
                  | inl f_mem =>
                    apply False.elim
                    apply term_not_in_prev_node_core
                    exists f
                  | inr f_mem =>
                    have t_mem : t ∈ origin.fst.val.mapped_head[origin.snd.val].flatMap GeneralizedAtom.terms := by
                      rw[List.mem_flatMap]
                      exists f
                    rw [PreTrigger.mem_terms_mapped_head_iff] at t_mem
                    cases t_mem with
                    | inl t_mem =>
                      rcases t_is_func with ⟨_, _, _, t_is_func⟩
                      rcases t_mem with ⟨_, _, t_mem⟩
                      rw [t_is_func] at t_mem
                      simp [GroundTerm.const, GroundTerm.func] at t_mem
                    | inr t_mem =>
                      cases t_mem with
                      | inl t_mem =>
                      apply False.elim; apply term_not_in_prev_node_core
                      apply FactSet.terms_subset_of_subset (cb.origin_trg_is_active_core n cn cn_eq).left
                      rw [FactSet.mem_terms_toSet]
                      rw [PreTrigger.mem_terms_mapped_body_iff]
                      apply Or.inr
                      rw [List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
                      exists v
                      constructor
                      . apply Rule.frontier_subset_vars_body; apply Rule.mem_frontier_iff_mem_frontier_for_head.mpr; exact ⟨_, v_mem⟩
                      . exact t_mem
                      | inr t_mem => exact t_mem

  @[grind]
  theorem ex_func_eq {disj_idx : Nat} {t : GroundTerm sig} {trg : RTrigger obs.toLaxObsoletenessCondition kb.rules} {lt : disj_idx < trg.val.rule.head.length} (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok := by
      cases cn_eq : t with
      | const _ =>
        rw [cn_eq] at t_mem_trg
        simp [PreTrigger.fresh_terms_for_head_disjunct, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem_trg
      | func func ts arity_ok => exists func, ts, arity_ok

  @[grind]
  theorem trigger_introducing_functional_term_occurs_in_chase_core
    {cb : CoreChaseBranch kb} {cn : CoreChaseNode kb.rules}
    {disj_idx n : Nat}
    (cn_eq : cb.branch.infinite_list n = some cn)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ cn.fs.terms)
    {trg : RTrigger obs.toLaxObsoletenessCondition kb.rules}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    -- war das ∃ (m : Nat), m < n, ... hier wichtig ?
    ∃ (m : Nat), m < n ∧ (cb.branch.infinite_list m).is_some_and (fun node2 => node2.origin.is_some_and (fun origin => origin.fst.equiv trg ∧ origin.snd.val = disj_idx)) := by
      rcases functional_term_originates_from_some_trigger_core cb n cn cn_eq t (ex_func_eq t_mem_trg) t_mem_node with ⟨n2, h⟩
      simp only [Option.is_some_and_iff] at h
      rcases h with ⟨cn2, cn2_eq, origin, origin_eq, t_mem_origin⟩
      simp only [Option.is_some_and_iff]
      exists n2
      constructor
      sorry
      exists cn2
      constructor
      exact cn2_eq
      exists origin
      constructor
      exact origin_eq
      exact RTrigger.equiv_of_term_mem_fresh_terms_for_head_disjunct t_mem_origin t_mem_trg

  @[grind]
  theorem exHomStepToAllFollowing (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cb.branch.infinite_list n = some cn) :
    ∀ m, n < m → (cb.branch.infinite_list m).is_none_or (fun cn2 => ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism cn.fs cn2.fs) := by
      intro m lt
      simp only [Option.is_none_or_iff]
      intro cn2 cn2_eq
      have diff : ∃ x, n + x = m := Nat.le.dest (Nat.le_of_lt lt)
      rcases diff with ⟨x, hx⟩
      have ex_hom := exHomFsAllFollowingFs cb n cn cn_eq x
      rw [Option.is_none_or_iff] at ex_hom
      specialize ex_hom cn2 (by grind)
      exact ex_hom

  @[grind]
  theorem result_of_trigger_introducing_functional_term_occurs_in_chase_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules)
    (disj_idx n : Nat) (trg: RTrigger obs.toLaxObsoletenessCondition kb.rules) (cn_eq : cb.branch.infinite_list n = some cn)
    (t : GroundTerm sig ) (lt : disj_idx < trg.val.rule.head.length)
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) (t_mem_node : t ∈ cn.fs.terms) :
      ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet cn.fs := by
        rcases trigger_introducing_functional_term_occurs_in_chase_core cn_eq t_mem_node t_mem_trg with ⟨n2, lt, h⟩
        simp only [Option.is_some_and_iff] at h
        rcases h with ⟨cn2, cn2_eq, origin, origin_eq, equiv, index_eq⟩
        have ex_hom_following := exHomStepToAllFollowing cb n2 cn2 cn2_eq n lt
        simp only [cn_eq, Option.is_none_or] at ex_hom_following
        have := cn2.fs_contains_origin_result
        simp only [origin_eq, Option.is_none_or] at this
        simp only [← PreTrigger.result_eq_of_equiv equiv, ← index_eq]
        rcases ex_hom_following with ⟨gtm, h2⟩
        have := GroundTermMapping.subPreservesHom cn2.fs cn.fs origin.fst.val.mapped_head[↑origin.snd].toSet this gtm h2
        exact Exists.intro gtm this

  @[grind]
  theorem result_of_trigger_introducing_functional_term_occurs_in_chase_core' (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules)
    (disj_idx n : Nat) (trg: RTrigger obs.toLaxObsoletenessCondition kb.rules) (cn_eq : cb.branch.infinite_list n = some cn)
    (t : GroundTerm sig ) (lt : disj_idx < trg.val.rule.head.length)
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) (t_mem_node : t ∈ cn.fs.terms) :
      ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet cn.core := by
      rcases result_of_trigger_introducing_functional_term_occurs_in_chase_core cb cn disj_idx n trg cn_eq t lt t_mem_trg t_mem_node with ⟨gtm, gtm_hom⟩
      rcases exHomFsCore cb n cn cn_eq with ⟨gtm2, gtm2_hom⟩
      exists gtm2 ∘ gtm
      exact GroundTermMapping.isHomomorphism_compose gtm gtm2 (trg.val.mapped_head[disj_idx]'(by grind)).toSet cn.fs cn.core gtm_hom gtm2_hom


theorem ex_endo_hom  (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules)
    (disj_idx n : Nat) (trg: RTrigger obs.toLaxObsoletenessCondition kb.rules) (cn_eq : cb.branch.infinite_list n = some cn)
    (t : GroundTerm sig ) (lt : disj_idx < trg.val.rule.head.length)
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) (t_mem_node : t ∈ cn.fs.terms) :
      ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism (trg.val.mapped_head[disj_idx]'(by rw [PreTrigger.length_mapped_head]; exact lt)).toSet cn.core ∧ gtm.isHomomorphism cn.core cn.core ∧ (Function.surjective_for_domain_and_image_set gtm cn.core.terms cn.core.terms) := by
        sorry

  -- jeder surjektive endomorphisms auf endlichen mengen ist auch ein isomorphismus


  theorem prevNodeEqDbIfOriginNone (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cb.branch.infinite_list n = some cn) (cn_origin_none : cn.origin.isNone) :
    cn.fs = kb.db.toFactSet ∧ cn.core = kb.db.toFactSet := by
      by_cases c : n = 0
      have := cb.database_first
      subst c
      grind
      have gt : n > 0 := Nat.zero_lt_of_ne_zero c
      have eq : n - 1 + 1 = n := Nat.sub_add_cancel gt
      have := @origin_isSome _ _ _ _ _ cb (n - 1) cn (by rw [eq]; exact cn_eq)
      grind

  @[grind]
  theorem exPrevCoreChaseNodeIfOriginIsSome (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cb.branch.infinite_list n = some cn) (cn_origin_some : cn.origin.isSome) :
    ∃ (prev_cn : CoreChaseNode kb.rules), (cb.branch.infinite_list (n - 1) = some prev_cn) := by
      rw [Option.isSome_iff_exists] at cn_origin_some
      induction n with
        | zero =>
          simp [cb.database_first]
        | succ n ih =>
          grind

  @[grind]
  theorem origin_trg_inactive_in_fs (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cb.branch.infinite_list n = some cn) (cn_origin_some : cn.origin.isSome) :
    ¬ (cn.origin.get cn_origin_some).fst.val.active cn.fs := by
        have trg_ex := cb.triggers_exist (n - 1)
        by_cases c_lt : n = 0
        subst c_lt
        have dbf := cb.database_first
        grind
        have c_lt := Nat.zero_lt_of_ne_zero c_lt
        have ex_prev_cn := exPrevCoreChaseNodeIfOriginIsSome cb cn n cn_eq cn_origin_some
        rcases ex_prev_cn with ⟨prev_cn, prev_cn_eq⟩
        rw [Option.is_none_or_iff] at trg_ex
        specialize trg_ex prev_cn prev_cn_eq
        rcases trg_ex with trg_ex | trg_nex
        rcases trg_ex with ⟨trg, trg_act, ⟨c, i, h2⟩⟩
        rw [Option.is_some_and_iff] at h2
        rcases h2 with ⟨cn', cn'_eq, cn'_h1, cn'h2, cn'_h3⟩
        have cn_eq_cn' : cn = cn' := by grind
        subst cn'
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
        intro contra
        rcases contra with ⟨loaded, non_obs⟩
        apply non_obs
        simp only [obs, RestrictedObsoleteness]
        unfold PreTrigger.satisfied
        rcases trg_nex with ⟨next_eq, _⟩
        grind


  theorem trg_obs_in_core_if_obs_in_fs_and_loaded_in_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cb.branch.infinite_list n = some cn) (trg : Trigger obs.toLaxObsoletenessCondition) :
      (obs.cond trg.toPreTrigger cn.fs) ∧ (trg.loaded cn.core) → obs.cond trg.toPreTrigger cn.core := by
        simp only [obs, RestrictedObsoleteness]
        intro ⟨trg_sat, trg_loaded⟩
        unfold PreTrigger.satisfied at *
        rcases trg_sat with ⟨i, gs, h1, h2⟩
        rcases (exHomFsCore cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
        have ex_eq_list : ∃ (tl : List (GroundTerm sig)), tl.toSet = cn.core.terms := by
          have := FactSet.terms_finite_of_finite cn.core (all_core_finite cn)
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
        intro v v_in
        have eq : trg.subs_for_mapped_head ⟨i, lt⟩ v = trg.subs v := by apply trg.apply_to_var_or_const_frontier_var i v v_in
        have one_more_eq : gtm.repeat_hom (rep + 1) (gs v) = gtm.repeat_hom rep (gtm (gs v)) := GroundTermMapping.repeat_hom_swap gtm rep (gs v)
        simp only [Function.comp_apply]
        specialize h1 v v_in
        rw [← h1]
        simp [rep_hom]

        rw [one_more_eq]
        specialize h (gs v) (by
          rw [← Set.ext_iff] at tl_eq
          specialize tl_eq (gs v)
          rw [← List.mem_toSet, tl_eq]
          rw [h1]
          have terms_sub := FactSet.terms_subset_of_subset cn.core_sse.left
          have ex_cnl : ∃ (cnl : List (Fact sig)), ∀ e, (e ∈ cnl ↔ e ∈ cn.core) := Set.exListOfSetIfFin cn.core (all_core_finite cn)
          rcases ex_cnl with ⟨cn_core_l, cn_core_l_eq⟩
          have eq : cn_core_l.toSet = cn.core := Set.ext cn_core_l.toSet cn.core cn_core_l_eq
          have t1 := @FactSet.mem_terms_toSet _ _ _ _ cn_core_l (trg.subs v)
          rw [eq] at t1
          rw [t1]
          have t2 := PreTrigger.mem_terms_mapped_body_iff trg.toPreTrigger (trg.subs v)
          have eq2 : cn_core_l = trg.mapped_body := by
            sorry
          rw [eq2, t2]
          have := @Rule.frontier_subset_vars_body _ _ _ _ trg.rule
          right
          exists v
          constructor
          exact this v_in
          rfl
          )
        exact h

        intro f f_in
        have rep_hom_hom' : rep_hom.isHomomorphism cn.fs cn.core := by
          simp only [rep_hom]
          have g1 := gtm_hom

          have gtm_endo : gtm.isHomomorphism cn.core cn.core := homFsToFsAlsoHomCoreToFs cn.core cn gtm gtm_hom
          have : ∀ k, (gtm.repeat_hom k).isHomomorphism cn.core cn.core := by
            intro k
            induction k with
              | zero => exact FactSet.id_is_hom
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
        --apply rep_hom_hom.right
        unfold GroundTermMapping.applyFactSet GroundTermMapping.applyFact
        apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set


        --have e : trg.mapped_head[↑i].toSet = cn.core := by sorry -- ⇐ stimmt nicht, maybe ⊆ ?
        --rw [← e]
        apply h2
        rw [List.mem_toSet]
        unfold GroundSubstitution.apply_function_free_conj TermMapping.apply_generalized_atom_list
        rw [List.mem_map]
        exists a

  theorem trg_obs_in_fs_if_obs_in_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cb.branch.infinite_list n = some cn) (trg : Trigger obs.toLaxObsoletenessCondition) :
    obs.cond trg.toPreTrigger cn.core → obs.cond trg.toPreTrigger cn.fs := by
      simp only [obs, RestrictedObsoleteness]
      unfold PreTrigger.satisfied
      rcases (exHomFsCore cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
      intro ⟨i, gs, h1, h2⟩
      exists i, gs
      constructor
      intro v v_in
      exact h1 v v_in
      have sub := cn.core_sse.left
      apply Set.subset_trans h2 sub

  @[grind]
  theorem trg_inactive_in_core_if_inactive_in_fs_and_loaded_in_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cb.branch.infinite_list n = some cn) (trg : Trigger obs.toLaxObsoletenessCondition) :
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

  @[grind]
  theorem not_first_if_origin_some (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (cn_origin_some : cn.origin.isSome) :
    ∀ (n : Nat), cb.branch.infinite_list n = some cn → n > 0 := by
      intro n cn_eq
      have dbf := cb.database_first
      grind

  theorem origin_trg_inactive_in_core

  theorem triggerInactiveAfterApplication (cb : CoreChaseBranch kb) (cn cn_succ : CoreChaseNode kb.rules) (n k : Nat)
    (cn_eq : cb.branch.infinite_list n = some cn) (cn_succ_eq : cb.branch.infinite_list (n + k) = some cn_succ) (cn_origin_some : cn.origin.isSome) :
      ¬ (cn.origin.get cn_origin_some).fst.val.active cn_succ.core := by

        have ex_prev_node := exPrevCoreChaseNodeIfOriginIsSome cb cn n cn_eq cn_origin_some
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



            have ex_cn : ∃ (cn_k : CoreChaseNode kb.rules), cb.branch.infinite_list (n + k) = some cn_k := by
              have := prev_is_some_if_is_some' cb (n + (k + 1)) cn_succ cn_succ_eq (n + k) (Nat.le_succ (n + k))
              exact Option.ne_none_iff_exists'.mp this
            rcases ex_cn with ⟨cn_k, cn_k_eq⟩
            specialize ih cn_k cn_k_eq

            unfold Trigger.active at ih
            have ih' : ¬(cn.origin.get cn_origin_some).fst.val.loaded cn_k.core ∨ (obs.cond (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn_k.core ∧ (cn.origin.get cn_origin_some).fst.val.loaded cn_k.core) := by grind
            cases ih' with
              | inl trg_not_loaded_k =>
                --intro ⟨trg_loaded_succ, trg_non_obs_succ⟩

                /-
                  A(c)
                  --------
                  A(x) -> ex z. R(x, z), R(x,x)
                  R(x,y) -> B(y)
                  --------
                  SC : {A(c); R(c, n), R(c, c); B(n); B(c)}
                  CC : {A(c); R(c,c); B(c)}
                -/

                have k_geq : k = 0 ∨ k > 0 := Nat.eq_zero_or_pos k
                cases k_geq with
                  | inl eq =>
                    simp_all
                    subst cn_k
                    intro ⟨x, y⟩

                    sorry

                  | inr gt =>
                    sorry




                have t_mem : ∃ (t : GroundTerm sig), t ∈ cn.core.terms ∧ ¬ t ∈ cn_k.core.terms ∧ t ∈ cn_succ.core.terms := by

                  have gt : n > 0 := not_first_if_origin_some cb cn cn_origin_some n cn_eq

                  have trg_active_cn' : (cn.origin.get cn_origin_some).fst.val.active prev_cn.core := by
                    have := cb.origin_trg_is_active_core (n-1) cn
                    simp [Nat.sub_add_cancel gt] at this
                    specialize this cn_eq
                    grind

                  have trg_active_cn : (cn.origin.get cn_origin_some).fst.val.active cn.core := by
                    have ex_cn_1 : ∃ (cn_1 : CoreChaseNode kb.rules), cb.branch.infinite_list (n + 1) = some cn_1 := by
                      have := prev_is_some_if_is_some' cb (n + (k + 1)) cn_succ cn_succ_eq (n + 1) (by grind)
                      exact Option.ne_none_iff_exists'.mp this
                    rcases ex_cn_1 with ⟨cn_1, cn_1_eq⟩
                    have := cb.origin_trg_is_active_core n cn sorry -- ← Def is giga sus ඞ


                    sorry

                  --have l1 := trg_active_cn.left
                  have l1 := trg_active_cn'.left
                  have l2 := trg_not_loaded_k
                  have l3 := trg_loaded_succ


                  unfold PreTrigger.loaded at l1 l2 l3
                  have s1 := FactSet.terms_subset_of_subset cn.core_sse.left
                  have s2 := FactSet.terms_subset_of_subset cn_k.core_sse.left
                  have s3 := FactSet.terms_subset_of_subset cn_succ.core_sse.left

                  have ex_f_nin : ∃ (f : Fact sig), f ∈ (cn.origin.get cn_origin_some).fst.val.mapped_body.toSet ∧ ¬ f ∈ cn_k.core := by
                    unfold Subset instHasSubsetSet at l2
                    simp at l2
                    exact l2


                  rcases ex_f_nin with ⟨f, f_in, f_nin⟩

                  have all_terms_sub : ∀ (t : GroundTerm sig), t ∈ FactSet.terms (cn.origin.get cn_origin_some).fst.val.mapped_body.toSet → t ∈ cn_k.core.terms := by sorry
                  --apply Classical.byContradiction

                  --intro contra
                  --simp only [not_exists, Classical.not_and_iff_not_or_not, Classical.not_not] at contra

                  /-
                  Was wir zeigen wollen ist: `∃ t, t ∈ cn.core.terms ∧ ¬t ∈ cn_k.core.terms ∧ t ∈ cn_succ.core.terms`

                  gleiche (oder mehr) terme aber weniger fakten (⊈)
                  -> es gibt einen Fakt in A der nicht in B ist (∃ f, f ∈ A ∧ f ∉ B)
                    -> der neu entstehende fakt mit einer neuen null muss mandatory keep sein und einen alten ersetzen

                  -> B enthält alle Terme aus A (A.terms ⊆ B.terms)


                  σ_1 : P(x,y) → ∃z, Q(y,z)
                  σ_2 : Q(x,y) → P(y,x)
                  σ_3 : P(x,y), Q(y,z), P(z,y) → ∃w, R(y,w), Q(w,w)

                  σ_3'​ : P(x,y), Q(y,z), P(z,y) → ∃(w v), R(y,w), Q(z,z), T(v,v)

                  σ_3'' : P(x,y), Q(y,z), P(z,y), T(v,v) → ∃w, R(y,w), Q(z,z), T(z,z), G(v)


                  σ_4 : P(x,y), Q(y, z), P(z, y) → ∃w, G(x,y,z,w)


                  I_0 = {P(a,b), T(c,c)}
                  I_1 = {P(a,b), T(c,c), Q(b,n_1)} (σ_1)
                  I_2 = {P(a,b), T(c,c), Q(b, n_1), P(n_1, b)} (σ_2)


                  mit σ_1
                  I_3 = {P(a,b), Q(b, n_1), P(n_1, b), `Q(b, n_2)`} -> n_1 ↦ n_2 -> core(I_3) = {P(a,b), Q(b, n_1), P(n_1, b)}
                  I_2.terms = {a,b,n_1} = core(I_3).terms = {a,b,n_1}

                  mit σ_3
                  I_3 = {P(a,b), Q(b, n_1), P(n_1, b), R(b, n_2), Q(n_2, n_2)} = core(I_3)
                  I_2.terms = {a,b,n_1} ≠ I_3.terms = {a,b,n_1,n_2} -> I_2.terms ⊆ I_3.terms

                  mit σ_3'
                  I_3 ​ = {P(a,b), T(c,c), Q(b,n_1​), P(n_1​,b), R(b,n_2​), Q(n_2​,n_2​), T(n_3,n_3)}  mit core(I_3) = {P(a,b), T(c,c) Q(b,n_1​), P(n_1​,b), R(b,n_2​)}
                  Fact removed: T(n_3, n_3) (T(c, c) muss bleiben da orginal)

                  mit σ_3''
                  I_3 ​ = {P(a,b), T(c,c), Q(b,n_1​), P(n_1​,b), R(b,n_2​), Q(n_2​,n_2​), T(n_2,n_2), G(c)}  mit core(I_3) = {P(a,b), Q(b,n_1), P(n_1,b), R(b,n_2), Q(n_2,n_2), T(c,c), G(c)}
                  Fact removed: T(c, c)


                  I_0 = {All(a,b,c,...), P(a,b), P(b,a)} -> I_0.terms = {a,b,c...} (alle Terme) [kann es so ein All() Fakt geben ?]

                  I_1 = {All(), R(n)}



                  -/
                  have f_in' : f ∈ cn.core := by
                    have : (cn.origin.get cn_origin_some).fst.val.mapped_body.toSet ⊆ cn.core := by grind
                    exact l1 f f_in

                  have ex_cm := exIntermeadiateCoreChaseNodeIfFactMissing cb cn cn_k n k cn_eq cn_k_eq f f_in' f_nin


                  rcases ex_cm with ⟨cm, f_in_cm, f_nin_cm⟩


                  sorry

                rcases t_mem with ⟨t, t_in_cn, t_in_cn_k, t_in_cn_succ⟩
                cases eq : t with
                  | const c =>
                    have := allFfInNextFsIfSome cb (n + k) cn_k cn_k_eq
                    rw [Option.is_none_or_iff] at this
                    specialize this cn_succ cn_succ_eq

                    have ex_f : ∃ (f : Fact sig), f ∈ cn.fs ∧ t ∈ f.terms ∧ f.isFunctionFree := by sorry

                    rcases ex_f with ⟨f, f_in_cn_fs, t_in_f, f_is_ff⟩
                    specialize this f
                    have ff_in_all_succ := allFfInAllSuccIfSome cb n k cn cn_eq
                    rw [Option.is_none_or_iff] at ff_in_all_succ
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

                        -- m_origin_some not given, thus theorem not recurively applicable :c

                        sorry


              | inr trg_obs_loaded =>
                rcases trg_obs_loaded with ⟨trg_obs_k_core, trg_loaded_k_core⟩
                intro contra
                apply contra.right
                have trg_loaded_cn_succ_core := contra.left

                have trg_obs_succ_fs : obs.cond (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn_succ.fs := by
                  have := prevCoreSubsetOfFactset cb (n + k) cn_k cn_succ cn_k_eq cn_succ_eq
                  exact obs.monotone (cn.origin.get cn_origin_some).fst.val.toPreTrigger cn_k.core cn_succ.fs this trg_obs_k_core

                have := trg_obs_in_core_if_obs_in_fs_and_loaded_in_core cb cn_succ (n + (k + 1)) cn_succ_eq ((cn.origin.get cn_origin_some).fst.val) ⟨trg_obs_succ_fs, trg_loaded_cn_succ_core⟩
                exact this


  -- set_option maxHeartbeats 5000000
  noncomputable def inductive_homomorphism_core_with_prev_node_and_trg (cb : CoreChaseBranch kb) (m : FactSet sig) (m_mod : m.modelsKb  kb) (kb_det : kb.isDeterministic) (prev_depth : Nat) (prev_result : InductiveHomomorphismResultCore cb m prev_depth) (prev_node : CoreChaseNode kb.rules) (prev_node_eq : (cb.branch.infinite_list prev_depth = some prev_node)) (trg_ex : exists_trigger_opt_fs_core kb.rules prev_node (cb.branch.infinite_list prev_depth.succ)): InductiveHomomorphismResultCore cb m (prev_depth + 1) :=

    let ⟨prev_hom, prev_cond⟩ := prev_result

    have prev_hom_is_hom : prev_hom.isHomomorphism prev_node.fs m := by
      rw [Option.is_none_or_iff] at prev_cond
      specialize prev_cond prev_node prev_node_eq
      simp_all only [Option.get_some]

    have prev_hom_is_hom_core : prev_hom.isHomomorphism prev_node.core m := by
      exact homFsToFsAlsoHomCoreToFs m prev_node prev_hom prev_hom_is_hom

    let trg := Classical.choose trg_ex
    let trg_spec := Classical.choose_spec trg_ex
    let trg_active_for_current_step := trg_spec.left
    let trg_result_used_for_next_chase_step := trg_spec.right

    let trg_variant_for_m : RTrigger obs.toLaxObsoletenessCondition kb.rules := {
      val := {
        rule := trg.val.rule
        subs := fun t => prev_hom (trg.val.subs t)
      }
      property := trg.property
    }

  have trg_variant_loaded_for_m : trg_variant_for_m.val.loaded m := by
    have : trg_variant_for_m.val.loaded (prev_hom.applyFactSet prev_node.core) := by
      apply PreTrigger.term_mapping_preserves_loadedness
      . exact prev_hom_is_hom_core.left
      · exact trg_active_for_current_step.left
    apply Set.subset_trans
    . exact this
    . exact prev_hom_is_hom_core.right

  have trg_variant_satisfied_on_m : trg_variant_for_m.val.satisfied m := by
    have m_models_rule : m.modelsRule trg_variant_for_m.val.rule := by exact m_mod.right trg.val.rule trg.property
    unfold FactSet.modelsRule at m_models_rule
    apply m_models_rule
    apply trg_variant_loaded_for_m

  let head_index_for_m_subs := Classical.choose trg_variant_satisfied_on_m
  let h_head_index_for_m_subs := Classical.choose_spec trg_variant_satisfied_on_m
  let obs_for_m_subs := Classical.choose h_head_index_for_m_subs
  let h_obs_at_head_index_for_m_subs := Classical.choose_spec h_head_index_for_m_subs

  let result_index_for_trg : Fin trg.val.mapped_head.length := ⟨head_index_for_m_subs.val, by unfold PreTrigger.mapped_head; simp; exact head_index_for_m_subs.isLt⟩

  let next_hom : GroundTermMapping sig := fun t =>
    match t.val with
      | FiniteTree.leaf _ => t
      | FiniteTree.inner _ _ =>
          let t_in_step_j_dec := Classical.propDecidable (t ∈ prev_node.core.terms)
          --let t_in_step_j_dec := Classical.propDecidable (∃ (gtm : GroundTermMapping sig), t ∈ (gtm.applyFactSet prev_node.core).terms)
          match t_in_step_j_dec with
          | Decidable.isTrue _ => prev_hom t
          | Decidable.isFalse _ =>
            let t_in_trg_result_dec := Classical.propDecidable (∃ f, f ∈ (trg.val.mapped_head[result_index_for_trg.val]) ∧ t ∈ f.terms)
            match t_in_trg_result_dec with
            | Decidable.isFalse _ => t
            | Decidable.isTrue t_in_trg_result =>
              let f := Classical.choose t_in_trg_result
              let f_spec := Classical.choose_spec t_in_trg_result
              let v_for_t := trg.val.var_or_const_for_result_term result_index_for_trg f_spec.left f_spec.right
              obs_for_m_subs.apply_var_or_const v_for_t

    have next_hom_id_const : next_hom.isIdOnConstants := by
      intro term
      cases eq : term with
      | const c => rfl
      | func _ _ => trivial

    ⟨next_hom, by
      rw [Option.is_none_or_iff] at prev_cond
      specialize prev_cond prev_node prev_node_eq

      simp [Option.is_none_or_iff]
      intro next_node next_node_eq
      constructor
      exact next_hom_id_const
      -- prev node @ j, next node at j+1
      -- next_node_eq

      have head_i_eq : head_index_for_m_subs.val = 0 := by
        rw [← Nat.lt_one_iff]
        have len_eq := kb_det_head_len_eq kb_det trg_variant_for_m.val.rule trg.property
        have trg_len_eq : trg_variant_for_m.val.mapped_head.length = trg_variant_for_m.val.rule.head.length := PreTrigger.length_mapped_head trg_variant_for_m.val.toPreTrigger
        subst trg_variant_for_m
        rw [← len_eq]
        exact head_index_for_m_subs.isLt

      have next_node_results_from_trg : next_node.fs = prev_node.core ∪ trg.val.mapped_head[result_index_for_trg.val].toSet := by
        unfold exists_trigger_opt_fs_core at trg_ex

        rcases trg_result_used_for_next_chase_step with ⟨c, i, c_eq⟩

        rw [Option.is_some_and_iff] at c_eq
        rcases c_eq with ⟨_, aux_eq, next_node_fs_eq,_⟩
        rw [next_node_eq, Option.some_inj] at aux_eq; rw [← aux_eq] at next_node_fs_eq

        have i_eq : i.val = 0 := by
          rw [← Nat.lt_one_iff]
          have len_eq := kb_det_head_len_eq kb_det trg.val.rule trg.property
          have trg_len_eq : trg.val.mapped_head.length = trg.val.rule.head.length := PreTrigger.length_mapped_head trg.val.toPreTrigger
          subst trg
          rw [← len_eq]
          have := i.isLt
          exact Nat.lt_of_lt_of_eq this trg_len_eq

        subst trg
        have next_node_fs_eq' := next_node_fs_eq

        subst result_index_for_trg
        simp only [Nat.succ_eq_add_one]

        simp only [i_eq, ← head_i_eq] at next_node_fs_eq
        exact next_node_fs_eq

      rw [next_node_results_from_trg]
      intro mapped_fact fact_in_chase
      rcases fact_in_chase with ⟨fact, fact_in_chase, rw_aux⟩
      rw [rw_aux]

      cases fact_in_chase with
        | inl fact_in_prev_step =>
            apply prev_cond.right
            exists fact
            constructor
            exact prev_node.core_sse.left fact fact_in_prev_step
            unfold TermMapping.apply_generalized_atom
            rw [GeneralizedAtom.mk.injEq]
            constructor
            . rfl
            rw [List.map_inj_left]
            intro ground_term _
            have : ∃ f, f ∈ prev_node.core ∧ ground_term ∈ f.terms := by
              exists fact
            cases eq : ground_term with
            | const c =>
              simp only [GroundTerm.const, next_hom]
              apply Eq.symm
              apply GroundTermMapping.apply_constant_is_id_of_isIdOnConstants prev_cond.left c
            | func _ _ =>
              simp only [GroundTerm.func, next_hom]
              split
              . rfl
              . simp only [eq, GroundTerm.func] at this
                contradiction
        | inr fact_in_trg_result =>
                apply h_obs_at_head_index_for_m_subs.right
                rw [List.mem_toSet]
                rw [List.mem_toSet] at fact_in_trg_result
                unfold GroundSubstitution.apply_function_free_conj TermMapping.apply_generalized_atom_list
                rw [List.mem_map]
                exists (trg.val.atom_for_result_fact result_index_for_trg fact_in_trg_result)
                constructor
                . unfold trg_variant_for_m
                  unfold PreTrigger.atom_for_result_fact
                  apply List.getElem_mem
                . conv => right; rw [← trg.val.apply_on_atom_for_result_fact_is_fact result_index_for_trg fact_in_trg_result]
                  rw [← PreTrigger.apply_subs_for_atom_eq]
                  rw [← GroundTermMapping.applyFact.eq_def]
                  rw [← GroundSubstitution.apply_function_free_atom_compose _ _ _ (by intro c _; exact next_hom_id_const (.const c))]
                  unfold GroundSubstitution.apply_function_free_atom
                  apply TermMapping.apply_generalized_atom_congr_left
                  intro voc voc_mem
                  cases voc with
                  | const c => simp [GroundSubstitution.apply_var_or_const]
                  | var v =>
                    rw [GroundSubstitution.apply_var_or_const_compose_of_isIdOnConstants _ _ next_hom_id_const]
                    simp only [Function.comp_apply, GroundSubstitution.apply_var_or_const]
                    cases Decidable.em (v ∈ trg.val.rule.frontier) with
                    -- non existential var
                    | inl v_front =>
                      rw [h_obs_at_head_index_for_m_subs.left v v_front]
                      unfold PreTrigger.subs_for_mapped_head
                      rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ v_front]
                      unfold trg_variant_for_m
                      simp only
                      cases eq_v : trg.val.subs v with
                      | const c =>
                        unfold GroundTerm.const
                        unfold next_hom
                        simp only
                        apply GroundTermMapping.apply_constant_is_id_of_isIdOnConstants
                        exact prev_hom_is_hom.left
                      | func func ts arity_ok =>
                        unfold GroundTerm.func
                        unfold next_hom
                        simp only
                        have h : ∃ f, f ∈ prev_node.core ∧ (GroundTerm.func func ts arity_ok) ∈ f.terms := by
                          have frontier_occurs_in_body : ∀ (r : Rule sig) v, v ∈ r.frontier -> ∃ f, f ∈ r.body ∧ (VarOrConst.var v) ∈ f.terms := by
                            intro r
                            unfold Rule.frontier
                            cases r.body with
                            | nil => intros; contradiction
                            | cons head tail =>
                              intro v vInFrontier
                              rw [List.mem_filter] at vInFrontier
                              have mem_body := vInFrontier.left
                              unfold FunctionFreeConjunction.vars at mem_body
                              rw [List.mem_flatMap] at mem_body
                              rcases mem_body with ⟨a, a_mem, v_mem⟩
                              exists a
                              constructor
                              . exact a_mem
                              . unfold FunctionFreeAtom.variables at v_mem
                                apply VarOrConst.filterVars_occur_in_original_list
                                exact v_mem
                          rcases frontier_occurs_in_body trg.val.rule v v_front with ⟨body_atom, v_front'⟩
                          exists trg.val.subs.apply_function_free_atom body_atom
                          constructor
                          . apply trg_active_for_current_step.left
                            rw [List.mem_toSet]
                            apply List.mem_map_of_mem
                            exact v_front'.left
                          . rw [← eq_v]
                            unfold GroundSubstitution.apply_function_free_atom TermMapping.apply_generalized_atom
                            rw [List.mem_map]
                            exists VarOrConst.var v
                            simp [GroundSubstitution.apply_var_or_const, v_front'.right]

                        have : Classical.propDecidable ((GroundTerm.func func ts arity_ok) ∈ prev_node.core.terms) = isTrue h := by
                          cases Classical.propDecidable ((GroundTerm.func func ts arity_ok) ∈ prev_node.core.terms) <;> trivial
                        unfold GroundTerm.func at this
                        rw [this]
                    -- existential var
                    | inr v_front =>
                      unfold PreTrigger.subs_for_mapped_head
                      rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
                      unfold PreTrigger.functional_term_for_var
                      unfold next_hom

                      have h : ¬ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ prev_node.core.terms := by
                        intro contra
                        apply trg_active_for_current_step.right

                        rcases trg_spec.left with ⟨tsl, tsr⟩
                        unfold PreTrigger.loaded at tsl

                        simp only [obs]
                        simp only [RestrictedObsoleteness]
                        unfold PreTrigger.satisfied
                        exists head_index_for_m_subs
                        unfold PreTrigger.satisfied_for_disj

                        have lt : result_index_for_trg.val < trg.val.rule.head.length := by
                          have len_eq := kb_det_head_len_eq kb_det trg_variant_for_m.val.rule trg.property
                          rw [head_i_eq, len_eq]
                          exact Nat.one_pos

                        have t_mem_fresh : (trg.val.functional_term_for_var (↑result_index_for_trg) v ∈ trg.val.fresh_terms_for_head_disjunct result_index_for_trg.val lt) := by
                          simp [PreTrigger.fresh_terms_for_head_disjunct, PreTrigger.functional_term_for_var, GroundTerm.func]
                          unfold Rule.existential_vars_for_head_disjunct
                          rw [List.mem_filter]
                          constructor
                          rw [FunctionFreeConjunction.mem_vars]
                          exists (trg.val.atom_for_result_fact result_index_for_trg fact_in_trg_result)
                          exact ⟨PreTrigger.atom_for_result_fact_mem_head, voc_mem⟩
                          exact decide_eq_true v_front

                        have : ∃ func ts arity_ok, trg.val.functional_term_for_var (↑result_index_for_trg) v = GroundTerm.func func ts arity_ok := ex_func_eq t_mem_fresh

                        have := functional_term_originates_from_some_trigger_core
                          cb prev_depth prev_node prev_node_eq (trg.val.functional_term_for_var result_index_for_trg.val v) this
                          (fs_terms_sub_core_terms prev_node (trg.val.functional_term_for_var (↑result_index_for_trg) v) contra)
                        rcases this with ⟨m, h2⟩
                        rw [Option.is_some_and_iff] at h2
                        rcases h2 with ⟨cn_m, cn_m_eq, h3⟩
                        rw [Option.is_some_and_iff] at h3
                        rcases h3 with ⟨m_origin, m_origin_eq, h4⟩

                        have ex_gtm := result_of_trigger_introducing_functional_term_occurs_in_chase_core'
                          cb prev_node result_index_for_trg.val prev_depth trg prev_node_eq
                            (trg.val.functional_term_for_var result_index_for_trg.val v) lt t_mem_fresh
                            (fs_terms_sub_core_terms prev_node (trg.val.functional_term_for_var (↑result_index_for_trg) v) contra)

                        rcases ex_gtm with ⟨gtm, gtm_hom⟩
                        ----

                        have ex_gtm := ex_endo_hom cb prev_node result_index_for_trg.val prev_depth trg prev_node_eq
                            (trg.val.functional_term_for_var result_index_for_trg.val v) lt t_mem_fresh
                            (fs_terms_sub_core_terms prev_node (trg.val.functional_term_for_var (↑result_index_for_trg) v) contra)

                        rcases ex_gtm with ⟨gtm, gtm_hom, gtm_endo, gtm_surj⟩

                        have ex_eq_list : ∃ (tl : List (GroundTerm sig)), tl.toSet = prev_node.core.terms := by
                          have := Set.exListOfSetIfFin prev_node.core.terms sorry
                          sorry

                        rcases ex_eq_list with ⟨tl, tl_eq⟩
                        have gtm_surj_list : Function.surjective_for_domain_and_image_list gtm tl tl := by sorry
                        have ex_reps := gtm.exists_repetition_that_is_inverse_of_surj tl gtm_surj_list

                        rcases ex_reps with ⟨rep, h⟩


                        let rep_hom := gtm.repeat_hom rep
                        --exists (rep_hom ∘ trg.val.subs_for_mapped_head result_index_for_trg)
                        exists (gtm ∘ trg.val.subs_for_mapped_head result_index_for_trg)



                        constructor
                        intro v2 v2_in
                        rcases h_obs_at_head_index_for_m_subs with ⟨lhs, rhs⟩
                        specialize lhs v2 v2_in

                        /-
                          fallunterscheidung des hom ob surjektiv von frontier nach frontier -> permulation der terme

                          anwendung von trigger auf v kann nicht vorher kommen, da der trigger sonnst hätte schon eher benutzt werden müssen und somit nicht mehr anwendbar wäre

                          ggf. term mapping a → b → a

                          wenn gtm nicht id, dann gibt es sin subset der domain auf welchem er (ggf.) nicht surjektiv ist

                          nicht surjektiv auf frontier termen, dann kann aber sein dass er einen frontier term auf einen nicht frontier term mapped und einen nicht frontier term auf einen frontier term

                          homomorphismus solange wiederholen bis die permutation wieder die id ist

                           fs
                           |
                           ↓
                          core



                          das resultat mit endo auf core erstmal mit sorry
                          → auf prev node core ist gtm endo

                          core is weak und finite also strong daher h von fs.term nach fs.terms ist surjektiv

                          exists_repetition_that_is_inverse_or_surj -> gibt n wie of perm rep bis id

                          dann exists n fachte wdh von gtm ∘ ...

                          hom von mapped head in core
                          → n fache wdh von mapped head in core z.z.
                          → repeat_hom_is_isomorphism
                          → ishomomorphism_compose



                          jeder endo auf core ist surjektiv

                          result dass gtm auch endo auf core ist

                          problem: ein trigger wird wieder loaded -> duch core berechnung unloaded dann wieder loaded aber dann wird der funktions term der entfernt wurde wieder eingeführt wird das kann aber nicht sein weil dann ex trigger der 2 mal angewand wurde.


                          → in core chase trigger nicht 2 mal angewand werden also kommt nicht vor in allen späteren origins

                          wenn trigger angewender ist er danach obsolete falls er loaded war


                        -/
                        have eq : trg.val.subs_for_mapped_head result_index_for_trg v2 = trg.val.subs v2 := by --gleich auf frontier vars, auf ex. nicht by def
                          sorry



                        sorry
                        intro f' f'_in
                        unfold GroundSubstitution.apply_function_free_conj TermMapping.apply_generalized_atom_list at f'_in
                        rw [List.mem_toSet, List.mem_map] at f'_in
                        rcases f'_in with ⟨a, ahl, ahr⟩
                        rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants _ _ (gtm_hom.left)] at ahr
                        rw [← ahr]
                        simp only [Function.comp_apply]
                        apply gtm_hom.right
                        apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set

                        rw [← PreTrigger.apply_subs_for_mapped_head_eq]
                        rw [List.mem_toSet]
                        apply List.mem_map_of_mem
                        exact ahl

                      have : Classical.propDecidable ((trg.val.functional_term_for_var result_index_for_trg.val v) ∈ prev_node.core.terms) = isFalse h := by
                        cases Classical.propDecidable ((trg.val.functional_term_for_var result_index_for_trg.val v) ∈ prev_node.core.terms) <;> trivial
                      unfold PreTrigger.functional_term_for_var at this
                      rw [this]

                      have h : ∃ f, f ∈ (trg.val.mapped_head[result_index_for_trg.val]) ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms := by
                        exists fact
                        constructor
                        . exact fact_in_trg_result
                        . rw [← trg.val.apply_on_atom_for_result_fact_is_fact result_index_for_trg fact_in_trg_result]
                          rw [← trg.val.apply_to_var_or_const_non_frontier_var _ _ v_front]
                          unfold PreTrigger.apply_to_function_free_atom
                          apply List.mem_map_of_mem
                          exact voc_mem

                      have : Classical.propDecidable (∃ f, f ∈ (trg.val.mapped_head[result_index_for_trg.val]) ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms) = isTrue h := by
                        cases Classical.propDecidable (∃ f, f ∈ (trg.val.mapped_head[result_index_for_trg.val]) ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms) <;> trivial
                      unfold PreTrigger.functional_term_for_var at this
                      rw [this]
                      simp only [GroundTerm.func]

                      have spec := Classical.choose_spec h
                      have : trg.val.var_or_const_for_result_term result_index_for_trg spec.left spec.right = VarOrConst.var v := by
                        have : (trg.val.apply_to_var_or_const result_index_for_trg.val (trg.val.var_or_const_for_result_term result_index_for_trg spec.left spec.right)) = trg.val.apply_to_var_or_const result_index_for_trg.val (VarOrConst.var v) := by
                          rw [PreTrigger.apply_on_var_or_const_for_result_term_is_term]
                          rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
                        apply Eq.symm
                        apply trg.val.apply_to_var_or_const_injective_of_not_in_frontier ⟨result_index_for_trg.val, by rw [← PreTrigger.length_mapped_head]; exact result_index_for_trg.isLt⟩ v_front
                        rw [this]
                      rw [this]
                      simp only [GroundSubstitution.apply_var_or_const]
                      rfl
      ⟩

  noncomputable def inductive_homomorphism_core_with_prev_node (cb : CoreChaseBranch kb) (m : FactSet sig) (m_mod : m.modelsKb  kb) (kb_det : kb.isDeterministic) (prev_depth : Nat) (prev_result : InductiveHomomorphismResultCore cb m prev_depth) (prev_node : CoreChaseNode kb.rules) (prev_node_eq : (cb.branch.infinite_list prev_depth = some prev_node)) : InductiveHomomorphismResultCore cb m (prev_depth + 1) :=
    let trg_ex_dec := Classical.propDecidable (exists_trigger_opt_fs_core kb.rules prev_node (cb.branch.infinite_list prev_depth.succ))
    match trg_ex_dec with
      | .isFalse contra =>
        let ⟨prev_hom, prev_cond⟩ := prev_result
        ⟨prev_hom, by
          have trg_ex := cb.triggers_exist prev_depth
          rw [Option.is_none_or_iff] at trg_ex
          specialize trg_ex prev_node prev_node_eq
          cases trg_ex with
          | inl trg_ex => contradiction
          | inr trg_ex => rw [trg_ex.right]; simp [Option.is_none_or]
          ⟩

      | .isTrue trg_ex =>
        inductive_homomorphism_core_with_prev_node_and_trg cb m m_mod kb_det prev_depth prev_result prev_node prev_node_eq trg_ex

  noncomputable def inductive_homomorphism_core (cb : CoreChaseBranch kb) (m : FactSet sig) (m_mod : m.modelsKb  kb) (kb_det : kb.isDeterministic) : (depth : Nat) → InductiveHomomorphismResultCore cb m depth
    | .zero => ⟨id, by
        simp [Option.is_none_or]
        rw [cb.database_first]
        simp
        constructor
        intro gt
        split
        next => trivial
        next => trivial
        intro el el_in_set
        cases el_in_set with | intro f hf =>
        apply m_mod.left
        have : f = el := by have hfr := hf.right; simp [TermMapping.apply_generalized_atom] at hfr; rw [hfr]
        rw [this] at hf
        exact hf.left
      ⟩
    | .succ j =>
      let prev_hom := (inductive_homomorphism_core cb m m_mod kb_det j).val
      let prev_cond := (inductive_homomorphism_core cb m m_mod kb_det j).property
      let prev_node := cb.branch.infinite_list j

      match prev_node_eq : prev_node with
        | .none => ⟨prev_hom, by
          rw [Option.is_none_or_iff] at *
          intro cn cn_eq
          have := prev_is_some_if_is_some cb j.succ
            (Option.NeqNoneIfIsSome (cb.branch.infinite_list j.succ) cn cn_eq) j (Nat.lt_add_one j)
          contradiction
          ⟩
        | .some cn =>
          inductive_homomorphism_core_with_prev_node cb m m_mod kb_det j ⟨prev_hom, prev_cond⟩ cn prev_node_eq

  theorem coreChaseResultIsUniversal (cb : CoreChaseBranch kb) (ter' : cb.terminates') (kb_det : kb.isDeterministic) : ∀ (m : FactSet sig), m.modelsKb kb → ∃ (h : GroundTermMapping sig), h.isHomomorphism (cb.result ter') m := by
    intro m m_mod
    let result : FactSet sig := cb.result ter'
    rcases ter' with ⟨n_ter, ter_at_n⟩
    let h:= inductive_homomorphism_core cb m m_mod kb_det n_ter
    exists h
    have p := h.property
    unfold CoreChaseBranch.result
    simp only [Option.castToMemIfNotNone, ne_eq]
    split
    next _ _ _ cn _ _ _ =>
      rw [Option.is_none_or_iff] at p
      specialize p cn (by grind)
      exact homFsToFsAlsoHomCoreToFs m cn h.val p
    next => trivial

  -- main theorem
  -- if cb.terminates → cb.result.universalmodels kb ∧ Set.finite cb.result
  -- ∃ fs, Set.finite fs ∧ fs.universalmodels kb → cb.terminates


  theorem coreAndStandardChaseEqStart (scb : ChaseBranch obs kb) (ccb : CoreChaseBranch kb) :
    (scb.branch.infinite_list 0).is_some_and (fun scn => (ccb.branch.infinite_list 0).is_some_and (fun ccn => scn.facts.val = ccn.fs)) := by
      have ccb_dbf := ccb.database_first
      have scb_dbf := scb.database_first
      unfold PossiblyInfiniteList.head InfiniteList.head InfiniteList.get at scb_dbf
      simp only [Option.is_some_and]
      split
      next => grind
      next => grind


  @[grind]
  theorem prev_is_some_if_is_some_std (cb : ChaseBranch obs kb) (n : Nat) (is_some_at : cb.branch.infinite_list n ≠ none) : ∀ m, m < n → cb.branch.infinite_list m ≠ none := by
    intro m lt
    intro contra
    have := cb.branch.get?_eq_none_of_le_of_eq_none contra n (Nat.le_of_lt lt)
    simp only [PossiblyInfiniteList.get?, InfiniteList.get] at this
    rw [this] at is_some_at
    simp at is_some_at

  @[grind]
  theorem prev_is_some_if_is_some'_std (cb : ChaseBranch obs kb) (n : Nat) (is_some_at : (cb.branch.get? n).isSome) : ∀ m, m < n → (cb.branch.infinite_list m).isSome := by
    intro m lt
    have := prev_is_some_if_is_some_std cb n ((Option.isSomeIffNeqNone (cb.branch.infinite_list n)).mp is_some_at) m lt
    exact (Option.isSomeIffNeqNone (cb.branch.infinite_list m)).mpr this

  @[grind]
  theorem prev_eq_is_some_if_is_some_std (scb : ChaseBranch obs kb) (n : Nat) (is_some_at : scb.branch.infinite_list n ≠ none) : ∀ m, m ≤ n → scb.branch.infinite_list m ≠ none := by
    grind

   @[grind]
  theorem prev_eq_is_some_if_is_some'_std (scb : ChaseBranch obs kb) (n : Nat) (is_some_at : (scb.branch.infinite_list n).isSome) : ∀ m, m ≤ n → scb.branch.infinite_list m ≠ none := by
    grind


  @[grind]
  theorem allFfInNextFsIfSome_std (scb : ChaseBranch obs kb) (n : Nat) (x : ChaseNode obs kb.rules) (x_eq : scb.branch.infinite_list n = some x) :
    (scb.branch.infinite_list (n+1)).is_none_or (fun cn => ∀ f, f ∈ x.facts.val ∧ f.isFunctionFree → f ∈ cn.facts.val) := by
      rw [Option.is_none_or_iff]
      intro cn_succ cn_succ_eq f ⟨f_in, f_is_ff⟩
      have := scb.triggers_exist n
      rw [Option.is_none_or_iff] at this
      specialize this x x_eq
      simp at this
      rcases this with trg_ex | trg_nex
      unfold exists_trigger_opt_fs at trg_ex
      rcases trg_ex with ⟨trg, trg_act, ⟨i, h2⟩⟩
      unfold PossiblyInfiniteList.drop InfiniteList.drop PossiblyInfiniteList.tail PossiblyInfiniteList.head InfiniteList.head InfiniteList.get InfiniteList.tail InfiniteList.get at h2
      simp at h2
      rw [cn_succ_eq] at h2
      have x_core_sse : x.facts.val ⊆ cn_succ.facts.val := by
        intro f f_in
        grind
      exact x_core_sse f f_in
      rcases trg_nex with ⟨trg_nex, succ_eq⟩
      unfold PossiblyInfiniteList.drop InfiniteList.drop PossiblyInfiniteList.tail PossiblyInfiniteList.head InfiniteList.head InfiniteList.get InfiniteList.tail InfiniteList.get  at succ_eq
      simp at succ_eq
      rw [cn_succ_eq] at succ_eq
      contradiction


  @[grind]
  theorem cbDbInAllSucc_std (scb : ChaseBranch obs kb) (ccb : CoreChaseBranch kb) (n : Nat) (scn : ChaseNode obs kb.rules) (init : CoreChaseNode kb.rules) (init_eq : ccb.branch.infinite_list 0 = some init) (scn_eq : scb.branch.infinite_list n = some scn):
    init.fs ⊆ scn.facts.val := by
      have db_funfree := kb.db.toFactSet.property.right
      have init_eq' : init.fs = kb.db.toFactSet.val := by
        simp [ccb.database_first] at init_eq
        grind
      have scb_dbf := scb.database_first
      unfold PossiblyInfiniteList.head InfiniteList.head InfiniteList.get at scb_dbf

      induction n generalizing scn with
        | zero =>
          intro f f_in
          rw [init_eq'] at f_in
          simp_all only [Option.some.injEq]
        | succ n ih =>
          have prev_cn_ex : ∃ prev_cn, scb.branch.infinite_list n = some prev_cn:= by
            have := prev_is_some_if_is_some_std scb (n + 1) (Option.NeqNoneIfIsSome (scb.branch.infinite_list (n + 1)) scn scn_eq) n (Nat.lt_add_one n)
            exact Option.ne_none_iff_exists'.mp this
          intro f f_in
          rcases prev_cn_ex with ⟨prev_cn, prev_cn_eq⟩
          specialize ih prev_cn (by grind) f f_in
          have := allFfInNextFsIfSome_std scb n prev_cn prev_cn_eq
          rw [Option.is_none_or_iff] at this
          specialize this scn scn_eq f
          have f_in_prev_fs : f ∈ prev_cn.facts.val := ih
          apply this
          constructor
          exact f_in_prev_fs
          rw [init_eq'] at f_in
          exact db_funfree f f_in


  theorem exHomFactorization (cb : CoreChaseBranch kb) (A B C : CoreChaseNode kb.rules) (n m : Nat) (gt : m > n + 1)
    (A_eq : cb.branch.infinite_list n = some A) (B_eq : cb.branch.infinite_list (n + 1) = some B) (C_eq : cb.branch.infinite_list m = some C)
    (gtm : GroundTermMapping sig) (gtm_eq : gtm.isHomomorphism A.core C.core) :
      ∃ (gtm' : GroundTermMapping sig), gtm'.isHomomorphism B.core C.core := by

      have ex_step_hom := exHomCoreAllFollowingCore cb n A A_eq 1
      rw [Option.is_none_or_iff] at ex_step_hom
      specialize ex_step_hom B B_eq
      rcases ex_step_hom with ⟨step_hom, step_hom_is_hom⟩

      have gtm_Cfs_Ccore : ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism C.fs C.core := exHomFsCore cb m C C_eq
      -- C.fs = N_i+
      -- C.core = N_final
      -- gtm_Cfs_Ccore = φ_i
      rcases gtm_Cfs_Ccore with ⟨r, r_hom⟩

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

        have t1 : ∃ (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules), trg.val.active R := by
          apply Classical.byContradiction
          intro contra
          simp at contra
          unfold FactSet.universallyModelsKb at contra2
          simp only [Classical.not_and_iff_not_or_not] at contra2
          sorry

        have t2 : ∃ (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) (s : Nat), (scb.branch.infinite_list s).is_some_and (fun scn => trg.val.active scn.facts) := by sorry
        sorry

  theorem allCoreChaseStepsHomSubsetOfAllStandardChaseSteps (scb : ChaseBranch obs kb) (n : Nat) (n_some : (scb.branch.infinite_list n).isSome) :
    (scb.branch.infinite_list n).is_some_and (fun scn => ∃ (m : Nat) (ccb : CoreChaseBranch kb), (ccb.branch.infinite_list m).is_some_and (fun ccn => ccn.core.homSubset scn.facts.val)) := by

      have ex_scn : ((scb.branch.infinite_list n).isSome = true) → ∃ (scn : ChaseNode obs kb.rules), (scb.branch.infinite_list n) = scn  := by
        intro h
        exact Option.isSome_iff_exists.mp n_some

      rcases (ex_scn n_some) with ⟨scn, scn_eq⟩
      simp only [Option.is_some_and_iff]
      exists scn
      constructor
      exact scn_eq
      sorry


  theorem finalChaseBranchNodeHomSubsetFinalCoreChaseBranchNode (scb : ChaseBranch obs kb) (ccb : CoreChaseBranch kb) (scb_n_ter ccb_n_ter : Nat) (scn : ChaseNode obs kb.rules) (ccn : CoreChaseNode kb.rules)
    (scb_term : ((scb.branch.infinite_list scb_n_ter) = some scn) ∧ (scb.branch.infinite_list (scb_n_ter + 1) = none))
    (ccb_term : ((ccb.branch.infinite_list ccb_n_ter) = some ccn) ∧ (ccb.branch.infinite_list (ccb_n_ter + 1) = none)) :
      have ccb_ter' : ccb.terminates' := by
        exists ccb_n_ter
        constructor
        <;> grind
      scb.result.homSubset (ccb.result ccb_ter') := by
        unfold ChaseBranch.result
        simp only
        sorry

  theorem allCoreChaseStepsHomSubsetOfFinalStandardChaseStep (scb : ChaseBranch obs kb) (ccb : CoreChaseBranch kb) (n_ter m : Nat)
    (ccb_m_some : (ccb.branch.infinite_list m).isSome) (last_scn : ChaseNode obs kb.rules) (scb_term : ((scb.branch.infinite_list n_ter) = some last_scn) ∧ (scb.branch.infinite_list (n_ter + 1) = none)):

      have scb_n_nter_some : (scb.branch.infinite_list n_ter).isSome = true := by
        rw [Option.isSome_iff_exists]
        exists last_scn
        exact scb_term.left

      let final_scn := (scb.branch.infinite_list n_ter).get scb_n_nter_some

      --FactSet.homSubset ((ccb.branch.infinite_list m).get (ccb_m_some)).core final_scn.facts.val := by
      ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism ((ccb.branch.infinite_list m).get (ccb_m_some)).core final_scn.facts.val := by
        have scb_n_nter_some : (scb.branch.infinite_list n_ter).isSome = true := by
          rw [Option.isSome_iff_exists]
          exists last_scn
          exact scb_term.left

        simp
        induction m with
          | zero =>
            exists id
            simp [ccb.database_first]
            have := cbDbInAllSucc_std scb ccb n_ter ((scb.branch.infinite_list n_ter).get scb_n_nter_some) ((ccb.branch.infinite_list 0).get ccb_m_some) (Option.eq_some_of_isSome ccb_m_some) (Option.eq_some_of_isSome scb_n_nter_some)
            constructor
            exact GroundTermMapping.id_is_id_on_const id rfl
            have eq := FactSet.applyFactSetIdEq kb.db.toFactSet.val
            rw [← eq]
            have eq' : kb.db.toFactSet.val =  ((ccb.branch.infinite_list 0).get ccb_m_some).fs := by
              simp [ccb.database_first]
            grind
          | succ m ih =>
            rcases (Option.isSome_iff_exists.mp ccb_m_some) with ⟨cn_m, cn_m_eq⟩
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

            sorry


    -- wenn term dann gibt es eine node in der keine trigger mehr aktiv sind
    -- jedes .fs und .core @n aus der ccb ist homsubet der sbc @n

  theorem exLastNodeWithLastIndexIfTerminatesAndNoneAfter_std (scb : ChaseBranch obs kb) (ter : scb.terminates) :
    ∃ (last_cn : ChaseNode obs kb.rules) (n_ter : Nat), ((scb.branch.infinite_list n_ter) = some last_cn ∧ (scb.branch.infinite_list (n_ter + 1) = none)) := by
      sorry

  theorem exHomFromCoreIfExHomFromFs (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : (cb.branch.infinite_list n) = some cn) (fs : FactSet sig) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism cn.fs fs) :
    ∃ (gtm' : GroundTermMapping sig), gtm'.isHomomorphism cn.core fs := by
      rcases cn.core_sse.right with ⟨gtm2, gtm2_hom⟩
      sorry

  theorem List.range'_allElementsInRange (b : Nat) (idx_l : List Nat) (idx_l_eq : (idx_l = List.range' 1 b)) : ∀ n, n ∈ idx_l → n ≥ 1 ∧ n ≤ b := by
    intro n h
    grind


  def get_used_trigger_list (scb : ChaseBranch obs kb) (n : Nat) (idx_l : List Nat) (idx_l_eq : (idx_l = List.range' 1 n)) (term : (scb.branch.infinite_list n).isSome) : (List (RTrigger obs.toLaxObsoletenessCondition kb.rules)) :=
    idx_l.pmap (fun m hm => (((scb.branch.infinite_list m).get (by
        have m_in : m ∈ idx_l := hm
        have := List.range'_allElementsInRange n idx_l idx_l_eq m m_in
        rcases this with ⟨geq, leq⟩
        subst idx_l
        have := prev_eq_is_some_if_is_some'_std scb n term m leq
        exact Option.isSome_iff_ne_none.mpr this
      )).origin.get (by
        have m_in : m ∈ idx_l := hm
        have := List.range'_allElementsInRange n idx_l idx_l_eq m m_in
        rcases this with ⟨geq, leq⟩
        subst idx_l
        have := prev_eq_is_some_if_is_some'_std scb n term m leq
        have := @ChaseBranch.origin_isSome _ _ _ _ _ _ scb (m - 1)
        unfold PossiblyInfiniteList.drop InfiniteList.drop PossiblyInfiniteList.tail PossiblyInfiniteList.head InfiniteList.head InfiniteList.get InfiniteList.tail InfiniteList.get at this
        grind
      )).fst) (by
        intro m m_in
        exact m_in
      )

  def get_origin_list (scb : ChaseBranch obs kb) (n : Nat) (idx_l : List Nat) (idx_l_eq : (idx_l = List.range' 1 n)) (term : (scb.branch.infinite_list n).isSome) :
   (List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length)) :=
      idx_l.pmap (fun m hm => (((scb.branch.infinite_list m).get (by
          have m_in : m ∈ idx_l := hm
          have := List.range'_allElementsInRange n idx_l idx_l_eq m m_in
          rcases this with ⟨geq, leq⟩
          subst idx_l
          have := prev_eq_is_some_if_is_some'_std scb n term m leq
          exact Option.isSome_iff_ne_none.mpr this
        )).origin.get (by
          have m_in : m ∈ idx_l := hm
          have := List.range'_allElementsInRange n idx_l idx_l_eq m m_in
          rcases this with ⟨geq, leq⟩
          subst idx_l
          have := prev_eq_is_some_if_is_some'_std scb n term m leq
          have := @ChaseBranch.origin_isSome _ _ _ _ _ _ scb (m - 1)
          unfold PossiblyInfiniteList.drop InfiniteList.drop PossiblyInfiniteList.tail PossiblyInfiniteList.head InfiniteList.head InfiniteList.get InfiniteList.tail InfiniteList.get at this
          grind
        ))) (by
          intro m m_in
          exact m_in
        )

  theorem exTerminatingCoreChaseBranchIfExistsTerminatingChaseBranch (scb : ChaseBranch obs kb) (scb_term: scb.terminates) : (∃ (ccb : CoreChaseBranch kb), ccb.terminates) := by

    rcases scb_term with ⟨n_ter, n⟩
    let used_trigger_list : List (RTrigger obs.toLaxObsoletenessCondition kb.rules) := get_used_trigger_list scb n_ter (List.range' 1 (n_ter+1)) rfl (by sorry) -- some at n_ter
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


  noncomputable def buildCoreChaseBranchFromChaseBranch_rec (trg_list :  List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length)) (new_ccb_branch : List (CoreChaseNode kb.rules)) : List (CoreChaseNode kb.rules) :=
    match c : trg_list with
      -- there are no more triggers left to build into the new ccb
      -- wir müssen den ganzen origin mitnehmen
      | .nil => new_ccb_branch
      | .cons hd tl =>

        let trg := hd.fst
        let fin_i := hd.snd

        -- we need this to show new_ccb.isSome at n
        let prev_ccn : CoreChaseNode kb.rules := new_ccb_branch.getLast (sorry) -- can be added as hyp

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
              exact all_core_finite prev_ccn
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
              origin := some
                {
                  fst := trg
                  snd := fin_i
                }
              fs_contains_origin_result := by
                intro f f_in
                subst new_fs trg_result
                right
                exact f_in
            }

            let new_ccb_branch : List (CoreChaseNode kb.rules) := (new_ccb_branch.append [next_ccn])

            buildCoreChaseBranchFromChaseBranch_rec tl new_ccb_branch

          | Decidable.isFalse _ =>
            buildCoreChaseBranchFromChaseBranch_rec tl new_ccb_branch



  @[grind]
  theorem get_origin_list_length_eq_term_n_scb (scb : ChaseBranch obs kb) (n : Nat) (term_at_n : (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone)
    (origin_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length)) (origin_list_eq : origin_list = get_origin_list scb n (List.range' 1 n) rfl term_at_n.left) :
      origin_list.length = n := by
        unfold get_origin_list at origin_list_eq
        simp_all

  @[grind]
  theorem get_origin_list_length_eq_active_trigger_in_each_step (scb : ChaseBranch obs kb) (n m : Nat) (term_at_n : (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone)
    (origin_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length)) (lt : m < origin_list.length) (origin_list_eq : origin_list = get_origin_list scb n (List.range' 1 n) rfl term_at_n.left) :
      ∃ (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules), trg.val.active ((scb.branch.infinite_list m).get (by
      have len_eq : origin_list.length = n := get_origin_list_length_eq_term_n_scb scb n term_at_n origin_list origin_list_eq
      rw [len_eq] at lt
      have := prev_eq_is_some_if_is_some'_std scb n term_at_n.left m (by exact Nat.le_of_succ_le lt)
      exact Option.isSome_iff_ne_none.mpr this
      )).facts := by
        have len_eq : origin_list.length = n := get_origin_list_length_eq_term_n_scb scb n term_at_n origin_list origin_list_eq
        rw [len_eq] at lt
        let cm : ChaseNode obs kb.rules := ((scb.branch.infinite_list (m+1)).get (by
          by_cases c : (m + 1 = n)
          rw [c]
          exact term_at_n.left
          have c : m + 1 < n := by exact Nat.lt_of_le_of_ne lt c
          have := prev_eq_is_some_if_is_some'_std scb n term_at_n.left (m+1) lt
          exact Option.isSome_iff_ne_none.mpr this
          ))
        have := ChaseBranch.origin_trg_is_active scb (m) cm (by
          subst cm
          unfold PossiblyInfiniteList.drop InfiniteList.drop PossiblyInfiniteList.tail PossiblyInfiniteList.head InfiniteList.head InfiniteList.get InfiniteList.tail InfiniteList.get
          simp only [Nat.succ_eq_add_one, Nat.zero_add, Option.some_get]
          )
        exists (cm.origin.get (by grind)).fst

  @[grind]
  theorem active_trigger_yields_next_chase_node_std (scb : ChaseBranch obs kb) (scn : ChaseNode obs kb.rules) (n : Nat) (scn_eq : scb.branch.infinite_list n = some scn) (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) (trg_act : trg.val.active scn.facts) :
    ∃ (scn_succ : ChaseNode obs kb.rules), scb.branch.infinite_list (n+1) = some scn_succ := by
      have trg_ex := scb.triggers_exist n
      rw [Option.is_none_or_iff] at trg_ex
      specialize trg_ex scn scn_eq
      simp at trg_ex
      rcases trg_ex with trg_ex | trg_nex
      rcases trg_ex with ⟨trg', trg'_act, i, h⟩
      exact
        Exists.intro
          {
            facts := ⟨scn.facts.val ∪ trg'.val.mapped_head[↑i].toSet,
            exists_trigger_opt_fs._proof_3 obs kb.rules scn trg' i⟩,
            origin := some ⟨trg', i⟩,
            facts_contain_origin_result := exists_trigger_opt_fs._proof_5 obs kb.rules scn trg' i
            } (id (Eq.symm h))
      rcases trg_nex with ⟨lhs, rhs⟩
      simp at lhs
      specialize lhs trg
      contradiction

  @[grind]
  theorem no_active_triggers_in_scb_if_empty_get_origin_list_empty (scb : ChaseBranch obs kb) (n : Nat) (term_at_n : (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone) :
    get_origin_list scb n (List.range' 1 n) rfl term_at_n.left = [] → ¬ ∃ (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules), trg.val.active ((scb.branch.infinite_list 0).get (by
      by_cases c : n = 0
      subst c
      exact term_at_n.left
      have gt : n > 0 := Nat.zero_lt_of_ne_zero c
      exact prev_is_some_if_is_some'_std scb n term_at_n.left 0 gt
    )).facts := by
      intro h
      apply Classical.byContradiction
      intro contra
      simp only [not_exists, Classical.not_forall, Classical.not_not] at contra
      rcases contra with ⟨trg, trg_loaded, trg_non_obs⟩
      unfold get_origin_list at h
      -- if we have an active trigger then we have a next node whose origin should be in the list but the list is empty thus we get a contradiction
      let init_scn := (scb.branch.infinite_list 0).get (by
        by_cases c : n = 0
        subst c
        exact term_at_n.left
        have gt : n > 0 := Nat.zero_lt_of_ne_zero c
        exact prev_is_some_if_is_some'_std scb n term_at_n.left 0 gt)
      have : ∃ (scn : ChaseNode obs kb.rules), (scb.branch.infinite_list 1) = some scn := by
        exact active_trigger_yields_next_chase_node_std scb init_scn 0 (by grind) trg ⟨trg_loaded, trg_non_obs⟩

      rcases this with ⟨scn, scn_eq⟩
      have : get_origin_list scb n (List.range' 1 n) rfl term_at_n.left ≠ [] := by
        unfold get_origin_list List.pmap
        split
        next => grind
        next => grind
      contradiction


  -- wo ist der unterschied wenn ich anstelle von  (no_act_trg : ∀ (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules), ¬ trg.val.active scn.facts) als hyp
  -- statdessen (trg : (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules)) und (not_active : ¬ trg.val.active scn.facts) nehme ?
  @[grind]
  theorem no_succ_chase_node_if_not_exists_active_trigger (scb : ChaseBranch obs kb) (scn : ChaseNode obs kb.rules) (n m : Nat) (gt : m > n) (scn_eq : scb.branch.infinite_list n = some scn)
    (no_act_trg : ∀ (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules), ¬ trg.val.active scn.facts) : (scb.branch.infinite_list m).isNone := by
      apply Classical.byContradiction
      intro contra
      simp only [Option.isNone_iff_eq_none, ne_eq, ← Option.isSome_iff_ne_none] at contra
      have ex_cn_succ : ∃ (cn_succ : ChaseNode obs kb.rules), scb.branch.infinite_list (n+1) = some cn_succ := by
        have := prev_eq_is_some_if_is_some'_std scb m contra (n + 1) gt
        exact Option.ne_none_iff_exists'.mp this
      rcases ex_cn_succ with ⟨cn_succ, cn_succ_eq⟩
      have trg_ex := scb.triggers_exist n
      rw [Option.is_none_or_iff] at trg_ex
      unfold PossiblyInfiniteList.drop InfiniteList.drop PossiblyInfiniteList.tail PossiblyInfiniteList.head InfiniteList.head InfiniteList.get InfiniteList.tail InfiniteList.get at trg_ex
      simp only [Nat.succ_eq_add_one, Nat.zero_add] at trg_ex
      specialize trg_ex scn scn_eq
      rcases trg_ex with trg_ex | trg_nex
      rcases trg_ex with ⟨trg', trg'_act, ⟨i, h⟩⟩
      specialize no_act_trg trg'
      contradiction
      rcases trg_nex with ⟨lhs, rhs⟩
      simp only [not_exists] at lhs
      let trg := (cn_succ.origin.get (ChaseBranch.origin_isSome scb n cn_succ_eq)).fst
      specialize lhs trg
      grind


  theorem buildCoreChaseBranchFromChaseBranch_rec_non_empty_if_new_ccb_non_empty (origin_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length)) (a : CoreChaseNode kb.rules) :
  (buildCoreChaseBranchFromChaseBranch_rec origin_list [a]) ≠ [] := by
    sorry

  theorem buildCoreChaseBranchFromChaseBranch_rec_appendsList (origin_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length))
    (l tl : List (CoreChaseNode kb.rules)) :
      (buildCoreChaseBranchFromChaseBranch_rec origin_list l) = l ++ tl := sorry

  theorem buildCoreChaseBranchFromChaseBranch_rec_head_eq (origin_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length))
    (hd : CoreChaseNode kb.rules) (tl : List (CoreChaseNode kb.rules)) :
      (buildCoreChaseBranchFromChaseBranch_rec origin_list (hd :: tl)).head sorry = hd := by sorry

  theorem buildCoreChaseBranchFromChaseBranch_rec_head_eq' (origin_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length))
    (l : List (CoreChaseNode kb.rules)) (l_non_empty : l ≠ []) (origin_list_non_empty : origin_list ≠ []):
      (buildCoreChaseBranchFromChaseBranch_rec origin_list l).head sorry = l.head l_non_empty := by
        unfold buildCoreChaseBranchFromChaseBranch_rec
        sorry



  theorem buildCoreChaseBranchFromChaseBranch_rec_len_eq (origin_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length)) (node_list : List (CoreChaseNode kb.rules)) :
    (buildCoreChaseBranchFromChaseBranch_rec origin_list node_list).length ≥ node_list.length := by
      unfold buildCoreChaseBranchFromChaseBranch_rec
      cases c1 : origin_list with
        | nil => simp
        | cons hd tl =>
          sorry

  --set_option pp.proofs true
  set_option pp.rawOnError true
  theorem buildCoreChaseBranchFromChaseBranch_rec_head' (origin_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length))
    (hd : CoreChaseNode kb.rules) (tl : List (CoreChaseNode kb.rules)) :
      (buildCoreChaseBranchFromChaseBranch_rec origin_list (hd :: tl))[0]? = some hd := by

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


  theorem buildCoreChaseBranchFromChaseBranch_rec_first_eq (l : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length)) (a : CoreChaseNode kb.rules) :
    (PossiblyInfiniteList.from_list (buildCoreChaseBranchFromChaseBranch_rec l [a])).infinite_list 0 = some a := by
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
  theorem buildCoreChaseBranchFromChaseBranch_rec_get_n (origin_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length)) (node_list : List (CoreChaseNode kb.rules)) (n : Nat) (n_fin : n < node_list.length):
  (buildCoreChaseBranchFromChaseBranch_rec origin_list node_list)[n]? = node_list.get ⟨n, n_fin⟩ := by
    unfold buildCoreChaseBranchFromChaseBranch_rec
    simp only [Fin.getElem_fin, List.append_eq]
    induction node_list with
      | nil =>
        grind
      | cons hd tl ih =>
        cases c : origin_list with
        | nil =>
          simp
        | cons hd_o tl_o =>
          simp
          cases c2 : Classical.propDecidable (hd_o.fst.val.active ((hd :: tl).getLast (List.cons_ne_nil hd tl)).core) with
            | isTrue t =>
              simp
              split at ih
              next => grind
              next hd' tl' =>
                ·-- have := buildCoreChaseBranchFromChaseBranch_rec_get_n tl_o _ n n_fin
                sorry


            | isFalse f =>
              sorry


  theorem ex_active_trigger_in_core_chase_step_leq_standard_chase_step (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) (scb : ChaseBranch obs kb) (ccb_branch : PossiblyInfiniteList (CoreChaseNode kb.rules)) (n_sc : Nat)
    (scn : ChaseNode obs kb.rules) (scn_eq : scb.branch.infinite_list n_sc = some scn) (trg_act_scn : trg.val.active scn.facts) :
      ∃ (n_cc : Nat), (n_sc ≥ n_cc) ∧ (ccb_branch.infinite_list n_cc).is_some_and  (fun ccn => trg.val.active ccn.core) := by sorry


  theorem xyz (scb : ChaseBranch obs kb) (ccn : CoreChaseNode kb.rules) (init_ccn : CoreChaseNode kb.rules) (n scb_term_n : Nat) (some_at : (scb.branch.infinite_list scb_term_n).isSome = true)
    (scb_trg_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length))
    (scb_trg_list_eq : scb_trg_list = (get_origin_list scb scb_term_n (List.range' 1 scb_term_n) rfl some_at))
    (ccn_eq : (PossiblyInfiniteList.from_list (buildCoreChaseBranchFromChaseBranch_rec (get_origin_list scb scb_term_n (List.range' 1 scb_term_n) rfl some_at) [init_ccn])).infinite_list n = some ccn) :
      ∃ (k : Fin scb_trg_list.length), n ≤ k ∧ (scb_trg_list.get k).fst.val.active ccn.core := sorry

  theorem get_origin_list_length_eq_scb_term_n (scb : ChaseBranch obs kb) (n : Nat) (some_at : (scb.branch.infinite_list n).isSome) :
    (get_origin_list scb n (List.range' 1 n) rfl some_at).length = n + 1 := by sorry

  theorem uvw (scb : ChaseBranch obs kb) (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) (init_ccn : CoreChaseNode kb.rules)
    (k scb_term_n : Nat) (some_at : (scb.branch.infinite_list scb_term_n).isSome = true) (lt : k ≤ scb_term_n)
    (scb_trg_list : List ((trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) × Fin trg.val.mapped_head.length))
    (scb_trg_list_eq : scb_trg_list = (get_origin_list scb scb_term_n (List.range' 1 scb_term_n) rfl some_at))
    (trg_eq : trg = (scb_trg_list.get ⟨k, by
      have := get_origin_list_length_eq_scb_term_n scb scb_term_n some_at
      grind
      ⟩).fst) :
      (∃ (m : Nat), m ≤ k ∧ trg.val.active (((PossiblyInfiniteList.from_list (buildCoreChaseBranchFromChaseBranch_rec (get_origin_list scb scb_term_n (List.range' 1 scb_term_n) rfl some_at) [init_ccn])).infinite_list m).get sorry).core) ∨
        (∀ (m : Nat), m > k ∧ ¬ trg.val.active (((PossiblyInfiniteList.from_list (buildCoreChaseBranchFromChaseBranch_rec (get_origin_list scb scb_term_n (List.range' 1 scb_term_n) rfl some_at) [init_ccn])).infinite_list m).get sorry).core) := sorry


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
      is_core := by exact eachKbDbIsWeakCore kb
      core_sse := by
        constructor
        exact fun _ a => a
        exists id
        apply FactSet.id_is_hom
      origin := none,
      fs_contains_origin_result := by simp [Option.is_none_or]
    }

    have : ∃ (n : Nat), (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone := by
      rw [scb.terminating_has_last_index] at scb_term
      rcases scb_term with ⟨n_ter, n_ter_some, gt_none⟩
      exists n_ter
      specialize gt_none (n_ter + 1)
      rw [PossiblyInfiniteList.get?, InfiniteList.get] at n_ter_some gt_none
      specialize gt_none (Nat.lt_add_one n_ter)
      exact ⟨n_ter_some, (Option.isNone_iff_eq_none.mpr gt_none)⟩


    let scb_term_n := Classical.choose this
    let scb_term_h := Classical.choose_spec this

    let scb_trg_list := get_origin_list scb scb_term_n (List.range' 1 scb_term_n) rfl scb_term_h.left

    let new_ccb_branch := PossiblyInfiniteList.from_list (buildCoreChaseBranchFromChaseBranch_rec scb_trg_list [init_ccn])

    let new_ccb : CoreChaseBranch kb :=
    {
      branch := new_ccb_branch
      database_first := buildCoreChaseBranchFromChaseBranch_rec_first_eq scb_trg_list init_ccn
      triggers_exist := by

        /-
          ∀ (n : Nat), CC.ex_trg(n) ∨ CC.not_ex_trg(n)
          → intro n
          Each trigger in the SC is in the origin list, trg in position n in origin list was active at position n-1 in the sc
          Each trigger (lets say at postion p1) in the SC is either active in the CC at some postion (p2 ≤ p1) or never
          → Thus if we intro n (which is a position p in the CC) we only have to look at all triggers in the SC with postions p ≤ n

          Maybe use induction:

          for n = 0 clearly if the SC had an active trigger then only p2 ≤ p1 with p1 = 0 thus p2 = 0 thus the first element in the origin list (pos 0) must be used in the CC

          We want to show that for each n there either is a exists a trigger or not

          For this we have:
            - A CoreChaseNode at n

          For each Trigger trg at some position k in the scb_trigger_list we know that trg either
            a) was active in some step m ≤ k in the CoreChaseBranch
            b) not active at all in the CoreChaseBranch

          If there exists a trigger on n then:
            → We know by the way the CCB is constructed that this trigger mustve also occured active in the SCB at some point k
              → Thus at some position k there is an acitve trigger for cn.core in the scb_trigger_list


          -- jeder trigger in der scb_trigger_list ist entweder vor oder an der stelle k in der konstruierten CCB active oder nie active

          theorem uvw (trg : RTrigger _) (k : Nat) (trg_ex : trg = scb_trigger_list.get k)
            (∃ (m : Nat), m ≤ k ∧ trg.active cn@m) ∨ (∀ m, m > k ∧ ¬ trg.active cn@m)

          SC : 0 → 1 → ... → k → ... → n → (n+1)=none (maybe k = n)
          CC : 0 → 1 →
        -/

        --Each trigger (lets say at postion p1) in the SC is either active in the CC at some postion (p2 ≤ p1) or never
        -- as we will do an induction over n (which is the ccb index) we always can find such an index
        have trg_from_scb_active_at_some_leq_in_ccb (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) (p1 : Nat) :
          (((scb.branch.infinite_list p1).is_some_and (fun scn => trg.val.active scn.facts)) →
            (∃ (p2 : Nat), (p2 ≤ p1) ∧ (new_ccb_branch.infinite_list p2).is_some_and (fun ccn => trg.val.active ccn.core))) := by sorry


        have trg_from_ccb_activeαt_some_geq_in_scb (trg : RTrigger obs.toLaxObsoletenessCondition kb.rules) (p1 : Nat) :
          (((new_ccb_branch.infinite_list p1).is_some_and (fun ccn => trg.val.active ccn.core)) →
            (∃ (p2 : Nat), (p2 ≥ p1) ∧ (scb.branch.infinite_list p2).is_some_and (fun scn => trg.val.active scn.facts))) := by sorry

        intro n
        rw [Option.is_none_or_iff]
        intro cn cn_eq
        simp

        induction n generalizing cn with
          | zero =>
            have scb_trg_ex := scb.triggers_exist 0
            rw [Option.is_none_or_iff] at scb_trg_ex
            specialize scb_trg_ex
            have ex_init_scn : ∃ (init_scn : ChaseNode obs kb.rules), scb.branch.infinite_list 0 = init_scn :=
              Exists.intro {facts := have fs := kb.db.toFactSet; ⟨fs.val, fs.property.left⟩, origin := none, facts_contain_origin_result := True.intro } dbf
            rcases ex_init_scn with ⟨init_scn, init_scn_eq⟩
            specialize scb_trg_ex init_scn init_scn_eq

            -- does an active trigger ex at pos 0 in the scb ?

            -- zwei Falluntershceidung4n, gibt es den trigger aktiv in der SC und gibt es den trigger aktiv in der CC
            -- in beiden fällen falls ja, nehmen wir uns den index heraus wo der trigger vorkommt, exact dieser trigger ist dann jender der an der stelle n existiert
            -- in den beiden nein fällen muss man zeigen das die origin_list kleiner wird und dann termt der gen algo für CC auf leerer origin list und fügt nichts mehr in die infinite list ein thus alles none danach
            -- was ist mit ja nein fällen ?
            -- für jeden schritt n in der cc gibt es by contstuction einen schritt n+k in der sc welcher den gleichen trigger benutzt

            cases scb_trg_ex with
              | inl trg_ex =>
                rcases trg_ex with ⟨trg, trg_act, i, eq1⟩
                have ex_ccn_with_scb_trg_at_leq_index := trg_from_scb_active_at_some_leq_in_ccb trg 0
                rw [Option.is_some_and_iff] at ex_ccn_with_scb_trg_at_leq_index
                have init_some : (∃ a, scb.branch.infinite_list 0 = some a ∧ trg.val.active a.facts.val) := by grind
                -- does a core chase node exists at p2 ≤ 0 where the scb trg is used or is the scb trg never used ?
                  -- active trigger in scb at p1=0 and ex core chase node at p2≤p1=0 where scb trg is used
                specialize ex_ccn_with_scb_trg_at_leq_index init_some
                rcases ex_ccn_with_scb_trg_at_leq_index with ⟨p2, lt, h⟩
                rw [Option.is_some_and_iff] at h
                rcases h with ⟨ccn_with_scb_trg, ccn_with_scb_trg_eq, trg_act_in_ccn_with_scb_trg⟩
                -- ex trigger side
                left
                exists trg
                constructor
                grind
                have fin' : (init_scn.facts.val ∪ trg.val.mapped_head[↑i].toSet).finite := by grind
                rcases fin' with ⟨l, l_nd, l_eq⟩
                have ex_wc := FactSet.exists_weak_core_for_finite_set l.length l rfl
                rcases ex_wc with ⟨wc, wc_core, wc_homsub⟩
                exists wc, i
                rw [Option.is_some_and_iff]

                let ccn_one : CoreChaseNode kb.rules := {
                  fs := (init_scn.facts.val ∪ trg.val.mapped_head[↑i].toSet)
                  fs_fin := by grind
                  core := wc
                  is_core := wc_core
                  core_sse := by
                    have eq : l.toSet = (init_scn.facts.val ∪ trg.val.mapped_head[i].toSet) := Set.ext l.toSet (init_scn.facts.val ∪ trg.val.mapped_head[i].toSet) l_eq
                    rw [eq] at wc_homsub
                    exact wc_homsub
                  origin := some ⟨trg, i⟩
                  fs_contains_origin_result := by grind
                }
                exists ccn_one

                have eq' : init_scn.facts.val = cn.core := by
                  have t1 : init_scn.facts.val = kb.db.toFactSet := by grind
                  have t2 : cn.core = kb.db.toFactSet := by sorry
                  grind

                constructor
                subst new_ccb_branch
                unfold buildCoreChaseBranchFromChaseBranch_rec

                have : ∃ tl, scb_trg_list = ⟨trg, i⟩ :: tl := by sorry
                rcases this with ⟨scb_trg_list_tl, scb_trg_list_eq⟩
                rw [scb_trg_list_eq]
                have : trg.val.active init_ccn.core := by grind
                unfold PossiblyInfiniteList.from_list
                simp only [List.getLast_singleton, Fin.getElem_fin, List.append_eq, List.cons_append, List.nil_append, Nat.zero_add]
                cases (Classical.propDecidable (trg.val.active init_ccn.core)) with
                  | isTrue =>
                    subst ccn_one
                    simp
                    constructor
                    grind
                    sorry -- use classical choose on ... then this is resolved by rfl
                  | isFalse =>
                    contradiction
                subst ccn_one
                simp

                exact congrFun (congrArg Union.union eq') trg.val.mapped_head[↑i].toSet

              | inr trg_nex =>
                -- if there is no active trigger on scb at p1=0 then origin list will be empty thus no successor node in ccb can be created
                rcases trg_nex with ⟨trg_nex, is_none⟩
                have scb_trg_list_empty : scb_trg_list = [] := by sorry
                right
                constructor
                have eq' : init_scn.facts.val = cn.core := by sorry --both SC and CC are indentical with the core of
                rw [eq'] at trg_nex
                exact trg_nex
                unfold PossiblyInfiniteList.drop InfiniteList.drop PossiblyInfiniteList.tail PossiblyInfiniteList.head InfiniteList.head InfiniteList.get InfiniteList.tail InfiniteList.get at is_none
                simp only [Nat.succ_eq_add_one, Nat.zero_add] at is_none
                subst new_ccb_branch
                rw [scb_trg_list_empty]
                unfold buildCoreChaseBranchFromChaseBranch_rec
                simp only [Nat.zero_add]
                unfold PossiblyInfiniteList.from_list
                simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_irrefl, not_false_eq_true, getElem?_neg]

          | succ n ih =>
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


        /-

        have := xyz scb cn init_ccn n scb_term_n scb_term_h.left scb_trg_list rfl cn_eq
        rcases this with ⟨k, lt, trg_act_k⟩


        -- as the scb list has each trigger from SC in order we can just get the index where the trigger/origin is equal to the one we are searching, so no offset calculation is needed
        -- as the trigger was used in (buildCoreChaseBranchFromChaseBranch_rec scb_trg_list [init_ccn]) we know that it must've been active


        have scb_trg_ex_k := scb.triggers_exist (k) --> = (scb_trg_list.get k).fst
        rw [Option.is_none_or_iff] at scb_trg_ex_k
        -- cnk used the k-th trigger from the origin list
        have ex_cnk : ∃ (cnk : ChaseNode obs kb.rules), scb.branch.infinite_list k = some cnk := sorry
        rcases ex_cnk with ⟨cnk, cnk_eq⟩
        specialize scb_trg_ex_k cnk cnk_eq -- (n-k) needs to be some


        cases scb_trg_ex_k with
          | inl scb_trg_ex_k =>
            left
            rcases scb_trg_ex_k with ⟨scb_trg_k, scb_trg_k_act, scb_trg_k_h⟩
            exists (scb_trg_list.get k).fst
            constructor
            -- this prob comes from proof that this n+k thing even exists
            exact trg_act_k

            sorry
          | inr trx_nex =>
            sorry

        /-

        subst new_ccb_branch
        unfold buildCoreChaseBranchFromChaseBranch_rec PossiblyInfiniteList.from_list
        cases c : scb_trg_list with
          | nil =>
            simp
            right
            unfold not_exists_trigger_opt_fs_core
            constructor
            rw [c] at cn_eq
            unfold buildCoreChaseBranchFromChaseBranch_rec at cn_eq
            have eq : n = 0 := by
              apply Classical.byContradiction
              intro contra
              have gt : n > 0 := Nat.zero_lt_of_ne_zero contra
              induction n with
                | zero => contradiction
                | succ n ih =>
                  unfold PossiblyInfiniteList.from_list at cn_eq
                  simp_all
            subst eq
            have eq : init_ccn = cn := by
              unfold PossiblyInfiniteList.from_list at cn_eq
              simp at cn_eq
              exact cn_eq
            subst eq
            have eq : init_ccn.core = kb.db.toFactSet := rfl
            rw [eq]
            have := no_active_triggers_in_scb_if_empty_get_origin_list_empty scb scb_term_n scb_term_h c
            simp_all
            rfl

          | cons hd tl =>
            simp

            /-
              we are in the nth step of the core chase with a non empty trigger list from scb
              cn is the n-th build corechasenode from the trigger list
              → cn being a position n here does not neccessarily mean that in the scb there were also used n triggers but there are used n+k triggeres where k is the nuber of triggers skipped

              -----

              das k muss der offset sein an dem der trigger den wir zum bauen des n-ten schritts des ccb's benutzen im scb vorkommt

              SC : 0 → t0 → 1 → t1 → 2 → t2 → 3 → t3 → 4 → t4 → 5

              CC : 0 → t0 → 1 →       {+k}      → t3 → 2' → t4 → 3'

              hier k = 2 bei 2' also der trigger der im 2-ten schritt benutzt um die CC zu bauen, ist in der SC der 4-te

              scb_trigger_list = t0, t1, t2, t3, t4

            -/

            cases Classical.propDecidable (hd.fst.val.active init_ccn.core) with
              | isTrue t =>
                left
                simp_all
                -- is this the correct trigger we fetch here ?
                --have ex_trg := ex_active_trigger_in_core_chase_step_leq_standard_chase_step hd.fst scb (PossiblyInfiniteList.from_list (buildCoreChaseBranchFromChaseBranch_rec scb_trg_list [init_ccn])) n sorry sorry sorry
                --rcases ex_trg with ⟨n_cc, gt, h2⟩




                sorry
              | isFalse f =>
                right
                unfold not_exists_trigger_opt_fs_core
                simp
                constructor
                intro trg
                sorry
                sorry
        -/-/
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
    grind

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
      unfold ChaseBranch.terminates PossiblyInfiniteList.finite PossiblyInfiniteList.get? at inf_scb
      simp only [not_exists, ne_eq] at inf_scb
      specialize inf_scb n
      contradiction


    -- 4.
    -- R = A_ω
    let R := scb.result

    have R_umod : R.universallyModelsKb kb := deterministicChaseBranchResultUniversallyModelsKb scb kb_det

    -- 5.
    have hom_U_R : ∃ (h : GroundTermMapping sig), h.isHomomorphism U R := by
      rcases U_umod with ⟨U_umod_l, U_umod_r⟩
      specialize U_umod_r R (ChaseBranch.result_models_kb scb)
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
    have f_first_somewhere : ∀ (f : Fact sig), f ∈ R → ∃ (n_min : Nat), f ∈ ((scb.branch.infinite_list (n_min)).get (scb_all_some (n_min))).facts.val ∧
      ∀ (m : Nat), m < n_min → ¬ f ∈ ((scb.branch.infinite_list (m)).get (scb_all_some (m))).facts.val := by

        intro f f_in_R
        simp only [R] at f_in_R
        unfold ChaseBranch.result at f_in_R
        simp only [Option.is_some_and_iff] at f_in_R
        rcases f_in_R with ⟨n, ⟨cn, cn_eq, f_in⟩⟩
        unfold PossiblyInfiniteList.get? at cn_eq
        let Ix := fun (n : Nat) => f ∈ ((scb.branch.infinite_list n).get (scb_all_some n)).facts.val
        have Ix_non_empty : ∃ (n : Nat), Ix n := by
          simp only [Ix]
          exists n
          have eq : ((scb.branch.infinite_list n).get (scb_all_some n)) = cn := Option.get_of_eq_some (scb_all_some n) cn_eq
          rw [eq]
          exact f_in

        -- well ordering principle
        have hmin := wop Ix Ix_non_empty
        rcases hmin with ⟨n_min, h1, h2⟩
        have t1 : f ∈ ((scb.branch.infinite_list n_min).get (scb_all_some n_min)).facts.val := h1
        have t2 : ∀ n, f ∈ ((scb.branch.infinite_list n).get (scb_all_some n)).facts.val → n_min ≤ n := h2

        have nin_before : ∀ (n : Nat), n < n_min → ¬ f ∈ ((scb.branch.infinite_list (n)).get (scb_all_some (n))).facts.val := by
          intro n lt contra
          have := h2 n contra
          grind

        exists n_min

    -- 8.
    have monotonicity : ∀ (n : Nat), ((scb.branch.infinite_list (n)).get (scb_all_some (n))).facts.val ⊆ ((scb.branch.infinite_list (n+1)).get (scb_all_some (n+1))).facts.val := by
      intro n f f_in
      have ex_scn : ∃ (scn : ChaseNode obs kb.rules), scb.branch.infinite_list n = some scn := Option.isSome_iff_exists.mp (scb_all_some n)
      have ex_scn_succ : ∃ (scn : ChaseNode obs kb.rules), scb.branch.infinite_list (n + 1) = some scn := Option.isSome_iff_exists.mp (scb_all_some (n + 1))
      rcases ex_scn with ⟨scn, scn_eq⟩
      rcases ex_scn_succ with ⟨scn_succ, scn_succ_eq⟩
      have subsetAllFollowing := ChaseBranch.stepIsSubsetOfAllFollowing scb n scn scn_eq 1
      rw [Option.is_none_or_iff] at subsetAllFollowing
      specialize subsetAllFollowing scn_succ scn_succ_eq
      have : ((scb.branch.infinite_list n).get (scb_all_some n)) = scn := Option.get_of_eq_some (scb_all_some n) scn_eq
      rw [← this] at subsetAllFollowing
      specialize subsetAllFollowing f f_in
      grind

    have ex_hom_U_An : ∃ (n : Nat) (gtm : GroundTermMapping sig), gtm.isHomomorphism U ((scb.branch.infinite_list n).get (scb_all_some n)).facts.val := by

      --1
      rcases hom_U_R with ⟨gtm_U_R, gtm_U_R_hom⟩

      --2
      have t1 : ∀ (f : Fact sig), f ∈ U → (gtm_U_R.applyFact f) ∈ R := by sorry

      have t2 : ∀ (f : Fact sig), f ∈ U → ∃ (n : Nat), (gtm_U_R.applyFact f) ∈ ((scb.branch.infinite_list n).get (scb_all_some n)).facts.val := by sorry
      sorry


    -- 9.
    rcases ex_hom_U_An with ⟨n_max, ⟨gtm_U_An, gtm_U_An_hom⟩⟩

    let An := ((scb.branch.infinite_list n_max).get (scb_all_some n_max)).facts.val

    have ex_hom_An_U : ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism An U := by

      have sub : An ⊆ R := by
        have := ChaseBranch.stepIsSubsetOfResult scb n_max
        rw [Option.is_none_or_iff] at this
        exact this ((scb.branch.infinite_list n_max).get (scb_all_some n_max)) (Option.eq_some_of_isSome (scb_all_some n_max))

      have ex_gtm_An_R := GroundTermMapping.exHomSubToSet An R sub
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
      ∃ (c : FactSet sig), c.isWeakCore ∧ c.homSubset scn.facts.val := by
        rcases (scn.facts.property) with ⟨scn_fsl, scn_fsl_nodup, scn_fsl_eq⟩
        have ex_wc_sub := FactSet.exists_weak_core_for_finite_set scn_fsl.length scn_fsl rfl
        rcases ex_wc_sub with ⟨c, wc, sub, ⟨gtm, gtm_hom⟩⟩
        exists c
        constructor
        exact wc
        have eq : scn_fsl.toSet = scn.facts.val := Set.ext scn_fsl.toSet scn.facts.val scn_fsl_eq
        rw [← eq]
        exact ⟨sub, Exists.intro gtm gtm_hom⟩


    -- nehme den core den man aus der stelle n im scn berechnet hat
    rcases (ex_core_of_scn_step scb n_max ((scb.branch.infinite_list n_max).get (scb_all_some n_max)) (Option.eq_some_of_isSome (scb_all_some n_max))) with ⟨An_core, An_core_wc, An_core_homsub⟩

    -- es gibt eine stelle im ccb wo der core gleich (nur isomorph ?) zum scn_core (aus der zeile drüber) ist
    have : ∃ (n : Nat), ((ccb.branch.infinite_list n).get sorry).core = An_core := by sorry

    -- variante mit iso, ist iso def correct ?
    have scn_core_iso_some_ccb_core : ∃ (n : Nat) (iso : GroundTermMapping sig), iso.isIsomorphism An_core ((ccb.branch.infinite_list n).get sorry).core := by sorry


    -- 12.

    have ex_U_core : ∃ (c : FactSet sig), c.isWeakCore ∧ c.homSubset U := by
      rcases U_fin with ⟨Ul, Ul_nodup, Ul_eq⟩
      have ex_wc_sub := FactSet.exists_weak_core_for_finite_set Ul.length Ul rfl
      rcases ex_wc_sub with ⟨c, wc, sub, ⟨gtm, gtm_hom⟩⟩
      exists c
      constructor
      exact wc
      have eq : Ul.toSet = U := Set.ext Ul.toSet U Ul_eq
      rw [← eq]
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
