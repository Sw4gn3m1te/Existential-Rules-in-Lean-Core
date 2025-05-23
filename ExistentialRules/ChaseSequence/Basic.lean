import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic

import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.RTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

structure ChaseNode (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  fact : { fs : FactSet sig // fs.finite }
  -- the origin is none only for the database
  origin : Option ((trg : RTrigger (obs : LaxObsoletenessCondition sig) rules) × Fin trg.val.mapped_head.length)
  fact_contains_origin_result : origin.is_none_or (fun origin => origin.fst.val.mapped_head[origin.snd.val].toSet ⊆ fact)

def ChaseNode.origin_result {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) (isSome : node.origin.isSome) :
    List (Fact sig) :=
  let origin := node.origin.get isSome
  origin.fst.val.mapped_head[origin.snd.val]

def exists_trigger_opt_fs (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger (obs : LaxObsoletenessCondition sig) rules), trg.val.active before.fact ∧ ∃ i, some {
    fact := ⟨
      before.fact ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet,
      by
        rcases before.fact.property with ⟨l_before, _, l_eq⟩
        let new_list := (l_before ++ trg.val.mapped_head[i.val]).eraseDupsKeepRight
        exists new_list
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro e
          unfold new_list
          rw [List.mem_eraseDupsKeepRight, List.mem_append]
          unfold Set.union
          rw [l_eq]
          simp only [List.mem_toSet]
          simp [Set.element]
    ⟩
    origin := some ⟨trg, i⟩
    fact_contains_origin_result := by simp [Option.is_none_or]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
  } = after

def exists_trigger_list_condition (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) (trg : RTrigger obs rules) : Prop :=
  trg.val.active before.fact ∧ trg.val.mapped_head.zipIdx_with_lt.attach.map (fun ⟨⟨head, i⟩, h⟩ => {
    fact := ⟨
      before.fact ∪ head.toSet,
      by
        rw [List.mk_mem_zipIdx_with_lt_iff_getElem] at h
        rcases before.fact.property with ⟨l_before, _, l_eq⟩
        let new_list := (l_before ++ trg.val.mapped_head[i.val]).eraseDupsKeepRight
        exists new_list
        constructor
        . apply List.nodup_eraseDupsKeepRight
        . intro e
          unfold new_list
          rw [List.mem_eraseDupsKeepRight, List.mem_append]
          unfold Set.union
          rw [l_eq]
          simp only [List.mem_toSet]
          rw [← h]
          simp [Set.element]
    ⟩
    origin := some ⟨trg, i⟩
    fact_contains_origin_result := by
      have : head = trg.val.mapped_head[i.val] := by rw [List.mk_mem_zipIdx_with_lt_iff_getElem] at h; rw [h]
      simp only [Option.is_none_or]
      apply Set.subset_union_of_subset_right
      rw [this]
      apply Set.subset_refl
  }) = after

def exists_trigger_list (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger obs rules), exists_trigger_list_condition obs rules before after trg

def not_exists_trigger_opt_fs (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : Option (ChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.fact) ∧ after = none

def not_exists_trigger_list (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : ChaseNode obs rules) (after : List (ChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.fact) ∧ after = []

structure ChaseBranch (obs : ObsoletenessCondition sig) (kb : KnowledgeBase sig) where
  branch : PossiblyInfiniteList (ChaseNode obs kb.rules)
  database_first : branch.infinite_list 0 = some {
    fact := (
      let fs := kb.db.toFactSet
      ⟨fs.val, fs.property.left⟩
    ),
    origin := none,
    fact_contains_origin_result := by simp [Option.is_none_or]
  }
  triggers_exist : ∀ n : Nat, (branch.infinite_list n).is_none_or (fun before =>
    let after := branch.infinite_list (n+1)
    (exists_trigger_opt_fs obs kb.rules before after) ∨
    (not_exists_trigger_opt_fs obs kb.rules before after))
  fairness : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ((branch.infinite_list i).is_some_and (fun fs => ¬ trg.val.active fs.fact))
    ∧ (∀ j : Nat, j > i -> (branch.infinite_list j).is_none_or (fun fs => ¬ trg.val.active fs.fact))

namespace ChaseBranch

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  def result (cb : ChaseBranch obs kb) : FactSet sig :=
    fun f => ∃ n : Nat, (cb.branch.infinite_list n).is_some_and (fun fs => f ∈ fs.fact)

  theorem predecessor_isSome_of_isSome (cb : ChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.infinite_list (i + 1)).isSome) :
      (cb.branch.infinite_list i).isSome := by
    cases eq : cb.branch.infinite_list (i+1) with
    | none => rw [eq] at isSome; simp at isSome
    | some node =>
      cases eq_prev : cb.branch.infinite_list i with
      | some prev => simp
      | none =>
        apply False.elim
        have no_holes := cb.branch.no_holes (i+1)
        simp [eq] at no_holes
        specialize no_holes ⟨i, by simp⟩
        apply no_holes
        exact eq_prev

  def prev_node (cb : ChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.infinite_list (i + 1)).isSome) : ChaseNode obs kb.rules :=
    (cb.branch.infinite_list i).get (cb.predecessor_isSome_of_isSome i isSome)

  theorem prev_node_eq (cb : ChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.infinite_list (i + 1)).isSome) :
      cb.branch.infinite_list i = some (cb.prev_node i isSome) := by
    simp [prev_node]

  theorem origin_isSome (cb : ChaseBranch obs kb) (i : Nat) {node : ChaseNode obs kb.rules}
      (eq : cb.branch.infinite_list (i + 1) = some node) : node.origin.isSome := by
    have trg_ex := cb.triggers_exist i
    rw [prev_node_eq _ _ (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_opt_fs at trg_ex
      rcases trg_ex with ⟨trg, _, disj, trg_eq⟩
      simp only [eq] at trg_eq
      injection trg_eq with trg_eq
      rw [← trg_eq]
      simp
    | inr trg_ex =>
      unfold not_exists_trigger_opt_fs at trg_ex
      simp only [eq] at trg_ex
      simp at trg_ex

  theorem origin_trg_is_active (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list (i + 1) = some node) :
      (node.origin.get (cb.origin_isSome i eq)).fst.val.active (cb.prev_node i (by simp [eq])).fact.val := by
    have trg_ex := cb.triggers_exist i
    rw [prev_node_eq _ _ (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq; simp at eq
    | inl trg_ex =>
      unfold exists_trigger_opt_fs at trg_ex
      rcases trg_ex with ⟨trg, trg_active, disj, trg_eq⟩
      simp only [eq] at trg_eq
      injection trg_eq with trg_eq
      simp only [← trg_eq]
      exact trg_active

  theorem origin_trg_result_yields_next_node_fact (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list (i + 1) = some node) :
      node.fact.val = (cb.prev_node i (by simp [eq])).fact.val ∪ (node.origin_result (cb.origin_isSome i eq)).toSet := by
    have trg_ex := cb.triggers_exist i
    rw [prev_node_eq _ _ (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq; simp at eq
    | inl trg_ex =>
      unfold exists_trigger_opt_fs at trg_ex
      rcases trg_ex with ⟨trg, trg_active, disj, trg_eq⟩
      simp only [eq] at trg_eq
      injection trg_eq with trg_eq
      simp only [← trg_eq]
      unfold ChaseNode.origin_result
      simp

  theorem stepIsSubsetOfAllFollowing (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      ∀ j, (cb.branch.infinite_list (i + j)).is_none_or (fun node2 => node.fact.val ⊆ node2.fact.val) := by
    intro j
    induction j with
    | zero => rw [Nat.add_zero, eq]; simp only [Option.is_none_or]; apply Set.subset_refl
    | succ j ih =>
      rw [Option.is_none_or_iff]
      intro node2 eq2
      let prev_node := (cb.prev_node (i + j) (by rw [Nat.add_assoc]; simp [eq2]))
      apply Set.subset_trans (b := prev_node.fact.val)
      . rw [Option.is_none_or_iff] at ih
        specialize ih prev_node (by apply cb.prev_node_eq)
        exact ih
      . rw [cb.origin_trg_result_yields_next_node_fact (i + j) node2 eq2]
        apply Set.subset_union_of_subset_left
        apply Set.subset_refl

  theorem stepIsSubsetOfResult (cb : ChaseBranch obs kb) : ∀ n : Nat, (cb.branch.infinite_list n).is_none_or (fun fs => fs.fact ⊆ cb.result) := by
    intro n
    unfold Option.is_none_or

    cases eq : cb.branch.infinite_list n with
    | none => simp
    | some fs =>
      simp only
      unfold ChaseBranch.result
      intro f h
      exists n
      rw [Option.is_some_and_iff]
      exists fs

  theorem constantsInStepAreFromDatabaseOrRuleSet (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      node.fact.val.constants ⊆ (kb.db.constants.val ∪ kb.rules.head_constants) := by
    induction i generalizing node with
    | zero =>
      rw [cb.database_first] at eq
      injection eq with eq
      rw [← eq]
      rw [Database.toFactSet_constants_same]
      apply Set.subset_union_of_subset_left
      apply Set.subset_refl
    | succ i ih =>
      let prev_node := (cb.prev_node i (by simp [eq]))

      rw [cb.origin_trg_result_yields_next_node_fact i node eq]
      unfold FactSet.constants
      intro c c_mem
      rcases c_mem with ⟨f, f_mem, c_mem⟩
      cases f_mem with
      | inl f_mem =>
        apply ih prev_node
        . apply cb.prev_node_eq
        . exists f
      | inr f_mem =>
        unfold ChaseNode.origin_result at f_mem
        let origin := node.origin.get (cb.origin_isSome i eq)
        have c_mem : c ∈ FactSet.constants (origin.fst.val.mapped_head[origin.snd.val]).toSet := by unfold FactSet.constants; exists f
        apply Set.subset_trans (origin.fst.val.mapped_head_constants_subset origin.snd)
        . intro c c_mem
          rw [List.mem_toSet, List.mem_append] at c_mem
          cases c_mem with
          | inl c_mem =>
            apply ih prev_node
            . apply cb.prev_node_eq
            . rw [List.mem_flatMap] at c_mem
              rcases c_mem with ⟨t, t_mem, c_mem⟩
              rw [List.mem_map] at t_mem
              rcases t_mem with ⟨v, v_mem, t_mem⟩
              rcases origin.fst.val.rule.frontier_occurs_in_body v v_mem with ⟨a, a_mem, v_mem'⟩
              exists origin.fst.val.subs.apply_function_free_atom a
              constructor
              . have := cb.origin_trg_is_active i node eq
                apply this.left
                rw [List.mem_toSet]
                unfold PreTrigger.mapped_body
                unfold GroundSubstitution.apply_function_free_conj
                apply List.mem_map_of_mem
                exact a_mem
              . unfold Fact.constants
                rw [List.mem_flatMap]
                exists t
                constructor
                . unfold GroundSubstitution.apply_function_free_atom
                  rw [List.mem_map]
                  exists VarOrConst.var v
                  constructor
                  . exact v_mem'
                  . unfold PreTrigger.subs_for_mapped_head at t_mem
                    rw [PreTrigger.apply_to_var_or_const_frontier_var] at t_mem
                    . exact t_mem
                    . exact v_mem
                . exact c_mem
          | inr c_mem =>
            apply Or.inr
            exists origin.fst.val.rule
            constructor
            . exact origin.fst.property
            . unfold Rule.head_constants
              rw [List.mem_flatMap]
              exists origin.fst.val.rule.head[origin.snd.val]'(by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)
              constructor
              . apply List.get_mem
              . exact c_mem
        . exact c_mem

  theorem trg_loaded_at_some_step_of_trg_loaded_for_result (cb : ChaseBranch obs kb) : ∀ trg : Trigger obs, trg.loaded cb.result -> ∃ n : Nat, (cb.branch.infinite_list n).is_some_and (fun fs => trg.loaded fs.fact.val) := by
    intro trg
    unfold ChaseBranch.result
    unfold PreTrigger.loaded

    induction trg.mapped_body
    case nil =>
      intro _
      exists 0
      rw [cb.database_first]
      simp [Option.is_some_and]
      intro _ contra
      simp [List.mem_toSet] at contra
    case cons hd tl ih =>
      intro loaded
      rcases loaded hd (by simp [List.mem_toSet]) with ⟨hd_idx, hd_mem⟩
      rw [Option.is_some_and_iff] at hd_mem

      rcases ih (by intro e e_mem; rw [List.mem_toSet] at e_mem; apply loaded; simp [List.mem_toSet, e_mem]) with ⟨tl_idx, tl_mem⟩
      rw [Option.is_some_and_iff] at tl_mem

      exists max hd_idx tl_idx
      rw [Option.is_some_and_iff]

      cases Decidable.em (tl_idx ≤ hd_idx) with
      | inl le =>
        rcases hd_mem with ⟨node, node_eq, hd_mem⟩
        exists node
        constructor
        . rw [Nat.max_eq_left le]
          exact node_eq
        . intro e e_mem
          rw [List.mem_toSet, List.mem_cons] at e_mem
          cases e_mem with
          | inl e_mem => rw [e_mem]; exact hd_mem
          | inr e_mem =>
            rcases tl_mem with ⟨tl_node, tl_node_eq, tl_mem⟩
            have := cb.stepIsSubsetOfAllFollowing tl_idx tl_node tl_node_eq (hd_idx - tl_idx)
            rw [Nat.add_sub_cancel' le] at this
            rw [node_eq, Option.is_none_or] at this
            apply this
            apply tl_mem
            rw [List.mem_toSet]
            exact e_mem
      | inr le =>
        have le := Nat.le_of_not_le le
        rcases tl_mem with ⟨node, node_eq, tl_mem⟩
        exists node
        constructor
        . rw [Nat.max_eq_right le]
          exact node_eq
        . intro e e_mem
          rw [List.mem_toSet, List.mem_cons] at e_mem
          cases e_mem with
          | inr e_mem => apply tl_mem; rw [List.mem_toSet]; exact e_mem
          | inl e_mem =>
            rcases hd_mem with ⟨hd_node, hd_node_eq, hd_mem⟩
            have := cb.stepIsSubsetOfAllFollowing hd_idx hd_node hd_node_eq (tl_idx - hd_idx)
            rw [Nat.add_sub_cancel' le] at this
            rw [node_eq, Option.is_none_or] at this
            apply this
            rw [e_mem]
            exact hd_mem

  theorem trg_active_at_some_step_of_trg_active_for_result (cb : ChaseBranch obs kb) : ∀ trg : Trigger obs, trg.active cb.result -> ∃ n : Nat, (cb.branch.infinite_list n).is_some_and (fun fs => trg.active fs.fact) := by
    intro trg
    intro active
    rcases cb.trg_loaded_at_some_step_of_trg_loaded_for_result trg active.left with ⟨step, loaded_step⟩
    rw [Option.is_some_and_iff] at loaded_step
    rcases loaded_step with ⟨node, node_eq, loaded_step⟩
    exists step
    rw [Option.is_some_and_iff]
    exists node
    constructor
    . exact node_eq
    . constructor
      . exact loaded_step
      . intro contra
        apply active.right
        apply obs.monotone
        . have := cb.stepIsSubsetOfResult step
          rw [node_eq, Option.is_none_or] at this
          exact this
        . exact contra

  theorem result_models_kb (cb : ChaseBranch obs kb) : cb.result.modelsKb kb := by
    constructor
    . unfold FactSet.modelsDb
      unfold ChaseBranch.result
      intro f h
      exists 0
      rw [cb.database_first, Option.is_some_and]
      exact h
    . unfold FactSet.modelsRules
      intro r h
      unfold FactSet.modelsRule
      intro subs subs_loaded
      apply Classical.byContradiction
      intro subs_not_obsolete
      let trg : Trigger obs := ⟨r, subs⟩
      have trg_loaded : trg.loaded cb.result := by apply subs_loaded
      have trg_not_obsolete : ¬ obs.cond trg cb.result := by
        intro contra
        have obs_impl_sat := obs.cond_implies_trg_is_satisfied contra
        apply subs_not_obsolete
        rcases obs_impl_sat with ⟨i, s', obs_impl_sat⟩
        exists i
        exists s'

      rcases cb.trg_active_at_some_step_of_trg_active_for_result trg ⟨trg_loaded, trg_not_obsolete⟩ with ⟨step, step_active⟩
      rw [Option.is_some_and_iff] at step_active
      rcases step_active with ⟨node, node_eq, step_active⟩

      rcases cb.fairness ⟨trg, by apply h⟩ with ⟨step', step'_not_active⟩
      rw [Option.is_some_and_iff] at step'_not_active
      rcases step'_not_active.left with ⟨node', node'_eq, step'_not_active_left⟩

      apply step'_not_active_left
      constructor
      . cases Decidable.em (step ≤ step') with
        | inl le =>
          apply Set.subset_trans (b := node.fact.val)
          . exact step_active.left
          . have := cb.stepIsSubsetOfAllFollowing step node node_eq (step' - step)
            rw [Nat.add_sub_cancel' le, node'_eq, Option.is_none_or] at this
            exact this
        | inr le =>
          have gt := Nat.gt_of_not_le le
          apply False.elim
          have := step'_not_active.right step gt
          rw [node_eq, Option.is_none_or] at this
          apply this
          exact step_active
      . intro contra
        apply trg_not_obsolete
        apply obs.monotone
        . have := cb.stepIsSubsetOfResult step'
          rw [node'_eq, Option.is_none_or] at this
          exact this
        . exact contra

  theorem funcTermForExisVarInChaseMeansTriggerIsUsed (cb : ChaseBranch obs kb) (i : Nat) {node : ChaseNode obs kb.rules} (eq : cb.branch.infinite_list i = some node)
      (trg : RTrigger obs kb.rules) (trg_idx : Fin trg.val.mapped_head.length) {v : sig.V} (v_front : ¬ v ∈ trg.val.rule.frontier)
      (term_in_node : ∃ (f : Fact sig), f ∈ node.fact ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) :
      ∃ drop_number : Fin i, (cb.branch.infinite_list (i - drop_number.val)).is_some_and (fun prev_node => prev_node.origin.is_some_and (fun origin => trg.equiv origin.fst ∧ trg_idx.val = origin.snd.val)) := by
    induction i generalizing node with
    | zero =>
      rw [cb.database_first] at eq
      rw [Option.some.injEq] at eq
      have func_free := kb.db.toFactSet.property.right
      unfold FactSet.isFunctionFree at func_free
      rcases term_in_node with ⟨f, f_mem, term_in_node⟩
      rw [← eq] at f_mem
      specialize func_free f f_mem
      unfold Fact.isFunctionFree at func_free
      specialize func_free _ term_in_node
      rcases func_free with ⟨_, func_free⟩
      simp [PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at func_free
    | succ i ih =>
      let prev_node := (cb.prev_node i (by simp [eq]))
      cases Classical.em (∃ (f : Fact sig), f ∈ prev_node.fact ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) with
      | inl term_in_prev_node =>
        rcases ih (by apply cb.prev_node_eq) term_in_prev_node with ⟨drop, ih⟩
        exists ⟨drop.val + 1, by simp⟩
        rw [Nat.add_sub_add_right]
        exact ih
      | inr term_not_in_prev_node =>
        exists ⟨0, by simp⟩
        rw [Nat.sub_zero, eq]
        rw [Option.is_some_and]
        rw [Option.is_some_and_iff]

        let origin := node.origin.get (cb.origin_isSome i eq)
        exists origin
        constructor
        . simp [origin]
        . rcases term_in_node with ⟨f, f_mem, t_mem⟩
          rw [cb.origin_trg_result_yields_next_node_fact _ _ eq] at f_mem
          cases f_mem with
          | inl f_mem => apply False.elim; apply term_not_in_prev_node; exists f
          | inr f_mem =>
            rw [List.mem_toSet] at f_mem
            unfold ChaseNode.origin_result at f_mem
            rw [← PreTrigger.apply_subs_for_mapped_head_eq] at f_mem
            unfold GroundSubstitution.apply_function_free_conj at f_mem
            rw [List.mem_map] at f_mem
            rcases f_mem with ⟨a, a_mem, f_mem⟩
            rw [← f_mem] at t_mem
            unfold GroundSubstitution.apply_function_free_atom at t_mem
            rw [List.mem_map] at t_mem
            rcases t_mem with ⟨voc, voc_mem, t_mem⟩
            cases voc with
            | const c => simp [GroundSubstitution.apply_var_or_const, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem
            | var v2 =>
              have v2_front : ¬ v2 ∈ origin.fst.val.rule.frontier := by
                intro contra
                rw [PreTrigger.apply_subs_for_var_or_const_eq, PreTrigger.apply_to_var_or_const_frontier_var _ _ _ contra] at t_mem
                apply term_not_in_prev_node
                rcases origin.fst.val.rule.frontier_occurs_in_body _ contra with ⟨b, b_mem, v2_mem⟩
                exists origin.fst.val.subs.apply_function_free_atom b
                constructor
                . have active := cb.origin_trg_is_active i node eq
                  apply active.left
                  rw [List.mem_toSet]
                  unfold PreTrigger.mapped_body
                  unfold GroundSubstitution.apply_function_free_conj
                  apply List.mem_map_of_mem
                  exact b_mem
                . rw [← t_mem]
                  unfold GroundSubstitution.apply_function_free_atom
                  rw [List.mem_map]
                  exists VarOrConst.var v2
              rw [PreTrigger.apply_subs_for_var_or_const_eq, PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v2_front] at t_mem

              have := RTrigger.funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame
                trg
                origin.fst
                ⟨trg_idx.val, by rw [← PreTrigger.length_mapped_head]; exact trg_idx.isLt⟩
                ⟨origin.snd.val, by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt⟩
                v
                v2
                v_front
                v2_front
              apply this
              rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
              rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v2_front]
              exact Eq.symm t_mem

  theorem funcTermForExisVarInChaseMeansTriggerResultOccurs (cb : ChaseBranch obs kb) (i : Nat) {node : ChaseNode obs kb.rules} (eq : cb.branch.infinite_list i = some node)
      (trg : RTrigger obs kb.rules) (trg_idx : Fin trg.val.mapped_head.length) {v : sig.V} (v_front : ¬ v ∈ trg.val.rule.frontier)
      (term_in_node : ∃ (f : Fact sig), f ∈ node.fact ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) :
      trg.val.mapped_head[trg_idx.val].toSet ⊆ node.fact.val := by
    rcases cb.funcTermForExisVarInChaseMeansTriggerIsUsed i eq trg trg_idx v_front term_in_node with ⟨drop, h⟩
    rw [Option.is_some_and_iff] at h
    rcases h with ⟨prev_node, prev_node_eq, h⟩
    rw [Option.is_some_and_iff] at h
    rcases h with ⟨origin, origin_eq, h⟩
    simp only [PreTrigger.result_eq_of_equiv _ _ h.left, h.right]
    have := prev_node.fact_contains_origin_result
    rw [origin_eq, Option.is_none_or] at this
    apply Set.subset_trans this
    have := cb.stepIsSubsetOfAllFollowing (i - drop.val) prev_node prev_node_eq drop.val
    rw [Nat.sub_add_cancel (Nat.le_of_lt drop.isLt), eq, Option.is_none_or] at this
    exact this

end ChaseBranch

structure ChaseTree (obs : ObsoletenessCondition sig) (kb : KnowledgeBase sig) where
  tree : FiniteDegreeTree (ChaseNode obs kb.rules)
  database_first : tree.get [] = some {
      fact := (
        let fs := kb.db.toFactSet
        ⟨fs.val, fs.property.left⟩
      )
      origin := none
      fact_contains_origin_result := by simp [Option.is_none_or]
    }
  triggers_exist : ∀ node : List Nat, (tree.get node).is_none_or (fun before =>
    let after := tree.children node
    (exists_trigger_list obs kb.rules before after) ∨
    (not_exists_trigger_list obs kb.rules before after))

  fairness_leaves : ∀ leaf, leaf ∈ tree.leaves -> ∀ trg : (RTrigger obs kb.rules), ¬ trg.val.active leaf.fact
  fairness_infinite_branches : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ∀ node : List Nat, node.length ≥ i ->
    (tree.get node).is_none_or (fun fs => ¬ trg.val.active fs.fact)

namespace ChaseTree

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  def branches (ct : ChaseTree obs kb) : Set (ChaseBranch obs kb) := fun branch =>
    branch.branch ∈ ct.tree.branches

  def branches_through (ct : ChaseTree obs kb) (node : List Nat) : Set (ChaseBranch obs kb) := fun branch =>
    branch.branch ∈ ct.tree.branches_through node

  def result (ct : ChaseTree obs kb) : Set (FactSet sig) := fun fs => ∃ branch, branch ∈ ct.branches ∧ branch.result = fs

  theorem predecessor_isSome_of_isSome (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (isSome : (ct.tree.get (i::path)).isSome) :
      (ct.tree.get path).isSome := by
    cases eq : ct.tree.get (i::path) with
    | none => rw [eq] at isSome; simp at isSome
    | some node =>
      cases eq_prev : ct.tree.get path with
      | some prev => simp
      | none =>
        apply False.elim
        have no_holes := ct.tree.tree.no_orphans (i::path)
        unfold FiniteDegreeTree.get at eq
        unfold PossiblyInfiniteTree.get at eq
        simp [eq] at no_holes
        specialize no_holes path [i] (by simp)
        apply no_holes
        exact eq_prev

  def prev_node (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (isSome : (ct.tree.get (i::path)).isSome) : ChaseNode obs kb.rules :=
    (ct.tree.get path).get (ct.predecessor_isSome_of_isSome path i isSome)

  theorem prev_node_eq (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (isSome : (ct.tree.get (i::path)).isSome) :
      ct.tree.get path = some (ct.prev_node path i isSome) := by
    simp [prev_node]

  theorem origin_isSome (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) {node : ChaseNode obs kb.rules}
      (eq : ct.tree.get (i::path) = some node) : node.origin.isSome := by
    have trg_ex := ct.triggers_exist path
    rw [prev_node_eq _ _ i (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_list at trg_ex
      unfold exists_trigger_list_condition at trg_ex
      rcases trg_ex with ⟨trg, _, trg_eq⟩
      let i_fin : Fin (ct.tree.children path).length := ⟨i, by
        unfold FiniteDegreeTree.get at eq
        rw [← ct.tree.tree.getElem_children_eq_get path i] at eq
        rw [← ct.tree.getElem_children_eq_getElem_lifted_children path] at eq
        rw [List.getElem?_eq_some_iff] at eq
        rcases eq with ⟨h, _⟩
        exact h
      ⟩
      have := List.getElem_of_eq (Eq.symm trg_eq) i_fin.isLt
      rw [List.getElem_map] at this
      simp only at this
      rw [← Option.some.injEq] at this
      rw [ct.tree.getElem_children_eq_get path i_fin] at this
      simp only [i_fin, eq] at this
      rw [Option.some.injEq] at this
      rw [this]
      simp
    | inr trg_ex =>
      unfold not_exists_trigger_list at trg_ex
      have := ct.tree.each_successor_none_of_children_empty _ trg_ex.right i
      rw [this] at eq
      simp at eq

  theorem origin_trg_is_active (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (node : ChaseNode obs kb.rules) (eq : ct.tree.get (i::path) = some node) :
      (node.origin.get (ct.origin_isSome path i eq)).fst.val.active (ct.prev_node path i (by simp [eq])).fact.val := by
    have trg_ex := ct.triggers_exist path
    rw [prev_node_eq _ _ i (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_list at trg_ex
      unfold exists_trigger_list_condition at trg_ex
      rcases trg_ex with ⟨trg, trg_active, trg_eq⟩
      let i_fin : Fin (ct.tree.children path).length := ⟨i, by
        unfold FiniteDegreeTree.get at eq
        rw [← ct.tree.tree.getElem_children_eq_get path i] at eq
        rw [← ct.tree.getElem_children_eq_getElem_lifted_children path] at eq
        rw [List.getElem?_eq_some_iff] at eq
        rcases eq with ⟨h, _⟩
        exact h
      ⟩
      have := List.getElem_of_eq (Eq.symm trg_eq) i_fin.isLt
      rw [List.getElem_map] at this
      simp only at this
      rw [← Option.some.injEq] at this
      rw [ct.tree.getElem_children_eq_get path i_fin] at this
      simp only [i_fin, eq] at this
      rw [Option.some.injEq] at this
      simp [this, trg_active]
    | inr trg_ex =>
      unfold not_exists_trigger_list at trg_ex
      have := ct.tree.each_successor_none_of_children_empty _ trg_ex.right i
      rw [this] at eq
      simp at eq

  theorem origin_trg_result_yields_next_node_fact (ct : ChaseTree obs kb) (path : List Nat) (i : Nat) (node : ChaseNode obs kb.rules) (eq : ct.tree.get (i::path) = some node) :
      node.fact.val = (ct.prev_node path i (by simp [eq])).fact.val ∪ (node.origin_result (ct.origin_isSome path i eq)).toSet := by
    have trg_ex := ct.triggers_exist path
    rw [prev_node_eq _ _ i (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_list at trg_ex
      unfold exists_trigger_list_condition at trg_ex
      rcases trg_ex with ⟨trg, trg_active, trg_eq⟩
      let i_fin : Fin (ct.tree.children path).length := ⟨i, by
        unfold FiniteDegreeTree.get at eq
        rw [← ct.tree.tree.getElem_children_eq_get path i] at eq
        rw [← ct.tree.getElem_children_eq_getElem_lifted_children path] at eq
        rw [List.getElem?_eq_some_iff] at eq
        rcases eq with ⟨h, _⟩
        exact h
      ⟩
      have := List.getElem_of_eq (Eq.symm trg_eq) i_fin.isLt
      rw [List.getElem_map] at this
      simp only at this
      rw [← Option.some.injEq] at this
      rw [ct.tree.getElem_children_eq_get path i_fin] at this
      simp only [i_fin, eq] at this
      rw [Option.some.injEq] at this
      unfold ChaseNode.origin_result
      have i_lt : i < trg.val.mapped_head.length := by
        have : trg.val.mapped_head.length = (ct.tree.children path).length := by
          rw [← trg_eq]
          rw [List.length_map, List.length_attach, List.length_zipIdx_with_lt]
        rw [this]
        exact i_fin.isLt
      have origin_eq : node.origin.get (by simp [this]) = ⟨trg, ⟨i, i_lt⟩⟩ := by simp only [this]; simp [List.zipIdx_with_lt_getElem_snd_eq_index i_lt]
      have idx_eq : (node.origin.get (by simp [this])).snd.val = i := by rw [origin_eq]
      simp only [this]
      simp [List.zipIdx_with_lt_getElem_fst_eq_getElem i_lt, idx_eq]
    | inr trg_ex =>
      unfold not_exists_trigger_list at trg_ex
      have := ct.tree.each_successor_none_of_children_empty _ trg_ex.right i
      rw [this] at eq
      simp at eq

  theorem stepIsSubsetOfAllFollowing (ct : ChaseTree obs kb) (path : List Nat) (node : ChaseNode obs kb.rules) (eq : ct.tree.get path = some node) :
      ∀ path2, (ct.tree.get (path2 ++ path)).is_none_or (fun node2 => node.fact.val ⊆ node2.fact.val) := by
    intro path2
    induction path2 with
    | nil => rw [List.nil_append, eq]; simp only [Option.is_none_or]; apply Set.subset_refl
    | cons hd tl ih =>
      rw [Option.is_none_or_iff]
      intro node2 eq2
      let prev_node := (ct.prev_node (tl ++ path) hd (by rw [← List.cons_append, eq2]; simp))
      apply Set.subset_trans (b := prev_node.fact.val)
      . rw [Option.is_none_or_iff] at ih
        specialize ih prev_node (by apply ct.prev_node_eq)
        exact ih
      . rw [ct.origin_trg_result_yields_next_node_fact (tl ++ path) hd node2 eq2]
        apply Set.subset_union_of_subset_left
        apply Set.subset_refl

  theorem result_models_kb (ct : ChaseTree obs kb) : ∀ fs, fs ∈ ct.result -> fs.modelsKb kb := by
    intro fs fs_mem
    rcases fs_mem with ⟨branch, _, fs_mem⟩
    rw [← fs_mem]
    apply branch.result_models_kb

  theorem funcTermForExisVarInChaseMeansTriggerIsUsed (ct : ChaseTree obs kb) (path : List Nat) {node : ChaseNode obs kb.rules} (eq : ct.tree.get path = some node)
      (trg : RTrigger obs kb.rules) (trg_idx : Fin trg.val.mapped_head.length) {v : sig.V} (v_front : ¬ v ∈ trg.val.rule.frontier)
      (term_in_node : ∃ (f : Fact sig), f ∈ node.fact ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) :
      ∃ drop_number : Fin path.length, (ct.tree.get (path.drop drop_number.val)).is_some_and (fun prev_node => prev_node.origin.is_some_and (fun origin => trg.equiv origin.fst ∧ trg_idx.val = origin.snd.val)) := by
    induction path generalizing node with
    | nil =>
      rw [ct.database_first] at eq
      rw [Option.some.injEq] at eq
      have func_free := kb.db.toFactSet.property.right
      unfold FactSet.isFunctionFree at func_free
      rcases term_in_node with ⟨f, f_mem, term_in_node⟩
      rw [← eq] at f_mem
      specialize func_free f f_mem
      unfold Fact.isFunctionFree at func_free
      specialize func_free _ term_in_node
      rcases func_free with ⟨_, func_free⟩
      simp [PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at func_free
    | cons i path ih =>
      let prev_node := (ct.prev_node path i (by simp [eq]))
      cases Classical.em (∃ (f : Fact sig), f ∈ prev_node.fact ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) with
      | inl term_in_prev_node =>
        rcases ih (by apply ct.prev_node_eq) term_in_prev_node with ⟨drop, ih⟩
        exists ⟨drop.val + 1, by simp⟩
      | inr term_not_in_prev_node =>
        exists ⟨0, by simp⟩
        rw [List.drop_zero, eq]
        rw [Option.is_some_and]
        rw [Option.is_some_and_iff]

        let origin := node.origin.get (ct.origin_isSome path i eq)
        exists origin
        constructor
        . simp [origin]
        . rcases term_in_node with ⟨f, f_mem, t_mem⟩
          rw [ct.origin_trg_result_yields_next_node_fact _ _ _ eq] at f_mem
          cases f_mem with
          | inl f_mem => apply False.elim; apply term_not_in_prev_node; exists f
          | inr f_mem =>
            rw [List.mem_toSet] at f_mem
            unfold ChaseNode.origin_result at f_mem
            rw [← PreTrigger.apply_subs_for_mapped_head_eq] at f_mem
            unfold GroundSubstitution.apply_function_free_conj at f_mem
            rw [List.mem_map] at f_mem
            rcases f_mem with ⟨a, a_mem, f_mem⟩
            rw [← f_mem] at t_mem
            unfold GroundSubstitution.apply_function_free_atom at t_mem
            rw [List.mem_map] at t_mem
            rcases t_mem with ⟨voc, voc_mem, t_mem⟩
            cases voc with
            | const c => simp [GroundSubstitution.apply_var_or_const, PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.const] at t_mem
            | var v2 =>
              have v2_front : ¬ v2 ∈ origin.fst.val.rule.frontier := by
                intro contra
                rw [PreTrigger.apply_subs_for_var_or_const_eq, PreTrigger.apply_to_var_or_const_frontier_var _ _ _ contra] at t_mem
                apply term_not_in_prev_node
                rcases origin.fst.val.rule.frontier_occurs_in_body _ contra with ⟨b, b_mem, v2_mem⟩
                exists origin.fst.val.subs.apply_function_free_atom b
                constructor
                . have active := ct.origin_trg_is_active path i node eq
                  apply active.left
                  rw [List.mem_toSet]
                  unfold PreTrigger.mapped_body
                  unfold GroundSubstitution.apply_function_free_conj
                  apply List.mem_map_of_mem
                  exact b_mem
                . rw [← t_mem]
                  unfold GroundSubstitution.apply_function_free_atom
                  rw [List.mem_map]
                  exists VarOrConst.var v2
              rw [PreTrigger.apply_subs_for_var_or_const_eq, PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v2_front] at t_mem

              have := RTrigger.funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame
                trg
                origin.fst
                ⟨trg_idx.val, by rw [← PreTrigger.length_mapped_head]; exact trg_idx.isLt⟩
                ⟨origin.snd.val, by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt⟩
                v
                v2
                v_front
                v2_front
              apply this
              rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
              rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v2_front]
              exact Eq.symm t_mem

  theorem funcTermForExisVarInChaseMeansTriggerResultOccurs (ct : ChaseTree obs kb) (path : List Nat) {node : ChaseNode obs kb.rules} (eq : ct.tree.get path = some node)
      (trg : RTrigger obs kb.rules) (trg_idx : Fin trg.val.mapped_head.length) {v : sig.V} (v_front : ¬ v ∈ trg.val.rule.frontier)
      (term_in_node : ∃ (f : Fact sig), f ∈ node.fact ∧ (trg.val.functional_term_for_var trg_idx.val v) ∈ f.terms) :
      trg.val.mapped_head[trg_idx.val].toSet ⊆ node.fact.val := by
    rcases ct.funcTermForExisVarInChaseMeansTriggerIsUsed path eq trg trg_idx v_front term_in_node with ⟨drop, h⟩
    rw [Option.is_some_and_iff] at h
    rcases h with ⟨prev_node, prev_node_eq, h⟩
    rw [Option.is_some_and_iff] at h
    rcases h with ⟨origin, origin_eq, h⟩
    simp only [PreTrigger.result_eq_of_equiv _ _ h.left, h.right]
    have := prev_node.fact_contains_origin_result
    rw [origin_eq, Option.is_none_or] at this
    apply Set.subset_trans this
    have := ct.stepIsSubsetOfAllFollowing (path.drop drop.val) prev_node prev_node_eq (path.take drop.val)
    rw [List.take_append_drop, eq, Option.is_none_or] at this
    exact this

end ChaseTree

