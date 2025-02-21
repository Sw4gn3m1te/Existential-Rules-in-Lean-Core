import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic

import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.RTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

structure ChaseNode (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  fact : { fs : FactSet sig // fs.finite }
  -- the origin is none only for the database
  origin : Option ((trg : RTrigger (obs : LaxObsoletenessCondition sig) rules) × Fin trg.val.mapped_head.length)
  fact_contains_origin_result : origin.is_none_or (fun origin => origin.fst.val.mapped_head[origin.snd.val].toSet ⊆ fact)

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
  trg.val.active before.fact ∧ trg.val.mapped_head.enum_with_lt.attach.map (fun ⟨⟨i, head⟩, h⟩ => {
    fact := ⟨
      before.fact ∪ head.toSet,
      by
        rw [List.mk_mem_enum_with_lt_iff_getElem] at h
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
      have : head = trg.val.mapped_head[i.val] := by rw [List.mk_mem_enum_with_lt_iff_getElem] at h; rw [h]
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

  def result (branch : ChaseBranch obs kb) : FactSet sig :=
    fun f => ∃ n : Nat, (branch.branch.infinite_list n).is_some_and (fun fs => f ∈ fs.fact)

  theorem origin_is_some (cb : ChaseBranch obs kb) :
      ∀ i, (cb.branch.infinite_list (i + 1)).is_none_or (fun node => node.origin.isSome) := by
    intro i
    cases eq : cb.branch.infinite_list (i + 1) with
    | none => simp [Option.is_none_or]
    | some node =>
      simp only [Option.is_none_or]
      have trg_ex := cb.triggers_exist i
      cases eq2 : cb.branch.infinite_list i with
      | none =>
        have no_holes := cb.branch.no_holes (i + 1)
        simp [eq] at no_holes
        specialize no_holes ⟨i, by simp⟩
        apply False.elim
        apply no_holes
        exact eq2
      | some prev_node =>
        rw [eq2, Option.is_none_or] at trg_ex
        cases trg_ex with
        | inl trg_ex =>
          unfold exists_trigger_opt_fs at trg_ex
          rcases trg_ex with ⟨trg, _, disj, trg_eq⟩
          rw [eq] at trg_eq
          injection trg_eq with trg_eq
          rw [← trg_eq]
          simp
        | inr trg_ex =>
          unfold not_exists_trigger_opt_fs at trg_ex
          rw [eq] at trg_ex
          simp at trg_ex

  -- TODO: check if this simplifies code where we used cb.triggers_exist before
  theorem origin_trg_is_active (cb : ChaseBranch obs kb) (i : Nat) (node prev_node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list (i + 1) = some node) (eq2 : cb.branch.infinite_list i = some prev_node) :
      (node.origin.get (by
        have is_some := cb.origin_is_some i
        rw [eq, Option.is_none_or] at is_some
        exact is_some
      )).fst.val.active prev_node.fact.val := by
    have trg_ex := cb.triggers_exist i
    rw [eq2, Option.is_none_or] at trg_ex
    cases trg_ex with
    | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq; simp at eq
    | inl trg_ex =>
      unfold exists_trigger_opt_fs at trg_ex
      rcases trg_ex with ⟨trg, trg_active, disj, trg_eq⟩
      rw [eq] at trg_eq
      injection trg_eq with trg_eq
      simp [← trg_eq]
      exact trg_active

  -- TODO: check if this simplifies code where we used cb.triggers_exist before
  theorem origin_trg_result_yields_next_node_fact (cb : ChaseBranch obs kb) (i : Nat) (node prev_node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list (i + 1) = some node) (eq2 : cb.branch.infinite_list i = some prev_node) (origin : ((trg : RTrigger obs kb.rules) × Fin trg.val.mapped_head.length)) (eq_origin : node.origin = some origin) :
      node.fact.val = prev_node.fact.val ∪ (origin.fst.val.mapped_head[origin.snd.val].toSet) := by
    have trg_ex := cb.triggers_exist i
    rw [eq2, Option.is_none_or] at trg_ex
    cases trg_ex with
    | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq; simp at eq
    | inl trg_ex =>
      unfold exists_trigger_opt_fs at trg_ex
      rcases trg_ex with ⟨trg, trg_active, disj, trg_eq⟩
      rw [eq] at trg_eq
      injection trg_eq with trg_eq
      simp [← trg_eq]
      have : trg = origin.fst ∧ disj.val = origin.snd.val := by
        have : node.origin = some ⟨trg, disj⟩ := by rw [← trg_eq]
        rw [eq_origin] at this
        injection this with this
        rw [this]
        simp
      simp [this]
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
end ChaseTree


variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

theorem chaseBranchSetIsSubsetOfNext (cb : ChaseBranch obs kb) : ∀ n : Nat,
  match cb.branch.infinite_list n with
  | .none => cb.branch.infinite_list (n+1) = none
  | .some fs => (cb.branch.infinite_list (n+1)).is_none_or (fun fs2 => fs.fact.val ⊆ fs2.fact.val) :=
by
  intro n
  cases eq : cb.branch.infinite_list n with
  | none =>
    simp
    have dec : Decidable (cb.branch.infinite_list (n+1) = none) := Option.decidable_eq_none
    apply dec.byContradiction
    intro contra
    let n' : Fin (n+1) := ⟨n, by simp⟩
    have : ¬ cb.branch.infinite_list n' = none := by apply cb.branch.no_holes; apply contra
    contradiction
  | some fs =>
    simp
    cases eq2 : cb.branch.infinite_list (n+1) with
    | none => simp [Option.is_none_or]
    | some fs2 =>
      simp [Option.is_none_or]
      intro f h
      have trg_ex_n := cb.triggers_exist n
      simp [eq, Option.is_none_or] at trg_ex_n
      cases trg_ex_n with
      | inl g =>
        cases g with | intro trg h_trg =>
          cases h_trg.right with | intro i h_i =>
            rw [eq2] at h_i
            injection h_i with h_i
            rw [← h_i]
            simp [Set.element, Set.union]
            apply Or.inl
            exact h
      | inr g =>
        have g_right := g.right
        rw [eq2] at g_right
        contradiction

theorem chaseTreeSetIsSubsetOfEachNext (ct : ChaseTree obs kb) : ∀ address : List Nat,
  match ct.tree.get address with
  | .none => ct.tree.children address = []
  | .some fs => ∀ fs2, fs2 ∈ ct.tree.children address -> fs.fact.val ⊆ fs2.fact.val :=
by
  intro address
  cases eq : ct.tree.get address with
  | none => simp; apply FiniteDegreeTree.children_empty_of_get_eq_none; exact eq
  | some fs =>
    simp
    intro fs2 h
    have trg_ex_addr := ct.triggers_exist address
    simp [eq, Option.is_none_or] at trg_ex_addr
    cases trg_ex_addr with
    | inl g =>
      cases g with | intro trg h_trg =>
        rw [← h_trg.right] at h
        rw [List.mem_map] at h
        cases h with | intro head h_head =>
          rw [← h_head.right]
          intro f h
          apply Or.inl
          exact h
    | inr g =>
      rw [g.right] at h
      contradiction

theorem chaseBranchSetIsSubsetOfAllFollowing (cb : ChaseBranch obs kb) : ∀ (n m : Nat),
  match cb.branch.infinite_list n with
  | .none => cb.branch.infinite_list (n+m) = none
  | .some fs => (cb.branch.infinite_list (n+m)).is_none_or (fun fs2 => fs.fact.val ⊆ fs2.fact.val) :=
by
  intro n m
  induction m with
  | zero =>
    cases eq : cb.branch.infinite_list n with
    | none => simp; exact eq
    | some fs => simp [Option.is_none_or, eq, Set.subset]
  | succ m ih =>
    cases eq : cb.branch.infinite_list n with
    | none =>
      simp
      simp [eq] at ih
      have step := chaseBranchSetIsSubsetOfNext cb (n+m)
      simp [ih] at step
      exact step
    | some fs =>
      simp
      simp [eq, Option.is_none_or] at ih
      have step := chaseBranchSetIsSubsetOfNext cb (n+m)
      cases eq2 : cb.branch.infinite_list (n+m) with
      | none => simp [eq2] at step; rw [← Nat.add_assoc, step, Option.is_none_or]; simp
      | some fs2 =>
        simp [eq2] at step; simp [eq2] at ih; rw [← Nat.add_assoc]
        cases eq3 : cb.branch.infinite_list (n+m+1) with
        | none => simp [Option.is_none_or]
        | some fs3 =>
          simp [Option.is_none_or]; simp [eq3, Option.is_none_or] at step;
          apply Set.subset_trans; exact ih; exact step

theorem chaseTreeSetIsSubsetOfAllFollowing (ct : ChaseTree obs kb) : ∀ (n m : List Nat),
  match ct.tree.get n with
  | .none => ct.tree.get (m ++ n) = none
  | .some fs => (ct.tree.get (m ++ n)).is_none_or (fun fs2 => fs.fact.val ⊆ fs2.fact.val) :=
by
  intro n m
  induction m with
  | nil =>
    cases eq : ct.tree.get n with
    | none => simp; exact eq
    | some fs => simp [Option.is_none_or, eq, Set.subset]
  | cons i m ih =>
    cases eq : ct.tree.get n with
    | none =>
      simp
      simp [eq] at ih
      have step := chaseTreeSetIsSubsetOfEachNext ct (m ++ n)
      simp [ih] at step
      apply FiniteDegreeTree.each_successor_none_of_children_empty
      apply step
    | some fs =>
      simp
      simp [eq, Option.is_none_or] at ih
      have step := chaseTreeSetIsSubsetOfEachNext ct (m ++ n)
      cases eq2 : ct.tree.get (m ++ n) with
      | none =>
        simp [eq2] at step
        unfold Option.is_none_or
        have helper := ct.tree.each_successor_none_of_children_empty (m ++ n) step
        rw [helper]
        simp
      | some fs2 =>
        simp [eq2] at step; simp [eq2] at ih
        cases eq3 : ct.tree.get (i :: (m ++ n)) with
        | none => simp [Option.is_none_or]
        | some fs3 =>
          simp [Option.is_none_or]
          apply Set.subset_trans
          . exact ih
          . apply step
            rw [ct.tree.in_children_iff_index_exists]
            exists i

theorem chaseBranchSetIsSubsetOfResult (cb : ChaseBranch obs kb) : ∀ n : Nat, (cb.branch.infinite_list n).is_none_or (fun fs => fs.fact ⊆ cb.result) := by
  intro n
  unfold Option.is_none_or

  cases eq : cb.branch.infinite_list n with
  | none => simp
  | some fs =>
    simp
    unfold ChaseBranch.result
    intro f h
    simp [Set.element]
    exists n
    unfold Option.is_some_and
    simp [eq]
    exact h

theorem chaseTreeSetIsSubsetOfResult (ct : ChaseTree obs kb) : ∀ node : List Nat, (ct.tree.get node).is_none_or (fun fs => ∀ branch, branch ∈ ct.branches_through node -> fs.fact ⊆ branch.result) := by
  intro node
  unfold Option.is_none_or

  cases eq : ct.tree.get node with
  | none => simp
  | some fs =>
    simp
    intro branch branch_through_node
    have : branch.branch.infinite_list node.length = ct.tree.get node := by
      unfold ChaseTree.branches_through at branch_through_node
      unfold FiniteDegreeTree.branches_through at branch_through_node
      unfold PossiblyInfiniteTree.branches_through at branch_through_node
      unfold InfiniteTreeSkeleton.branches_through at branch_through_node
      simp [Set.element] at branch_through_node
      rcases branch_through_node with ⟨nodes, eq, eq2⟩
      rw [eq node.length, eq2]
      rfl

    have branch_subs_result := chaseBranchSetIsSubsetOfResult branch node.length
    rw [this] at branch_subs_result
    simp [eq, Option.is_none_or] at branch_subs_result
    apply branch_subs_result

theorem constantsInChaseBranchAreFromDatabase (cb : ChaseBranch obs kb) : ∀ n : Nat, (cb.branch.infinite_list n).is_none_or (fun fs => fs.fact.val.constants ⊆ (kb.db.constants.val ∪ kb.rules.head_constants)) := by
  intro n
  induction n with
  | zero =>
    rw [cb.database_first, Option.is_none_or]
    simp only
    rw [Database.toFactSet_constants_same]
    apply Set.subset_union_of_subset_left
    apply Set.subset_refl
  | succ n ih =>
    cases eq_node : cb.branch.infinite_list (n+1) with
    | none => simp [Option.is_none_or]
    | some node =>
      cases eq_prev : cb.branch.infinite_list n with
      | none =>
        have no_holes := cb.branch.no_holes (n+1)
        simp [eq_node] at no_holes
        specialize no_holes ⟨n, by simp⟩
        simp [eq_prev] at no_holes
      | some prev =>
        rw [Option.is_none_or]
        rw [eq_prev, Option.is_none_or] at ih

        have trg_ex := cb.triggers_exist n
        rw [eq_prev, Option.is_none_or] at trg_ex
        cases trg_ex with
        | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [eq_node] at trg_ex; simp at trg_ex
        | inl trg_ex =>
          unfold exists_trigger_opt_fs at trg_ex
          rcases trg_ex with ⟨trg, trg_active, disj_index, trg_ex⟩
          rw [eq_node] at trg_ex
          injection trg_ex with trg_ex
          rw [← trg_ex]
          simp only
          unfold FactSet.constants
          intro c c_mem
          rcases c_mem with ⟨f, f_mem, c_mem⟩
          cases f_mem with
          | inl f_mem =>
            apply ih
            exists f
          | inr f_mem =>
            unfold Fact.constants at c_mem
            rw [List.mem_toSet] at f_mem
            unfold PreTrigger.mapped_head at f_mem
            simp at f_mem
            rcases f_mem with ⟨a, a_mem, f_eq⟩
            unfold PreTrigger.apply_to_function_free_atom at f_eq
            rw [← f_eq] at c_mem
            simp only at c_mem

            rw [List.mem_flatMap] at c_mem
            rcases c_mem with ⟨tree, tree_mem, c_mem⟩
            rw [List.mem_map] at tree_mem
            rcases tree_mem with ⟨voc, voc_mem, tree_eq⟩
            unfold PreTrigger.apply_to_var_or_const at tree_eq

            cases voc with
            | const d =>
              simp only [Function.comp_apply, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at tree_eq
              apply Or.inr
              unfold RuleSet.head_constants
              exists trg.val.rule
              constructor
              . exact trg.property
              . unfold Rule.head_constants
                rw [List.mem_flatMap]
                exists trg.val.rule.head[disj_index.val]'(by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt)
                constructor
                . simp
                . unfold FunctionFreeConjunction.consts
                  rw [List.mem_flatMap]
                  exists a
                  constructor
                  . exact a_mem
                  . unfold FunctionFreeAtom.constants
                    apply VarOrConst.mem_filterConsts_of_const
                    rw [← tree_eq] at c_mem
                    rw [GroundTerm.constants_const, List.mem_singleton] at c_mem
                    rw [c_mem]
                    exact voc_mem
            | var v =>
              simp only [Function.comp_apply, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize] at tree_eq

              cases Decidable.em (v ∈ trg.val.rule.frontier) with
              | inl v_frontier =>
                simp [v_frontier] at tree_eq

                apply ih
                rcases (trg.val.rule.frontier_occurs_in_body _ v_frontier) with ⟨b, b_mem, v_mem⟩
                exists trg.val.subs.apply_function_free_atom b
                constructor
                . apply trg_active.left
                  rw [List.mem_toSet]
                  unfold PreTrigger.mapped_body
                  simp only [GroundSubstitution.apply_function_free_conj]
                  rw [List.mem_map]
                  exists b
                . unfold Fact.constants
                  rw [List.mem_flatMap]
                  exists tree
                  constructor
                  . rw [← tree_eq]
                    unfold GroundSubstitution.apply_function_free_atom
                    rw [List.mem_map]
                    exists (VarOrConst.var v)
                  . exact c_mem
              | inr v_frontier =>
                simp [v_frontier] at tree_eq
                rw [← tree_eq] at c_mem
                rw [GroundTerm.constants_func, List.mem_flatMap] at c_mem
                rcases c_mem with ⟨tree, tree_mem, c_mem⟩
                rw [List.mem_map] at tree_mem
                rcases tree_mem with ⟨v, v_frontier, tree_eq⟩

                -- from here its the same as in the inl case
                apply ih
                rcases (trg.val.rule.frontier_occurs_in_body _ v_frontier) with ⟨b, b_mem, v_mem⟩
                exists trg.val.subs.apply_function_free_atom b
                constructor
                . apply trg_active.left
                  rw [List.mem_toSet]
                  unfold PreTrigger.mapped_body
                  simp only [GroundSubstitution.apply_function_free_conj]
                  rw [List.mem_map]
                  exists b
                . unfold Fact.constants
                  rw [List.mem_flatMap]
                  exists tree
                  constructor
                  . rw [← tree_eq]
                    unfold GroundSubstitution.apply_function_free_atom
                    rw [List.mem_map]
                    exists (VarOrConst.var v)
                  . exact c_mem

theorem trgLoadedForChaseResultMeansLoadedAtSomeIndex (cb : ChaseBranch obs kb) : ∀ trg : Trigger obs, trg.loaded cb.result -> ∃ n : Nat, (cb.branch.infinite_list n).is_some_and (fun fs => trg.loaded fs.fact) := by
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
    contradiction
  case cons head tail ih =>
    intro loaded
    have ex_head_n := loaded head
    simp [Set.element, List.toSet, Set.union] at ex_head_n

    have ex_tail_n := by
      apply ih
      simp [List.toSet] at loaded
      have ⟨ _, tailSubs ⟩ := (Set.union_subset_iff_both_subset _ _ _).mp loaded
      exact tailSubs
    cases ex_head_n with | intro i hi =>
      cases ex_tail_n with | intro j hj =>
        exists Nat.max i j
        simp [List.toSet]

        have max_help_left : ∀ a b : Nat, a ≤ Nat.max a b := by
          intro a b
          simp [Nat.max_def]
          cases Decidable.em (a ≤ b)
          case inl h => simp [h]
          case inr h => simp [h]
        have max_help_right : ∀ a b : Nat, b ≤ Nat.max a b := by
          intro a b
          simp [Nat.max_def]
          split -- seems to be the same as the following above: cases Decidable.em (a ≤ b)
          case isTrue h => simp [h]
          case isFalse h => apply Nat.le_of_lt; apply Nat.lt_of_succ_le; rw [← Nat.not_le_eq]; exact h
        have help_i : i ≤ Nat.max i j := by apply max_help_left
        have help_j : j ≤ Nat.max i j := by apply max_help_right

        unfold Option.is_some_and
        split
        case h_1 heq =>
          simp [Nat.max_def] at heq
          split at heq
          . rw [heq] at hj
            simp [Option.is_some_and] at hj
          . rw [heq] at hi
            simp [Option.is_some_and] at hi

        case h_2 heq =>
          simp
          rw [Set.union_subset_iff_both_subset]
          constructor
          . unfold Option.is_some_and at hi
            split at hi
            . contradiction
            case h_2 a heq2 =>
              apply Set.subset_trans (b := a.fact)
              . intro e he
                simp [Set.element] at he
                rw [he]
                assumption
              . cases Nat.le.dest help_i with | intro m hm =>
                have subsOfAllFollowing := chaseBranchSetIsSubsetOfAllFollowing cb i m
                rw [heq2] at subsOfAllFollowing
                simp at subsOfAllFollowing
                rw [← hm] at heq
                rw [heq] at subsOfAllFollowing
                simp [Option.is_none_or] at subsOfAllFollowing
                exact subsOfAllFollowing
          . cases Nat.le.dest help_j with | intro m hm =>
              have subsOfAllFollowing := chaseBranchSetIsSubsetOfAllFollowing cb j m
              split at subsOfAllFollowing
              . rw [hm, heq] at subsOfAllFollowing; contradiction
              case h_2 heq2 =>
                rw [heq2] at hj
                simp [Option.is_some_and] at hj
                rw [← hm] at heq
                rw [heq] at subsOfAllFollowing
                simp [Option.is_none_or] at subsOfAllFollowing
                apply Set.subset_trans
                . exact hj
                . exact subsOfAllFollowing

theorem trgActiveForChaseResultMeansActiveAtSomeIndex (cb : ChaseBranch obs kb) : ∀ trg : Trigger obs, trg.active cb.result -> ∃ n : Nat, (cb.branch.infinite_list n).is_some_and (fun fs => trg.active fs.fact) := by
  intro trg
  unfold Trigger.active
  simp
  intro loaded active
  have trgLoadedForN := trgLoadedForChaseResultMeansLoadedAtSomeIndex cb trg loaded
  cases trgLoadedForN with | intro n loadedN =>
    exists n
    unfold Option.is_some_and
    split
    case h_1 heq => rw [heq] at loadedN; simp [Option.is_some_and] at loadedN
    case h_2 heq =>
      simp
      constructor
      . rw [heq] at loadedN; simp [Option.is_some_and] at loadedN; exact loadedN
      . intro contra
        apply active
        apply obs.monotone
        . have subsetOfResult := chaseBranchSetIsSubsetOfResult cb n
          rw [heq] at subsetOfResult
          simp [Option.is_none_or] at subsetOfResult
          apply subsetOfResult
        . apply contra

theorem funcTermForExisVarInChaseTreeMeansTriggerIsUsed (ct : ChaseTree obs kb) (trg : RTrigger obs kb.rules) (result_index : Fin trg.val.mapped_head.length) (var : sig.V) (node : ChaseNode obs kb.rules) (node_path : List Nat) : some node = ct.tree.get node_path ∧ (¬ var ∈ trg.val.rule.frontier) ∧ (∃ f: Fact sig, f ∈ node.fact ∧ (trg.val.apply_to_var_or_const result_index (VarOrConst.var var)) ∈ f.terms) -> ∃ drop_number : Fin node_path.length, (ct.tree.get (node_path.drop drop_number.val)).is_some_and (fun prev_node => prev_node.origin.is_some_and (fun origin => trg.equiv origin.fst ∧ result_index.val = origin.snd.val)) := by
  intro ⟨node_is_at_path, var_not_in_frontier, exis_f⟩
  induction node_path generalizing node with
  | nil =>
    cases exis_f with | intro f hf =>
      let ⟨f_in_db, functional_term_in_f⟩ := hf
      rw [ct.database_first] at node_is_at_path
      injection node_is_at_path with node_is_at_path
      rw [node_is_at_path] at f_in_db
      simp only at f_in_db
      have isFunctionFree := kb.db.toFactSet.property.right
      specialize isFunctionFree _ f_in_db
      specialize isFunctionFree (trg.val.apply_to_var_or_const (result_index.val) (VarOrConst.var var)) functional_term_in_f
      rcases isFunctionFree with ⟨c, isFunctionFree⟩
      simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, var_not_in_frontier, GroundTerm.const, GroundTerm.func] at isFunctionFree
  | cons head tail ih =>
    cases eq : ct.tree.get tail with
    | none =>
      apply False.elim
      apply ct.tree.tree.no_orphans (head::tail) _ ⟨tail, by exists [head]⟩
      unfold FiniteDegreeTree.get at eq
      unfold PossiblyInfiniteTree.get at eq
      exact eq
      unfold FiniteDegreeTree.get at node_is_at_path
      unfold PossiblyInfiniteTree.get at node_is_at_path
      rw [← node_is_at_path]
      simp
    | some tail_node =>
      -- TODO: this should actually be decidable but we need to change the implementation for this
      cases Classical.em (∃ f: Fact sig, f ∈ tail_node.fact ∧ (trg.val.subs.apply_skolem_term (VarOrConst.skolemize trg.val.rule.id result_index.val trg.val.rule.frontier (VarOrConst.var var))) ∈ f.terms) with
      | inl f_in_j =>
        cases ih tail_node (Eq.symm eq) f_in_j with | intro k _ =>
          exists ⟨k+1, by simp⟩
      | inr f_not_in_j =>
        exists ⟨0, by simp⟩
        simp [Option.is_some_and]
        rw [← node_is_at_path]
        simp
        have triggers_exist := ct.triggers_exist tail
        rw [eq] at triggers_exist
        simp [Option.is_none_or] at triggers_exist
        cases triggers_exist with
        | inr no_trg_ex =>
          unfold not_exists_trigger_list at no_trg_ex
          have : ct.tree.get (head::tail) = none := by
            apply ct.tree.each_successor_none_of_children_empty
            exact no_trg_ex.right
          rw [this] at node_is_at_path
          simp at node_is_at_path
        | inl trg_ex =>
          unfold exists_trigger_list at trg_ex
          cases trg_ex with | intro trg' htrg' =>
            have head_lt_tail_children_length : head < (ct.tree.children tail).length := by
              apply Decidable.byContradiction
              intro contra
              have : none = (ct.tree.children tail)[head]? := by
                simp at contra
                apply Eq.symm
                apply List.getElem?_eq_none
                exact contra
              rw [FiniteDegreeTree.getElem_children_eq_getElem_lifted_children] at this
              rw [PossiblyInfiniteTree.getElem_children_eq_get] at this
              unfold FiniteDegreeTree.get at node_is_at_path
              rw [← node_is_at_path] at this
              contradiction
            have head_lt_aux_1 : head < trg'.val.mapped_head.length := by rw [← htrg'.right] at head_lt_tail_children_length; simp [List.length_enum_with_lt] at head_lt_tail_children_length; exact head_lt_tail_children_length
            have head_lt_aux_2 : head < trg'.val.rule.head.length := by rw [← htrg'.right] at head_lt_tail_children_length; simp [List.length_enum_with_lt] at head_lt_tail_children_length; rw [← PreTrigger.length_mapped_head]; exact head_lt_tail_children_length

            rw [← ct.tree.getElem_children_eq_get tail ⟨head, head_lt_tail_children_length⟩] at node_is_at_path
            injection node_is_at_path with node_is_at_path

            have : ∃ f, f ∈ trg'.val.mapped_head[head] ∧ (trg.val.apply_to_var_or_const result_index (VarOrConst.var var)) ∈ f.terms := by
              cases exis_f with | intro f hf =>
                exists f
                constructor
                . have f_in_next_step := hf.left
                  rw [node_is_at_path] at f_in_next_step
                  simp [← htrg'.right] at f_in_next_step
                  cases f_in_next_step with
                  | inr f_in_result =>
                    rw [List.enum_with_lt_getElem_snd_eq_getElem, List.mem_toSet] at f_in_result
                    assumption
                  | inl f_in_j =>
                    apply False.elim
                    apply f_not_in_j
                    exists f
                    constructor
                    exact f_in_j
                    exact hf.right
                . exact hf.right

            have : ∃ var2, ¬ var2 ∈ trg'.val.rule.frontier ∧ (trg.val.apply_to_var_or_const result_index (VarOrConst.var var)) = (trg'.val.apply_to_var_or_const head (VarOrConst.var var2)) := by
              cases this with | intro f hf =>
                have ⟨f_in_res, apply_var_in_f_terms⟩ := hf

                let term_for_f := trg'.val.var_or_const_for_result_term ⟨head, head_lt_aux_1⟩ f_in_res apply_var_in_f_terms
                have h_term_for_f := trg'.val.apply_on_var_or_const_for_result_term_is_term ⟨head, head_lt_aux_1⟩ f_in_res apply_var_in_f_terms

                cases eq : term_for_f with
                | const c =>
                  apply False.elim
                  have contra := h_term_for_f
                  unfold term_for_f at eq
                  rw [eq, PreTrigger.apply_to_var_or_const_for_const] at contra
                  rw [trg.val.apply_to_var_or_const_non_frontier_var result_index _ var_not_in_frontier] at contra
                  simp [PreTrigger.functional_term_for_var, GroundTerm.const, GroundTerm.func] at contra
                | var v =>
                  exists v
                  unfold term_for_f at eq
                  rw [eq] at h_term_for_f
                  constructor
                  . intro contra
                    apply f_not_in_j
                    rcases trg'.val.rule.frontier_occurs_in_body v contra with ⟨body_atom, contra'⟩
                    exists (trg'.val.subs.apply_function_free_atom body_atom)
                    constructor
                    . have trg'_loaded := htrg'.left.left
                      apply trg'_loaded
                      rw [List.mem_toSet]
                      unfold PreTrigger.mapped_body
                      unfold GroundSubstitution.apply_function_free_conj
                      apply List.mem_map_of_mem
                      exact contra'.left
                    . conv at h_term_for_f => right; unfold PreTrigger.apply_to_var_or_const; unfold PreTrigger.skolemize_var_or_const; rw [Function.comp_apply]
                      rw [← h_term_for_f]
                      rw [trg'.val.apply_to_var_or_const_frontier_var head v contra]
                      unfold GroundSubstitution.apply_function_free_atom
                      rw [List.mem_map]
                      exists VarOrConst.var v
                      simp [GroundSubstitution.apply_var_or_const, contra']
                  . rw [h_term_for_f]

            have : trg.equiv trg' ∧ result_index.val = head := by
              cases this with | intro var2 hvar2 =>
                apply RTrigger.funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame trg trg' ⟨result_index.val, by rw [← PreTrigger.length_mapped_head]; exact result_index.isLt⟩ ⟨head, head_lt_aux_2⟩
                apply var_not_in_frontier
                apply hvar2.left
                apply hvar2.right

            simp [← htrg'.right] at node_is_at_path
            rw [node_is_at_path]
            simp
            rw [List.enum_with_lt_getElem_fst_eq_index head_lt_aux_1]
            exact this

theorem funcTermForExisVarInChaseTreeMeansTriggerResultOccurs (ct : ChaseTree obs kb) (trg : RTrigger obs kb.rules) (result_index : Fin trg.val.mapped_head.length) (var : sig.V) (node : ChaseNode obs kb.rules) (node_path : List Nat) : (some node = ct.tree.get node_path) ∧ (¬ var ∈ trg.val.rule.frontier) ∧ (∃ (f : Fact sig), f ∈ node.fact ∧ (trg.val.apply_to_var_or_const result_index (VarOrConst.var var)) ∈ f.terms) -> trg.val.mapped_head[result_index.val].toSet ⊆ node.fact := by
  intro h
  have node_is_at_path := h.left
  cases funcTermForExisVarInChaseTreeMeansTriggerIsUsed ct trg result_index var node node_path h with | intro drop_number h =>
    cases eq : ct.tree.get (node_path.drop drop_number) with
    | none => rw [eq] at h; simp [Option.is_some_and] at h
    | some prev_node =>
      rw [eq] at h; simp [Option.is_some_and] at h
      have : trg.val.mapped_head[result_index.val].toSet ⊆ prev_node.fact := by
        cases eq : prev_node.origin with
        | none => simp [eq] at h
        | some origin =>
          have fact_contains_origin_result := prev_node.fact_contains_origin_result
          simp [eq] at h
          rw [eq] at fact_contains_origin_result
          simp [Option.is_none_or] at fact_contains_origin_result
          simp [h.right]
          unfold RTrigger.equiv at h
          simp [PreTrigger.result_eq_of_equiv _ _ h.left]
          exact fact_contains_origin_result

      apply Set.subset_trans
      . exact this
      . have subsetAllFollowing := chaseTreeSetIsSubsetOfAllFollowing ct (node_path.drop drop_number) (node_path.take drop_number)
        rw [eq] at subsetAllFollowing
        rw [List.take_append_drop] at subsetAllFollowing
        rw [← node_is_at_path] at subsetAllFollowing
        simp [Option.is_none_or] at subsetAllFollowing
        exact subsetAllFollowing

theorem chaseBranchResultModelsKb (cb : ChaseBranch obs kb) : cb.result.modelsKb kb := by
  constructor
  . unfold FactSet.modelsDb
    unfold ChaseBranch.result
    intro f h
    exists 0
    rw [cb.database_first]
    simp [Option.is_some_and]
    exact h
  . unfold FactSet.modelsRules
    intro r h
    unfold FactSet.modelsRule
    simp
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

    cases (trgActiveForChaseResultMeansActiveAtSomeIndex cb trg ⟨trg_loaded, trg_not_obsolete⟩) with | intro i active_i =>
      have not_active_eventually := cb.fairness ⟨trg, by apply h⟩
      cases not_active_eventually with | intro j not_active =>
        have not_active_j := not_active.left
        simp [Trigger.active] at not_active_j
        unfold Option.is_some_and at not_active_j
        split at not_active_j
        . contradiction
        case h_2 heq =>
          have obsolete_j := not_active_j (by
            simp [PreTrigger.loaded]
            unfold Option.is_some_and at active_i
            cases eq : cb.branch.infinite_list i with
            | none => rw [eq] at active_i; simp at active_i
            | some step_i =>
              rw [eq] at active_i; simp at active_i
              apply Set.subset_trans
              . apply active_i.left
              . cases Decidable.em (i ≤ j) with
                | inl j_ge_i =>
                  cases Nat.le.dest j_ge_i with | intro m hm =>
                    have step_i_subs_following := chaseBranchSetIsSubsetOfAllFollowing cb i m
                    rw [eq] at step_i_subs_following
                    simp at step_i_subs_following
                    rw [hm, heq] at step_i_subs_following
                    simp [Option.is_none_or] at step_i_subs_following
                    exact step_i_subs_following
                | inr h =>
                  have h : j < i := Nat.lt_of_not_le h
                  have contra := not_active.right i h
                  rw [eq] at contra
                  simp [Option.is_none_or] at contra
                  contradiction
          )
          apply trg_not_obsolete
          apply obs.monotone
          have step_j_subs_result := chaseBranchSetIsSubsetOfResult cb j
          rw [heq] at step_j_subs_result
          simp [Option.is_none_or] at step_j_subs_result
          exact step_j_subs_result
          exact obsolete_j

theorem chaseTreeResultModelsKb (ct : ChaseTree obs kb) : ∀ fs, fs ∈ ct.result -> fs.modelsKb kb := by
  intro fs is_result
  unfold Set.element at is_result
  unfold ChaseTree.result at is_result
  cases is_result with | intro branch h =>
    rw [← h.right]
    apply chaseBranchResultModelsKb

