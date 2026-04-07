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

import ExistentialRules.ChaseSequence.CoreChase.Util
import ExistentialRules.ChaseSequence.CoreChase.Basic
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseNode
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


namespace CoreChaseBranch

  def terminates (cb : CoreChaseBranch kb) : Prop :=
    ∃ n, (cb.branch.infinite_list n = none)

  def terminates_at_step (cb : CoreChaseBranch kb) (n : Nat) : Prop :=
    (cb.branch.infinite_list n) ≠ none ∧ (cb.branch.infinite_list (n+1) = none)

  def terminates' (cb : CoreChaseBranch kb) : Prop :=
    ∃ n, terminates_at_step cb n

  @[grind]
  theorem terminatesIfTerminates' (cb : CoreChaseBranch kb) : cb.terminates' → cb.terminates := by
    intro ⟨n, a, b⟩
    exists (n + 1)

  @[grind]
  theorem terminates'IfTerminatesAndNonEmpty (cb : CoreChaseBranch kb) (non_empty : ∃ m, cb.branch.infinite_list m ≠ none) : cb.terminates → cb.terminates' := by
    intro ⟨n, a⟩
    rcases non_empty with ⟨m, c⟩
    -- n yielded from terminates, thus (n ≥ m)
    induction d : (n - m) generalizing n with
      | zero =>
        have ngt : m > n ∨ m = n := by grind
        cases ngt with
          | inl case =>
            have := cb.branch.get?_eq_none_of_le_of_eq_none a m (Nat.le_of_lt case)
            simp only [PossiblyInfiniteList.get?, InfiniteList.get] at this
            rw [this] at c
            simp at c
          | inr case =>
            rw [case] at c
            contradiction
      | succ n' ih =>
        specialize ih (n' + m)
        by_cases case : (cb.branch.infinite_list (n' + m) = none)
        grind
        have x : n = (n' + m) + 1 := by grind
        exists n' + m
        unfold terminates_at_step
        constructor
        exact case
        grind

  def last_element_index_rec  (cb : CoreChaseBranch kb) (ter' : cb.terminates') (n : Nat) : Nat :=
    match eq : cb.branch.infinite_list n with
      | none => n - 1
      | some cn =>
        have : Classical.choose ter' + 1 - (n + 1) < Classical.choose ter' + 1 - n := by
          apply Nat.sub_succ_lt_self
          let n_max := Classical.choose ter'
          have not_none := Classical.choose_spec ter'
          have lt : n ≤ n_max := by
            apply Classical.byContradiction
            intro contra
            have gt : n > n_max := by grind
            have lt_is_some : ∀ m, m ≤ n → cb.branch.infinite_list m ≠ none := by grind
            apply lt_is_some (n_max + 1)
            exact gt
            exact not_none.right
          exact Nat.lt_add_one_of_le lt
        last_element_index_rec cb ter' (n+1)
      termination_by Classical.choose ter' + 1 - n

  def last_element_index (cb : CoreChaseBranch kb) (ter' : cb.terminates') : Nat := last_element_index_rec cb ter' 0

  @[grind]
  theorem last_element_index_eq_termintes'_index_leq (cb : CoreChaseBranch kb) (n : Nat) (term_at_n : cb.terminates_at_step n) : ∀ m, m ≤ n → last_element_index_rec cb (by exists n) m = n := by
    intro m m_leq
    have ter : cb.terminates := terminatesIfTerminates' cb (Exists.intro n term_at_n)
    rcases term_at_n with ⟨lhs, rhs⟩
    have ter' : cb.terminates' := Exists.intro n ⟨lhs, rhs⟩
    unfold last_element_index_rec
    induction d : (n - m) generalizing m with
      | zero =>
        have eq : m = n := by grind
        rw [eq]
        split
        next => contradiction
        next =>
          unfold last_element_index_rec
          split
          next => simp
          next x cn heq =>
            rw [rhs] at heq
            contradiction
      | succ n' ih =>
        specialize ih (m + 1)
        -- m = - n' -1 + n < n
        split
        next => grind
        next x cn heq =>
          unfold last_element_index_rec
          rw [ih]
          grind
          grind

  @[grind]
  theorem last_element_index_eq_termintes'_index (cb : CoreChaseBranch kb) (n : Nat) (term_at_n : cb.terminates_at_step n) : last_element_index cb (by exists n) = n := by
    apply last_element_index_eq_termintes'_index_leq
    exact term_at_n
    exact Nat.zero_le n

  @[grind]
  theorem terminates'_at_last_index_ter' (cb : CoreChaseBranch kb) (ter' : cb.terminates') : cb.terminates_at_step (last_element_index cb ter') := by
    rcases ter' with ⟨n, is_some, is_none⟩
    grind

  @[grind]
  theorem last_index_is_some (cb : CoreChaseBranch kb) (ter' : cb.terminates') : cb.branch.infinite_list (cb.last_element_index ter') ≠ none := by
    rcases ter' with ⟨n, term_at_n⟩
    have := last_element_index_eq_termintes'_index cb n term_at_n
    rw [this]
    exact term_at_n.left

  def last_node (cb : CoreChaseBranch kb) (ter' : cb.terminates') : CoreChaseNode kb.rules :=
    (cb.branch.infinite_list (last_element_index cb ter')).get (by
      have := last_index_is_some cb ter'
      exact Option.isSome_iff_ne_none.mpr this
      )

  def result (cb : CoreChaseBranch kb) (ter' : cb.terminates') : FactSet sig :=
    ((cb.branch.infinite_list (last_element_index cb ter')).get (by
      have := last_index_is_some cb ter'
      exact Option.isSome_iff_ne_none.mpr this
      )).core

  @[grind]
  theorem terminating_eq_index (cb : CoreChaseBranch kb) (m n : Nat) : ((cb.branch.infinite_list n) ≠ none ∧ (cb.branch.infinite_list (n+1) = none) ∧ (cb.branch.infinite_list m) ≠ none ∧ (cb.branch.infinite_list (m+1) = none)) → m = n := by
    rintro ⟨h1, h2, h3, h4⟩
    apply Classical.byContradiction
    intro contra
    have : m > n ∨ m < n := by exact Nat.lt_or_gt_of_ne fun a => contra (id (Eq.symm a))
    rcases this with gt | lt
    have : ∃ k, n + k = m := by
      apply Nat.le.dest
      apply Nat.le_of_lt
      exact gt
    rcases this with ⟨k, add⟩
    induction k with
      | zero =>
        simp only [Nat.add_zero] at add
        rw [add] at contra
        contradiction
      | succ k ih =>
        apply h3
        rw [← add]
        rw [← Nat.add_assoc]
        apply succ_is_none_if_is_none cb (n + 1) h2 (n + k + 1) (by grind)
    have : ∃ k, m + k = n := by
      apply Nat.le.dest
      apply Nat.le_of_lt
      exact lt
    rcases this with ⟨k, add⟩
    induction k with
      | zero =>
        simp only [Nat.add_zero] at add
        rw [add] at contra
        contradiction
      | succ k ih =>
        apply h1
        rw [← add]
        rw [← Nat.add_assoc]
        apply succ_is_none_if_is_none cb (m + 1) h4 (m + k + 1) (by grind)

  @[grind]
  theorem terminating_has_last_index_core (cb : CoreChaseBranch kb) : cb.terminates ↔ ∃ n, (cb.branch.infinite_list n) ≠ none ∧ ∀ m, m > n -> cb.branch.infinite_list m = none := by
  unfold CoreChaseBranch.terminates
  constructor
  . intro h
    rcases h with ⟨n, h⟩
    induction n with
    | zero => rw [cb.database_first] at h; simp at h
    | succ n ih =>
      cases eq : cb.branch.infinite_list n with
      | none => apply ih; exact eq
      | some _ =>
        exists n
        rw [eq]
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, gt_iff_lt, true_and]
        intro m n_lt_m
        have : n+1 ≤ m := by apply Nat.succ_le_of_lt; exact n_lt_m
        rw [Nat.le_iff_lt_or_eq] at this
        cases this with
        | inr n_eq_m => rw [← n_eq_m]; exact h
        | inl n_lt_m =>
          have no_holes := cb.branch.no_holes
          apply Option.decidableEqNone.byContradiction
          intro contra
          have := cb.branch.get?_eq_none_of_le_of_eq_none h m (Nat.le_of_lt n_lt_m)
          simp only [PossiblyInfiniteList.get?, InfiniteList.get] at this
          rw [this] at contra
          simp at contra
  . intro h
    rcases h with ⟨n, _, h⟩
    exists n+1
    apply h
    simp only [gt_iff_lt, Nat.lt_add_one]

  @[grind]
  theorem exLastNodeOfTerminatingCoreChaseBranch (cb : CoreChaseBranch kb) (ter' : cb.terminates') : ∃ cn, cn = cb.last_node ter' := by
    exists cb.last_node ter'

  @[grind]
  theorem exResultOfTerminatingCoreChaseBranch (cb : CoreChaseBranch kb) (ter' : cb.terminates') : ∃ fs, fs = cb.result ter' := by
    exists cb.result ter'

  @[grind]
  theorem coreChaseResultIsCore (cb : CoreChaseBranch kb) (ter' : cb.terminates') : (cb.result ter').isWeakCore := by
    unfold CoreChaseBranch.result
    have : ∃ cn, cn = cb.last_node ter' := by exact exLastNodeOfTerminatingCoreChaseBranch cb ter'
    rcases this with ⟨cn, cn_last⟩
    unfold CoreChaseBranch.last_node at cn_last
    rw [← cn_last]
    rcases cn with ⟨_,_,_,is_core,_,_,_⟩
    exact is_core

  @[grind]
    theorem all_succ_of_last_index_none (cb : CoreChaseBranch kb) (n : Nat) (term_at_n : cb.terminates_at_step n) : ∀ m, m > n → cb.branch.infinite_list m = none := by
      intro m gt
      rcases term_at_n with ⟨is_some, is_none⟩
      exact succ_eq_is_none_if_is_none cb (n + 1) is_none m gt

  @[grind]
  theorem exLastNodeWithLastIndexIfTerminates' (cb : CoreChaseBranch kb) (ter' : cb.terminates') : ∃ last_cn, cb.branch.infinite_list (cb.last_element_index ter') = some last_cn := by
    exists cb.last_node ter'
    unfold last_node
    exact Option.eq_some_of_isSome (by
      have := last_index_is_some cb ter'
      exact Option.isSome_iff_ne_none.mpr this
      )

  theorem neqTerminates'IfCbAllSome (cb : CoreChaseBranch kb) : (∀ (n : Nat), (cb.branch.infinite_list n).isSome) → ¬ cb.terminates' := by
    intro all_some ⟨n, ⟨n_some, n_succ_none⟩⟩
    specialize all_some (n + 1)
    rw [Option.isSomeIffNeqNone] at all_some
    contradiction

  @[grind]
  theorem neqTerminatesIffCbAllSome (cb : CoreChaseBranch kb) : (∀ (n : Nat), (cb.branch.infinite_list n).isSome) ↔ ¬ cb.terminates := by
    constructor
    intro all_some ⟨n, n_none⟩
    specialize all_some n
    rw [Option.isSomeIffNeqNone] at all_some
    contradiction
    unfold terminates
    intro n_ter
    simp only [not_exists, ne_eq] at n_ter
    intro n
    specialize n_ter n
    rw [Option.isSomeIffNeqNone]
    exact n_ter


      -- this one or the one below this is superfluous
  theorem result_finite_if_cb_terminates2 (cb : CoreChaseBranch kb) (ter' : cb.terminates') : Set.finite (cb.result ter') := by
    have : ∃ cn, cn = cb.last_node ter' := by exact exLastNodeOfTerminatingCoreChaseBranch cb ter'
    rcases this with ⟨cn, cn_eq⟩
    rcases ter' with ⟨n, term_at_n⟩
    have := CoreChaseBranch.all_core_finite cn
    unfold result
    exact all_core_finite ((cb.branch.infinite_list (cb.last_element_index (Exists.intro n term_at_n))).get (by
      have := last_index_is_some cb (Exists.intro n term_at_n)
      exact Option.isSome_iff_ne_none.mpr this
      ))

  @[grind]
  theorem result_finite_if_cb_terminates (cb : CoreChaseBranch kb) (ter' : cb.terminates') : Set.finite (cb.result ter') := by
    have : ∃ cn, cn = cb.last_node ter' := by exact exLastNodeOfTerminatingCoreChaseBranch cb ter'
    rcases this with ⟨cn, cn_eq⟩
    unfold last_node at cn_eq
    exact result_finite_if_cb_terminates2 cb ter'

  @[grind]
  theorem resultIsSome (cb : CoreChaseBranch kb) (ter' : cb.terminates') : cb.branch.infinite_list (cb.last_element_index ter') = some (cb.last_node ter') := by
    unfold last_element_index last_node
    exact Option.eq_some_of_isSome (by
      have := last_index_is_some cb ter'
      exact Option.isSome_iff_ne_none.mpr this
      )

  --have c : CoreChaseNode kb.rules := {fs := sorry, fs_fin:=sorry,core:=sorry,is_core:=sorry,core_sse:=sorry,origin:=sorry,fs_contains_origin_result:=sorry}

  @[grind]
  theorem cbNoneAfterLastIndex (cb : CoreChaseBranch kb) (ter' : cb.terminates') : cb.branch.infinite_list ((cb.last_element_index ter') + 1) = none := by
    apply Classical.byContradiction
    rcases ter' with ⟨n_ter, n_ter_at⟩
    intro contra
    induction n_ter with
      | zero =>
        grind
      | succ n_ter ih =>
        grind

  @[grind]
  theorem cbDbSubsetResult (cb : CoreChaseBranch kb) (ter' : cb.terminates') : (kb.db.toFactSet.val ⊆ cb.result ter') := by
    let init_node := (cb.branch.infinite_list 0).get (Option.isSome_of_mem cb.database_first)
    rcases (exLastNodeWithLastIndexIfTerminates' cb ter') with ⟨last_node, last_node_eq⟩
    have t := CoreChaseBranch.cbDbInAllSucc cb (cb.last_element_index ter') init_node last_node (by grind)
    intro f f_in
    let := cb.database_first
    have eq : init_node.fs = kb.db.toFactSet.val := by simp_all only [Option.get_some, init_node]
    specialize t last_node_eq f (by grind)
    rw [result]
    grind

  theorem coreChaseResultModelsKb (cb : CoreChaseBranch kb) (ter' : cb.terminates') : (cb.result ter').modelsKb kb := by
    constructor
    intro f f_in
    unfold result
    have last_index := (cb.last_element_index ter')
    have := CoreChaseBranch.cbDbSubsetResult cb ter'
    exact this f f_in

    intro r r_in gs sub
    apply Classical.byContradiction
    intro subs_not_obsolete
    let trg : Trigger obs.toLaxObsoletenessCondition := ⟨r, gs⟩
    have trg_loaded : trg.loaded (cb.result ter') := by apply sub
    have trg_not_obsolete : ¬ obs.cond trg (cb.result ter') := by
      intro contra
      have obs_impl_sat := obs.cond_implies_trg_is_satisfied contra
      apply subs_not_obsolete
      rcases obs_impl_sat with ⟨i, s', obs_impl_sat⟩
      exists i

    have ex_next_node := exNextNodeIfExLoadedNonObsoleteTrigger cb (cb.last_element_index ter') (cb.last_node ter') (resultIsSome cb ter') ⟨trg, r_in⟩ sub trg_not_obsolete
    grind
    -- entweder gibt es active trigger in result, dann muss es aber eine nachfolger node geben → contradiction to termainates at result
    -- es gibt keine active trigger → models ist trivial erfüllt



end CoreChaseBranch
