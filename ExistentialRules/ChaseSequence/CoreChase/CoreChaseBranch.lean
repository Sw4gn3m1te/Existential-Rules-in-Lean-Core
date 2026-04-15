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
import ExistentialRules.ChaseSequence.CoreChase.Basic


import ExistentialRules.ChaseSequence.CoreChase.CoreChaseNode


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}

theorem exFactIfExTerm (kb : KnowledgeBase sig) (t : GroundTerm sig) : t ∈ kb.db.toFactSet.val.terms → ∃ f, f ∈ kb.db.toFactSet.val := by
  intro ⟨f, f_in_fs, f_in_ter⟩
  exists f

@[grind .]
theorem eachKbDbIsWeakCore (kb : KnowledgeBase sig) : kb.db.toFactSet.val.isWeakCore := by
  let db := kb.db
  let fs := db.val
  intro gtm gtm_hom
  constructor
  · intro f gt h contra
    have eq : gtm.applyFact f = f := by
      unfold GroundTermMapping.applyFact
      rw [GeneralizedAtom.mk.injEq]
      constructor
      · rfl
      · apply List.map_id_of_id_on_all_mem
        intro e e_in
        unfold GroundTermMapping.isHomomorphism at gtm_hom
        specialize gt e e_in
        rcases gt with ⟨f2, f2_mem, e_mem⟩
        have db_funfree := kb.db.toFactSet.property.right
        specialize db_funfree f2 f2_mem e e_mem
        rcases db_funfree with ⟨c, c_eq⟩
        rw [c_eq]
        exact @gtm_hom.left c
    rw [eq] at contra
    · contradiction
  -- id is injective
  intro a b a_in b_in eq
  have a_mem : ∃ fa, fa ∈ kb.db.toFactSet.val := exFactIfExTerm kb a a_in
  rcases a_mem with ⟨fa, fa_in⟩
  have gtm_eq : ∀ f, f ∈ kb.db.toFactSet.val → gtm.applyFact f = f := by exact fun f a => GroundTermMapping.hom_on_db_id f gtm gtm_hom a
  specialize gtm_eq fa fa_in
  have gt_eq : ∀ t, t ∈ kb.db.toFactSet.val.terms → gtm t = t := by exact fun t a => GroundTermMapping.hom_on_db_term_id t gtm gtm_hom a
  rw [gt_eq, gt_eq] at eq
  exact eq
  exact b_in
  exact a_in

def exists_trigger_opt_fs_core (rules : RuleSet sig) (before : CoreChaseNode rules) (after : Option (CoreChaseNode rules)) : Prop :=
  ∀ node ∈ after,
  ∃ trg : (RTrigger (obs.toLaxObsolescenceCondition) rules),
  -- ∃ (c : FactSet sig),
  ∃ (i : Fin trg.val.mapped_head.length),

    let fs : FactSet sig := before.core ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet

    have fs_fin : fs.finite := by
      apply Set.union_finite_of_both_finite
      exact CoreChaseNode.core_finite_if_fs_finite before before.fs_fin
      exact List.finite_toSet trg.val.mapped_head[↑i]

    have ex_wc : ∃ (wc: FactSet sig), wc.isWeakCore ∧ wc.homSubset fs := fs.exists_weak_core_for_finite_set fs_fin

    node = {
      fs := fs
      fs_fin := fs_fin
      core := Classical.choose ex_wc
      is_core := (Classical.choose_spec ex_wc).left
      core_sse := (Classical.choose_spec ex_wc).right
      origin := some ⟨trg, i⟩
      fs_contains_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
    }

structure CoreChaseBranch (kb: KnowledgeBase sig) where
  branch : PossiblyInfiniteList (CoreChaseNode kb.rules)
  database_first : branch.get? 0 = some {
    fs := kb.db.toFactSet
    fs_fin := kb.db.toFactSet.property.left
    core := kb.db.toFactSet
    is_core := eachKbDbIsWeakCore kb
    core_sse := by
      constructor
      · exact Set.subset_refl
      · exists id
        exact GroundTermMapping.id_is_hom
    origin := none,
    fs_contains_origin_result := by simp
  }

  triggers_active : ∀ (n : Nat), ∀ before ∈ branch.get? n, ∀ after ∈ branch.get? (n+1), ∃ o ∈ after.origin, o.fst.val.active before.core

  triggers_exist : ∀ n : Nat, ∀ before ∈ branch.get? n,
    let after := branch.get? (n+1)
    (exists_trigger_opt_fs_core kb.rules before after)

  fairness : ∀ trg : (RTrigger obs.toLaxObsolescenceCondition kb.rules), ∃ (i : Nat), (∃ node ∈ branch.get? i, ¬ trg.val.active node.fs)
    ∧ (∀ (j : Nat), j > i → ∀ node2  ∈ branch.get? j, ¬ trg.val.active node2.fs)


namespace CoreChaseBranch

  instance : Membership (CoreChaseNode kb.rules) (CoreChaseBranch kb) where
  mem cd node := node ∈ cd.branch

  theorem mem_iff {cd : CoreChaseBranch kb} : ∀ {e}, e ∈ cd ↔ ∃ n, cd.branch.get? n = some e := by rfl

  def head (cb : CoreChaseBranch kb) : CoreChaseNode kb.rules := cb.branch.head.get (Option.isSome_of_mem cb.database_first)

  def next (cb : CoreChaseBranch kb) : Option (CoreChaseNode kb.rules) := cb.branch.tail.head

  def IsSuffix (cb1 cb2 : CoreChaseBranch kb) : Prop := cb1.branch <:+ cb2.branch
  infixl:50 " <:+ " => IsSuffix

  def predecessor {cb1 : CoreChaseBranch kb} (cn1 cn2 : CoreChaseNode kb.rules) : Prop := ∃ cb2, cb2 <:+ cb1 ∧ cb2.head = cn1 ∧ cn2 ∈ cb2
  infixl:50 " ≼ " => predecessor

  def strict_predecessor {cb : CoreChaseBranch kb} (cn1 cn2 : CoreChaseNode kb.rules) : Prop := @CoreChaseBranch.predecessor _ _ _ _ _ cb cn1 cn2 ∧ cn1 ≠ cn2
  infixl:50 " ≺ " => strict_predecessor

  @[grind <-]
  theorem head_mem {cb : CoreChaseBranch kb} : cb.head ∈ cb := by exists 0; simp [head, PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?]

  @[grind ->]
  theorem isSome_origin_next {cb : CoreChaseBranch kb} {next : CoreChaseNode kb.rules} (eq : cb.next = some next) : next.origin.isSome := by
    have trg_ex := cb.triggers_exist 0 cb.head (by simp [head]; exact Eq.symm PossiblyInfiniteList.head_eq)
    specialize trg_ex _ eq
    rcases trg_ex with ⟨_, _, trg_ex⟩; rw [trg_ex]; simp

  @[grind ->]
  theorem active_trigger_origin_next {cb : CoreChaseBranch kb} {next : CoreChaseNode kb.rules} (eq : cb.next = some next) :
      (next.origin.get (cb.isSome_origin_next eq)).fst.val.active cb.head.fs := by
    have trg_act := cb.triggers_active 0 cb.head
      (by simp [CoreChaseBranch.head];exact Eq.symm PossiblyInfiniteList.head_eq) next
      (by simp [← eq, CoreChaseBranch.next];exact Eq.symm PossiblyInfiniteList.head_eq)
    rcases trg_act with ⟨orig, orig_mem, trg_act⟩
    rw [Option.mem_def] at orig_mem
    simp only [orig_mem, Option.get_some]
    have eq : cb.head.fs = cb.head.core := by sorry
    rw [eq]
    exact trg_act

  theorem active_trigger_origin_next_core {cb : CoreChaseBranch kb} {next : CoreChaseNode kb.rules} (eq : cb.next = some next) :
      (next.origin.get (cb.isSome_origin_next eq)).fst.val.active cb.head.core := by sorry


  /--------------------------------------------------------------------------------
  -/

  @[grind .]
  theorem mem_eq (cb : CoreChaseBranch kb) (cn1 cn2 : CoreChaseNode kb.rules) (n : Nat) (cn1_eq : cn1 ∈ cb.branch.get? n) (cn2_eq : cn2 ∈ cb.branch.get? n) : cn1 = cn2 := by
    rw [Option.mem_def] at cn1_eq cn2_eq
    grind

  @[grind .]
  theorem none_get_eq (cb : CoreChaseBranch kb) : cb.branch.infinite_list m = none ↔ cb.branch.get? m = none := Option.isSome_eq_isSome.mp rfl

  @[grind .]
  theorem all_prev_some_if_is_some (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? n).isSome) : ∀ m, m ≤ n → (cb.branch.get? m).isSome := by
    intro m leq
    grind

  @[grind .]
  theorem ex_prev_node_at_each_leq (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? n).isSome) : ∀ m, m ≤ n → ∃ cn, cn ∈ (cb.branch.get? m) := by
    intro m leq
    have := all_prev_some_if_is_some cb n is_some m leq
    exact Option.isSome_iff_exists.mp this

  @[grind .]
  theorem all_succ_none_if_none (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? n).isNone) : ∀ m, m ≥ n → (cb.branch.get? m).isNone := by
    intro m geq
    grind

  def prev_node (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? (n+1)).isSome) : CoreChaseNode kb.rules := by
    exact (cb.branch.get? n).get (by grind)

  @[grind .]
  theorem prev_node_eq (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? (n+1)).isSome) :
    cb.branch.get? n = some (cb.prev_node n is_some) := by
      simp [prev_node]

  @[grind .]
  theorem origin_isSome (cb : CoreChaseBranch kb) (n : Nat) {node : CoreChaseNode kb.rules} (eq : cb.branch.get? (n + 1) = node) : node.origin.isSome := by
    have ex_before := ex_prev_node_at_each_leq cb n (by grind) n (Nat.le_refl n)
    rcases ex_before with ⟨before, before_eq⟩
    have trg_ex := cb.triggers_exist n before before_eq node eq
    rcases trg_ex with ⟨trg, i, eq⟩
    grind


  /-
    node1 (n) ----> node2 (n + 1)
    ~.core      ⊆   ~.fs
    because ex trigger from n1 to n2 thus n2.fs = n1.core + trig.result thus n1.core ⊆ n2.fs
  -/

  -- replaces prevCoreSubsetOfFactset
  theorem before_core_sub_after_fs (cb : CoreChaseBranch kb) (n : Nat) (before after : CoreChaseNode kb.rules) (before_eq : before ∈ cb.branch.get? n) (after_eq : after ∈ cb.branch.get? (n + 1)) :
    before.core ⊆ after.fs := by
      have trg_ex := cb.triggers_exist n before before_eq after after_eq
      rcases trg_ex with ⟨trg, i, eq⟩
      simp at eq
      have eq : after.fs = before.core ∪ trg.val.mapped_head[↑i].toSet := by grind
      rw [eq]
      exact Set.subset_union_of_subset_left fun e a => a

  @[simp]
  theorem cb_fist_is_some (cb : CoreChaseBranch kb) : (cb.branch.get? 0).isSome := by
    exact Option.isSome_of_mem cb.database_first

  @[simp]
  theorem cb_first_fs_finite (cb : CoreChaseBranch kb) : ((cb.branch.get? 0).get (by simp)).fs.finite := ((cb.branch.get? 0).get (by simp)).fs_fin

  @[simp]
  theorem cb_first_core_finite (cb : CoreChaseBranch kb) : ((cb.branch.get? 0).get (by simp)).core.finite := CoreChaseNode.all_core_finite ((cb.branch.get? 0).get (by simp))

  @[grind .]
  theorem origin_result_finite {rules : RuleSet sig} (node : CoreChaseNode rules) (is_some : node.origin.isSome) : (node.origin_result is_some).toSet.finite := by
    apply Set.finite_of_list_with_same_elements (node.origin_result is_some)
    intro _; rw [List.mem_toSet]

  @[grind .]
  -- signature might be changed
  theorem origin_trg_is_active_prev_core (cb : CoreChaseBranch kb) (n : Nat) (after : CoreChaseNode kb.rules) (after_eq : after ∈ cb.branch.get? (n+1)) :
    let prev_node : CoreChaseNode kb.rules := cb.prev_node n (Option.isSome_of_mem after_eq)
    o ∈ after.origin → o.fst.val.active prev_node.core := by
      let prev_node : CoreChaseNode kb.rules := cb.prev_node n (Option.isSome_of_mem after_eq)
      have trg_ex := cb.triggers_exist n prev_node (by grind) after after_eq
      have trg_act := cb.triggers_active n prev_node (by grind) after after_eq
      grind

  @[grind .]
  theorem origin_trg_result_yields_next_node_fs (cb : CoreChaseBranch kb) (n : Nat) (node : CoreChaseNode kb.rules) (node_eq : node ∈ cb.branch.get? (n+1)) :
    let prev_node : CoreChaseNode kb.rules := cb.prev_node n (Option.isSome_of_mem node_eq)
    node.fs = prev_node.core ∪ (node.origin_result (cb.origin_isSome n node_eq)).toSet := by
      let prev_node : CoreChaseNode kb.rules := cb.prev_node n (Option.isSome_of_mem node_eq)
      have trg_ex := cb.triggers_exist n prev_node (by grind) node node_eq
      rcases trg_ex with ⟨i, c, eq⟩
      simp_all
      constructor

  @[grind .]
  -- all_fs_finite
  theorem all_fs_in_cb_finite (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (eq : cn ∈ cb.branch.get? n) : cn.fs.finite := by
    exact cn.fs_fin


  @[grind .]
  theorem exNextNodeIfExLoadedNonObsoleteTrigger (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cn ∈ cb.branch.get? n)
     (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (trg_loaded : trg.val.loaded cn.core) (trg_non_obs : ¬ obs.cond trg.val cn.core) :
        ∃ (cn' : CoreChaseNode kb.rules), cn' ∈ cb.branch.infinite_list (n+1) := by
          have trg_ex := cb.triggers_exist n cn cn_eq
          cases h : cb.branch.infinite_list (n+1) with
            | none =>
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


  theorem isSome_next_iff_trg_ex {cb : CoreChaseBranch kb} : cb.next.isSome ↔ ∃ (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules), trg.val.active cb.head.fs := by
    constructor
    . rw [Option.isSome_iff_exists]
      rintro ⟨next, eq⟩
      exists (next.origin.get (cb.isSome_origin_next eq)).fst
      exact active_trigger_origin_next eq
    . rintro ⟨trg, active⟩
      apply Decidable.byContradiction
      rw [Option.not_isSome_iff_eq_none]
      intro eq_none
      have fair := cb.fairness trg
      rcases cb.fairness trg with ⟨i, ⟨node, node_mem, not_active⟩, fair⟩
      cases i with
      | zero =>
        apply not_active
        have eq : cb.head = node := by unfold CoreChaseBranch.head; exact Option.get_of_eq_some (Option.isSome_of_mem cb.database_first) node_mem
        rw [← eq]
        exact active
      | succ i =>
        simp only [CoreChaseBranch.next, ← PossiblyInfiniteList.empty_iff_head_none] at eq_none
        rw [← PossiblyInfiniteList.get?_tail, eq_none] at node_mem
        simp at node_mem

  @[grind .]
  theorem cbNextFsEq (cb : CoreChaseBranch kb) (n : Nat) (a b : CoreChaseNode kb.rules) (eq_a : a ∈ cb.branch.get? n) (eq_b : b ∈ cb.branch.get? (n + 1)) :
    b.fs = (b.origin_result (origin_isSome cb n eq_b)).toSet ∪ a.core := by grind

  @[grind .]
  theorem next_step_finite_if_finite (cb : CoreChaseBranch kb) (n : Nat) (a b : CoreChaseNode kb.rules) (eq_a : cb.branch.infinite_list n = some a) (eq_b : cb.branch.infinite_list (n + 1) = some b) (a_fin : a.core.finite) :
    b.core.finite := by
      rcases a_fin with ⟨al, al_nodup, al_eq⟩
      have b_fs_eq := cbNextFsEq cb n a b eq_a eq_b
      apply CoreChaseNode.core_finite_if_fs_finite
      rw [b_fs_eq, ← Set.unionOfFinteIsFinte]
      constructor
      · exact origin_result_finite b (origin_isSome cb n eq_b)
      · exact Set.finite_of_list_with_same_elements al al_eq


  @[grind .]
  theorem allElemDbMappedId (cb : CoreChaseBranch kb) (init : CoreChaseNode kb.rules) (init_eq : init ∈  cb.branch.get? 0) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism init.fs fs2) :
    ∀ f, f ∈ init.fs → gtm.applyFact f = f := by
      intro f f_in
      unfold GroundTermMapping.applyFact
      rw [GeneralizedAtom.mk.injEq]
      constructor
      · rfl
      · apply List.map_id_of_id_on_all_mem
        intro gt gt_in
        unfold GroundTermMapping.isHomomorphism at gtm_hom
        have db_funfree := kb.db.toFactSet.property.right
        rw [cb.database_first] at init_eq
        simp only [Option.mem_def, Option.some.injEq] at init_eq
        rw [← init_eq] at f_in
        specialize db_funfree f f_in gt gt_in
        rcases db_funfree with ⟨c, c_eq⟩
        rw [c_eq]
        exact @gtm_hom.left c

  @[grind .]
  theorem ff_in_core_if_ff_in_fs (cb : CoreChaseBranch kb) (n : Nat) (x_eq : x ∈ cb.branch.get? n) (f : Fact sig) (f_in : f ∈ x.fs) (f_is_ff : f.isFunctionFree) : f ∈ x.core := by
      have ex_gtm := x.core_sse.right
      rcases ex_gtm with ⟨gtm, gtm_hom⟩
      have eq : gtm.applyFact f = f := GroundTermMapping.homApplyFactFunctionFreeId x.fs x.core f f_is_ff gtm gtm_hom
      have x_core := x.is_core
      rcases gtm_hom with ⟨gtm_c, gtm_st⟩
      specialize gtm_st f
      apply gtm_st
      exists f

  @[grind .]
  theorem allFfInNextFsIfSome (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : x ∈ cb.branch.get? n) :
    ∀ cn ∈ cb.branch.get? (n+1), ∀ f, f ∈ x.fs ∧ f.isFunctionFree → f ∈ cn.fs := by
      intro cn cn_eq f ⟨f_in, f_in_ff⟩
      have trg_ex := cb.triggers_exist n x x_eq cn cn_eq
      rcases trg_ex with ⟨c, i, h2⟩
      rcases h2 with ⟨lhs, rhs⟩
      grind

  @[grind .]
  theorem allFfInAllSuccIfSome (cb : CoreChaseBranch kb) (n m : Nat) (x : CoreChaseNode kb.rules) (x_eq : x ∈ cb.branch.get? n) :
     ∀ cn ∈ cb.branch.get? (n+m), ∀ f, f ∈ x.fs ∧ f.isFunctionFree → f ∈ cn.fs := by
      induction m with
        | zero =>
          simp only [Nat.add_zero, and_imp]
          intro cn_succ cn_succ_eq f f_in_fs f_is_ff
          have eq : x = cn_succ := mem_eq cb x cn_succ n x_eq cn_succ_eq
          subst eq
          exact f_in_fs
        | succ m ih =>
          intro cn_succ cn_succ_eq f ⟨f_in_fs, f_is_ff⟩
          have ex_cm : ∃ (cn_mid : CoreChaseNode kb.rules), cn_mid ∈ cb.branch.get? (n + m) :=
            cb.ex_prev_node_at_each_leq (n + m + 1) (Option.isSome_of_mem cn_succ_eq) (n + m) (Nat.le_add_right (n + m) 1)
          rcases ex_cm with ⟨cm, cm_eq⟩
          have := cb.triggers_exist (n + m) cm cm_eq cn_succ cn_succ_eq
          grind

  @[grind]
  theorem cbDbInAllSucc (cb : CoreChaseBranch kb) (n : Nat) (init cn : CoreChaseNode kb.rules) (init_eq : init ∈ cb.branch.get? 0) (cn_eq : cn ∈ cb.branch.get? n) :
    init.fs ⊆ cn.core := by
      have db_funfree := kb.db.toFactSet.property.right
      have init_eq' : init.fs = kb.db.toFactSet.val := by
        have := cb.database_first
        grind

      induction n generalizing cn with
        | zero =>
          intro f f_in
          have eq : cn = init := by simp_all
          exact ff_in_core_if_ff_in_fs cb 0 cn_eq f
            (by rw [eq]; exact f_in)
            (by rw [init_eq'] at f_in; exact db_funfree f f_in)
        | succ n ih =>
          have prev_cn_ex : ∃ prev_cn, prev_cn ∈ cb.branch.get? n :=
            cb.ex_prev_node_at_each_leq (n + 1) (Option.isSome_of_mem cn_eq) n (Nat.le_add_right n 1)
          intro f f_in
          refine ff_in_core_if_ff_in_fs cb (n + 1) cn_eq f ?_ ?_
          · rcases prev_cn_ex with ⟨prev_cn, prev_cn_eq⟩
            specialize ih prev_cn (by grind) f f_in
            have := allFfInNextFsIfSome cb n prev_cn prev_cn_eq cn cn_eq f
            have f_in_prev_fs : f ∈ prev_cn.fs := by
              have prev_cn_core_sse := prev_cn.core_sse.left f ih
              exact prev_cn_core_sse
            apply this
            constructor
            · exact f_in_prev_fs
            · rw [init_eq'] at f_in
              exact db_funfree f f_in
          · rw [init_eq'] at f_in
            exact db_funfree f f_in

 theorem exIntermeadiateCoreChaseNodeIfFactMissing (cb : CoreChaseBranch kb) (cn cn_succ : CoreChaseNode kb.rules) (n k : Nat)
    (cn_eq : cn ∈ cb.branch.get? n) (cn_succ_eq : cn_succ ∈ cb.branch.get? (n + k))
    (f : Fact sig) (f_in : f ∈ cn.core) (f_nin : ¬ f ∈ cn_succ.core) :
      ∃ (cm : CoreChaseNode kb.rules), f ∈ cm.fs ∧ ¬ f ∈ cm.core := by
      induction k generalizing cn_succ with
        | zero =>
          grind
        | succ k ih =>
          have ex_cm : ∃ cm, cb.branch.infinite_list (n + k) = some cm :=
            cb.ex_prev_node_at_each_leq (n + k + 1) (Option.isSome_of_mem cn_succ_eq) (n+k) (Nat.le_add_right (n + k) 1)
          rcases ex_cm with ⟨cm, cm_eq⟩
          by_cases c : (f ∈ cm.core)
          exists cn_succ
          constructor
          · have := before_core_sub_after_fs cb (n + k) cm cn_succ cm_eq cn_succ_eq
            exact this f c
          · exact f_nin
          specialize ih cm cm_eq c
          exact ih

end CoreChaseBranch
