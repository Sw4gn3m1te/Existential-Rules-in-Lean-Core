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

@[grind]
theorem all_core_finite (node : CoreChaseNode kb.rules) : Set.finite (node.core) := by
  apply CoreChaseNode.core_finite_if_fs_finite
  exact node.fs_fin

@[grind]
theorem eachKbDbIsWeakCore (kb : KnowledgeBase sig) : kb.db.toFactSet.val.isWeakCore := by
  let db := kb.db
  let fs := db.val
  intro gtm gtm_hom
  constructor
  intro f gt h contra
  have eq : gtm.applyFact f = f := by
    unfold GroundTermMapping.applyFact
    rw [GeneralizedAtom.mk.injEq]
    constructor
    rfl
    apply List.map_id_of_id_on_all_mem
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
  contradiction
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

theorem finFactSetHasCore (fs : FactSet sig) (fin : fs.finite) : ∃ (c : FactSet sig), c.isWeakCore ∧ c.homSubset fs := by
  

def exists_trigger_opt_fs_core (rules : RuleSet sig) (before : CoreChaseNode rules) (after : Option (CoreChaseNode rules)) : Prop :=
  have ex_wc : ∃ (wc: FactSet sig), wc.isWeakCore ∧ wc.homSubset before.fs := finFactSetHasCore before.fs before.fs_fin
  ∀ node ∈ after,
  ∃ trg : (RTrigger (obs.toLaxObsolescenceCondition) rules),
  ∃ (c : FactSet sig),
  ∃ (i : Fin trg.val.mapped_head.length),
    node = {
      fs := before.core ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet
      fs_fin := by
        apply Set.union_finite_of_both_finite
        exact CoreChaseNode.core_finite_if_fs_finite before before.fs_fin
        exact List.finite_toSet trg.val.mapped_head[↑i]
      core := c
      is_core := sorry
      core_sse := sorry
      origin := sorry
      fs_contains_origin_result := sorry
    }

structure CoreChaseBranch (kb: KnowledgeBase sig) where
  branch : PossiblyInfiniteList (CoreChaseNode kb.rules)
  database_first : branch.infinite_list 0 = some {
    fs := kb.db.toFactSet
    fs_fin := kb.db.toFactSet.property.left
    core := kb.db.toFactSet
    is_core := eachKbDbIsWeakCore kb
    core_sse := by
      constructor
      exact Set.subset_refl
      exists id
      exact GroundTermMapping.id_is_hom
    origin := none,
    fs_contains_origin_result := by simp
  }

  triggers_active : ∀ (n : Nat), ∀ before ∈ branch.get? n, ∀ after ∈ branch.get? (n+1), ∃ o ∈ after.origin, o.fst.val.active before.core

  triggers_exist : ∀ n : Nat, ∀ before ∈ branch.get? n,
    let after := branch.get? (n+1)
    (exists_trigger_opt_fs_core kb.rules before after)

  fairness : ∀ trg : (RTrigger obs.toLaxObsolescenceCondition kb.rules), ∃ (i : Nat), ∃ node ∈ branch.get? i, ¬ trg.val.active node.fs
    ∧ (∀ (j : Nat), j > i → ∀ node2  ∈ branch.get? j, ¬ trg.val.active node2.fs)


namespace CoreChaseBranch

  theorem all_prev_some_if_is_some (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? n).isSome) : ∀ m, m ≤ n → (cb.branch.get? m).isSome := by
    intro m leq
    grind

  theorem ex_prev_node_all (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? n).isSome) : ∀ m, m ≤ n → ∃ cn, (cb.branch.get? m) = cn := by apply?

  theorem all_succ_none_if_none (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? n).isNone) : ∀ m, m ≥ n → (cb.branch.get? m).isNone := by
    intro m geq
    grind

  def prev_node (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? (n+1)).isSome) : CoreChaseNode kb.rules := by
    exact (cb.branch.get? n).get (by grind)

    @[grind]
    theorem prev_node_eq (cb : CoreChaseBranch kb) (i : Nat) (isSome : (cb.branch.infinite_list (i + 1)).isSome) :
        cb.branch.infinite_list i = some (cb.prev_node i isSome) := by
      simp [prev_node]
      exact (Option.map_inj_right fun x y a => a).mp rfl

  @[grind]
  theorem origin_isSome (cb : CoreChaseBranch kb) (n : Nat) {node : CoreChaseNode kb.rules} (eq : cb.branch.get? (n + 1) = node) : node.origin.isSome := by

    have ex_before : ∃ before, cb.branch.get? n = before := by grind
    rcases ex_before with ⟨before, before_eq⟩


    have trg_act := cb.triggers_active

    have trg_ex := cb.triggers_exist i
    rw [prev_node_eq _ _ (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inl trg_ex =>
      unfold exists_trigger_opt_fs at trg_ex
      rcases trg_ex with ⟨trg, _, core_fs, disj, trg_eq⟩
      simp only [eq] at trg_eq
      rcases trg_eq with ⟨fs_eq, core_eq, origin_eq⟩
      exact Option.isSome_of_mem origin_eq
    | inr trg_nex =>
      unfold not_exists_trigger_opt_fs at trg_nex
      simp only [eq] at trg_nex
      rcases trg_nex with ⟨fs_eq, core_eq, origin_eq⟩

  /-
    node1 (n) ----> node2 (n + 1)
    ~.core      ⊆   ~.fs
    because ex trigger from n1 to n2 thus n2.fs = n1.core + trig.result thus n1.core ⊆ n2.fs
  -/

  @[grind]
  theorem prevCoreSubsetOfFactset (cb : CoreChaseBranch kb) (n : Nat) (x y : CoreChaseNode kb.rules) (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) :
    x.core ⊆ y.fs := by
      have trg_ex := cb.triggers_exist n
      rw [prev_node_eq _ _ (Option.isSome_of_mem y_eq), Option.is_none_or] at trg_ex
      cases trg_ex with
        | inl trg_ex =>
          rcases trg_ex with ⟨trg, _, core_fs, disj, trg_eq⟩
          simp_all only
          rcases trg_eq with ⟨lhs, rhs⟩
          intro f f_in
          rw [lhs]
          unfold prev_node
          have eq : ((cb.branch.infinite_list n).get (Option.isSome_of_mem x_eq)) = x := by exact Option.get_of_eq_some (Option.isSome_of_mem x_eq) x_eq
          simp only [eq]
          change f ∈ x.core ∨ f ∈ trg.val.mapped_head[↑disj].toSet
          left
          exact f_in
        | inr trg_nex =>
          unfold not_exists_trigger_opt_fs_core at trg_nex
          simp only [not_exists] at trg_nex
          rcases trg_nex with ⟨h1, h2⟩
          rw [h2] at y_eq
          contradiction


  @[grind]
  theorem db_finite (cb : CoreChaseBranch kb) (isSome : (cb.branch.infinite_list 0).isSome = true) : Set.finite ((cb.branch.infinite_list 0).get isSome).core := by
    have := cb.database_first
    simp_all only [Option.get_some]
    grind

  @[grind]
  theorem origin_result_finite {rules : RuleSet sig} (node : CoreChaseNode rules) (isSome : node.origin.isSome) : Set.finite (node.origin_result isSome).toSet := by
    apply Set.finite_of_list_with_same_elements (node.origin_result isSome)
    intro _; rw [List.mem_toSet]

   theorem origin_trg_is_active_core (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cb.branch.infinite_list (n + 1) = some cn) :
        (cn.origin.get (cb.origin_isSome n cn_eq)).fst.val.active (cb.prev_node n (Option.isSome_of_mem cn_eq)).core := by
      have trg_ex := cb.triggers_exist n
      rw [prev_node_eq cb n (Option.isSome_of_mem cn_eq), Option.is_none_or] at trg_ex
      cases trg_ex with
      | inl trg_ex =>
        unfold exists_trigger_opt_fs_core at trg_ex
        rcases trg_ex with ⟨trg, trg_act_c, c, i, h⟩
        rw [Option.is_some_and_iff] at h
        rcases h with ⟨succ_cn, succ_cn_eq⟩
        grind
      | inr trg_nex =>
        rw [trg_nex.right] at cn_eq
        simp at cn_eq

  @[grind]
  theorem origin_trg_result_yields_next_node_fs (cb : CoreChaseBranch kb) (i : Nat) (node : CoreChaseNode kb.rules) (eq : cb.branch.infinite_list (i + 1) = some node) :
      node.fs = (cb.prev_node i (by simp [eq])).core ∪ (node.origin_result (cb.origin_isSome i eq)).toSet := by
    have trg_ex := cb.triggers_exist i
    rw [prev_node_eq _ _ (by simp [eq]), Option.is_none_or] at trg_ex
    cases trg_ex with
    | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [trg_ex.right] at eq; simp at eq
    | inl trg_nex =>
      unfold exists_trigger_opt_fs at trg_nex
      rcases trg_nex with ⟨trg, trg_active, core_fs, disj, trg_eq⟩
      simp only [eq] at trg_eq
      rcases trg_eq with ⟨fs_eq, core_eq, origin_eq⟩
      have : trg.val.mapped_head[↑disj].toSet = (node.origin_result (origin_isSome cb i eq)).toSet := by
        unfold CoreChaseNode.origin_result
        simp only [Fin.getElem_fin]
        have eq' : (node.origin.get (origin_isSome cb i eq)) = ⟨trg, disj⟩ := by
          exact Option.get_of_eq_some (origin_isSome cb i eq) origin_eq
        simp only [eq']
        have eq'' : (node.origin.get (origin_isSome cb i eq)).snd.val = disj.val := by rw [eq']
        simp only [eq'']
      rw [← this]
      exact fs_eq

  @[grind]
  theorem all_fs_finite (cb : CoreChaseBranch kb) (n : Nat) (node : CoreChaseNode kb.rules) (eq : cb.branch.infinite_list n = some node) : Set.finite (node.fs) := by
    induction n generalizing node with
      | zero =>
        have := cb.database_first
        grind
      | succ n ih =>
        specialize ih (prev_node cb n (Option.isSome_of_mem eq)) (prev_node_eq cb n (Option.isSome_of_mem eq))
        have origin_yield := origin_trg_result_yields_next_node_fs cb n node eq
        rw [origin_yield, ← Set.unionOfFinteIsFinte]
        constructor
        grind
        have := origin_result_finite node (origin_isSome cb n eq)
        exact this

  @[grind]
  theorem exNextNodeIfExLoadedNonObsoleteTrigger (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules)
     (cn_eq : cb.branch.infinite_list n = some cn) (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (trg_loaded : trg.val.loaded cn.core) (trg_non_obs : ¬ obs.cond trg.val cn.core) :
      ∃ (cn' : CoreChaseNode kb.rules), cb.branch.infinite_list (n+1) = some cn' := by
      cases h : cb.branch.infinite_list (n+1) with
        | none =>
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
        | some succ_cn =>
          exists succ_cn

  @[grind]
  theorem cbNextFsEq (cb : CoreChaseBranch kb) (n : Nat) (a b : CoreChaseNode kb.rules) (eq_a : cb.branch.infinite_list n = some a) (eq_b : cb.branch.infinite_list (n + 1) = some b) :
    b.fs = (b.origin_result (origin_isSome cb n eq_b)).toSet ∪ a.core := by
      have trg_ex := cb.triggers_exist n
      rw [Option.is_none_or_iff] at trg_ex
      specialize trg_ex a eq_a
      simp only [eq_b] at trg_ex
      rcases trg_ex with trg_ex | trg_nex
      rcases trg_ex with ⟨trg, trg_act, ⟨c, i, h2⟩⟩
      rw [Option.is_some_and] at h2
      rcases h2 with ⟨lhs, rhs⟩
      have eq : (b.origin_result (origin_isSome cb n eq_b)).toSet = trg.val.mapped_head[↑i].toSet := by
        unfold CoreChaseNode.origin_result
        grind
      rw [eq, Set.unionSym]
      exact lhs
      rcases trg_nex with ⟨trg_nex, b_eq⟩
      grind


  @[grind]
  theorem next_step_finite_if_finite (cb : CoreChaseBranch kb) (n : Nat) (a b : CoreChaseNode kb.rules) (eq_a : cb.branch.infinite_list n = some a) (eq_b : cb.branch.infinite_list (n + 1) = some b) (a_fin : a.core.finite) :
    b.core.finite := by
      rcases a_fin with ⟨al, al_nodup, al_eq⟩
      have b_fs_eq := cbNextFsEq cb n a b eq_a eq_b
      apply CoreChaseNode.core_finite_if_fs_finite
      rw [b_fs_eq, ← Set.unionOfFinteIsFinte]
      constructor
      exact origin_result_finite b (origin_isSome cb n eq_b)
      exact Set.finite_of_list_with_same_elements al al_eq


  @[grind]
  theorem allElemDbMappedId (cb : CoreChaseBranch kb) (init : CoreChaseNode kb.rules) (init_eq : cb.branch.infinite_list 0 = some init) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism init.fs fs2) :
    ∀ f, f ∈ init.fs → gtm.applyFact f = f := by
      intro f f_in
      unfold GroundTermMapping.applyFact
      rw [GeneralizedAtom.mk.injEq]
      constructor
      rfl
      apply List.map_id_of_id_on_all_mem
      intro gt gt_in
      unfold GroundTermMapping.isHomomorphism at gtm_hom
      have db_funfree := kb.db.toFactSet.property.right
      rw [cb.database_first] at init_eq
      simp only [Option.some.injEq] at init_eq
      rw [← init_eq] at f_in
      specialize db_funfree f f_in gt gt_in
      rcases db_funfree with ⟨c, c_eq⟩
      rw [c_eq]
      apply gtm_hom.left (.const c)

  @[grind]
  theorem ff_in_core_if_ff_in_fs (cb : CoreChaseBranch kb) (n : Nat) (x_eq : cb.branch.infinite_list n = some x) (f : Fact sig) (f_in : f ∈ x.fs) (f_is_ff : f.isFunctionFree) : f ∈ x.core := by
      have ex_gtm := x.core_sse.right
      rcases ex_gtm with ⟨gtm, gtm_hom⟩
      have eq : gtm.applyFact f = f := GroundTermMapping.homApplyFactFunctionFreeId x.fs x.core f f_is_ff gtm gtm_hom
      have x_core := x.is_core
      rcases gtm_hom with ⟨gtm_c, gtm_st⟩
      specialize gtm_st f
      apply gtm_st
      exists f; constructor
      . exact f_in
      . conv => left; rw [← eq]

  @[grind]
  theorem allFfInNextFsIfSome (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : cb.branch.infinite_list n = some x) :
    (cb.branch.infinite_list (n+1)).is_none_or (fun cn => ∀ f, f ∈ x.fs ∧ f.isFunctionFree → f ∈ cn.fs) := by
      rw [Option.is_none_or_iff]
      intro cn_succ cn_succ_eq f ⟨f_in, f_is_ff⟩
      have := cb.triggers_exist n
      rw [x_eq, Option.is_none_or] at this
      simp at this
      rcases this with trg_ex | trg_nex
      unfold exists_trigger_opt_fs_core at trg_ex
      rcases trg_ex with ⟨trg, trg_act, ⟨c, i, h2⟩⟩
      rw [cn_succ_eq, Option.is_some_and] at h2
      rcases h2 with ⟨lhs, rhs⟩
      have f_in_core : f ∈ x.core := ff_in_core_if_ff_in_fs cb n x_eq f f_in f_is_ff
      have x_core_sse : x.core ⊆ cn_succ.fs := prevCoreSubsetOfFactset cb n x cn_succ x_eq cn_succ_eq
      exact x_core_sse f f_in_core
      rcases trg_nex with ⟨trg_nex, succ_eq⟩
      grind

  @[grind]
  theorem allFfInAllSuccIfSome (cb : CoreChaseBranch kb) (n m : Nat) (x : CoreChaseNode kb.rules) (x_eq : cb.branch.infinite_list n = some x) :
    (cb.branch.infinite_list (n+m)).is_none_or (fun cn => ∀ f, f ∈ x.fs ∧ f.isFunctionFree → f ∈ cn.fs) := by
      induction m with
        | zero =>
          simp only [Nat.add_zero, and_imp]
          rw [Option.is_none_or_iff]
          intro cn_succ cn_succ_eq f f_in_fs f_is_ff
          have eq : x = cn_succ := by grind
          subst eq
          exact f_in_fs
        | succ m ih =>
          rw [Option.is_none_or_iff]
          intro cn_succ cn_succ_eq f ⟨f_in_fs, f_is_ff⟩
          have := cb.triggers_exist (n + m)
          rw [Option.is_none_or_iff] at ih
          have ex_cn : ∃ (cn_mid : CoreChaseNode kb.rules), cb.branch.infinite_list (n + m) = some cn_mid := by
            have := prev_is_some_if_is_some' cb (n + (m + 1)) cn_succ cn_succ_eq (n + m) (Nat.le_succ (n + m))
            exact Option.ne_none_iff_exists'.mp this
          rcases ex_cn with ⟨cn_mid, cn_mid_eq⟩
          have := allFfInNextFsIfSome cb (n + m) cn_mid cn_mid_eq
          rw [Option.is_none_or_iff] at this
          specialize ih cn_mid cn_mid_eq f
          specialize this cn_succ cn_succ_eq f
          apply this
          grind

  @[grind]
  theorem cbDbInAllSucc (cb : CoreChaseBranch kb) (n : Nat) (init cn : CoreChaseNode kb.rules) (init_eq : cb.branch.infinite_list 0 = some init) (cn_eq : cb.branch.infinite_list n = some cn) :
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
          have prev_cn_ex : ∃ prev_cn, cb.branch.infinite_list n = some prev_cn:= by
            have := prev_is_some_if_is_some cb (n + 1) (Option.NeqNoneIfIsSome (cb.branch.infinite_list (n + 1)) cn cn_eq) n (Nat.lt_add_one n)
            exact Option.ne_none_iff_exists'.mp this
          intro f f_in
          refine ff_in_core_if_ff_in_fs cb (n + 1) cn_eq f ?_ ?_
          rcases prev_cn_ex with ⟨prev_cn, prev_cn_eq⟩
          specialize ih prev_cn (by grind) f f_in
          have := allFfInNextFsIfSome cb n prev_cn prev_cn_eq
          rw [Option.is_none_or_iff] at this
          specialize this cn cn_eq f
          have f_in_prev_fs : f ∈ prev_cn.fs := by
            have prev_cn_core_sse := prev_cn.core_sse.left f ih
            exact prev_cn_core_sse
          apply this
          constructor
          exact f_in_prev_fs
          rw [init_eq'] at f_in
          exact db_funfree f f_in
          rw [init_eq'] at f_in
          exact db_funfree f f_in

 theorem exIntermeadiateCoreChaseNodeIfFactMissing (cb : CoreChaseBranch kb) (cn cn_succ : CoreChaseNode kb.rules) (n k : Nat)
    (cn_eq : cb.branch.infinite_list n = some cn) (cn_succ_eq : cb.branch.infinite_list (n + k) = some cn_succ)
    (f : Fact sig) (f_in : f ∈ cn.core) (f_nin : ¬ f ∈ cn_succ.core) :
      ∃ (cm : CoreChaseNode kb.rules), f ∈ cm.fs ∧ ¬ f ∈ cm.core := by
      induction k generalizing cn_succ with
        | zero =>
          grind
        | succ k ih =>
          have ex_cm : ∃ cm, cb.branch.infinite_list (n + k) = some cm := by
            have := prev_is_some_if_is_some'' cb (n + k + 1) (Option.isSome_of_mem cn_succ_eq) (n + k) (Nat.lt_add_one (n + k))
            exact Option.isSome_iff_exists.mp this
          rcases ex_cm with ⟨cm, cm_eq⟩
          by_cases c : (f ∈ cm.core)
          exists cn_succ
          constructor
          have := prevCoreSubsetOfFactset cb (n + k) cm cn_succ cm_eq cn_succ_eq
          exact this f c
          exact f_nin
          specialize ih cm cm_eq c
          exact ih

end CoreChaseBranch
