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


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


namespace CoreChaseBranch

  -- jeder surjektive endomorphisms auf endlichen mengen ist auch ein isomorphismus

  theorem triggerInactiveAfterApplication' (cb : CoreChaseBranch kb) (cn cn_succ : CoreChaseNode kb.rules) (n k : Nat)
    (cn_eq : cn ∈ cb.branch.infinite_list n) (cn_succ_eq : cn_succ ∈ cb.branch.infinite_list (n + k))
    (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) (trg_act_cn : trg.val.active cn.core) :
      ¬ trg.val.active cn_succ.core := by sorry


  theorem apply_constant_is_id_of_isIdOnConstants {h : GroundTermMapping sig} (isId : h.isIdOnConstants) (c : sig.C) :
      h (GroundTerm.const c) = GroundTerm.const c := Subtype.ext (congrArg Subtype.val isId)




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

  noncomputable def generateNextCoreChaseBranchElement' (o : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) (last_node : CoreChaseNode kb.rules) : CoreChaseNode kb.rules :=


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

    noncomputable def generateNextCoreChaseBranchElement (ccn : CoreChaseNode kb.rules) (o : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) : CoreChaseNode kb.rules :=

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


  noncomputable def generateNextCoreChaseBranchElement_opt (ccn : CoreChaseNode kb.rules) (o : (trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) : Option (CoreChaseNode kb.rules) :=
    match Classical.propDecidable (o.fst.val.active ccn.core) with
      | isTrue _ =>
        generateNextCoreChaseBranchElement ccn o
      | isFalse _ =>
        none


  def κ (nl : PossiblyInfiniteList (CoreChaseNode kb.rules)) (n : Nat) : Nat :=
    match n with
      | .zero => 0
      | .succ n =>
        match nl.get? (κ nl n) with
          | none => κ nl n
          | some cn =>




  theorem exists_active_trigger_of_step [DecidableEq β] (origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))
    (init_ccn : CoreChaseNode kb.rules) (node_list : (List (CoreChaseNode kb.rules × Option ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length))))
    (node_list_eq : node_list = foldl_save_hist_opt_nodup_trace origin_list init_ccn generateNextCoreChaseBranchElement_opt)
    (n : Nat) (h : n + 1 < node_list.length) (before after : CoreChaseNode kb.rules)
    (before_eq : before = (node_list.get ⟨n, (Nat.lt_of_succ_lt h)⟩).fst) (after_eq : after = (node_list.get ⟨n+1, Nat.lt_of_succ_le h⟩).fst) (origin_some : after.origin ≠ none) :
      (after.origin.get (Option.isSome_iff_ne_none.mpr origin_some)).fst.val.active before.core := by
        --subst before_eq after_eq node_list_eq
        unfold foldl_save_hist_opt_nodup_trace at *

        have hstep : after ≠ before := by
          have := foldl_save_hist_opt_nodup_trace_adjacent_ne
            origin_list init_ccn generateNextCoreChaseBranchElement_opt n
            (Nat.lt_of_lt_of_eq h (congrArg List.length node_list_eq))
          subst node_list_eq after_eq before_eq
          -- because nodup
          sorry

        have hex :
          ∃ o ∈ origin_list,
            generateNextCoreChaseBranchElement_opt before o = some after := by sorry

        rcases hex with ⟨o, ho_mem, hgen⟩

        unfold generateNextCoreChaseBranchElement_opt at hgen

        cases hdec :
          Classical.propDecidable ((after.origin.get (Option.isSome_iff_ne_none.mpr origin_some)).fst.val.active before.core) with
        | isTrue hactive =>
          exact hactive
        | isFalse hnot =>

          -- then result is none → contradiction
            simp_all
            sorry


  noncomputable def buildCoreChaseBranchFromChaseBranch (scb : ChaseBranch obs kb) (scb_term : scb.terminates) : CoreChaseBranch kb :=

    have term_n := Classical.choose scb_term


    let origin_list : List ((trg : RTrigger obs.toLaxObsolescenceCondition kb.rules) × Fin trg.val.mapped_head.length) := scb.get_origin_list term_n (List.range' 1 term_n) rfl sorry

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
    origin_list = [o1, o2, o3]

    cn1 = generateNextCoreChaseBranchElement_usingTrigger init_ccn o1
    cn2 = generateNextCoreChaseBranchElement_usingTrigger cn1 o1
    cn3 = generateNextCoreChaseBranchElement_usingTrigger cn2 o1

    node_list = [init_ccn cn1, cn2, cn3]
  -/

  let node_list := foldl_save_hist_opt_nodup origin_list init_ccn generateNextCoreChaseBranchElement_opt

    let new_ccb : CoreChaseBranch kb := {


      branch := PossiblyInfiniteList.from_list node_list
      database_first := by
        rw [PossiblyInfiniteList.get?_from_list, ← List.head?_eq_getElem?]
        exact foldl_save_hist_opt_nodup_head_eq
          origin_list init_ccn generateNextCoreChaseBranchElement_opt

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
      -- das gilt nicht xD F in den chat, können wir trotzdem dem hom constructen ?
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

    rcases ex_An_core with ⟨An_core, An_core_c, An_core_homsub⟩

    let ccb_with_An_core : CoreChaseBranch kb := {
      branch := PossiblyInfiniteList.from_list [{
        fs := An_core
        fs_fin := by sorry
        core := An_core
        is_core := An_core_c
        core_sse := FactSet.homSubset_refl An_core
        origin := none
        fs_contains_origin_result := by simp
      }]
      database_first := sorry
      triggers_active := sorry
      triggers_exist := sorry
      fairness := sorry
    }
    --have ex_ccb_with_An_core : ∃ (ccb_with_An_core : CoreChaseBranch kb) (m : Nat), ((ccb_with_An_core.branch.infinite_list m).get sorry).core.homSubset An := by sorry

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
