import ExistentialRules.ChaseSequence.CoreChase.Util
import ExistentialRules.ChaseSequence.CoreChase.Basic
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseNode
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch
import ExistentialRules.ChaseSequence.CoreChase.Termination

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


  /-
    (x)              (y)
    A_1  --- →  ---  A_2
     |                |
     fs           →   fs
     ↓         ↗      ↓
   id (⊆)  (h)     id (⊆)
     ↓   ↗           ↓
   core → (h ∘ id) → core

  -/

namespace CoreChaseBranch


  @[grind]
  theorem exHomFsCore (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : cb.branch.infinite_list n = some x) :
    ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fs x.core := by
      exact x.core_sse.right

  @[grind]
  theorem exHomPrevCoreToFactSet (cb : CoreChaseBranch kb) (n : Nat) (x y : CoreChaseNode kb.rules)
    (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) : ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.fs := by
      have trg_ex := cb.triggers_exist n
      have sub : _ := prevCoreSubsetOfFactset cb n x y x_eq y_eq
      have := GroundTermMapping.exHomSubToSet x.core y.fs sub
      exact this

  @[grind]
  theorem exGtmHomSubsetFsCore (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cb.branch.infinite_list n = some cn) :
    ∃ (gtm : GroundTermMapping sig), gtm.applyFactSet cn.fs ⊆ cn.core := by
      rcases (exHomFsCore cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
      exists gtm
      intro f f_in
      unfold GroundTermMapping.applyFactSet at f_in
      rcases f_in with ⟨a, ahl, ahr⟩
      rw [ahr]
      apply gtm_hom.right
      apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
      exact ahl

    @[grind]
  theorem exHomCoreSuccCoreIfSuccIsSome (cb : CoreChaseBranch kb) (n : Nat) (x y : CoreChaseNode kb.rules)
    (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.core := by
      have y_core := y.core_sse
      rcases y_core with ⟨sub, ⟨gtm_yfs_ycore, gtm_yfs_ycore_hom⟩⟩
      have : ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.fs := exHomPrevCoreToFactSet cb n x y x_eq y_eq
      rcases this with ⟨gtm_xcore_yfs, gtm_xcore_yfs_hom⟩
      exists (gtm_yfs_ycore ∘ gtm_xcore_yfs)
      exact GroundTermMapping.isHomomorphism_compose gtm_xcore_yfs gtm_yfs_ycore x.core y.fs y.core gtm_xcore_yfs_hom gtm_yfs_ycore_hom

  @[grind]
  theorem exHomFsSuccFsIfSuccIsSome (cb : CoreChaseBranch kb) (n : Nat) (x y : CoreChaseNode kb.rules)
    (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fs y.fs := by
        have x_core := x.core_sse
        have : ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.fs := exHomPrevCoreToFactSet cb n x y x_eq y_eq
        rcases this with ⟨gtm_xcore_yfs, gtm_xcore_yfs_hom⟩
        rcases x_core with ⟨sub, gtm_xfs_xcore, gtm_xfs_xcore_hom⟩
        exists (gtm_xcore_yfs ∘ gtm_xfs_xcore)
        exact GroundTermMapping.isHomomorphism_compose gtm_xfs_xcore gtm_xcore_yfs x.fs x.core y.fs gtm_xfs_xcore_hom gtm_xcore_yfs_hom

  -- t16 (A_0 → A_1 → A_2 → ...)
  @[grind]
  theorem exHomCoreAllFollowingCore (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : cb.branch.infinite_list n = some x) :
        ∀ m, (cb.branch.infinite_list (n + m)).is_none_or (fun y => ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.core) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.add_zero, Option.is_none_or]
        split
        next => trivial
        next a b y heq => apply GroundTermMapping.exHomSubToSet x.core y.core (by
          have eq : x = y := by grind
          rw [eq]
          apply Set.subset_refl
          )
      | succ m ih =>
        rw [Option.is_none_or_iff]
        intro y y_eq
        let prev_node := (cb.prev_node (n + m) (by rw [Nat.add_assoc]; simp [y_eq]))
        simp only [Option.is_none_or] at ih
        split at ih
        next => apply GroundTermMapping.exHomSubToSet x.core y.core (by grind)
        next a b z heq =>
          have : ∃ (h : GroundTermMapping sig), h.isHomomorphism z.core y.core := exHomCoreSuccCoreIfSuccIsSome cb (n + m) z y heq y_eq
          rcases ih with ⟨gtm_x_z, gtm_x_z_hom⟩
          rcases this with ⟨gtm_z_y, gtm_z_y_hom⟩
          exists (gtm_z_y ∘ gtm_x_z)
          exact GroundTermMapping.isHomomorphism_compose gtm_x_z gtm_z_y x.core z.core y.core gtm_x_z_hom gtm_z_y_hom

  @[grind]
  theorem exHomFsAllFollowingFs (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : cb.branch.infinite_list n = some x) :
        ∀ m, (cb.branch.infinite_list (n + m)).is_none_or (fun y => ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fs y.fs) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.add_zero, Option.is_none_or]
        split
        next => trivial
        next a b y heq => apply GroundTermMapping.exHomSubToSet x.fs y.fs (by
          have eq : x = y := by grind
          rw [eq]
          apply Set.subset_refl
          )
      | succ m ih =>
        rw [Option.is_none_or_iff]
        intro y y_eq
        let prev_node := (cb.prev_node (n + m) (by rw [Nat.add_assoc]; simp [y_eq]))
        simp only [Option.is_none_or] at ih
        split at ih
        next => apply GroundTermMapping.exHomSubToSet x.fs y.fs (by grind)
        next a b z heq =>
          have : ∃ (h : GroundTermMapping sig), h.isHomomorphism z.fs y.fs := exHomFsSuccFsIfSuccIsSome cb (n + m) z y heq y_eq
          rcases ih with ⟨gtm_x_z, gtm_x_z_hom⟩
          rcases this with ⟨gtm_z_y, gtm_z_y_hom⟩
          exists (gtm_z_y ∘ gtm_x_z)
          exact GroundTermMapping.isHomomorphism_compose gtm_x_z gtm_z_y x.fs z.fs y.fs gtm_x_z_hom gtm_z_y_hom

  @[grind]
  theorem exHomResultIfIsSome (cb : CoreChaseBranch kb) (ter' : cb.terminates') (m : Nat) (cn cn_res : CoreChaseNode kb.rules)
    (cn_eq : cb.branch.infinite_list m = some cn) (cn_res_eq : cn_res.core = cb.result ter') :
    ∃ (h : GroundTermMapping sig), h.isHomomorphism cn.fs cn_res.core := by
      unfold result at cn_res_eq
      rcases ter' with ⟨n, term_at_n⟩
      have ter'_eq : cb.last_element_index (Exists.intro n term_at_n : ∃ n, cb.terminates_at_step n) = n := last_element_index_eq_termintes'_index cb n term_at_n
      simp only [ter'_eq] at cn_res_eq
      simp_all only [Option.castToMemIfNotNone, ne_eq]
      split at cn_res_eq
      next a b c d e f =>
        rw [← cn_res_eq]
        by_cases case : m < n
        have := exHomCoreAllFollowingCore cb m cn cn_eq
        specialize this (n - m)
        have eq : m + (n - m) = n := by grind
        rw [eq, e] at this
        rcases this with ⟨gtm_cn_core_cn_res_core, gtm_cn_core_cn_res_core_hom⟩
        rcases cn.core_sse.right with ⟨gtm_cn_fs_cn_core, gtm_cn_fs_cn_core_hom⟩
        rw [← cn_res_eq] at gtm_cn_core_cn_res_core_hom
        exists (gtm_cn_core_cn_res_core ∘ gtm_cn_fs_cn_core)
        exact GroundTermMapping.isHomomorphism_compose gtm_cn_fs_cn_core gtm_cn_core_cn_res_core cn.fs cn.core cn_res.core gtm_cn_fs_cn_core_hom gtm_cn_core_cn_res_core_hom
        have case : m = n ∨ m > n:= Nat.eq_or_lt_of_not_lt case
        cases case with
          | inl eq =>
            grind
          | inr gt =>
            have contra := CoreChaseBranch.last_element_index_eq_termintes'_index_leq cb n term_at_n m
            unfold CoreChaseBranch.last_element_index at ter'_eq
            have := all_succ_of_last_index_none cb n term_at_n m gt
            rw [cn_eq] at this
            contradiction
      next => contradiction

end CoreChaseBranch
