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


  @[grind .]
  theorem exHomFsCore (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : x ∈ cb.branch.get? n) :
    ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fs x.core := by
      exact x.core_sse.right

  @[grind .]
  theorem exHomPrevCoreToFactSet (cb : CoreChaseBranch kb) (n : Nat) (x y : CoreChaseNode kb.rules)
    (x_eq : x ∈ cb.branch.get? n) (y_eq : y ∈ cb.branch.get? (n + 1)) : ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.fs := by
      have sub : x.core ⊆ y.fs := before_core_sub_after_fs cb n x y x_eq y_eq
      have := x.core.exHomSubToSet y.fs sub
      exact this

  @[grind .]
  theorem exGtmHomSubsetFsCore (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) :
    ∃ (gtm : GroundTermMapping sig), gtm.applyFactSet cn.fs ⊆ cn.core := by
      rcases (exHomFsCore cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
      exists gtm
      intro f f_in
      unfold GroundTermMapping.applyFactSet at f_in
      rcases f_in with ⟨a, ahl, ahr⟩
      rw [← ahr]
      apply gtm_hom.right
      apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
      exact ahl

  @[grind .]
  theorem exHomCoreSuccCoreIfSuccIsSome (cb : CoreChaseBranch kb) (n : Nat) (x y : CoreChaseNode kb.rules)
    (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.core := by
      have y_core := y.core_sse
      rcases y_core with ⟨sub, ⟨gtm_yfs_ycore, gtm_yfs_ycore_hom⟩⟩
      have : ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.fs := exHomPrevCoreToFactSet cb n x y x_eq y_eq
      rcases this with ⟨gtm_xcore_yfs, gtm_xcore_yfs_hom⟩
      exists (gtm_yfs_ycore ∘ gtm_xcore_yfs)
      exact GroundTermMapping.isHomomorphism_compose gtm_xcore_yfs gtm_yfs_ycore x.core y.fs y.core gtm_xcore_yfs_hom gtm_yfs_ycore_hom

  @[grind .]
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
  @[grind .]
  theorem exHomCoreAllFollowingCore (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : x ∈ cb.branch.get? n) :
      ∀ m, ∀ y, y ∈ cb.branch.get? (n + m) → ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.core := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.add_zero, Option.mem_def]
        intro cn cn_eq
        have eq : cn = x := by grind
        exists id
        rw [eq]
        exact GroundTermMapping.id_is_hom
      | succ m ih =>
        intro y y_eq
        simp only [Option.mem_def] at ih

        have ex_cm : ∃ (z : CoreChaseNode kb.rules), cb.branch.infinite_list (n + m) = some z :=
          cb.ex_prev_node_at_each_leq (n + m + 1) (Option.isSome_of_mem y_eq) (n + m) (Nat.le_add_right (n + m) 1)

        rcases ex_cm with ⟨z, z_eq⟩
        specialize ih z z_eq
        rcases ih with ⟨gtm_x_z, gtm_x_z_hom⟩
        have : ∃ (h : GroundTermMapping sig), h.isHomomorphism z.core y.core := exHomCoreSuccCoreIfSuccIsSome cb (n + m) z y z_eq y_eq
        rcases this with ⟨gtm_z_y, gtm_z_y_hom⟩
        exists (gtm_z_y ∘ gtm_x_z)
        exact GroundTermMapping.isHomomorphism_compose gtm_x_z gtm_z_y x.core z.core y.core gtm_x_z_hom gtm_z_y_hom

  @[grind .]
  theorem exHomFsAllFollowingFs (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : x ∈ cb.branch.get? n) :
        ∀ m, ∀ y, y ∈ cb.branch.get? (n + m) → ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fs y.fs := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.add_zero, Option.mem_def]
        intro cn cn_eq
        have eq : cn = x := by grind
        exists id
        rw [eq]
        exact GroundTermMapping.id_is_hom
      | succ m ih =>
        intro y y_eq
        let prev_node := cb.prev_node (n + m) (Option.isSome_of_mem y_eq)
        specialize ih prev_node
        grind

  @[grind .]
  theorem exHomResultIfIsSome (cb : CoreChaseBranch kb) (ter' : cb.terminates') (m : Nat) (cn cn_res : CoreChaseNode kb.rules)
    (cn_eq : cn ∈ cb.branch.get? m) (cn_res_eq : cn_res ∈ cb.branch.get? (cb.last_element_index ter')) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism cn.fs cn_res.core := by
        rcases ter' with ⟨n, term_at_n⟩
        have ter'_eq : cb.last_element_index (Exists.intro n term_at_n : ∃ n, cb.terminates_at_step n) = n := last_element_index_eq_termintes'_index cb n term_at_n
        simp only [ter'_eq] at cn_res_eq
        by_cases case : m < n
        have := exHomCoreAllFollowingCore cb m cn cn_eq
        specialize this (n - m)
        have eq : m + (n - m) = n := by grind
        grind
        have case : m = n ∨ m > n:= Nat.eq_or_lt_of_not_lt case
        cases case with
          | inl eq =>
            grind
          | inr gt =>
            have contra := CoreChaseBranch.last_element_index_eq_termintes'_index_leq cb n term_at_n m
            unfold CoreChaseBranch.last_element_index at ter'_eq
            have := all_succ_of_last_index_none cb n term_at_n m gt
            grind

  @[grind .]
  theorem homFsToFsAlsoHomCoreToFs (fs : FactSet sig) (cn : CoreChaseNode kb.rules) (h : GroundTermMapping sig) (h_hom : h.isHomomorphism cn.fs fs) : h.isHomomorphism cn.core fs := by
    rcases h_hom with ⟨h_c, h_af⟩
    constructor
    exact h_c
    intro f f_in
    specialize h_af f
    apply h_af
    exact GroundTermMapping.memApplyFactSetIfMemApplyFactSetSubSet h cn.core cn.fs f f_in (cn.core_sse.left)

  @[grind .]
  theorem gtmFsCoreIsEndo (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cb.branch.infinite_list n = some cn) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism cn.fs cn.core):
     (gtm.surjective_for_domain_and_image_set cn.core.terms cn.core.terms) := by
      have sc := FactSet.isStrongCore_of_isWeakCore_of_finite cn.core cn.is_core (CoreChaseNode.all_core_finite cn)
      specialize sc gtm (homFsToFsAlsoHomCoreToFs cn.core cn gtm gtm_hom)
      rcases sc with ⟨s1, s2, s3⟩
      exact s3

end CoreChaseBranch
