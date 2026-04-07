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


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


namespace Fact

  def Fact.hom_mem (f : Fact sig) (fs : FactSet sig) :=
    ∃ (gtm : GroundTermMapping sig), gtm.isHomomorphism (fun x => x = f) fs ∧ (gtm.applyFact f) ∈ fs

  theorem applyFactIdEq (f g : Fact sig) : GroundTermMapping.applyFact id f = g → f = g := by
    intro h
    unfold GroundTermMapping.applyFact TermMapping.apply_generalized_atom at h
    simp only [List.map_id_fun, id_eq] at h
    rw [GeneralizedAtom.mk.injEq]
    exact ⟨congrArg GeneralizedAtom.predicate h, congrArg GeneralizedAtom.terms h⟩

  @[grind]
  theorem FactGeneralizedAtomEq (f : Fact sig) (ga : GeneralizedAtom sig (GroundTerm sig)) : f = ga ↔ f.predicate = ga.predicate ∧ f.terms = ga.terms := by
      constructor
      intro eq
      rw [eq]
      exact ⟨rfl, rfl⟩
      intro ⟨eq_p, eq_t⟩
      rw [GeneralizedAtom.mk.injEq]
      exact ⟨eq_p, eq_t⟩

end Fact


namespace FactSet

  @[grind]
  theorem applyFactSetIdEq (fs : FactSet sig) : fs = GroundTermMapping.applyFactSet id fs := by
    unfold GroundTermMapping.applyFactSet TermMapping.apply_generalized_atom_set
    apply Set.ext
    intro f
    constructor
    intro f_in
    exists f
    constructor
    exact f_in
    exact Fact.applyFactIdEq f (TermMapping.apply_generalized_atom id f) rfl
    intro f_in_map
    rcases f_in_map with ⟨ga, ga_in, ga_eq⟩
    unfold TermMapping.apply_generalized_atom at ga_eq
    rw [GeneralizedAtom.mk.injEq] at ga_eq
    simp only [List.map_id_fun, id_eq] at ga_eq
    apply Classical.byContradiction
    intro contra
    have neq : ga ≠ f := ne_of_mem_of_not_mem ga_in contra
    have := Fact.FactGeneralizedAtomEq f ga
    rw [← this] at ga_eq
    exact neq (id (Eq.symm ga_eq))

end FactSet

namespace ChaseNode

  def ChaseNode.isWeakCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
    Prop := FactSet.isWeakCore node.facts.val

  def ChaseNode.isStrongCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
  Prop := FactSet.isStrongCore node.facts.val

end ChaseNode


namespace GroundTermMapping

  @[grind]
  theorem id_is_id_on_const (h : GroundTermMapping sig) (h_eq : h = id) : h.isIdOnConstants := by
    rw [h_eq]
    intro gt
    split
    next => trivial
    next => trivial

  def isIsomorphism (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
      h.isHomomorphism A B ∧ Function.injective_for_domain_set h A.terms ∧ Function.surjective_for_domain_and_image_set h A.terms B.terms ∧ h.strong A.terms A B


  @[simp, grind]
  theorem homApplyFactFunctionFreeId (fs1 fs2 : FactSet sig) (f : Fact sig) (f_is_ff : f.isFunctionFree) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism fs1 fs2) : gtm.applyFact f = f := by
      rw [GeneralizedAtom.mk.injEq]
      constructor
      rfl
      apply List.map_id_of_id_on_all_mem
      intro gt gt_in
      specialize f_is_ff gt gt_in
      rcases f_is_ff with ⟨c, c_eq⟩
      rw [c_eq]
      apply gtm_hom.left (.const c)

  @[simp, grind]
  theorem homApplyFactSetFunctionFreeId (fs1 fs2 : FactSet sig) (fs1_is_ff : fs1.isFunctionFree) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism fs1 fs2) : gtm.applyFactSet fs1 = fs1 := by
    unfold GroundTermMapping.applyFactSet
    apply Set.ext
    intro f
    constructor
    intro ⟨ff, ff_in, ff_eq⟩
    have := homApplyFactFunctionFreeId fs1 fs2 ff (fs1_is_ff ff ff_in) gtm gtm_hom
    grind
    intro h
    exists f
    constructor
    exact h
    rw [← GroundTermMapping.applyFact.eq_def]
    rw [homApplyFactFunctionFreeId fs1 fs2 f (fs1_is_ff f h) gtm gtm_hom]


  @[grind]
  theorem hom_on_db_id (f : Fact sig) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism kb.db.toFactSet.val kb.db.toFactSet.val) (f_in_db : f ∈ kb.db.toFactSet.val) :
    gtm.applyFact f = f := by
      unfold GroundTermMapping.applyFact
      rw [GeneralizedAtom.mk.injEq]
      constructor
      rfl
      apply List.map_id_of_id_on_all_mem
      intro gt gt_in
      unfold GroundTermMapping.isHomomorphism at gtm_hom
      have db_funfree := kb.db.toFactSet.property.right
      unfold FactSet.isFunctionFree at db_funfree
      specialize db_funfree f f_in_db
      unfold Fact.isFunctionFree at db_funfree
      specialize db_funfree gt gt_in
      rcases db_funfree with ⟨c, c_eq⟩
      rcases f_in_db with ⟨ff, ff_in, ff_eq⟩
      unfold FunctionFreeFact.toFact at ff_eq
      rw [GeneralizedAtom.mk.injEq] at ff_eq
      rcases ff_eq with ⟨ff_pred_eq, ff_map_eq⟩
      rcases gtm_hom with ⟨gtm_c, gtm_sub⟩
      rw [c_eq]
      apply gtm_c (.const c)

  @[grind]
  theorem hom_on_db_term_id (t : GroundTerm sig) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism kb.db.toFactSet.val kb.db.toFactSet.val) (t_in_db_terms : t ∈ kb.db.toFactSet.val.terms) :
    gtm t = t := by
      have db_funfree := kb.db.toFactSet.property.right
      have ex_fact : ∃ f, f ∈ kb.db.toFactSet.val ∧ t ∈ f.terms := t_in_db_terms
      rcases ex_fact with ⟨f, f_in, f_in_ter⟩
      unfold FactSet.isFunctionFree at db_funfree
      specialize db_funfree f f_in t f_in_ter
      rcases db_funfree with ⟨c, c_eq⟩
      rw [c_eq]
      apply gtm_hom.left (.const c)

  @[grind]
  theorem exHomSubToSet (A B : FactSet sig) (sub : A ⊆ B) : ∃ (h : GroundTermMapping sig), h.isHomomorphism A B := by
    exists id
    constructor
    intro gt
    simp only [id_eq]
    split
    next => trivial
    next => trivial
    intro f f_in
    specialize sub f
    apply sub
    rcases f_in with ⟨g, g_in_a, g_in_ida⟩
    have eq := Fact.applyFactIdEq g f (Eq.symm g_in_ida)
    rw [← eq]
    exact g_in_a


  @[grind]
  theorem memApplyFactSetIfMemApplyFactSetSubSet (h : GroundTermMapping sig) (fs1 fs2 : FactSet sig) (f : Fact sig) (f_af_in_f1 : f ∈ h.applyFactSet fs1) (sub : fs1 ⊆ fs2) :  f ∈ h.applyFactSet fs2 := by
    unfold GroundTermMapping.applyFactSet
    rcases f_af_in_f1 with ⟨f', f'_in, f'_af_eq⟩
    exists f'
    exact ⟨sub f' f'_in, f'_af_eq⟩


  theorem isHomIfEq (gtm1 gtm2 : GroundTermMapping sig) (A B : FactSet sig) : gtm1 = gtm2 → (gtm1.isHomomorphism A B ↔ gtm2.isHomomorphism A B) := fun a => Eq.to_iff (congrFun (congrFun (congrArg GroundTermMapping.isHomomorphism a) A) B)

  theorem gtm_rep_swap (gtm : GroundTermMapping sig) (rep : Nat) (A B : FactSet sig) : (gtm.repeat_hom (rep + 1)).isHomomorphism A B ↔ GroundTermMapping.isHomomorphism (gtm.repeat_hom rep ∘ gtm) A B := by
    have := isHomIfEq (gtm.repeat_hom rep ∘ gtm) (gtm.repeat_hom (rep + 1)) A B
    rw [this]
    have := GroundTermMapping.repeat_hom_add gtm rep 1
    funext t
    specialize this t
    exact id (Eq.symm this)

 @[grind]
  theorem subPreservesHom (A B C : FactSet sig) (sub : C ⊆ A) (h : GroundTermMapping sig) (h_hom : h.isHomomorphism  A B) : h.isHomomorphism C B := by
    rcases h_hom with ⟨idc, af⟩
    constructor
    exact idc
    intro f f_in_afc
    have f_in_afb := memApplyFactSetIfMemApplyFactSetSubSet h C A
    specialize f_in_afb f f_in_afc sub
    exact af f f_in_afb

end GroundTermMapping
