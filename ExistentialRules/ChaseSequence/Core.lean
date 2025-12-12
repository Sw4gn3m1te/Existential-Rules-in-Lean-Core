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

--import ExistentialRules.BasicTypes.Sets.Set
--import ExistentialRules.BasicTypes.Sets.Finite
--import ExistentialRules.BasicTypes.Functions.Function


-- import Aesop
-- import Canonical
-- import Mathlib.Combinatorics.Graph.Basic


-- set_option pp.proofs true
-- set_option diagnostics true

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}


/-------------------------
---
· "We extend the definition of chase sequence to core chase sequence in the obvious way" :)
· Core Chase sequences are determinted up to isomorphism (there is no non-deterministic picking of rules)
· The result of the Core Chase is unique up to isomorphism
---


Proof sketch Thm. 7
(Σ: Set of TGDs/EGDs) (I: Instance)

1)                                                  2)
There exists a (finite ?) universal model for Σ,I ↔ The Core Chase on Σ,I terminates (and yields such a model)

1) → 2):
Let U be a (finite?) universal Model for Σ,I

! Assume, ad absudum, there does not exist a finite Core Chase Sequence on Σ, I !

(contra) Thus there is a infinite Core Chase Sequence A = A_1, A_2, A_3, ...

Let A_ω = ⋃_i A_i
(union of all node.fs i assume ? So normal Chase ?)
This set is well-defined because ∀ i, A_i ⊆ A_{i+1} (this is not true for the Core Chase ? What is A refering too ?)

a) By assumption U is a universal model and thus a model for Σ,I we know that
  A_ω → U,
  (reason ?)

b) We know (why ?) that A_ω ⊧ Σ and because U is universal we know that
  U → A_ω

  -- assumen wir hier nicht, dass A_ω das result der Core Chase ist und es einen isom. zw. A_ω und U gibt ?

From b) and U being finite we know that
  U → A_n for some bounding (n : Nat)

and by t16 A_n → U ??

Thus core(U) ≅ core(A_n) thus U,A_n ⊧ Σ, which is a contradiction ?



2) → 1):

Assume the Core Chase termiantes

Let A = A_1, A_2, A_3, ... , A_n be a Core Chase sequence on Σ,I

Lemma: ∀ i j, (i < j) → ∃ (h : A_i → A_j)

  (We call an instance or set of instances T universal for K if T → K)

Thus the Core Chase preserves universality at each step

If the Core Chase terminates there is some (n : Nat), s.t. Result = A_n



-------------------------/

def ChaseNode.isWeakCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
  Prop := FactSet.isWeakCore node.facts.val

def ChaseNode.isStrongCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
 Prop := FactSet.isStrongCore node.facts.val

def getCore (fs : FactSet sig) (fs_fin : fs.finite) : {wc : FactSet sig // wc.isWeakCore ∧ wc.homSubset fs} := by sorry

def GroundTermMapping.isIsomorphism (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
    h.isHomomorphism A B ∧ Function.injective_for_domain_set h A.terms ∧ Function.surjective_for_domain_and_image_set h A.terms B.terms ∧ h.strong A.terms A B

structure CoreChaseNode (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  fs : FactSet sig
  fs_fin : fs.finite
  core : FactSet sig
  is_core : core.isWeakCore
  core_sse : core.homSubset fs
  origin : Option ((trg : RTrigger (obs : LaxObsoletenessCondition sig) rules) × Fin trg.val.mapped_head.length)
  fs_contains_origin_result : origin.is_none_or (fun origin => origin.fst.val.mapped_head[origin.snd.val].toSet ⊆ fs)


def CoreChaseNode.origin_result {obs : ObsoletenessCondition sig} (node : CoreChaseNode obs rules) (isSome : node.origin.isSome) : List (Fact sig) :=
  let origin := node.origin.get isSome
  origin.fst.val.mapped_head[origin.snd.val]


-- checkt ob wenn man einen trigger (trg) auf einer menge (before) anwendet, die menge (after) rauskommt
def RTrigger.isStep (trg : Trigger (obs : LaxObsoletenessCondition sig)) (before after : FactSet sig) : Prop :=
  ∃ fact, fact ∈ before → after = before ∪ (trg.mapped_head).flatten.toSet


def exists_trigger_opt_fs_core (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : CoreChaseNode obs rules) (after : Option (CoreChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger (obs : LaxObsoletenessCondition sig) rules), trg.val.active before.core ∧ ∃ (c : FactSet sig) (i : _),
    after.is_some_and (fun a => a.fs = before.core ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet ∧ a.core = c ∧ a.origin = some ⟨trg, i⟩)

def not_exists_trigger_opt_fs_core (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : CoreChaseNode obs rules) (after : Option (CoreChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.core) ∧ after = none

theorem exFactIfExTerm (kb : KnowledgeBase sig) (t : GroundTerm sig) : t ∈ kb.db.toFactSet.val.terms → ∃ f, f ∈ kb.db.toFactSet.val := by
  intro ⟨f, f_in_fs, f_in_ter⟩
  exists f

theorem id_is_injective (A : Set α) : Function.injective_for_domain_set id A := by
  intro a b a_in b_in eq
  simp at eq
  exact eq

theorem id_is_surjective (A : Set α) : Function.surjective_for_domain_and_image_set id A A := by
  intro a a_in
  exists a

@[simp, grind]
theorem gtmHomApplyFactFunctionFreeId (fs1 fs2 : FactSet sig) (f : Fact sig) (f_is_ff : f.isFunctionFree) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism fs1 fs2) : gtm.applyFact f = f := by
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
theorem gtmHomApplyFactSetFunctionFreeId (fs1 fs2 : FactSet sig) (fs1_is_ff : fs1.isFunctionFree) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism fs1 fs2) : gtm.applyFactSet fs1 = fs1 := by
  unfold GroundTermMapping.applyFactSet
  apply Set.ext
  intro f
  constructor
  intro ⟨ff, ff_in, ff_eq⟩
  have := gtmHomApplyFactFunctionFreeId fs1 fs2 ff (fs1_is_ff ff ff_in) gtm gtm_hom
  grind
  intro h
  exists f
  constructor
  exact h
  rw [← GroundTermMapping.applyFact.eq_def]
  rw [gtmHomApplyFactFunctionFreeId fs1 fs2 f (fs1_is_ff f h) gtm gtm_hom]


@[grind]
theorem gtm_hom_on_db_id (f : Fact sig) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism kb.db.toFactSet.val kb.db.toFactSet.val) (f_in_db : f ∈ kb.db.toFactSet.val) :
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
theorem gtm_hom_on_db_term_id (t : GroundTerm sig) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism kb.db.toFactSet.val kb.db.toFactSet.val) (t_in_db_terms : t ∈ kb.db.toFactSet.val.terms) :
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
    apply gtm_hom.left (.const c)
  rw [eq] at contra
  contradiction
  -- id is injective
  intro a b a_in b_in eq
  have a_mem : ∃ fa, fa ∈ kb.db.toFactSet.val := exFactIfExTerm kb a a_in
  rcases a_mem with ⟨fa, fa_in⟩
  have gtm_eq : ∀ f, f ∈ kb.db.toFactSet.val → gtm.applyFact f = f := by exact fun f a => gtm_hom_on_db_id f gtm gtm_hom a
  specialize gtm_eq fa fa_in
  have gt_eq : ∀ t, t ∈ kb.db.toFactSet.val.terms → gtm t = t := by exact fun t a => gtm_hom_on_db_term_id t gtm gtm_hom a
  rw [gt_eq, gt_eq] at eq
  exact eq
  exact b_in
  exact a_in

structure CoreChaseBranch (obs : ObsoletenessCondition sig) (kb: KnowledgeBase sig) where
  branch : PossiblyInfiniteList (CoreChaseNode obs kb.rules)
  database_first : branch.infinite_list 0 = some {
    fs := kb.db.toFactSet
    fs_fin := by exact kb.db.toFactSet.property.left
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

  triggers_exist : ∀ (n : Nat), (branch.infinite_list n).is_none_or (fun before =>
  let after := branch.infinite_list (n+1)
  (exists_trigger_opt_fs_core obs kb.rules before after) ∨
    (not_exists_trigger_opt_fs_core obs kb.rules before after))
  fairness : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ((branch.infinite_list i).is_some_and (fun fs => ¬ trg.val.active fs.fs))
    ∧ (∀ j : Nat, j > i -> (branch.infinite_list j).is_none_or (fun fs => ¬ trg.val.active fs.fs))


@[grind]
theorem Option.isSomeIffNeqNone (o : Option α) : o.isSome ↔ o ≠ none := by
  constructor
  grind
  intro h
  unfold Option.isSome
  split
  next => grind
  next => grind

theorem Option.NeqNoneIfIsSome (o : Option α) (a : α) : o = some a →  o ≠ none := by
  intro h
  exact (isSomeIffNeqNone o).mp (Option.isSome_of_mem h)

@[simp, grind]
def Option.castToMemIfNotNone (o : Option α) (not_none : o ≠ none) : α :=
    match o with
      | some o => o
      | none => by contradiction

@[simp, grind]
def Option.castToMemIfIsSome (o : Option α) (is_some : o.isSome) : α :=
  match o with
    | some o => o
    | none => by contradiction

namespace CoreChaseBranch

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  def terminates (cb : CoreChaseBranch obs kb) : Prop :=
    ∃ n, (cb.branch.infinite_list n = none)

  def terminates_at_step (cb : CoreChaseBranch obs kb) (n : Nat) : Prop :=
    (cb.branch.infinite_list n) ≠ none ∧ (cb.branch.infinite_list (n+1) = none)

  def terminates' (cb : CoreChaseBranch obs kb) : Prop :=
    ∃ n, terminates_at_step cb n

  @[grind]
  theorem terminatesIfTerminates' (cb : CoreChaseBranch obs kb) : cb.terminates' → cb.terminates := by
    intro ⟨n, a, b⟩
    exists (n + 1)

  @[grind]
  theorem terminates'IfTerminatesAndNonEmpty (cb : CoreChaseBranch obs kb) (non_empty : ∃ m, cb.branch.infinite_list m ≠ none) : cb.terminates → cb.terminates' := by
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

  @[grind]
  theorem prev_is_some_if_is_some (cb : CoreChaseBranch obs kb) (n : Nat) (is_some_at : cb.branch.infinite_list n ≠ none) : ∀ m, m < n → cb.branch.infinite_list m ≠ none := by
    intro m lt
    intro contra
    have := cb.branch.get?_eq_none_of_le_of_eq_none contra n (Nat.le_of_lt lt)
    simp only [PossiblyInfiniteList.get?, InfiniteList.get] at this
    rw [this] at is_some_at
    simp at is_some_at

  @[grind]
  theorem prev_eq_is_some_if_is_some (cb : CoreChaseBranch obs kb) (n : Nat) (is_some_at : cb.branch.infinite_list n ≠ none) : ∀ m, m ≤ n → cb.branch.infinite_list m ≠ none := by
    grind

  @[grind]
  theorem prev_is_some_if_is_some' (cb : CoreChaseBranch obs kb) (n : Nat) (is_some_at : (cb.branch.infinite_list n).isSome) : ∀ m, m < n → (cb.branch.infinite_list m).isSome := by
    intro m lt
    have := prev_is_some_if_is_some cb n ((Option.isSomeIffNeqNone (cb.branch.infinite_list n)).mp is_some_at) m lt
    exact (Option.isSomeIffNeqNone (cb.branch.infinite_list m)).mpr this


  @[grind]
  theorem succ_is_none_if_is_none (cb : CoreChaseBranch obs kb) (n : Nat) (is_none_at : cb.branch.infinite_list n = none) : ∀ m, m > n → cb.branch.infinite_list m = none := by
    intro m gt
    apply Classical.byContradiction
    intro contra
    have := cb.branch.get?_eq_none_of_le_of_eq_none is_none_at m (Nat.le_of_lt gt)
    simp only [PossiblyInfiniteList.get?, InfiniteList.get] at this
    rw [this] at contra
    simp at contra

  @[grind]
  theorem succ_eq_is_none_if_is_none (cb : CoreChaseBranch obs kb) (n : Nat) (is_none_at : cb.branch.infinite_list n = none) : ∀ m, m ≥ n → cb.branch.infinite_list m = none := by
    grind

  @[grind]
  theorem all_succ_of_last_index_none (cb : CoreChaseBranch obs kb) (n : Nat) (term_at_n : cb.terminates_at_step n) : ∀ m, m > n → cb.branch.infinite_list m = none := by
    intro m gt
    rcases term_at_n with ⟨is_some, is_none⟩
    exact succ_eq_is_none_if_is_none cb (n + 1) is_none m gt

  def prev_node (cb : CoreChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.infinite_list (i + 1)).isSome) : CoreChaseNode obs kb.rules :=
    (cb.branch.infinite_list i).get (by grind)

  @[grind]
  theorem prev_node_eq (cb : CoreChaseBranch obs kb) (i : Nat) (isSome : (cb.branch.infinite_list (i + 1)).isSome) :
      cb.branch.infinite_list i = some (cb.prev_node i isSome) := by
    simp [prev_node]

  def last_element_index_rec  (cb : CoreChaseBranch ob kb) (ter' : cb.terminates') (n : Nat) : Nat :=
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

  def last_element_index (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : Nat := last_element_index_rec cb ter' 0

  /-
  def connected (cb : CoreChaseBranch obs kb) (n m : Nat) (gt : n ≥ m) (isSome : (cb.branch.infinite_list n).isSome) : Prop :=
    ((cb.branch.infinite_list (n-1)).get (by grind) = (cb.branch.infinite_list m).get (by grind)) ∨ cb.connected (n-1) m (by
      have eqgt : m = n ∨ m < n := Nat.eq_or_lt_of_le gt
      rcases eqgt with eq | gt
      apply Classical.byContradiction
      intro contra
      simp only [ge_iff_le, Nat.not_le] at contra
      rw [eq] at contra
      have : n > 0 := Nat.zero_lt_of_lt contra
      sorry
      grind
    ) (by grind)

  def connected2 (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') (isSome : (cb.branch.infinite_list (cb.last_element_index ter')).isSome) : Prop :=
    ∀ n, n ≤ (cb.last_element_index ter') → exists_trigger_opt_fs_core obs kb.rules ((cb.branch.infinite_list n).get sorry)
  -/

  @[grind]
  theorem last_element_index_eq_termintes'_index_leq (cb : CoreChaseBranch obs kb) (n : Nat) (term_at_n : cb.terminates_at_step n) : ∀ m, m ≤ n → last_element_index_rec cb (by exists n) m = n := by
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
  theorem last_element_index_eq_termintes'_index (cb : CoreChaseBranch obs kb) (n : Nat) (term_at_n : cb.terminates_at_step n) : last_element_index cb (by exists n) = n := by
    apply last_element_index_eq_termintes'_index_leq
    exact term_at_n
    exact Nat.zero_le n

  @[grind]
  theorem terminates'_at_last_index_ter' (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : cb.terminates_at_step (last_element_index cb ter') := by
    rcases ter' with ⟨n, is_some, is_none⟩
    grind

  @[grind]
  theorem last_index_is_some (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : cb.branch.infinite_list (cb.last_element_index ter') ≠ none := by
    rcases ter' with ⟨n, term_at_n⟩
    have := last_element_index_eq_termintes'_index cb n term_at_n
    rw [this]
    exact term_at_n.left

  def last_node (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : CoreChaseNode obs kb.rules :=
    (Option.castToMemIfNotNone (cb.branch.infinite_list (last_element_index cb ter')) (by exact last_index_is_some cb ter'))

  def result (cb : CoreChaseBranch ob kb) (ter' : cb.terminates') : FactSet sig :=
    (Option.castToMemIfNotNone (cb.branch.infinite_list (last_element_index cb ter')) (by
      exact last_index_is_some cb ter')).core

  @[grind]
  theorem terminating_eq_index (cb : CoreChaseBranch obs kb) (m n : Nat) : ((cb.branch.infinite_list n) ≠ none ∧ (cb.branch.infinite_list (n+1) = none) ∧ (cb.branch.infinite_list m) ≠ none ∧ (cb.branch.infinite_list (m+1) = none)) → m = n := by
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
  theorem terminating_has_last_index_core (cb : CoreChaseBranch obs kb) : cb.terminates ↔ ∃ n, (cb.branch.infinite_list n) ≠ none ∧ ∀ m, m > n -> cb.branch.infinite_list m = none := by
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
  theorem exLastNodeOfTerminatingCoreChaseBranch (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : ∃ cn, cn = cb.last_node ter' := by
    exists cb.last_node ter'

  @[grind]
  theorem exResultOfTerminatingCoreChaseBranch (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : ∃ fs, fs = cb.result ter' := by
    exists cb.result ter'

  @[grind]
  theorem coreChaseResultIsCore (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : (cb.result ter').isWeakCore := by
    unfold CoreChaseBranch.result
    have : ∃ cn, cn = cb.last_node ter' := by exact exLastNodeOfTerminatingCoreChaseBranch cb ter'
    rcases this with ⟨cn, cn_last⟩
    unfold CoreChaseBranch.last_node at cn_last
    rw [← cn_last]
    rcases cn with ⟨_,_,_,is_core,_,_,_⟩
    exact is_core

  @[grind]
  theorem origin_isSome (cb : CoreChaseBranch obs kb) (i : Nat) {node : CoreChaseNode obs kb.rules} (eq : cb.branch.infinite_list (i + 1) = some node) : node.origin.isSome := by
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
  theorem prevCoreSubsetOfFactset {x} (cb : CoreChaseBranch obs kb) (n : Nat) (y : CoreChaseNode obs kb.rules) (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) :
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

  -- wrong location
  theorem applyFactIdEq (f g : Fact sig) : GroundTermMapping.applyFact id f = g → f = g := by
    intro h
    unfold GroundTermMapping.applyFact TermMapping.apply_generalized_atom at h
    simp only [List.map_id_fun, id_eq] at h
    rw [GeneralizedAtom.mk.injEq]
    exact ⟨congrArg GeneralizedAtom.predicate h, congrArg GeneralizedAtom.terms h⟩

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
    have eq := applyFactIdEq g f (Eq.symm g_in_ida)
    rw [← eq]
    exact g_in_a

  @[grind]
  theorem exHomFsCore (cb : CoreChaseBranch obs kb) (n : Nat) (x : CoreChaseNode obs kb.rules) (x_eq : cb.branch.infinite_list n = some x) :
    ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fs x.core := by
      exact x.core_sse.right

  @[grind]
  theorem exHomPrevCoreToFactSet (cb : CoreChaseBranch obs kb) (n : Nat) (x y : CoreChaseNode obs kb.rules)
    (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) : ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.fs := by
      have trg_ex := cb.triggers_exist n
      have sub : _ := prevCoreSubsetOfFactset cb n y x_eq y_eq
      have := exHomSubToSet x.core y.fs sub
      exact this

  @[grind]
  theorem origin_trg_result_yields_next_node_fs (cb : CoreChaseBranch obs kb) (i : Nat) (node : CoreChaseNode obs kb.rules) (eq : cb.branch.infinite_list (i + 1) = some node) :
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
  theorem ff_in_core_if_ff_in_fs (cb : CoreChaseBranch obs kb) (n : Nat) (x_eq : cb.branch.infinite_list n = some x) (f : Fact sig) (f_in : f ∈ x.fs) (f_is_ff : f.isFunctionFree) : f ∈ x.core := by
      have ex_gtm := exHomFsCore cb n x x_eq
      rcases ex_gtm with ⟨gtm, gtm_hom⟩
      have eq : gtm.applyFact f = f := gtmHomApplyFactFunctionFreeId x.fs x.core f f_is_ff gtm gtm_hom
      have x_core := x.is_core
      rcases gtm_hom with ⟨gtm_c, gtm_st⟩
      specialize gtm_st f
      apply gtm_st
      exists f; constructor
      . exact f_in
      . conv => left; rw [← eq]


  @[grind]
  theorem db_finite (cb : CoreChaseBranch obs kb) (isSome : (cb.branch.infinite_list 0).isSome = true) : Set.finite ((cb.branch.infinite_list 0).get isSome).core := by
    have := cb.database_first
    simp_all only [Option.get_some]
    grind

  @[grind]
  theorem origin_result_finite {obs : ObsoletenessCondition sig} (node : CoreChaseNode obs rules) (isSome : node.origin.isSome) : Set.finite (node.origin_result isSome).toSet := by
    apply Set.finite_of_list_with_same_elements (node.origin_result isSome)
    intro _; rw [List.mem_toSet]

  @[grind]
  theorem core_finite_if_fs_finite (node : CoreChaseNode obs rules) (fs_fin : node.fs.finite) : node.core.finite := by
    rcases node.core_sse with ⟨sub, ⟨gtm, gtm_hom⟩⟩
    exact Set.finite_of_subset_finite fs_fin sub

  @[grind]
  theorem subsetOfFiniteIsFinite [DecidableEq α] (A B : Set α) (b_fin : B.finite) (sub : A ⊆ B) : A.finite := by
    exact Set.finite_of_subset_finite b_fin sub

  @[grind]
  theorem unionOfFinteIsFinte [DecidableEq α] (A B : Set α) : A.finite ∧ B.finite ↔ (A ∪ B).finite := by
    constructor
    intro ⟨⟨al, al_nodup, al_eq⟩, ⟨bl, bl_nodup, bl_eq⟩⟩
    have dec := Classical.propDecidable
    exists (al ++ bl).eraseDupsKeepRight
    constructor
    exact List.nodup_eraseDupsKeepRight (al ++ bl)
    intro e
    rw [List.mem_eraseDupsKeepRight]
    constructor
    intro in_albl
    rw [List.mem_append] at in_albl
    rcases in_albl with in_a | in_b
    specialize al_eq e
    left
    rw [← al_eq]
    exact in_a
    specialize bl_eq e
    right
    rw [← bl_eq]
    exact in_b
    intro in_ab
    rw [@List.mem_append]
    rcases in_ab with in_a | in_b
    specialize al_eq e
    left
    rw [al_eq]
    exact in_a
    specialize bl_eq e
    right
    rw [bl_eq]
    exact in_b
    intro ab_fin
    have a_sub : A ⊆ (A ∪ B) := by exact Set.subset_union_of_subset_left fun e a => a
    have b_sub : B ⊆ (A ∪ B) := by exact Set.subset_union_of_subset_right B A B fun e a => a
    constructor
    exact subsetOfFiniteIsFinite A (A ∪ B) ab_fin a_sub
    exact subsetOfFiniteIsFinite B (A ∪ B) ab_fin b_sub


  @[grind]
  theorem exNextNodeIfExLoadedNonObsoleteTrigger (cb : CoreChaseBranch obs kb) (n : Nat) (cn : CoreChaseNode obs kb.rules)
     (cn_eq : cb.branch.infinite_list n = some cn) (trg : RTrigger obs kb.rules) (trg_loaded : trg.val.loaded cn.core) (trg_non_obs : ¬ obs.cond trg.val cn.core) :
      ∃ (cn' : CoreChaseNode obs kb.rules), cb.branch.infinite_list (n+1) = some cn' := by
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
  theorem cbNextFsEq (cb : CoreChaseBranch obs kb) (n : Nat) (a b : CoreChaseNode obs kb.rules) (eq_a : cb.branch.infinite_list n = some a) (eq_b : cb.branch.infinite_list (n + 1) = some b) :
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
      rw [eq, Set.union_sym]
      exact lhs
      rcases trg_nex with ⟨trg_nex, b_eq⟩
      grind


  @[grind]
  theorem next_step_finite_if_finite (cb : CoreChaseBranch obs kb) (n : Nat) (a b : CoreChaseNode obs kb.rules) (eq_a : cb.branch.infinite_list n = some a) (eq_b : cb.branch.infinite_list (n + 1) = some b) (a_fin : a.core.finite) :
    b.core.finite := by
      rcases a_fin with ⟨al, al_nodup, al_eq⟩
      have b_fs_eq := cbNextFsEq cb n a b eq_a eq_b
      apply core_finite_if_fs_finite
      rw [b_fs_eq, ← unionOfFinteIsFinte]
      constructor
      exact origin_result_finite b (origin_isSome cb n eq_b)
      exact Set.finite_of_list_with_same_elements al al_eq

  @[grind]
  theorem all_fs_finite (cb : CoreChaseBranch obs kb) (n : Nat) (node : CoreChaseNode obs kb.rules) (eq : cb.branch.infinite_list n = some node) : Set.finite (node.fs) := by
    induction n generalizing node with
      | zero =>
        have := cb.database_first
        grind
      | succ n ih =>
        specialize ih (prev_node cb n (Option.isSome_of_mem eq)) (prev_node_eq cb n (Option.isSome_of_mem eq))
        have origin_yield := origin_trg_result_yields_next_node_fs cb n node eq
        rw [origin_yield, ← unionOfFinteIsFinte]
        constructor
        grind
        have := origin_result_finite node (origin_isSome cb n eq)
        exact this

  @[grind]
  theorem all_core_finite (node : CoreChaseNode obs kb.rules) : Set.finite (node.core) := by
    apply core_finite_if_fs_finite
    exact node.fs_fin

  -- this one or the one below this is superfluous
  theorem result_finite_if_cb_terminates2 (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : Set.finite (cb.result ter') := by
    have : ∃ cn, cn = cb.last_node ter' := by exact exLastNodeOfTerminatingCoreChaseBranch cb ter'
    rcases this with ⟨cn, cn_eq⟩
    rcases ter' with ⟨n, term_at_n⟩
    have := all_core_finite cn
    unfold result
    simp only [Option.castToMemIfNotNone, ne_eq]
    split
    next a b c d e f => exact all_core_finite c
    next => contradiction

  @[grind]
  theorem result_finite_if_cb_terminates (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : Set.finite (cb.result ter') := by
    have : ∃ cn, cn = cb.last_node ter' := by exact exLastNodeOfTerminatingCoreChaseBranch cb ter'
    rcases this with ⟨cn, cn_eq⟩
    unfold last_node at cn_eq
    simp only [Option.castToMemIfNotNone, ne_eq] at cn_eq
    have := last_index_is_some cb ter'
    rcases ter' with ⟨n, term_at_n⟩
    have ter'_eq : cb.last_element_index (Exists.intro n term_at_n : ∃ n, cb.terminates_at_step n) = n := last_element_index_eq_termintes'_index cb n term_at_n
    induction n with
      | zero =>
        unfold result
        have := cb.database_first
        simp only [Option.castToMemIfNotNone, ne_eq]
        split
        next a b c d e f =>
          simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, Option.some.injEq, heq_eq_eq]
          grind
        next => contradiction
      | succ n ih =>
        unfold result
        simp only [Option.castToMemIfNotNone, ne_eq]
        split
        next => grind
        next => contradiction

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


  @[grind]
  theorem exHomCoreSuccCoreIfSuccIsSome (cb : CoreChaseBranch obs kb) (n : Nat) (x y : CoreChaseNode obs kb.rules)
    (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.core := by
      have y_core := y.core_sse
      rcases y_core with ⟨sub, ⟨gtm_yfs_ycore, gtm_yfs_ycore_hom⟩⟩
      have : ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.fs := exHomPrevCoreToFactSet cb n x y x_eq y_eq
      rcases this with ⟨gtm_xcore_yfs, gtm_xcore_yfs_hom⟩
      exists (gtm_yfs_ycore ∘ gtm_xcore_yfs)
      exact GroundTermMapping.isHomomorphism_compose gtm_xcore_yfs gtm_yfs_ycore x.core y.fs y.core gtm_xcore_yfs_hom gtm_yfs_ycore_hom

  @[grind]
  theorem exHomFsSuccFsIfSuccIsSome (cb : CoreChaseBranch obs kb) (n : Nat) (x y : CoreChaseNode obs kb.rules)
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
  theorem exHomCoreAllFollowingCore (cb : CoreChaseBranch obs kb) (n : Nat) (x : CoreChaseNode obs kb.rules) (x_eq : cb.branch.infinite_list n = some x) :
        ∀ m, (cb.branch.infinite_list (n + m)).is_none_or (fun y => ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.core) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.add_zero, Option.is_none_or]
        split
        next => trivial
        next a b y heq => apply exHomSubToSet x.core y.core (by
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
        next => apply exHomSubToSet x.core y.core (by grind)
        next a b z heq =>
          have : ∃ (h : GroundTermMapping sig), h.isHomomorphism z.core y.core := exHomCoreSuccCoreIfSuccIsSome cb (n + m) z y heq y_eq
          rcases ih with ⟨gtm_x_z, gtm_x_z_hom⟩
          rcases this with ⟨gtm_z_y, gtm_z_y_hom⟩
          exists (gtm_z_y ∘ gtm_x_z)
          exact GroundTermMapping.isHomomorphism_compose gtm_x_z gtm_z_y x.core z.core y.core gtm_x_z_hom gtm_z_y_hom

  @[grind]
  theorem exHomFsAllFollowingFs (cb : CoreChaseBranch obs kb) (n : Nat) (x : CoreChaseNode obs kb.rules) (x_eq : cb.branch.infinite_list n = some x) :
        ∀ m, (cb.branch.infinite_list (n + m)).is_none_or (fun y => ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fs y.fs) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.add_zero, Option.is_none_or]
        split
        next => trivial
        next a b y heq => apply exHomSubToSet x.fs y.fs (by
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
        next => apply exHomSubToSet x.fs y.fs (by grind)
        next a b z heq =>
          have : ∃ (h : GroundTermMapping sig), h.isHomomorphism z.fs y.fs := exHomFsSuccFsIfSuccIsSome cb (n + m) z y heq y_eq
          rcases ih with ⟨gtm_x_z, gtm_x_z_hom⟩
          rcases this with ⟨gtm_z_y, gtm_z_y_hom⟩
          exists (gtm_z_y ∘ gtm_x_z)
          exact GroundTermMapping.isHomomorphism_compose gtm_x_z gtm_z_y x.fs z.fs y.fs gtm_x_z_hom gtm_z_y_hom

  @[grind]
  theorem exHomResultIfIsSome (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') (m : Nat) (cn cn_res : CoreChaseNode obs kb.rules)
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

  @[grind]
  theorem allElemDbMappedId (cb : CoreChaseBranch obs kb) (init : CoreChaseNode obs kb.rules) (init_eq : cb.branch.infinite_list 0 = some init) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism init.fs fs2) :
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
  theorem allFfInNextFsIfSome (cb : CoreChaseBranch obs kb) (n : Nat) (x : CoreChaseNode obs kb.rules) (x_eq : cb.branch.infinite_list n = some x) :
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
      have x_core_sse : x.core ⊆ cn_succ.fs := prevCoreSubsetOfFactset cb n cn_succ x_eq cn_succ_eq
      exact x_core_sse f f_in_core
      rcases trg_nex with ⟨trg_nex, succ_eq⟩
      grind

  @[grind]
  theorem cbDbInAllSucc (cb : CoreChaseBranch obs kb) (n : Nat) (init cn : CoreChaseNode obs kb.rules) (init_eq : cb.branch.infinite_list 0 = some init) (cn_eq : cb.branch.infinite_list n = some cn) :
    init.fs ⊆ cn.core := by
      have db_funfree := kb.db.toFactSet.property.right
      have init_eq' : init.fs = kb.db.toFactSet.val := by
        have := cb.database_first
        grind
      induction n generalizing cn with
        | zero =>
          intro f f_in
          refine ff_in_core_if_ff_in_fs cb 0 cn_eq f ?_ ?_
          have eq : cn = init := by grind
          rw [eq]
          exact f_in
          rw [init_eq'] at f_in
          exact db_funfree f f_in
        | succ n ih =>
          have prev_cn_ex : ∃ prev_cn, cb.branch.infinite_list n =  some prev_cn:= by
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

  @[grind]
  theorem exLastNodeWithLastIndexIfTerminates' (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : ∃ last_cn, cb.branch.infinite_list (cb.last_element_index ter') = some last_cn := by
    exists cb.last_node ter'
    unfold last_node
    simp only [Option.castToMemIfNotNone, ne_eq]
    split
    next => trivial
    next => trivial

  @[grind]
  theorem cbDbSubsetResult (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : (kb.db.toFactSet.val ⊆ cb.result ter') := by
    let init_node := (cb.branch.infinite_list 0).get (Option.isSome_of_mem cb.database_first)
    rcases (exLastNodeWithLastIndexIfTerminates' cb ter') with ⟨last_node, last_node_eq⟩
    have t := cbDbInAllSucc cb (cb.last_element_index ter') init_node last_node (by grind)
    intro f f_in
    let := cb.database_first
    have eq : init_node.fs = kb.db.toFactSet.val := by simp_all only [Option.get_some, init_node]
    specialize t last_node_eq f (by grind)
    rw [result]
    simp only [Option.castToMemIfNotNone, ne_eq]
    split
    next => grind
    next => grind

  @[grind]
  theorem resultIsSome (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : cb.branch.infinite_list (cb.last_element_index ter') = some (cb.last_node ter') := by
    unfold last_element_index last_node
    simp only [Option.castToMemIfNotNone, ne_eq]
    split
    next => trivial
    next => trivial

  --have c : CoreChaseNode obs kb.rules := {fs := sorry, fs_fin:=sorry,core:=sorry,is_core:=sorry,core_sse:=sorry,origin:=sorry,fs_contains_origin_result:=sorry}

  @[grind]
  theorem cbNoneAfterLastIndex (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : cb.branch.infinite_list ((cb.last_element_index ter') + 1) = none := by
    apply Classical.byContradiction
    rcases ter' with ⟨n_ter, n_ter_at⟩
    intro contra
    induction n_ter with
      | zero =>
        grind
      | succ n_ter ih =>
        grind

  theorem cbResultModelsKb (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : (cb.result ter').modelsKb kb := by
    constructor
    intro f f_in
    unfold result
    simp only [Option.castToMemIfNotNone, ne_eq]
    split
    next a b c d e g =>
      have := cbDbSubsetResult cb ter'
      specialize this f f_in
      unfold result at this
      simp only [Option.castToMemIfNotNone, ne_eq] at this
      split at this
      next => simp_all only [ne_eq, Option.some.injEq, not_false_eq_true, heq_eq_eq]
      next => simp_all only [ne_eq, reduceCtorEq]
    next => contradiction

    intro r r_in gs sub
    apply Classical.byContradiction
    intro subs_not_obsolete
    let trg : Trigger obs := ⟨r, gs⟩
    have trg_loaded : trg.loaded (cb.result ter') := by apply sub
    have trg_not_obsolete : ¬ obs.cond trg (cb.result ter') := by
      intro contra
      have obs_impl_sat := obs.cond_implies_trg_is_satisfied contra
      apply subs_not_obsolete
      rcases obs_impl_sat with ⟨i, s', obs_impl_sat⟩
      exists i
      exists s'

    have ex_next_node := exNextNodeIfExLoadedNonObsoleteTrigger cb (cb.last_element_index ter') (cb.last_node ter') (resultIsSome cb ter') ⟨trg, r_in⟩ sub trg_not_obsolete
    grind
    -- entweder gibt es active trigger in result, dann muss es aber eine nachfolger node geben → contradiction to termainates at result
    -- es gibt keine active trigger → models ist trivial erfüllt


  /-


  -- if A{i+1}.fs \neq none \to A_i.fs \subset A{i+1}.fs
  -- if cb.terminates → cb.result.universalmodels kb ∧ Set.finite cb.result
  -- ∃ fs, Set.finite fs ∧ fs.universalmodels kb → cb.terminates

  If I is an instance and Σ is a set of tgds and egds,
  then there

  exists a universal model iff the core chase terminates and yields such a model.

  -/

  --@[grind]
  theorem all_results_isomorphic (cb1 cb2 : CoreChaseBranch obs kb) (ter1' : cb1.terminates') (ter2' : cb2.terminates') : ∃ (gtm : GroundTermMapping sig), gtm.isIsomorphism (cb1.result ter1') (cb2.result ter2') := by sorry

  abbrev InductiveHomomorphismResultCore (cb : CoreChaseBranch obs kb) (m : FactSet sig) (depth : Nat) := {gtm : GroundTermMapping sig // (cb.branch.infinite_list depth).is_none_or (fun cn => gtm.isHomomorphism cn.fs m)}


  @[grind]
  theorem memApplyFactSetIfMemApplyFactSetSubSet (h : GroundTermMapping sig) (fs1 fs2 : FactSet sig) (f : Fact sig) (f_af_in_f1 : f ∈ h.applyFactSet fs1) (sub : fs1 ⊆ fs2) :  f ∈ h.applyFactSet fs2 := by
    unfold GroundTermMapping.applyFactSet
    rcases f_af_in_f1 with ⟨f', f'_in, f'_af_eq⟩
    exists f'
    exact ⟨sub f' f'_in, f'_af_eq⟩

  @[grind]
  theorem homFsToFsAlsoHomCoreToFs (fs : FactSet sig) (cn : CoreChaseNode obs kb.rules) (h : GroundTermMapping sig) (h_hom : h.isHomomorphism cn.fs fs) : h.isHomomorphism cn.core fs := by
    rcases h_hom with ⟨h_c, h_af⟩
    constructor
    exact h_c
    intro f f_in
    specialize h_af f
    apply h_af
    exact memApplyFactSetIfMemApplyFactSetSubSet h cn.core cn.fs f f_in (cn.core_sse.left)

  theorem kb_det_head_len_eq (kb_det : kb.isDeterministic): ∀ (r : Rule sig), r ∈ kb.rules.rules → r.head.length = 1 := by
    unfold KnowledgeBase.isDeterministic RuleSet.isDeterministic Rule.isDeterministic at kb_det
    intro r r_in
    specialize kb_det r r_in
    grind

  noncomputable def induction_homomorphism_core (cb : CoreChaseBranch obs kb) (m : FactSet sig) (m_mod : m.modelsKb  kb) (kb_det : kb.isDeterministic) : (depth : Nat) → InductiveHomomorphismResultCore cb m depth
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
      let prev_hom := (induction_homomorphism_core cb m m_mod kb_det j).val
      let prev_cond := (induction_homomorphism_core cb m m_mod kb_det j).property
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
          -- does a trigger exist for prev_node (cn @ j-th index) ?
          let trg_ex_dec := Classical.propDecidable (exists_trigger_opt_fs_core obs kb.rules (prev_node.get (Option.isSome_of_mem prev_node_eq)) (cb.branch.infinite_list j.succ))

          match trg_ex_dec with
            | .isFalse contra => ⟨prev_hom, by
                have trg_ex := cb.triggers_exist j
                rw [Option.is_none_or_iff] at trg_ex
                specialize trg_ex cn prev_node_eq
                cases trg_ex with
                | inl trg_ex => simp only [prev_node_eq] at contra; contradiction
                | inr trg_ex => rw [trg_ex.right]; simp [Option.is_none_or]
                ⟩

            | .isTrue trg_ex =>
              have prev_hom_is_hom : prev_hom.isHomomorphism (prev_node.get (Option.isSome_of_mem prev_node_eq)).fs m := by
                rw [Option.is_none_or_iff] at prev_cond
                specialize prev_cond cn prev_node_eq
                subst prev_hom
                simp_all only [Option.get_some]

              have prev_hom_is_hom_core : prev_hom.isHomomorphism (prev_node.get (Option.isSome_of_mem prev_node_eq)).core m := by
                exact homFsToFsAlsoHomCoreToFs m (prev_node.get (Option.isSome_of_mem prev_node_eq)) prev_hom prev_hom_is_hom

              let trg := Classical.choose trg_ex
              let trg_spec := Classical.choose_spec trg_ex
              let trg_active_for_current_step := trg_spec.left
              let trg_result_used_for_next_chase_step := trg_spec.right

              let trg_variant_for_m : RTrigger obs kb.rules := {
                val := {
                  rule := trg.val.rule
                  subs := fun t => prev_hom (trg.val.subs t)
                }
                property := trg.property
              }

            have trg_variant_loaded_for_m : trg_variant_for_m.val.loaded m := by
              have : trg_variant_for_m.val.loaded (prev_hom.applyFactSet (prev_node.get (Option.isSome_of_mem prev_node_eq)).core) := by
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
                    let t_in_step_j_dec := Classical.propDecidable (∃ f, f ∈ (prev_node.get (Option.isSome_of_mem prev_node_eq)).core ∧ t ∈ f.terms)
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
                specialize prev_cond (prev_node.get (Option.isSome_of_mem prev_node_eq)) (Option.eq_some_of_isSome (Option.isSome_of_mem prev_node_eq))

                simp [Option.is_none_or_iff]
                intro next_node next_node_eq
                constructor
                exact next_hom_id_const
                -- prev node @ j, next node at j+1
                -- next_node_eq
                have next_node_results_from_trg : next_node.fs = (prev_node.get (Option.isSome_of_mem prev_node_eq)).core ∪ trg.val.mapped_head[result_index_for_trg.val].toSet := by
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

                  have head_i_eq : head_index_for_m_subs.val = 0 := by
                    rw [← Nat.lt_one_iff]
                    have len_eq := kb_det_head_len_eq kb_det trg_variant_for_m.val.rule trg.property
                    have trg_len_eq : trg_variant_for_m.val.mapped_head.length = trg_variant_for_m.val.rule.head.length := PreTrigger.length_mapped_head trg_variant_for_m.val.toPreTrigger
                    subst trg_variant_for_m
                    rw [← len_eq]
                    have := i.isLt
                    exact head_index_for_m_subs.isLt

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
                      exact (prev_node.get (Option.isSome_of_mem prev_node_eq)).core_sse.left fact fact_in_prev_step
                      unfold TermMapping.apply_generalized_atom
                      rw [GeneralizedAtom.mk.injEq]
                      constructor
                      . rfl
                      rw [List.map_inj_left]
                      intro ground_term _
                      have : ∃ f, f ∈ (prev_node.get (Option.isSome_of_mem prev_node_eq)).core ∧ ground_term ∈ f.terms := by
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
                                  have h : ∃ f, f ∈ (prev_node.get (Option.isSome_of_mem prev_node_eq)).core ∧ (GroundTerm.func func ts arity_ok) ∈ f.terms := by
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

                                  have : Classical.propDecidable (∃ f, f ∈ (prev_node.get (Option.isSome_of_mem prev_node_eq)).core ∧ (GroundTerm.func func ts arity_ok) ∈ f.terms) = isTrue h := by cases Classical.propDecidable (∃ f, f ∈ (prev_node.get (Option.isSome_of_mem prev_node_eq)).core ∧ (GroundTerm.func func ts arity_ok) ∈ f.terms) <;> trivial
                                  unfold GroundTerm.func at this
                                  rw [this]
                              | inr v_front =>
                                unfold PreTrigger.subs_for_mapped_head
                                rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
                                unfold PreTrigger.functional_term_for_var
                                unfold next_hom

                                have h : ¬ ∃ f, f ∈ (prev_node.get (Option.isSome_of_mem prev_node_eq)).core ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms := by
                                  intro contra
                                  apply trg_active_for_current_step.right
                                  apply obs.contains_trg_result_implies_cond result_index_for_trg
                                  have := (prev_node.get (Option.isSome_of_mem prev_node_eq)).fs_contains_origin_result
                                  have prev_node_origin_some : (prev_node.get (Option.isSome_of_mem prev_node_eq)).origin.isSome := by sorry
                                  simp only [Option.is_none_or_iff] at this
                                  specialize this ⟨trg, result_index_for_trg⟩ sorry
                                  apply Set.subset_trans this

                                  sorry


                                have : Classical.propDecidable (∃ f, f ∈ (prev_node.get (Option.isSome_of_mem prev_node_eq)).core ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms) = isFalse h := by cases Classical.propDecidable (∃ f, f ∈ (prev_node.get (Option.isSome_of_mem prev_node_eq)).core ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms) <;> trivial
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

                                have : Classical.propDecidable (∃ f, f ∈ (trg.val.mapped_head[result_index_for_trg.val]) ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms) = isTrue h := by cases Classical.propDecidable (∃ f, f ∈ (trg.val.mapped_head[result_index_for_trg.val]) ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms) <;> trivial
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


  theorem coreChaseResultIsUniversal (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : ∀ (m : FactSet sig), m.modelsKb kb → ∃ (h : GroundTermMapping sig), h.isHomomorphism (cb.result ter') m := by
    intro m m_mod
    let ind_hom := induction_homomorphism_core cb m m_mod 0
    exists ind_hom
    unfold InductiveHomomorphismResultCore at ind_hom
    have := ind_hom.property
    have db_first := cb.database_first
    simp only [db_first, Option.is_none_or] at this




  -- main theorem
  -- if cb.terminates → cb.result.universalmodels kb ∧ Set.finite cb.result
  -- ∃ fs, Set.finite fs ∧ fs.universalmodels kb → cb.terminates

  theorem neqTerminates'IfCbAllSome (cb : CoreChaseBranch obs kb) : (∀ (n : Nat), (cb.branch.infinite_list n).isSome) → ¬ cb.terminates' := by
    intro all_some ⟨n, ⟨n_some, n_succ_none⟩⟩
    specialize all_some (n + 1)
    rw [Option.isSomeIffNeqNone] at all_some
    contradiction

  @[grind]
  theorem neqTerminatesIffCbAllSome (cb : CoreChaseBranch obs kb) : (∀ (n : Nat), (cb.branch.infinite_list n).isSome) ↔ ¬ cb.terminates := by
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


  theorem main_lhs (cb : CoreChaseBranch obs kb ) : (∃ (fs : FactSet sig), fs.finite ∧ fs.universallyModelsKb kb) → cb.terminates' := by
    intro ⟨U, U_fin, U_umod⟩
    apply terminates'IfTerminatesAndNonEmpty
    have := cb.database_first
    grind
    apply Classical.byContradiction
    intro contra
    unfold terminates at contra
    simp only [not_exists] at contra
    have core_cb_all_some : ∀ (n : Nat), (cb.branch.infinite_list n).isSome := by grind
    have ex_inf_sc : ∀ (std_cb : ChaseBranch obs kb), ¬ std_cb.terminates := by sorry -- contraposition of ∃ finite SC → ∃ finite CC
    let std_cb : ChaseBranch obs kb := sorry
    specialize ex_inf_sc std_cb
    have std_cb_all_some : ∀ (n : Nat), (std_cb.branch.infinite_list n).isSome := by
      unfold ChaseBranch.terminates at ex_inf_sc
      grind
    let R := std_cb.result
    have R_umod : R.universallyModelsKb kb := by
      constructor
      exact ChaseBranch.result_models_kb std_cb
      sorry -- deterministicChaseBranchResultUniversallyModelsKb

    have hom_U_R : ∃ (h : GroundTermMapping sig), h.isHomomorphism U R := by sorry -- by universality
    have hom_R_U : ∃ (h : GroundTermMapping sig), h.isHomomorphism R U := by sorry -- by universality

    have f_first_somewhere : ∀ (f : Fact sig), f ∈ U → ∃ (n : Nat), f ∈ ((std_cb.branch.infinite_list (n + 1)).get (std_cb_all_some (n + 1))).facts.val ∧
      ¬ f ∈ ((std_cb.branch.infinite_list (n)).get (std_cb_all_some (n))).facts.val := sorry

    have hom_U_some_An : ∃ (n : Nat) (h : GroundTermMapping sig), h.isHomomorphism U ((std_cb.branch.infinite_list n).get (std_cb_all_some n)).facts.val := by sorry

    rcases hom_U_some_An with ⟨n_An, hom_U_An, hom_U_An_hom⟩

    let An := ((std_cb.branch.infinite_list n_An).get (std_cb_all_some n_An)).facts.val

    have hom_An_U : ∃ (h : GroundTermMapping sig), h.isHomomorphism An U := by sorry -- by subset

    have ex_cc_with_an_core : ∃ (cb_with_an_core : CoreChaseBranch obs kb) (m : Nat), ((cb.branch.infinite_list m).get (core_cb_all_some m)).core.homSubset An := by sorry

    rcases ex_cc_with_an_core with ⟨cc_with_an_core, an_core_index, is_an_core⟩

    let An_core := ((cc_with_an_core.branch.infinite_list an_core_index).get (by sorry)).core

    have ex_isom_U_core : ∃ (U_core : FactSet sig) (h : GroundTermMapping sig), h.isIsomorphism (U_core) An_core ∧ U_core.homSubset U := by sorry

    have an_umod : An_core.universallyModelsKb kb := by sorry

    have : ∀ (n : Nat), (((cc_with_an_core.branch.infinite_list n).get (by sorry)).core.universallyModelsKb kb) → cc_with_an_core.terminates_at_step n := by sorry

    specialize this an_core_index an_umod


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


    have every_trig : ∀ (n : Nat), exists_trigger_opt_fs_core obs kb.rules ((cb.branch.infinite_list n).get sorry) (cb.branch.infinite_list (n+1)) := by sorry

    sorry

  theorem main_rhs (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') (kb_det : kb.isDeterministic) : (cb.result ter').universallyModelsKb kb := by
    constructor
    exact cbResultModelsKb cb ter'
    apply coreChaseResultIsUniversal cb ter'

end CoreChaseBranch
