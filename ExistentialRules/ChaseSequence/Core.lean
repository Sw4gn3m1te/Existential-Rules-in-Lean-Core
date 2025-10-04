import ExistentialRules.ChaseSequence.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.Basic
import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms

--import ExistentialRules.BasicTypes.Sets.Set
--import ExistentialRules.BasicTypes.Sets.Finite
--import ExistentialRules.BasicTypes.Functions.Function


import Aesop
import Canonical
--import Mathlib.Combinatorics.Graph.Basic


/-
ToDos für Lukas:
  - Membership definieren
  - ChaseBranch.fact in ChaseBranch.fs refactorn
-/

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
    after.is_none_or (fun a => a.fs = before.core ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet ∧ a.core = c ∧ a.origin = some ⟨trg, i⟩)

def not_exists_trigger_opt_fs_core (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : CoreChaseNode obs rules) (after : Option (CoreChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.core) ∧ after = none

theorem exFactIfExTerm (kb : KnowledgeBase sig) (t : GroundTerm sig) : t ∈ kb.db.toFactSet.val.terms → ∃ f, f ∈ kb.db.toFactSet.val := by
  rintro ⟨f, f_in_fs, f_in_ter⟩
  exists f

theorem id_is_injective (A : Set α) : Function.injective_for_domain_set id A := by
  intro a b a_in b_in eq
  simp at eq
  exact eq

theorem id_is_surjective (A : Set α) : Function.surjective_for_domain_and_image_set id A A := by
  intro a a_in
  exists a

theorem eachKbDbIsWeakCore (kb : KnowledgeBase sig) : kb.db.toFactSet.val.isWeakCore := by
  let db := kb.db
  let fs := db.val
  intro gtm gtm_hom
  constructor
  intro f gt h contra
  have eq : gtm.applyFact f = f := by
    unfold GroundTermMapping.applyFact
    rw [Fact.mk.injEq]
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
  have : ∃ f, f ∈ kb.db.toFactSet.val := exFactIfExTerm kb a a_in
  have gtm_eq_id : gtm = id := by
    rw [@funext_iff]
    intro gt
    rcases this with ⟨f, f_in⟩
    have db_funfree := kb.db.toFactSet.property.right
    specialize db_funfree f f_in gt (by sorry)
    rcases db_funfree with ⟨c, c_eq⟩
    rcases f_in with ⟨ff, ff_in, ff_eq⟩
    unfold FunctionFreeFact.toFact at ff_eq
    rw [Fact.mk.injEq] at ff_eq
    rcases ff_eq with ⟨ff_pred_eq, ff_map_eq⟩
    rcases gtm_hom with ⟨gtm_c, gtm_sub⟩
    rw [c_eq]
    apply gtm_c (.const c)
  rw [gtm_eq_id] at eq
  exact eq

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
    rintro ⟨n, a, b⟩
    exists (n + 1)

  @[grind]
  theorem terminates'IfTerminatesAndNonEmpty (cb : CoreChaseBranch obs kb) (non_empty : ∃ m, cb.branch.infinite_list m ≠ none) : cb.terminates → cb.terminates' := by
    rintro ⟨n, a⟩
    rcases non_empty with ⟨m, c⟩
    -- n yielded from terminates, thus (n ≥ m)
    induction d : (n - m) generalizing n with
      | zero =>
        have ngt : m > n ∨ m = n := by grind
        cases ngt with
          | inl case =>
            rcases EQ : cb.branch with ⟨l, nh⟩
            have l_eq : l = cb.branch.infinite_list := by rw [EQ]
            have :  (∀ n, l n ≠ none → ∀ m, m < n → l m ≠ none) := by
              intro n' neq_none m' lt
              specialize nh n' neq_none ⟨m', lt⟩
              exact nh
            rw [l_eq] at this
            specialize this m c n case
            contradiction
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
    rcases EQ : cb.branch with ⟨l, nh⟩
    have l_eq : l = cb.branch.infinite_list := by rw [EQ]
    rw [l_eq] at nh
    specialize nh n is_some_at ⟨m, lt⟩
    simp only [← ne_eq]
    rw [← l_eq] at nh
    exact nh

  @[grind]
  theorem prev_eq_is_some_if_is_some (cb : CoreChaseBranch obs kb) (n : Nat) (is_some_at : cb.branch.infinite_list n ≠ none) : ∀ m, m ≤ n → cb.branch.infinite_list m ≠ none := by
    grind

  @[grind]
  theorem prev_is_some_if_is_some' (cb : CoreChaseBranch obs kb) (n : Nat) (is_some_at : (cb.branch.infinite_list n).isSome) : ∀ m, m < n → (cb.branch.infinite_list m).isSome := by
    grind

  @[grind]
  theorem succ_is_none_if_is_none (cb : CoreChaseBranch obs kb) (n : Nat) (is_none_at : cb.branch.infinite_list n = none) : ∀ m, m > n → cb.branch.infinite_list m = none := by
    intro m gt
    apply Classical.byContradiction
    intro contra
    rcases EQ : cb.branch with ⟨l, nh⟩
    have l_eq : l = cb.branch.infinite_list := by rw [EQ]
    rw [← l_eq] at contra is_none_at
    specialize nh m contra ⟨n, gt⟩
    contradiction

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

  def connected2 (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') (isSome : (cb.branch.infinite_list (cb.last_element_index ter')).isSome) : Prop :=
    ∀ n, n ≤ (cb.last_element_index ter') → exists_trigger_opt_fs_core obs kb.rules ((cb.branch.infinite_list n).get sorry)


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
          specialize no_holes m contra
          let n_succ_fin : Fin m := ⟨n+1, n_lt_m⟩
          specialize no_holes n_succ_fin
          apply no_holes
          exact h
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
  theorem prevCoreSubsetOfFactset (cb : CoreChaseBranch obs kb) (n : Nat) (y : CoreChaseNode obs kb.rules) (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) :
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
          grind
        | inr trg_nex =>
          unfold not_exists_trigger_opt_fs_core at trg_nex
          simp only [not_exists] at trg_nex
          rcases trg_nex with ⟨h1, h2⟩
          rw [h2] at y_eq
          contradiction

  -- wrong location
  theorem applyFactSetIdEq (f g : Fact sig) : GroundTermMapping.applyFact id f = g → f = g := by
    intro h
    unfold GroundTermMapping.applyFact at h
    simp only [List.map_id_fun, id_eq] at h
    rw [Fact.mk.injEq]
    exact ⟨congrArg Fact.predicate h, congrArg Fact.terms h⟩

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
    have eq := applyFactSetIdEq g f g_in_ida
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


  -- if A{i+1}.fs \neq none \to A_i.fs \subset A{i+1}.fs
  -- if cb.terminates → cb.result.universalmodels kb ∧ Set.fintie cb.result
  -- ∃ fs, Set.finite fs ∧ fs.universalmodels kb → cb.terminates

  -- (CoreChaseBranch.result cb ter').modelsKb kb muss gezeigt werden !

  -- theorem 7 (7 depends on 16)
  theorem ExUniversalModelIffCoreChaseHasModel (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : (CoreChaseBranch.result cb ter').modelsKb kb → (CoreChaseBranch.result cb ter').universallyModelsKb kb := by
    unfold FactSet.universallyModelsKb
    intro left
    have right : ∀ (m : FactSet sig), m.modelsKb kb → ∃ (h : GroundTermMapping sig), h.isHomomorphism (cb.result ter') m := by
      intro fs fs_mod
      let result := cb.result ter'
      have result_is_core : result.isWeakCore := by apply coreChaseResultIsCore cb
      specialize result_is_core sorry sorry
      sorry
    exact ⟨left, right⟩


  theorem result_models_kb_core (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : (CoreChaseBranch.result cb ter').modelsKb kb := by
    constructor
    unfold FactSet.modelsDb
    unfold CoreChaseBranch.result
    have : ∃ cn, cn = cb.last_node ter' := by exact exLastNodeOfTerminatingCoreChaseBranch cb ter'
    rcases this with ⟨cn, cn_last⟩
    unfold CoreChaseBranch.last_node at cn_last
    rw [← cn_last]
    intro f h
    -- db ⊆ core gilt immer
    -- das stimmt doch garnicht fü die core chase ?
    --> andere def für models benötigt ?
    sorry
    sorry

  -- wie will man das zeigen ?
  --> gibt es keinen core zu infinite sets oder kann es sein, dass es keinen gibt ?

  @[grind]
  theorem db_finite (cb : CoreChaseBranch obs kb) (isSome : (cb.branch.infinite_list 0).isSome = true) : Set.finite ((cb.branch.infinite_list 0).get isSome).core := by
    have := cb.database_first
    simp_all only [Option.get_some]
    grind

  @[grind]
  theorem origin_result_finite {obs : ObsoletenessCondition sig} (node : CoreChaseNode obs rules) (isSome : node.origin.isSome) : Set.finite (node.origin_result isSome).toSet := by
    rw [List.toSet_iff_toSet']
    unfold List.toSet' Set.finite
    exists (node.origin_result isSome).eraseDupsKeepRight
    constructor
    exact List.nodup_eraseDupsKeepRight (node.origin_result isSome)
    intro f
    change f ∈ (node.origin_result isSome).eraseDupsKeepRight ↔ f ∈ node.origin_result isSome
    exact List.mem_eraseDupsKeepRight (node.origin_result isSome) f

  @[grind]
  theorem core_finite_if_fs_finite (node : CoreChaseNode obs rules) (fs_fin : node.fs.finite) : node.core.finite := by
    rcases node.core_sse with ⟨sub, ⟨gtm, gtm_hom⟩⟩
    exact Set.finite_of_subset_finite fs_fin sub

  @[grind]
  theorem unionOfFinteIsFinte (A B : Set α) : A.finite ∧ B.finite ↔ (A ∪ B).finite := by
    constructor
    intro ⟨⟨al, al_nodup, al_eq⟩, ⟨bl, bl_nodup, bl_eq⟩⟩
    have dec := Classical.propDecidable
    exists (al ++ bl).eraseDupsKeepRight
    constructor
    exact List.nodup_eraseDupsKeepRight (al ++ bl)
    intro e
    rw [List.mem_eraseDupsKeepRight]
    grind
    intro ⟨abl, abl_nodup, abl_eq⟩
    -- mit AOC die union in A und B aufteilen ?
    sorry

  theorem cbNextFsEq (cb : CoreChaseBranch obs kb) (n : Nat) (a b : CoreChaseNode obs kb.rules) (eq_a : cb.branch.infinite_list n = some a) (eq_b : cb.branch.infinite_list (n + 1) = some b) :
    b.fs = (b.origin_result (origin_isSome cb n eq_b)).toSet ∪ a.core := by
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
        rw [origin_yield, List.toSet_iff_toSet', ← unionOfFinteIsFinte]
        constructor
        grind
        have := origin_result_finite node (origin_isSome cb n eq)
        rw [List.toSet_iff_toSet'] at this
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
        next a b y heq => apply exHomSubToSet x.core y.core (by grind)
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
        next a b y heq => apply exHomSubToSet x.fs y.fs (by grind)
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
      rw [Fact.mk.injEq]
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

  theorem exTrigUntilResult (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : false := sorry


  -- stimmt das so überhaupt ? Der hom könnte es ja umbenennen wodurch es kein subset mehr ist
  theorem cbDbSubsetResult (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : (kb.db.toFactSet.val ⊆ cb.result ter') := by
    let init_node := (cb.branch.infinite_list 0).get (by grind)
    let last_node := cb.last_node ter'
    have last_eq : last_node.core = cb.result ter' := by rfl
    have ex_gtm := exHomResultIfIsSome cb ter' 0 init_node (cb.last_node ter') (by grind) rfl
    rcases ex_gtm with ⟨gtm, gtm_hom⟩
    let := cb.database_first
    have eq : init_node.fs = kb.db.toFactSet.val := by simp_all only [Option.get_some, init_node]
    rw [← eq]
    -- only consts are mapped
    intro f f_in
    have eq2 := allElemDbMappedId cb init_node (by grind) gtm gtm_hom f f_in
    unfold result
    simp only [Option.castToMemIfNotNone, ne_eq]
    split
    next
    next opt not_none_opt cn_res not_none_cn_res cn_res_eq heq =>
      have trg_ex := origin_trg_result_yields_next_node_fs cb 0 init_node
      sorry
    next => contradiction


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
    sorry


end CoreChaseBranch


theorem coreChaseResultIsUniversal (cb : CoreChaseBranch obs kb) (rules : RuleSet sig) (ter' : cb.terminates') : (CoreChaseBranch.result cb ter').universallyModelsKb kb := by sorry

  -- core chase preserves universality at every step -> if it terminates then there is a universal model which is the result of the core chase
  theorem coreChaseUniversalForEachStep (cb : ChaseBranch obs kb) : ∀ node, node ∈ cb.branch → ChaseNode.isUniversal node := sorry
  -- define recurser maybe ?

  -- theorem 16, part 1 to 5
  -- (rules : Set (TGD sig)) wie ?


  theorem t16_2 (A_n : PossiblyInfiniteList (FactSet sig)) (A B : FactSet sig) (rules : RuleSet sig) :
    -- definition of membership for PossiblyInfinteList needed
    (A = setFlatten A_n.toSet ∧ B.modelsRules rules ∧ ∃ (h : GroundTermMapping sig), h.isHomomorphism A B) → ∀ a_i, a_i ∈ A_n → ∃ (h' : GroundTermMapping sig), h'.isHomomorphism a_i B := sorry

  -- t16_3
  -- core chase result is model
  -- core chase result is universal model
  -- use Chasebranch.result_models_kb
  theorem coreChaseYieldsUniversalModel (cb : CoreChaseBranch obs kb) : cb.result.universallyModelsKb kb := by sorry

  theorem t16_4 (A_n : PossiblyInfiniteList (FactSet sig)) (B : FactSet sig) (rules : RuleSet sig) (h : GroundTermMapping sig) :
    B.modelsRules rules ∧ ∀ a_i, ∃ (h : GroundTermMapping sig), a_i ∈ A_n ∧  h.isHomomorphism a_i B → ∃ (h' : GroundTermMapping sig), h.isHomomorphism sorry B := sorry

  -- ∃ fs, fs = cb.result ... means the chase result is defined, probably not how we want to express it though
  theorem t16_5 (A B : FactSet sig) (rules : RuleSet sig) (cb : ChaseBranch obs kb) :
    (B.modelsRules rules ∧ ∃ fs, fs = cb.result ∧ ∃ (h : GroundTermMapping sig), h.isHomomorphism A B) →  ∃ (h' : GroundTermMapping sig), h'.isHomomorphism cb.result B := by
      rintro ⟨h1, fs, h2, gtm, h3⟩
      have gtm' : GroundTermMapping sig := sorry
      have gtm'_hom : gtm'.isHomomorphism cb.result B := by sorry -- gtm' should extend gtm
      exists gtm'

--   theorem t16 (cb : ChaseBranch obs kb) (n : Nat) (x y : ChaseNode obs (ruleset : RuleSet sig)) (x_some : Option.isSome (cb.branch.infinite_list n)) (y_some : Option.isSome (cb.branch.infinite_list (n+1))) (x_def : x = Option.get (cb.branch.infinite_list n) x_some ) (y_def : y = Option.get (cb.branch.infinite_list (n+1)) y_some) : FactSet.homSubset x.fact y.fact := by


-- infinte set may not have a core !
-- finite core chase exists iff finite universal model exists
-- two distinct core chase branches have the same result
-- => core chase result does not depend on the order of trigger application
-- (bis auf isomorphie)

--=> not chase tree


-- resulting Factset of applying a set of gtm's to an existing fact set
-- we need this when implementing a core calculation later

-- eher Listen nutzen
def GroundTermMapping.applyMapSetFactSet (hs : Set (GroundTermMapping sig)) (fs : FactSet sig) : FactSet sig := sorry
  -- {h.applyFactSet fs | h ∈ hs}

-- parallel chase steps can be broken down intro a sequence of single-rule chase steps, both yielding the same result

def CoreChaseBranch.parallel_step : true := sorry

-- this is parallel_step with a core calc afterwards
def CoreChaseBranch.core_chase_step : true := sorry


theorem ChaseBranch.applyMapSetFactSetEqApplyFactSetSeq (hs : Set (GroundTermMapping sig)) (fs : FactSet sig) : true := sorry


  -- für eine nicht spezifische implementierung könnte man einfach nur den type angeben welcher einen core forced
  def FactSet.getCore (fs : FactSet sig) : FactSet sig := sorry

  -- cores calculation is only neccessary after finitely many steps
  theorem CoreCalcAfterFiniteEq : true := sorry

  theorem CoreCalcIsIdempotent (fs : FactSet sig) : fs.getCore.getCore = fs.getCore  := sorry


-- define structure of TGDs here
-- alle Regeln sind bereits TGDs aber mit disjunction
-- regeln sind deterministic wenn der head länge 1 hat
-- Aufbau {{∧} ∨ {∧} ... }
structure TGD extends Rule sig where
  -- idee hier ist eine extra liste "existential_binder" zu haben, welche alle existenziell gebundenen vars enthält
  -- "existential_binder_is_distinct" asserted, dass nur neue vars gebunden werden können
  -- => Was ist mit P(x,y) → ∃ x, R(x,y)  ,sagen wir einfach, dass man das nicht darf ?
  existential_binder : List sig.V
  existential_binder_is_distinct : ∀ v, v ∈ existential_binder → ¬ v ∈  List.map var (List.flatMap terms head)

-- define structure of EGDs here
structure EGD extends Rule sig where
  p1 : true
  p2 : true

def Rule.prec (a b : Rule sig) : Prop := sorry
--
infixr:50 " ≺ " => Rule.prec

-- the set of constraints in every cycle of G(Σ) is weakly acyclic (G(Σ)) is the chase graph)
def RuleSet.isStratified (rs : RuleSet sig) : true := sorry

-- for defining weakly acyclic
structure Position (A : Atom sig) where
  R : sig.P
  i : Nat
  i_in_range : 1 ≤ i ∧ i ≤ sig.arity R

-- we should realy consider using Mathlib Graphs / SimpleGraphs
structure Graph where
  V : Set α
  E : Set (α × α)

namespace Graph

  def reachNext (G : Graph) (v1 v2 : α) : Prop := (v1, v2) ∈ G.E

  -- show termination, but what if we have reachability by an infinite path, do we care ?
  def reachable (G : Graph) (v1 v2 : α) : Prop := ∃ v, (reachNext G v1 v ∧ reachable G v v2)

  def hasLoop (G : Graph) : Prop := ∃ v, v ∈ G.V → (v, v) ∈ G.E

  def hasCycle (G : Graph) : Prop := ∃ vs, vs ⊆ G.V → true

end Graph

-- (rules : Set (TGD sig)) wie ?

-- def 9 from appendix (weakly acyclic)
structure DependencyGraph (rules : RuleSet sig) extends Graph (RuleSet sig) where
  V : {Position.fromAtom A | A ∈ rule ∈ rules}
  E : sorry

-- rs is wa if its dependency graph has no cycles with an existential edge

def DependencyGraph.hasExistentialCycle (G : DependencyGraph rules) : Prop := sorry

-- implement check for cycle with existential edge

def RuleSet.isWeaklyAcyclic (rs : RuleSet sig) : Prop := ¬ DependencyGraph.hasExistentialCycle (DependencyGraph rs)

-- All weakly-acyclic sets of TGDs and EGDs are stratified
theorem rsWeaklyAcycIfStratified (rs : RuleSet sig) : rs.isWeaklyAcyclic → rs.isStratified := by sorry

-- should we define hom indepndent of GTMs ?
-- like make a more generell definition in the Function namespace

namespace GroundTermMapping

  -- if A ⊧ R(x) ↔ B ⊧ R(h x)
  def isFull (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
    h.isHomomorphism A B ∧ ∀ a, A.modelsFact a ↔ B.modelsFact (h.applyFact a)

  -- h is full injective hom.
  def isEmbedding (h : GroundTermMapping sig) (A B : FactSet sig) : Prop :=
    h.isFull A B ∧ Function.injective_for_domain_set h sorry

  -- r : A → B ⊆ A, e is the id on dom(B)
  def isRetract (h : GroundTermMapping sig) (A B : FactSet sig) : Prop := sorry

  def isProperRetract (h : GroundTermMapping sig) : Prop := sorry
    -- h.isRetract ∧ ¬ h.surjective

  def isExtension (h : GroundTermMapping sig) (A B C : FactSet sig) : Prop := sorry

end GroundTermMapping


-- if the body is machted return the head with applied h else do nothing
-- => we maybe should split this into a Rule.apply that always applies and a Rule.isActive
--    which returns a prop whenever the body can be matched
-- => ExistentialRules.ChaseSequence.Universality.lean
-- es gibt bereits GTM.isHomomorphism
def Rule.apply (r : Rule sig) (h : GroundTermMapping sig) (fs : FactSet sig) : FactSet sig := sorry




def FactSet.isFClosedFor (F : Set (GroundTermMapping sig)) (T : FactSet sig) (K : FactSet sig) : Prop := sorry

-- needs refinement
abbrev ModelSet := Set (FactSet sig)
-- U must be finite, K cannot
def isUniversalModelSet  (U : Set (FactSet sig)) (K : Set (FactSet sig)) (F : Set (GroundTermMapping sig)) :
  ∀ M, M ∈ K → ∃ T, T ∈ U → FactSet.isFClosedFor F T M ∧
  U ⊆ K ∧
  U.finite ∧
  ¬ ∃ U', U' ⊂ U → isUniversalModelSet U' U F := by sorry

-- chase sequence A_0,A_1... is terminating if A_n ⊧ Σ
theorem ChaseTermIfExModel (cb : ChaseBranch obs kb) (rules : RuleSet sig) : ∃ e, e ∈ cb.branch →  FactSet.modelsRules e rules := by sorry
-- => Membership on possibly infinite List ?

-- All chase results are hom equiv.
theorem ChaseResultHomEq (ct : ChaseTree obs kb) (cb cb' : ChaseBranch obs kb) (cb_mem : cb ∈ ct.branches) (cb'_mem : cb' ∈ ct.branches):
  ∃ (h : GroundTermMapping sig), h.applyFactSet cb.result = cb'.result := by sorry
