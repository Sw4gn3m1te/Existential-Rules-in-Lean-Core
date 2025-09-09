import ExistentialRules.ChaseSequence.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.Basic
import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms



import Aesop
--import Mathlib.Combinatorics.Graph.Basic


/-
ToDos für Lukas:
  - Membership definieren
  - ChaseBranch.fact in ChaseBranch.fs refactorn
-/

-- set_option pp.proofs true

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

def ChaseNode.isWeakCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
  Prop := FactSet.isWeakCore node.fact.val

def ChaseNode.isStrongCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
 Prop := FactSet.isStrongCore node.fact.val

def getCore (fs : FactSet sig) (fs_fin : fs.finite) : {wc : FactSet sig // wc.isWeakCore ∧ wc.homSubset fs} := by sorry

structure CoreChaseNode (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  fs : FactSet sig
  fs_fin : fs.finite
  core : FactSet sig
  is_core : core.isWeakCore
  core_sse : FactSet.homSubset core fact
  origin : Option ((trg : RTrigger (obs : LaxObsoletenessCondition sig) rules) × Fin trg.val.mapped_head.length)
  fs_contains_origin_result : origin.is_none_or (fun origin => origin.fst.val.mapped_head[origin.snd.val].toSet ⊆ fact)


-- checkt ob wenn man einen trigger (trg) auf einer menge (before) anwendet, die menge (after) rauskommt
def RTrigger.isStep (trg : Trigger (obs : LaxObsoletenessCondition sig)) (before after : FactSet sig) : Prop :=
  ∃ fact, fact ∈ before → after = before ∪ (trg.mapped_head).flatten.toSet


def exists_trigger_opt_fs_core (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : CoreChaseNode obs rules) (after : Option (CoreChaseNode obs rules)) : Prop :=
  ∃ trg : (RTrigger (obs : LaxObsoletenessCondition sig) rules), trg.val.active before.core ∧ ∃ (c :FactSet sig) (i : _),
    after.is_none_or (fun a => a.fs = before.core ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet ∧ a.core = c ∧ a.origin = some ⟨trg, i⟩)

def not_exists_trigger_opt_fs_core (obs : ObsoletenessCondition sig) (rules : RuleSet sig) (before : CoreChaseNode obs rules) (after : Option (CoreChaseNode obs rules)) : Prop :=
  ¬(∃ trg : (RTrigger obs rules), trg.val.active before.core) ∧ after = none


structure CoreChaseBranch (obs : ObsoletenessCondition sig) (kb: KnowledgeBase sig) where
  branch : PossiblyInfiniteList (CoreChaseNode obs kb.rules)
  database_first : branch.infinite_list 0 = some {
    fs := kb.db.toFactSet
    fs_fin := by exact kb.db.toFactSet.property.left
    core := kb.db.toFactSet -- db is always core
    is_core :=

    sorry
    core_sse := sorry
    origin := none,
    fs_contains_origin_result := by simp [Option.is_none_or]
  }

  triggers_exist : ∀ (n : Nat), (branch.infinite_list n).is_none_or (fun before =>
  let after := branch.infinite_list (n+1)
  (exists_trigger_opt_fs_core obs kb.rules before after) ∨
    (not_exists_trigger_opt_fs_core obs kb.rules before after))
  fairness : ∀ trg : (RTrigger obs kb.rules), ∃ i : Nat, ((branch.infinite_list i).is_some_and (fun fs => ¬ trg.val.active fs.fs))
    ∧ (∀ j : Nat, j > i -> (branch.infinite_list j).is_none_or (fun fs => ¬ trg.val.active fs.fs))


namespace CoreChaseBranch

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

    -- option.get


  -- this should be stronger than cb.finite
  def finite' (cb : CoreChaseBranch obs kb) : Prop :=
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

  def castCbOptionNotNoneToCb (ocb : Option (CoreChaseNode obs rules)) (not_none : ocb ≠ none) : CoreChaseNode obs rules := by
    match ocb with
      | some cb => exact cb
      | none => contradiction

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
    (castCbOptionNotNoneToCb (cb.branch.infinite_list (last_element_index cb ter')) (by exact last_index_is_some cb ter'))

  def result (cb : CoreChaseBranch ob kb) (ter' : cb.terminates') : FactSet sig :=
    (castCbOptionNotNoneToCb (cb.branch.infinite_list (last_element_index cb ter')) (by
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

  -- uses sorry, but there is none ?
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



  theorem eachCoreIsFinite (wc : FactSet sig) (is_core : wc.isWeakCore) : Set.finite wc := by
    unfold Set.finite
    sorry

  theorem result_finite_if_cb_terminates (cb : CoreChaseBranch obs kb) (ter' : cb.terminates') : Set.finite (cb.result ter') := by
    have : ∃ cn, cn = cb.last_node ter' := by exact exLastNodeOfTerminatingCoreChaseBranch cb ter'
    rcases ter' with ⟨n, is_none⟩
    rcases this with ⟨cn, last_node⟩
    refine eachCoreIsFinite (cb.result (Exists.intro n is_none)) ?_
    exact coreChaseResultIsCore cb (Exists.intro n is_none)


end CoreChaseBranch


def Function.isInjective (f : α → β) (A : Set α) (B : Set β) : Prop := ∀ x y, x ∈ A ∧ y ∈ A → (f x = f y → x = y)

def Function.isInjective' (f : α → β) (A : Set α) (B : Set β) : Prop := ∀ x y, x ∈ A ∧ y ∈ A → (x ≠ y → f x ≠ f y)

-- Mathlib.Tactic.Contrapose
theorem Function.isInjectiveIffisInjective' (f : α → β) (A : Set α) (B : Set β) : Function.isInjective f A B ↔ Function.isInjective' f A B := by
  unfold isInjective isInjective'
  constructor
  intro h x y ⟨x_in_A, y_in_A⟩ neq
  specialize h x y ⟨x_in_A, y_in_A⟩
  grind
  intro h x y ⟨x_in_A, y_in_A⟩ feq
  specialize h x y ⟨x_in_A, y_in_A⟩
  grind

def Function.isSurjective (f : α → β) (A : Set α) (B : Set β) : Prop := ∀ y, ∃ x, (y ∈ B ∧ x ∈ A) → (f x = y)

def Function.isBijective (f : α → β) (A : Set α) (B : Set β) : Prop := Function.isInjective f A B ∧ Function.isSurjective f A B

def Set.finite' (S : Set α) : Prop := ∃ (n : Nat) (h : α → Nat), h.isBijective S (fun e => (e ≤ n))

def Set.fin_size (S : Set α) (fin : S.finite') : Nat := by sorry -- n + 1 from S.finite'

theorem Set.singleton_is_finite' (a : α) (S : Set α) (S_def : S = Set.singleton a) : S.finite' := by
  unfold Set.finite'
  exists 0, fun e => 0
  constructor
  intro x y ⟨x_in, y_in⟩ f_eq
  grind
  intro n
  exists a
  rintro ⟨h1, h2⟩
  simp
  simp at h1
  rw [h1]

theorem Set.finite'_union_is_finite' (A B : Set α) (a_fin : A.finite') (b_fin : B.finite') : (A ∪ B).finite' := by
  rcases a_fin with ⟨n1, f1, inj1, surj1⟩
  rcases b_fin with ⟨n2, f2, inj2, surj2⟩
  unfold union finite'
  exists (n1 + n2), sorry
  sorry



------

-- define some syntactic suggar
/-
infixr:65 " ⊧ " => FactSet.modelsKb
infixr:65 " ⊧ " => FactSet.modelsDb
infixr:65 " ⊧ " => FactSet.modelsRule
infixr:65 " ⊧ " => FactSet.modelsRules
infixr:65 " ⊧ᵤ" => FactSet.universallyModelsKb
-/

def FactSet.modelsFact (fs : FactSet sig) (fact : Fact sig) : Prop := sorry

-- define CoreChaseBranch as extention from ChaseBranch
-- Idee, ChaseBranch mit assertion, dass jede Node muss Core sein


  -- problem: die nodes sind nur nach der core calc cores
  -- => wir können einfach sagen, dass es für jede node einen core gibt
  -- wie match ich das, ich will for alle elemente wo isSome true ist also das element nicht 'none' ist die node ein core ist
  -- => braucht ggf: define Membership for PossiblyInfiniteList
  -- nutze bereits gezeigtes resultat hier

namespace PossiblyInfiniteList

  -- class Membership (α : outParam (Type u)) (γ : Type v)


  -- save nicht right
  def toSet (l : PossiblyInfiniteList α) : Option α → Prop := fun x => x.is_some_and (fun f => f ∈ l)

end PossiblyInfiniteList

-- {{a,b},{a,c},{d}} -> {a,b,c,d}
def setFlatten (S : Set (Set α)) : Set α := sorry

-- same as original (kann man das iwi erben i.e. den beweis nicht nochmal komplett genauso hinschreiben ?)




theorem coreChaseResultIsUniversal (cb : CoreChaseBranch obs kb) (rules : RuleSet sig) (finite : cb.terminates) : (CoreChaseBranch.result cb finite).universallyModelsKb kb := by sorry

  -- core chase preserves universality at every step -> if it terminates then there is a universal model which is the result of the core chase
  theorem coreChaseUniversalForEachStep (cb : ChaseBranch obs kb) : ∀ node, node ∈ cb.branch → ChaseNode.isUniversal node := sorry
  -- define recurser maybe ?

  -- theorem 16, part 1 to 5
  -- (rules : Set (TGD sig)) wie ?

  -- A_0 → A_1 → A_2 → ...
  theorem t16_1 (rules : Set (Rule sig)) (cb : ChaseBranch obs kb) : true := sorry

  theorem t16 (cb : ChaseBranch obs kb) (n : Nat) (x y : ChaseNode obs kb.rules)
    (x_some : (cb.branch.infinite_list n).isSome) (y_some : (cb.branch.infinite_list (n+1)).isSome)
    (x_def : x = Option.get (cb.branch.infinite_list n) x_some) (y_def : y = Option.get (cb.branch.infinite_list (n+1)) y_some) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fact y.fact := by
        exists id
        constructor
        intro gt
        split
        next => trivial
        next => trivial
        intro e e_in
        have this1 : x.fact.val ⊆ y.fact.val := by
          have := ChaseBranch.stepIsSubsetOfAllFollowing cb n x (by grind) 1
          unfold Option.is_none_or at this
          split at this
          next => grind
          next => grind
        have this2 : e ∈ x.fact.val := by
          rcases e_in with ⟨f, lhs, rhs⟩
          have this3 : GroundTermMapping.applyFact id f = e → f = e := by
            unfold GroundTermMapping.applyFact
            simp only [List.map_id_fun, id_eq, imp_self]
          grind
        specialize this1 e this2
        exact this1

  theorem t16_core (cb : CoreChaseBranch obs kb) (n : Nat) (x y : CoreChaseNode obs kb.rules)
    (x_some : (cb.branch.infinite_list n).isSome) (y_some : (cb.branch.infinite_list (n+1)).isSome)
    (x_def : x = Option.get (cb.branch.infinite_list n) x_some) (y_def : y = Option.get (cb.branch.infinite_list (n+1)) y_some) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.core := by
        sorry


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
