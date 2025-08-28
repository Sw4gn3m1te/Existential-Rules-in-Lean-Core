import ExistentialRules.ChaseSequence.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.Basic
import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms

--import Mathlib.Combinatorics.Graph.Basic


/-
ToDos für Lukas:
  - Membership definieren
  - ChaseBranch.fact in ChaseBranch.fs refactorn
-/

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
  core_sse : core.homSubset fs
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
    is_core := sorry
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
  def castCbOptionNotNoneToCb (ocb : Option (CoreChaseNode obs rules)) (not_none : ocb ≠ none) : CoreChaseNode obs rules := by
    match ocb with
      | some cb => exact cb
      | none => contradiction

  def terminates (cb : CoreChaseBranch obs kb) : Prop :=
    ∃ n, (cb.branch.infinite_list n) ≠ none ∧ (cb.branch.infinite_list (n+1) = none)

  -- this should be stronger than cb.finite
  def terminates' (cb : CoreChaseBranch obs kb) : Prop :=
    ∃ n, (cb.branch.infinite_list n = none)

  def terminates_iff_terminates' (cb : CoreChaseBranch obs kb) (non_empty : ∃ n, cb.branch.infinite_list n ≠ none) : (cb.terminates ↔ cb.terminates') := by
    constructor
    intro h
    rcases h with ⟨m, is_some, is_none⟩
    unfold terminates'
    exists (m + 1)
    intro h
    rcases h with ⟨m, is_some⟩
    unfold terminates
    rcases non_empty with ⟨n, h⟩
    induction (m - n) with
      | zero =>
        exists n
        constructor
        exact h
        -- wir wissen, dass m - n = 0 daher ist m = n daher contradiction von is_some und h
        -- contradiction
        sorry
      | succ n ih =>
        rcases ih with ⟨m, ih⟩
        exists m


  theorem prev_is_some_if_is_some (cb : CoreChaseBranch obs kb) (n : Nat) (is_some_at : cb.branch.infinite_list n ≠ none) : ∀ m, m < n → cb.branch.infinite_list m ≠ none := by
    intro m lt
    rcases cb.branch with ⟨l, nh⟩
    have : l = cb.branch.infinite_list := by sorry -- wie merke ich mir das wenn ich cb.branch zerlege das l dann clearly cb.branch.infinite_list ist ?
    rw [this] at nh
    specialize nh n is_some_at
    unfold


    sorry

  theorem succ_is_none_if_is_none (cb : CoreChaseBranch obs kb) (n : Nat) (is_none_at : cb.branch.infinite_list n = n) : ∀ m, m > n → cb.branch.infinite_list m = none := by
    sorry


  def last_element_index_rec  (cb : CoreChaseBranch ob kb) (finite : cb.finite) (n : Nat) : Nat :=
    match cb.branch.infinite_list n with
      | none => n-1
      | some cn =>
        have : Classical.choose finite - (n + 1) < Classical.choose finite - n := by
          apply Nat.sub_add_lt_sub
          rcases finite with ⟨n_max, not_none_at, non_at⟩
          let remaining : Set (CoreChaseNode ob kb.rules) := fun e => ∃ i, e ∈ cb.branch.infinite_list i ∧ n ≤ i ∧ i ≤ n_max
          apply Classical.byContradiction
          intro contra
          simp only [ne_eq, ge_iff_le, Nat.not_le] at contra
          sorry
          simp
        last_element_index_rec cb finite (n+1)
      termination_by Classical.choose finite - n

  def last_element_index (cb : CoreChaseBranch obs kb) (finite : cb.finite) : Nat := last_element_index_rec cb finite 0

  theorem last_index_is_some (cb : CoreChaseBranch obs kb) (finite : cb.finite) : cb.branch.infinite_list (cb.last_element_index finite) ≠ none := by
    let index : Nat := cb.last_element_index finite
    have h1 : index = cb.last_element_index finite := by grind
    rw [← h1]
    rcases finite with ⟨n, some_at_n, non_at_succ_n⟩
    have h2 : index = n := by sorry
    rw [h2]
    exact some_at_n


  def result (cb : CoreChaseBranch ob kb) (finite : cb.finite) : FactSet sig :=
    (castCbOptionNotNoneToCb (cb.branch.infinite_list (last_element_index cb finite)) (by
      exact last_index_is_some cb finite
      )).core



end CoreChaseBranch


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
  -- save nicht right
  def toSet (l : PossiblyInfiniteList α) : Option α → Prop := fun x => x.is_some_and (fun f => f ∈ l)

end PossiblyInfiniteList

-- {{a,b},{a,c},{d}} -> {a,b,c,d}
def setFlatten (S : Set (Set α)) : Set α := sorry

-- theorem 7 (7 depends on 16)
theorem ExUniversalModelIffCoreChaseHasModel (cb : CoreChaseBranch obs kb) (finite : cb.terminates) : (CoreChaseBranch.result cb finite).modelsKb kb → (CoreChaseBranch.result cb finite).universallyModelsKb kb := by
  unfold FactSet.universallyModelsKb
  intro h
  constructor
  exact h
  intro fs fs_mod
  unfold FactSet.modelsKb FactSet.modelsDb FactSet.modelsRules at h
  rcases h with ⟨h1, h2⟩
  have r : Rule sig := sorry
  specialize h2 r
  by_cases case : r ∈ kb.rules.rules
  specialize h2 case
  unfold FactSet.modelsRule at h2
  have gtm : GroundTermMapping sig := by sorry
  have gts : GroundSubstitution sig := by sorry
  specialize h2 gts
  exists gtm
  sorry
  sorry


theorem result_models_kb_core (cb : CoreChaseBranch obs kb) (finite : cb.terminates) : (CoreChaseBranch.result cb finite).modelsKb kb := by
  constructor
  . unfold FactSet.modelsDb
    unfold CoreChaseBranch.result
    intro f h
    sorry



theorem coreChaseResultIsUniversal (cb : CoreChaseBranch obs kb) (rules : RuleSet sig) (finite : cb.terminates) : (CoreChaseBranch.result cb finite).universallyModelsKb kb := by sorry

  -- core chase preserves universality at every step -> if it terminates then there is a universal model which is the result of the core chase
  theorem coreChaseUniversalForEachStep (cb : ChaseBranch obs kb) : ∀ node, node ∈ cb.branch → ChaseNode.isUniversal node := sorry
  -- define recurser maybe ?

  -- theorem 16, part 1 to 5
  -- (rules : Set (TGD sig)) wie ?

  -- A_0 → A_1 → A_2 → ...
  theorem t16_1 (rules : Set (Rule sig)) (cb : ChaseBranch obs kb) : true := sorry

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
    (B.modelsRules rules ∧ ∃ fs, fs = cb.result ∧ ∃ (h : GroundTermMapping sig), h.isHomomorphism A B) →  ∃ (h' : GroundTermMapping sig), h'.isHomomorphism cb.result B := sorry


-- core chase result is core
-- strong oder weak ?
theorem coreChaseYieldsCore (cb : CoreChaseBranch obs kb) : cb.result.isWeakCore := by
  obtain ⟨pil, _, oc, _, _⟩ := cb
  rcases pil with ⟨l, _⟩

  intro gtm ⟨gtm_c, gtm_fs⟩
  constructor
  intro f f_in




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


def Function.isSurjective (f : α → β) (A : Set α) (B : Set β) : Prop := ∀ y, ∃ x, y ∈ B ∧ x ∈ A → (f x = y)

-- instanzieren der Membership class

def Function.bijective (f : α → β) (A : Set α) (B : Set β) : Prop := Function.isInjective f A B ∧ Function.isSurjective f A B

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
