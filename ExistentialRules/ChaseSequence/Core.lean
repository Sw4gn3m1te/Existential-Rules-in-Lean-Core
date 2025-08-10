import ExistentialRules.ChaseSequence.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.Basic
import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms

--import Mathlib.Combinatorics.Graph.Basic


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

def ChaseNode.isWeakCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
  Prop := FactSet.isWeakCore node.fact.val

def ChaseNode.isStrongCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
 Prop := FactSet.isStrongCore node.fact.val

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
structure CoreChaseBranch (obs : ObsoletenessCondition sig) (kb: KnowledgeBase sig) extends ChaseBranch obs kb where
  only_cores : ∀ (n : Nat), (branch.infinite_list n ≠ none) → ChaseNode.isWeakCore (branch.infinite_list n)
  -- wie match ich das, ich will for alle elemente wo isSome true ist also das element nicht 'none' ist die node ein core ist
  -- => braucht ggf: define Membership for PossiblyInfiniteList


namespace PossiblyInfiniteList

  def toSet (l : PossiblyInfiniteList α) : Set α := sorry

end PossiblyInfiniteList

-- {{a,b},{a,c},{d}} -> {a,b,c,d}
def setFlatten (S : Set (Set α)) : Set α := sorry

-- theorem 7 (7 depends on 16)
theorem ExUniversalModelIffCoreChaseHasModel : true := sorry



  -- what does it mean for a node to be universal
  def ChaseNode.isUniversal (node : ChaseNode obs rules) : Prop := sorry

  -- core chase preserves universality at every step
  theorem coreChaseUniversalForEachStep (cb : ChaseBranch obs kb) : ∀ node, node ∈ cb.branch → ChaseNode.isUniversal node := sorry


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
theorem coreChaseYieldsCore (cb : CoreChaseBranch obs kb) (core : FactSet sig) : FactSet.isWeakCore cb.result := sorry


-- finite core chase exists iff finite universal model exists
-- two distinct core chase branches have the same result
-- => core chase result does not depend on the order of trigger application


-- resulting Factset of applying a set of gtm's to an existing fact set
-- we need this when implementing a core calculation later
def GroundTermMapping.applyMapSetFactSet (hs : Set (GroundTermMapping sig)) (fs : FactSet sig) : FactSet sig := sorry
  -- {h.applyFactSet fs | h ∈ hs}

-- parallel chase steps can be broken down intro a sequence of single-rule chase steps, both yielding the same result

def CoreChaseBranch.parallel_step : true := sorry

-- this is parallel_step with a core calc afterwards
def CoreChaseBranch.core_chase_step : true := sorry

theorem ChaseBranch.applyMapSetFactSetEqApplyFactSetSeq (hs : Set (GroundTermMapping sig)) (fs : FactSet sig) : true := sorry

  def FactSet.getCore (fs : FactSet sig) : FactSet sig := sorry

  -- cores calculation is only neccessary after finitely many steps
  theorem CoreCalcAfterFiniteEq : true := sorry

  theorem CoreCalcIsIdempotent (fs : FactSet sig) : fs.getCore.getCore = fs.getCore  := sorry


-- define structure of TGDs here
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
