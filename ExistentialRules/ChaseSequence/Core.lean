import ExistentialRules.ChaseSequence.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.Basic
import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms


variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

def ChaseNode.isWeakCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
  Prop := FactSet.isWeakCore node.fact.val

def ChaseNode.isStrongCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
 Prop := FactSet.isStrongCore node.fact.val

------

def GroundTermMapping.applyMapSetFactSet (hs : Set (GroundTermMapping sig)) (fs : FactSet sig) : true := sorry

def ChaseBranch.applyMapSetFactSetEqApplyFactSetSeq (hs : Set (GroundTermMapping sig)) (fs : FactSet sig) : true := sorry


structure TGD extends Rule sig where
  -- define structure of TGDs here
  p1 : true
  p2 : true

structure EGD extends Rule sig where
 -- define structure of EGDs here
  p1 : true
  p2 : true

def Rule.stratified (a b : Rule sig) : Prop := sorry
-- b
infixr:50 " ≺ " => Rule.stratified

def RuleSet.isWeaklyAcyclic : Prop := sorry

theorem weaklyAcycIfStratified (rs : RuleSet sig) : RuleSet.isWeaklyAcyclic → ∀ r ∈ rs, r.isStratified := by sorry


-- theorem 7
theorem ExUniversalModelIffCoreChaseHasModel : true := sorry

infixr:65 " ⊧ " => FactSet.modelsKb
infixr:65 " ⊧ " => FactSet.modelsDb
infixr:65 " ⊧ " => FactSet.modelsRule
infixr:65 " ⊧ " => FactSet.modelsRules
infixr:65 " ⊧ᵤ" => FactSet.universallyModelsKb

-- if A ⊧ R(x) ↔ B ⊧ R(h x)
def GroundTermMapping.isFull (h : GroundTermMapping sig) : Prop := sorry

-- h is full injective hom.
def GroundTermMapping.isEmbedding (h : GroundTermMapping sig) : Prop := sorry

-- should we define hom indepndent of GTMs ?

-- r : A → B ⊆ A, e is the id on dom(B)
def GroundTermMapping.isRetract (h : GroundTermMapping sig) : Prop := sorry

def GroundTermmapping.isProperRetract (h : GroundTermMapping sig) : Prop := sorry
  -- h.isRetract ∧ ¬ h.surjective

-- if the body is machted return the head with applied h else do nothing
-- => we maybe should split this into a Rule.apply that always applies and a Rule.isActive
--    which returns a prop whenever the body can be matched
-- => ExistentialRules.ChaseSequence.Universality.lean
-- es gibt bereits GTM.isHomomorphism
def Rule.apply (r : Rule sig) (h : GroundTermMapping sig) (fs : FactSet sig) : FactSet sig := sorry

-- cores calculation is only neccessary after finitely many steps
theorem CoreCalcAfterFiniteEq : true := sorry

def FactSet.isFClosedFor (F : Set (GroundTermMapping sig)) (T : FactSet sig) (K : FactSet sig) : Prop := sorry

-- needs refinement
abbrev ModelSet := Set (FactSet sig)

-- U must be finite, K cannot
def isUniversalSetModel (U : Set (FactSet sig)) (K : Set (FactSet sig)) (F : Set (GroundTermMapping sig)) :
  ∀ M ∈ K, ∃ T ∈ U, FactSet.isFClosedFor F T M ∧
  U ⊆ K ∧
  U.finite ∧
  ¬ ∃ U' ⊂ U, isUniversalSetModel U' U F := by sorry
