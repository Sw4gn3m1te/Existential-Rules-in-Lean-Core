import ExistentialRules.ChaseSequence.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

def ChaseNode.isWeakCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
  Prop := FactSet.isWeakCore node.fact.val

def ChaseNode.isStrongCore {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) :
 Prop := FactSet.isStrongCore node.fact.val

theorem ChaseBranch.sequence_equals_parallel_step (cb : ChaseBranch obs kb) (ts : Set (PreTrigger sig)) : x = x := by sorry
