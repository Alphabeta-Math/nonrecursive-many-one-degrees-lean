import Mathlib
import Proofs.FiniteInjuryAndStabilization
import Proofs.FiniteMarkerAvoidance
import Proofs.CofiniteDomainLemma
import Proofs.FixedStageRowStability
import Proofs.ArithmeticalHierarchyLevels
import Proofs.RelativeComputabilityAndEnumerability
import Proofs.ComputablyEnumerableSet
import Proofs.OracleNegativePullbackDecision

set_option maxHeartbeats 2000000
#check Nat.RecursiveIn.comp
#check Nat.RecursiveIn.pair
#check Nat.RecursiveIn.rfind
#check Nat.rfind_dom
#check Nat.rfind
#check Nat.RecursiveIn.of_eq
#check Primrec.nat_pow
#check Primrec.pow
#check REPred.of_eq
#check Set.Infinite.exists_gt
#check Nat.div_add_mod
#check Finset.equivBitIndices_apply
#check Nat.Partrec.Code.exists_code
#check OracleNegativePullback.prim_bits
#check OracleNegativePullback.step_unique
#check OracleTapeSupplier.OAI.FiniteAlgebraicEnvelopes.MachineRealization.WordEvaluator.exists_safe_tape
#check OracleTapeSupplier.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.wrapper_eval
