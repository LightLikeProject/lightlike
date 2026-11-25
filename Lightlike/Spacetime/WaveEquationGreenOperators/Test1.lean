import Lightlike.Spacetime.WaveEquationGreenOperators.Retarded

/-! Sanity checks for G1-059 (test file): the retarded Green operator is a Green operator. -/

open Lightlike.Spacetime.WaveEquationGreenOperators

#check @isGreenOperator_retarded
#check @IsGreenOperator.unique
