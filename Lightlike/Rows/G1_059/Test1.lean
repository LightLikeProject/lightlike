import Lightlike.Rows.G1_059.Retarded

/-! Sanity checks for G1-059 (test file): the retarded Green operator is a Green operator. -/

open Lightlike.Rows.G1_059

#check @isGreenOperator_retarded
#check @IsGreenOperator.unique
