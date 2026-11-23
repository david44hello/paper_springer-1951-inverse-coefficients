import Springer.ComparisonBranches
open Springer
example (u τ : ℝ) (m : ℕ) : modelU (R:=ℂ) u τ m=Complex.ofReal (modelU (R:=ℝ) u τ m) := modelU_ofReal u τ m
example (u τ : ℝ) (m : ℕ) : modelV (R:=ℂ) u τ m=Complex.ofReal (modelV (R:=ℝ) u τ m) := modelV_ofReal u τ m
#check Springer.modelU_ofReal
#check Springer.modelV_ofReal
#print axioms Springer.modelU_ofReal
#print axioms Springer.modelV_ofReal
#print axioms Springer.comparisonBranch_complex
