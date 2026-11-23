import Challenge.ModelSeries

/- Frozen input: Springer/FunctionalRegularity.lean -/
noncomputable section
open PowerSeries Finset
namespace Springer

theorem modelU_ofReal (u τ : ℝ) (m : ℕ) : modelU (u:ℂ) (τ:ℂ) m=((modelU (R:=ℝ) u τ m:ℝ):ℂ) := by sorry

theorem modelV_ofReal (u τ : ℝ) (m : ℕ) : modelV (u:ℂ) (τ:ℂ) m=((modelV (R:=ℝ) u τ m:ℝ):ℂ) := by sorry

end Springer
end
