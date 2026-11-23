import Challenge.ResidueFunctional

/- Frozen input: Springer/ModelSeries.lean -/
noncomputable section
open PowerSeries
namespace Springer

def modelProfile {R : Type*} [CommRing R] (b τ : R) : PowerSeries R :=
  C τ * expand 2 (by decide)
    (rescale (b*τ) (PowerSeries.map (Nat.castRingHom R) catalanSeries))

def modelU {R : Type*} [Field R] (u τ : R) (m : ℕ) := functionalCoeff (modelProfile 1 τ) u m

def modelV {R : Type*} [Field R] (u τ : R) (m : ℕ) := functionalCoeff (modelProfile (1/2) τ) u m

end Springer
end
