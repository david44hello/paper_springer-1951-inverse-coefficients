import Springer.ResidueFunctional

noncomputable section
open PowerSeries
namespace Springer

/-- In reciprocal coordinates the Laurent series is X times this stored series.
The parameters b=1 and b=1/2 give S and F respectively. -/
def modelProfile {R : Type*} [CommRing R] (b τ : R) : PowerSeries R :=
  C τ * expand 2 (by decide)
    (rescale (b*τ) (PowerSeries.map (Nat.castRingHom R) catalanSeries))

theorem modelProfile_even {R : Type*} [CommRing R] (b τ : R) (k : ℕ) :
    (modelProfile b τ).coeff (2*k) = b^k*(catalan k:R)*τ^(k+1) := by
  simp only [modelProfile,coeff_C_mul,coeff_expand_mul,coeff_rescale,coeff_map,
    catalanSeries_coeff,mul_pow,pow_succ]
  ring_nf
  rfl

theorem modelProfile_odd {R : Type*} [CommRing R] (b τ : R) {k : ℕ} (hk : Odd k) :
    (modelProfile b τ).coeff k=0 := by
  have h : ¬2∣k := by obtain ⟨j,hj⟩ := hk; omega
  simp [modelProfile,coeff_C_mul,coeff_expand_of_not_dvd _ _ _ h]

theorem modelProfile_quadratic {R : Type*} [CommRing R] (b τ : R) :
    modelProfile b τ = C τ + C b*X^2*modelProfile b τ^2 := by
  let T := expand 2 (by decide) (R := R)
  let E := rescale (b*τ) (PowerSeries.map (Nat.castRingHom R) catalanSeries)
  have Q := congrArg (fun f : PowerSeries ℕ =>
    T (rescale (b*τ) (PowerSeries.map (Nat.castRingHom R) f))) catalanSeries_sq_mul_X_add_one
  change C τ * T E = C τ + C b*X^2*(C τ*T E)^2
  have q : (T E)^2*(C (b*τ)*X^2)+1=T E := by
    simpa [E,T,map_add,map_mul,map_pow,PowerSeries.rescale_X,PowerSeries.expand_C,
      PowerSeries.expand_X] using Q
  calc
    C τ * T E = C τ * ((T E)^2*(C (b*τ)*X^2)+1) := congrArg (C τ * ·) q.symm
    _ = _ := by rw [map_mul]; ring

def modelU {R : Type*} [Field R] (u τ : R) (m : ℕ) := functionalCoeff (modelProfile 1 τ) u m

def modelV {R : Type*} [Field R] (u τ : R) (m : ℕ) := functionalCoeff (modelProfile (1/2) τ) u m

theorem model_degree_zero {R : Type*} [Field R] [CharZero R] (u τ : R) :
    modelU u τ 0=τ ∧ modelV u τ 0=τ := by
  have h (b : R) : (modelProfile b τ).coeff 0=τ := by simpa using modelProfile_even b τ 0
  simp [modelU,modelV,functional_degree_zero,h]

theorem model_endpoint {R : Type*} [Field R] [CharZero R] (τ : R) (k : ℕ) :
    modelU 1 τ (2*k)=(catalan k:R)*τ^(k+1)/(2*k).factorial ∧
    modelV 1 τ (2*k)=(1/2:R)^k*(catalan k:R)*τ^(k+1)/(2*k).factorial := by
  simp [modelU,modelV,functional_one,modelProfile_even]

theorem model_odd {R : Type*} [Field R] (u τ : R) {m : ℕ} (hm : Odd m) :
    modelU u τ m=0 ∧ modelV u τ m=0 :=
  ⟨functional_odd_input _ (fun _ h => modelProfile_odd _ _ h) _ hm,
   functional_odd_input _ (fun _ h => modelProfile_odd _ _ h) _ hm⟩

theorem model_nonneg {u τ : ℝ} (hu : u∈Set.Icc 0 1) (hτ : 0≤τ) (m : ℕ) :
    0 ≤ modelV u τ m ∧ modelV u τ m ≤ modelU u τ m := by
  have h (j : ℕ) : 0≤(modelProfile (1/2) τ).coeff j ∧
      (modelProfile (1/2) τ).coeff j≤(modelProfile 1 τ).coeff j := by
    rcases Nat.even_or_odd j with he|ho
    · obtain ⟨k,rfl⟩ := he
      rw [←two_mul,modelProfile_even,modelProfile_even,one_pow,one_mul]
      have hp : (1/2:ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
      constructor
      · positivity
      · exact mul_le_mul_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (catalan k) : (0:ℝ)≤_))
          (pow_nonneg hτ _)
    · simp [modelProfile_odd _ _ ho]
  exact functional_mono hu (fun j => (h j).1) (fun j => (h j).2) m

end Springer
