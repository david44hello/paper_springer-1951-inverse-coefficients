import Springer.ModelSeries
noncomputable section
open PowerSeries Finset
namespace Springer

theorem functional_map {R S : Type*} [Field R] [Field S] (f : R →+* S) (H : PowerSeries R) (u : R) (m : ℕ) :
    functionalCoeff (PowerSeries.map f H) (f u) m=f (functionalCoeff H u m) := by
  unfold functionalCoeff
  simp only [map_sum,map_mul,map_div₀,map_pow,map_sub,map_one,map_natCast]
  apply sum_congr rfl
  intro j _
  unfold shiftedResidue
  split_ifs <;> simp [←map_pow,coeff_map]

theorem modelProfile_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (b τ : R) :
    PowerSeries.map f (modelProfile b τ) = modelProfile (f b) (f τ) := by
  ext j
  rw [coeff_map]
  rcases Nat.even_or_odd j with ⟨k,rfl⟩|ho
  · simp [←two_mul,modelProfile_even]
  · simp [modelProfile_odd _ _ ho]

theorem modelU_ofReal (u τ : ℝ) (m : ℕ) : modelU (u:ℂ) (τ:ℂ) m=((modelU (R:=ℝ) u τ m:ℝ):ℂ) := by
  simpa [modelU,modelProfile_map] using functional_map Complex.ofRealHom (modelProfile 1 τ) u m

theorem modelV_ofReal (u τ : ℝ) (m : ℕ) : modelV (u:ℂ) (τ:ℂ) m=((modelV (R:=ℝ) u τ m:ℝ):ℂ) := by
  simpa [modelV,modelProfile_map] using functional_map Complex.ofRealHom (modelProfile (1/2) τ) u m

private theorem ac_const (c : ℂ) (a b : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval

private theorem ac_finite_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) {a b : ℝ}
    (h : ∀ i∈s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i∈s, f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ac_const 0 a b
  | insert i s hi ih =>
    simp only [sum_insert hi]
    exact (h i (mem_insert_self _ _)).add (ih (fun j hj => h j (mem_insert_of_mem hj)))

/-- Absolute continuity of Laurent coefficients implies absolute continuity of
every residue coefficient, on a closed interval including its endpoints. -/
theorem functional_ac {H : ℝ → PowerSeries ℂ} {a b : ℝ}
    (h : ∀ j, AbsolutelyContinuousOnInterval (fun t => (H t).coeff j) a b) (u : ℂ) (m : ℕ) :
    AbsolutelyContinuousOnInterval (fun t => functionalCoeff (H t) u m) a b := by
  have hp (n : ℕ) : ∀ j, AbsolutelyContinuousOnInterval (fun t => (H t^n).coeff j) a b := by
    induction n with
    | zero => intro j; simpa using ac_const ((1:PowerSeries ℂ).coeff j) a b
    | succ n ih =>
      intro j
      simp only [pow_succ,coeff_mul]
      exact ac_finite_sum _ _ (fun k _ => (ih k.1).smul (h k.2))
  apply ac_finite_sum
  intro j _
  unfold shiftedResidue
  split_ifs
  · exact (hp (m-j+1) (j-(m-j))).const_smul (u^j*(1-u)^(m-j)/(j.factorial*((m-j+1).factorial:ℂ)))
  · simp only [mul_zero]
    exact ac_const _ a b


theorem modelProfile_ac {h : ℝ → ℂ} {a b : ℝ} (hh : AbsolutelyContinuousOnInterval h a b)
    (c : ℂ) (k : ℕ) :
    AbsolutelyContinuousOnInterval (fun t => (modelProfile c (h t)).coeff k) a b := by
  rcases Nat.even_or_odd k with ⟨j,rfl⟩|ho
  · simp_rw [←two_mul,modelProfile_even]
    have hp (n : ℕ) : AbsolutelyContinuousOnInterval (fun t => h t^n) a b := by
      induction n with
      | zero => simpa using ac_const 1 a b
      | succ n ih => simpa only [pow_succ,Pi.smul_def,smul_eq_mul,Pi.mul_def] using ih.smul hh
    exact (hp (j+1)).const_smul (c^j*(catalan j:ℂ))
  · simp only [modelProfile_odd _ _ ho]
    exact ac_const 0 a b

theorem modelU_ac {h : ℝ → ℂ} {a b : ℝ} (hh : AbsolutelyContinuousOnInterval h a b)
    (u : ℂ) (m : ℕ) : AbsolutelyContinuousOnInterval (fun t => modelU u (h t) m) a b :=
  functional_ac (modelProfile_ac hh 1) u m

theorem modelV_ac {h : ℝ → ℂ} {a b : ℝ} (hh : AbsolutelyContinuousOnInterval h a b)
    (u : ℂ) (m : ℕ) : AbsolutelyContinuousOnInterval (fun t => modelV u (h t) m) a b :=
  functional_ac (modelProfile_ac hh (1/2)) u m

end Springer
