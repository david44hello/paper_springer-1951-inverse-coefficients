import Springer.Basic

noncomputable section
open Set Filter Function Complex
open scoped Topology
namespace Springer

def beta (m : ℕ) : ℝ := 1-1/(m:ℝ)
def gamma (m : ℕ) : ℝ := 1/(2*(m:ℝ))

def triProfile (m : ℕ) (t : ℂ) := 1+(beta m:ℂ)*t^2+(gamma m:ℂ)*t^3

theorem trinomial_profile (m : ℕ) (t : ℂ) : profile (trinomialMap m) t=triProfile m t := by
  by_cases hn : t=0
  · simp [hn,triProfile]
  · rw [profile,if_neg hn]; simp [trinomialMap,triProfile,beta,gamma,div_eq_mul_inv]; ring_nf; rw [mul_inv_cancel₀ hn]

private theorem tri_value (m : ℕ) (z : ℂ) : trinomialMap m z=z+(beta m:ℂ)*z⁻¹+(gamma m:ℂ)*(z⁻¹)^2 := by
  simp [trinomialMap,beta,gamma,div_eq_mul_inv]

theorem trinomial_injective {m : ℕ} (hm : 3 ≤ m) : InjOn (trinomialMap m) exterior := by
  intro z hz v hv he
  by_contra hn
  have hz₁ : 1<‖z‖ := hz
  have hv₁ : 1<‖v‖ := hv
  have hz₀ := norm_pos_iff.mp (zero_lt_one.trans hz₁)
  have hv₀ := norm_pos_iff.mp (zero_lt_one.trans hv₁)
  have hM : (1:ℝ)< m := by exact_mod_cast (by omega : 1< m)
  have b : 0<beta m := by unfold beta; linarith [one_div_lt_one_div_of_lt zero_lt_one hM]
  have c : 0<gamma m := by unfold gamma; positivity
  have e : beta m+2*gamma m=1 := by unfold beta gamma; field_simp; ring
  have hz' : ‖z⁻¹‖<1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz₁
  have hv' : ‖v⁻¹‖<1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hv₁
  let B := ((beta m:ℂ)*z⁻¹*v⁻¹)
  let C := ((gamma m:ℂ)*z⁻¹*v⁻¹*(z⁻¹+v⁻¹))
  have eqn : (z-v)*(1-B-C)=0 := by
    rw [←sub_eq_zero] at he
    simp only [tri_value] at he
    calc
      _ = (z+(beta m:ℂ)*z⁻¹+(gamma m:ℂ)*(z⁻¹)^2)-(v+(beta m:ℂ)*v⁻¹+(gamma m:ℂ)*(v⁻¹)^2) := by
        dsimp only [B,C]; field_simp <;> ring
      _ = _ := he
  have hvz := (mul_eq_zero.mp eqn).resolve_left (sub_ne_zero.mpr hn)
  have hbc : B+C=1 := by linear_combination -hvz
  have bp : ‖z⁻¹‖*‖v⁻¹‖<1 := (mul_lt_mul_of_pos_right hz' (norm_pos_iff.mpr (inv_ne_zero hv₀))).trans_le (by simpa using hv'.le)
  have hB : ‖B‖<beta m := by
    simp only [B,norm_mul,Complex.norm_of_nonneg b.le,mul_assoc]
    exact mul_lt_of_lt_one_right b bp
  have hC : ‖C‖≤2*gamma m := by
    simp only [C,norm_mul,Complex.norm_of_nonneg c.le]
    have h := norm_add_le z⁻¹ v⁻¹
    calc
      _ ≤ (gamma m*(‖z⁻¹‖*‖v⁻¹‖))*2 := by rw [←mul_assoc]; gcongr; linarith
      _ ≤ _ := by rw [mul_comm 2]; gcongr; exact mul_le_of_le_one_right c.le bp.le
  have H := norm_add_le B C
  rw [hbc,norm_one] at H; linarith

theorem trinomial_sigma {m : ℕ} (hm : 3 ≤ m) : Sigma (trinomialMap m) := by
  have eq : profile (trinomialMap m)=triProfile m := funext (trinomial_profile m)
  refine ⟨fun z hz => ?_,trinomial_injective hm,?_,?_⟩
  · have hn : z≠0 := norm_pos_iff.mp (zero_lt_one.trans (show 1<‖z‖ from hz))
    unfold trinomialMap; fun_prop (disch := first | exact hn | exact pow_ne_zero _ hn)
  · rw [eq]; intro t ht; unfold triProfile; fun_prop
  · rw [eq]
    have hd := ((((hasDerivAt_id (0:ℂ)).pow 2).const_mul (beta m:ℂ)).const_add 1).add
      (((hasDerivAt_id (0:ℂ)).pow 3).const_mul (gamma m:ℂ))
    unfold triProfile; simpa [id_eq,Pi.add_def] using hd.deriv

end Springer
