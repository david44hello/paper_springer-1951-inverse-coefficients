import Springer.Basic

noncomputable section
open Set Filter Function Complex
open scoped Topology ComplexConjugate
namespace Springer

private def quad (w z : ℂ) := z^2-(w+1/2)*z+(w/2-3/4)
private theorem pole_ne {z : ℂ} (hz : 1<‖z‖) : 4*z-2≠0 := by
  intro he
  have Hz : z=(1/2:ℂ) := by linear_combination he/4
  rw [Hz] at hz; norm_num at hz

private theorem value_of_root {w z : ℂ} (h : quad w z=0) : arcMap z=w := by
  unfold quad at h
  have hn : 4*z-2≠0 := by
    intro he
    have Hz : z=(1/2:ℂ) := by linear_combination he/4
    rw [Hz] at h; ring_nf at h; norm_num at h
  unfold arcMap
  suffices E : (z-w)*(4*z-2)=3 by rw [←E,mul_div_cancel_right₀ _ hn]; ring
  linear_combination 4*h

private theorem root_of_value {w z : ℂ} (hz : 1<‖z‖) (h : arcMap z=w) : quad w z=0 := by
  unfold arcMap at h
  have e : 3/(4*z-2)=z-w := by linear_combination -h
  have E := (div_eq_iff (pole_ne hz)).mp e
  unfold quad; linear_combination -E/4

private theorem pair_gap {w a b : ℂ} (hs : a+b=w+1/2) (hp : a*b=w/2-3/4) :
    (1-‖b‖^2)*‖a-1/2‖^2=(3/4:ℝ)*(‖a‖^2-1) := by
  have he : (a-1/2)*b=a/2-1 := by linear_combination hp-hs/2
  have hn := congrArg (fun v : ℂ => ‖v‖^2) he
  simp only [norm_mul,mul_pow] at hn
  have h₂ : ‖a-1/2‖^2-‖a/2-1‖^2=(3/4:ℝ)*(‖a‖^2-1) := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    norm_num [div_eq_mul_inv,Complex.mul_re,Complex.mul_im]; ring
  linear_combination h₂-hn

private theorem roots (w : ℂ) : ∃ a b : ℂ, a+b=w+1/2 ∧ a*b=w/2-3/4 := by
  obtain ⟨d,hd⟩ := IsAlgClosed.exists_pow_nat_eq ((w+1/2)^2-4*(w/2-3/4)) (by decide : 0<2)
  refine ⟨(w+1/2+d)/2,(w+1/2-d)/2,by ring,?_⟩
  linear_combination -hd/4

private theorem factor {a b w : ℂ} (hs : a+b=w+1/2) (hp : a*b=w/2-3/4) (z : ℂ) :
    quad w z=(z-a)*(z-b) := by unfold quad; linear_combination z*hs-hp

theorem arcMap_injective : InjOn arcMap exterior := by
  intro z hz v hv eq
  by_contra hn
  let w := arcMap z
  let b := w+1/2-z
  have hs : z+b=w+1/2 := by dsimp [b]; ring
  have hzq := root_of_value hz (show arcMap z=w from rfl)
  have hp : z*b=w/2-3/4 := by dsimp [b]; unfold quad at hzq; linear_combination -hzq
  have hvq := root_of_value hv (show arcMap v=w from eq.symm)
  rw [factor hs hp,mul_eq_zero] at hvq
  have vb := sub_eq_zero.mp (hvq.resolve_left (sub_ne_zero.mpr (Ne.symm hn)))
  have gap := pair_gap hs hp
  rw [←vb] at gap
  have hs₁ : 1<‖v‖^2 := one_lt_pow₀ (show 1<‖v‖ from hv) (by decide)
  have hs₂ : 1<‖z‖^2 := one_lt_pow₀ (show 1<‖z‖ from hz) (by decide)
  linarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs₁.le) (sq_nonneg ‖z-1/2‖)]

def arcProfile (t : ℂ) := 1-3*t^2/(4-2*t)

theorem arc_profile (t : ℂ) (ht : ‖t‖<1) : profile arcMap t=arcProfile t := by
  by_cases hn : t=0
  · simp [hn,arcProfile]
  have h : 4-2*t≠0 := by
    intro he; have hh : t=2 := by linear_combination -he/2
    rw [hh] at ht; norm_num at ht
  have h' : 4*t⁻¹-2≠0 := by
    apply pole_ne
    rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.mpr hn)).mpr ht
  simp only [profile,if_neg hn,arcMap,arcProfile]
  field_simp <;> ring

theorem arcMap_sigma : Sigma arcMap := by
  have hd {t : ℂ} (ht : t∈disc) : 4-2*t≠0 := by
    intro he; have h : t=2 := by linear_combination -he/2
    simpa [h,disc] using ht
  have he (t : ℂ) (ht : t∈disc) : profile arcMap =ᶠ[𝓝 t] arcProfile := by
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with x hx
    exact arc_profile x (by simpa only [Metric.mem_ball,dist_zero_right] using hx)
  refine ⟨fun z hz => ?_,arcMap_injective,fun t ht => ?_,?_⟩
  · unfold arcMap; fun_prop (disch := exact pole_ne hz)
  · apply AnalyticAt.congr _ (he t ht).symm
    unfold arcProfile; fun_prop (disch := exact hd ht)
  · rw [(he 0 (by simp [disc])).deriv_eq]
    unfold arcProfile
    have H := (((hasDerivAt_id (0:ℂ)).pow 2).const_mul 3).div
      (((hasDerivAt_id (0:ℂ)).const_mul 2).const_sub 4) (by norm_num)
    simpa [id_eq] using (H.const_sub 1).deriv

private theorem one_add_norm_sq (v : ℂ) : ‖1+v‖^2=1+2*v.re+‖v‖^2 := by
  simp [Complex.sq_norm,Complex.normSq_apply]; ring

private theorem arc_iff (w : ℂ) :
    w∈circularArc ↔ ‖w/2-3/4‖=1 ∧ ‖1+(w/2-3/4)‖≤1 := by
  let v := w/2-3/4
  have e : w-3/2=2*v := by dsimp [v]; ring
  have er : v.re=w.re/2-3/4 := by simp [v,div_eq_mul_inv,Complex.mul_re,Complex.mul_im] <;> ring
  change (‖w-3/2‖=2 ∧ w.re≤1/2) ↔ ‖v‖=1 ∧ ‖1+v‖≤1
  rw [e,norm_mul,Complex.norm_ofNat]
  have h := one_add_norm_sq v
  constructor
  · rintro ⟨hn,hr⟩
    have hv : ‖v‖=1 := by linarith
    refine ⟨hv,le_of_sq_le_sq (by rw [h,hv,er]; nlinarith) zero_le_one⟩
  · rintro ⟨hn,hr⟩
    have hh := pow_le_pow_left₀ (norm_nonneg _) hr 2
    rw [h,hn,er] at hh
    exact ⟨by rw [hn]; norm_num,by nlinarith⟩

private theorem circle_roots {w : ℂ} (hw : w∈circularArc) :
    ∃ a b : ℂ, a+b=w+1/2 ∧ a*b=w/2-3/4 ∧ ‖a‖=1 ∧ ‖b‖=1 := by
  obtain ⟨hn,hb⟩ := (arc_iff w).mp hw
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq (w/2-3/4) (by decide : 0<2)
  have hu' := congrArg norm hu
  rw [norm_pow,hn] at hu'
  have hunit : ‖u‖=1 := by nlinarith [norm_nonneg u]
  have huconj : u*conj u=1 := by rw [Complex.mul_conj',hunit]; norm_num
  let x := 2*u.re
  have he : u*(x:ℂ)=1+(w/2-3/4) := by
    have h : (x:ℂ)=u+conj u := by dsimp [x]; push_cast; apply Complex.ext <;> simp <;> ring
    rw [h,mul_add,huconj,←sq,hu,add_comm]
  have hx : |x|≤1 := by simpa [←he,norm_mul,hunit,Complex.norm_real,Real.norm_eq_abs] using hb
  let y := Real.sqrt (1-x^2)
  have hy : y^2=1-x^2 := Real.sq_sqrt (by nlinarith [sq_abs x,pow_le_pow_left₀ (abs_nonneg x) hx 2])
  let v : ℂ := ⟨x,y⟩
  have hv : ‖v‖=1 := by
    have h : ‖v‖^2=1 := by simp [Complex.sq_norm,Complex.normSq_apply,v]; nlinarith
    nlinarith [norm_nonneg v]
  refine ⟨u*v,u*conj v,?_,?_,by rw [norm_mul,hunit,hv,one_mul],by rw [norm_mul,Complex.norm_conj,hunit,hv,one_mul]⟩
  · have e : v+conj v=2*(x:ℂ) := by apply Complex.ext <;> simp [v] <;> ring
    rw [←mul_add,e,show u*(2*(x:ℂ))=2*(u*(x:ℂ)) by ring,he]; ring
  · rw [show u*v*(u*conj v)=u^2*(v*conj v) by ring,Complex.mul_conj',hv,hu]; norm_num

/-- The complement is the exact closed arc, including its two endpoints. -/
theorem arcMap_image : arcMap '' exterior=circularArcᶜ := by
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩ hw
    obtain ⟨a,b,hs,hp,ha,hb⟩ := circle_roots hw
    have H := root_of_value hz rfl
    rw [factor hs hp,mul_eq_zero] at H
    rcases H with e|e
    · have := sub_eq_zero.mp e; have hz' : 1<‖z‖ := hz; rw [this,ha] at hz'; exact hz'.false
    · have := sub_eq_zero.mp e; have hz' : 1<‖z‖ := hz; rw [this,hb] at hz'; exact hz'.false
  · intro hw
    obtain ⟨a,b,hs,hp⟩ := roots w
    have qa : quad w a=0 := by simp [factor hs hp]
    have qb : quad w b=0 := by simp [factor hs hp]
    by_cases ha : 1<‖a‖
    · exact ⟨a,ha,value_of_root qa⟩
    by_cases hb : 1<‖b‖
    · exact ⟨b,hb,value_of_root qb⟩
    have both {x y : ℂ} (s : x+y=w+1/2) (p : x*y=w/2-3/4) (hx : ‖x‖≤1) (hy : ‖y‖≤1) : ‖x‖=1 := by
      have gap := pair_gap s p
      have hpos := mul_nonneg (sub_nonneg.mpr (show ‖y‖^2≤1 from by simpa using pow_le_pow_left₀ (norm_nonneg _) hy 2)) (sq_nonneg ‖x-1/2‖)
      by_contra ne
      have hlt := lt_of_le_of_ne hx ne
      nlinarith [mul_pos (sub_pos.mpr hlt) (show 0<1+‖x‖ by positivity)]
    have ua := both hs hp (le_of_not_gt ha) (le_of_not_gt hb)
    have ub := both (add_comm a b ▸ hs) (mul_comm a b ▸ hp) (le_of_not_gt hb) (le_of_not_gt ha)
    exfalso
    apply hw
    apply (arc_iff w).mpr
    refine ⟨by rw [←hp,norm_mul,ua,ub,one_mul],?_⟩
    have hnorm := norm_add_le a b
    have e : 1+(w/2-3/4)=(a+b)/2 := by rw [hs]; ring
    rw [e,norm_div,Complex.norm_ofNat]
    rw [ua,ub] at hnorm
    linarith

end Springer
