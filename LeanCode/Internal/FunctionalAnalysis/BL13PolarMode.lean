import BL12TensorCoordinates

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.FourierGrade

def angularPhaseLinear (mode : ℤ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (Complex.I * (mode : ℂ)) • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem angularPhaseLinear_norm_le (mode : ℤ) : ‖angularPhaseLinear mode‖ ≤ |(mode : ℝ)| := by
  rw [angularPhaseLinear, norm_smul, norm_mul, Complex.norm_I, one_mul]
  have simple : ‖Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro point
    change ‖(point.2 : ℂ)‖ ≤ 1 * ‖point‖
    rw [Complex.norm_real, one_mul]
    exact norm_snd_le point
  have normCast : ‖(mode : ℂ)‖ = |(mode : ℝ)| := by norm_cast
  rw [normCast]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left simple (abs_nonneg _)

theorem angularExponential_smooth (mode : ℤ) :
    ContDiff ℝ ∞ (fun point : ℝ × ℝ => cellExponential mode point.2) :=
  Complex.contDiff_exp.comp (angularPhaseLinear mode).contDiff

theorem angularExponential_iterated_bound (mode : ℤ) (order : ℕ) (point : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ order (fun source : ℝ × ℝ => cellExponential mode source.2) point‖ ≤
      |(mode : ℝ)| ^ order := by
  have representation : (fun source : ℝ × ℝ => cellExponential mode source.2) =
      Complex.exp ∘ angularPhaseLinear mode := rfl
  rw [representation, (angularPhaseLinear mode).iteratedFDeriv_comp_right
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)) point
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  have bound := (iteratedFDeriv ℝ order Complex.exp (angularPhaseLinear mode point)).norm_compContinuousLinearMap_le
    (fun _ => angularPhaseLinear mode)
  have expNorm : ‖iteratedFDeriv ℝ order Complex.exp (angularPhaseLinear mode point)‖ = 1 := by
    rw [complex_exp_real_iteratedFDeriv_norm]
    exact cellExponential_norm mode point.2
  rw [expNorm, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at bound
  exact bound.trans (pow_le_pow_left₀ (norm_nonneg _) (angularPhaseLinear_norm_le mode) order)

theorem radialProfile_iterated_bound (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (order : ℕ) (point : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ order (fun source : ℝ × ℝ => conjugatedProfile parameters mode source.1) point‖ ≤
      ‖iteratedDeriv order (conjugatedProfile parameters mode) point.1‖ := by
  have representation : (fun source : ℝ × ℝ => conjugatedProfile parameters mode source.1) =
      conjugatedProfile parameters mode ∘ ContinuousLinearMap.fst ℝ ℝ ℝ := rfl
  rw [representation, (ContinuousLinearMap.fst ℝ ℝ ℝ).iteratedFDeriv_comp_right
    (conjugatedProfile_smooth parameters mode) point
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  have bound := (iteratedFDeriv ℝ order (conjugatedProfile parameters mode) point.1).norm_compContinuousLinearMap_le
    (fun _ => ContinuousLinearMap.fst ℝ ℝ ℝ)
  rw [show (ContinuousLinearMap.fst ℝ ℝ ℝ) point = point.1 from rfl]
  simpa only [ContinuousLinearMap.norm_fst, Finset.prod_const_one, mul_one,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] using bound

def polarModeField {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) (point : ℝ × ℝ) : ComplexEuclidean dimension :=
  conjugatedProfile parameters mode point.1 • (cellExponential mode.1 point.2 • value)

theorem polarModeField_smooth {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) : ContDiff ℝ ∞ (polarModeField parameters mode value) :=
  ((conjugatedProfile_smooth parameters mode).comp contDiff_fst).smul
    ((angularExponential_smooth mode.1).smul contDiff_const)

theorem angularExponential_vector_iterated_bound {dimension : ℕ} (mode : ℤ)
    (value : ComplexEuclidean dimension) (order : ℕ) (point : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ order (fun source : ℝ × ℝ => cellExponential mode source.2 • value) point‖ ≤
      |(mode : ℝ)| ^ order * ‖value‖ := by
  let multiplication : ℂ →L[ℝ] ComplexEuclidean dimension :=
    (ContinuousLinearMap.toSpanSingleton ℂ value).restrictScalars ℝ
  have bound := multiplication.norm_iteratedFDeriv_comp_left
    (f := fun source : ℝ × ℝ => cellExponential mode source.2) (x := point) (n := order) (N := ∞)
    (angularExponential_smooth mode).contDiffAt
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  have operatorNorm : ‖multiplication‖ = ‖value‖ := by
    simp only [multiplication, ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_toSpanSingleton]
  rw [operatorNorm] at bound
  apply bound.trans
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (angularExponential_iterated_bound mode order point) (norm_nonneg value)

theorem polarModeField_iterated_bound {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) (order : ℕ) (point : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ order (polarModeField parameters mode value) point‖ ≤
      ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖iteratedDeriv index (conjugatedProfile parameters mode) point.1‖ *
          |(mode.1 : ℝ)| ^ (order - index) * ‖value‖ := by
  have product := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := ∞) (n := order)
    (f := fun source : ℝ × ℝ => conjugatedProfile parameters mode source.1)
    (g := fun source : ℝ × ℝ => cellExponential mode.1 source.2 • value)
    ((conjugatedProfile_smooth parameters mode).comp contDiff_fst)
    ((angularExponential_smooth mode.1).smul contDiff_const) point
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  change ‖iteratedFDeriv ℝ order (polarModeField parameters mode value) point‖ ≤ _ at product
  apply product.trans
  apply Finset.sum_le_sum
  intro index _
  have radial := radialProfile_iterated_bound parameters mode index point
  have angular := angularExponential_vector_iterated_bound mode.1 value (order - index) point
  calc
    _ ≤ (order.choose index : ℝ) * ‖iteratedDeriv index (conjugatedProfile parameters mode) point.1‖ *
        (|(mode.1 : ℝ)| ^ (order - index) * ‖value‖) := by gcongr
    _ = _ := by ring

end Grad.BoundaryLift
