import AST2HilbertFourierBessel

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.AngularSobolevTruncation
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.PhysicalFamily
local instance orbitPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

def gradeAngularRow (grade : ℕ) (mode : ℤ) (field : ClosedJet 1) (angle : ℝ) : APRow 1 grade :=
  angularCharacter mode angle • apRowLinear 1 0 0 1 0 (orthogonalJet (planeRotationEquiv angle) field)

theorem gradeAngularRow_coordinate (grade : ℕ) (mode : ℤ) (field : ClosedJet 1) (angle : ℝ)
    (index : DerivativeIndex grade) :
    gradeAngularRow grade mode field angle index =
      closedContinuousToDiskL2 (angularDerivativeFamily mode field
        (cartesianMultiIndexWord (derivativeMultiIndex index)) angle) := by
  change angularCharacter mode angle • apRowLinear 1 0 0 1 0 (orthogonalJet (planeRotationEquiv angle) field) index = _
  rw [apRowLinear_apply, unweightedJet]
  simp only [show scaledCellWeight 1 1 0 = 1 by norm_num [scaledCellWeight], Complex.ofReal_one, one_pow, one_smul]
  change angularCharacter mode angle • closedContinuousToDiskL2 (closedDerivative
    (orthogonalJet (planeRotationEquiv angle) field) (cartesianOrder (derivativeMultiIndex index))
    (cartesianMultiIndexWord (derivativeMultiIndex index))) = _
  rw [orthogonalJet_derivative]
  exact (closedContinuousToDiskL2_smul _ _).symm

theorem gradeAngularRow_continuous (grade : ℕ) (mode : ℤ) (field : ClosedJet 1) :
    Continuous (gradeAngularRow grade mode field) := by
  have each (index : DerivativeIndex grade) : Continuous (fun angle => gradeAngularRow grade mode field angle index) := by
    simp_rw [gradeAngularRow_coordinate]
    exact (closedValueL2Continuous 1).continuous.comp
      (angularDerivativeFamily_continuous mode field (cartesianMultiIndexWord (derivativeMultiIndex index)))
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi each)

theorem gradeAngularRow_integral (grade : ℕ) (mode : ℤ) (field : ClosedJet 1) :
    apRowLinear (grade := grade) 1 0 0 1 0 (angularClosedJet mode field) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in Icc (0 : ℝ) (2 * Real.pi), gradeAngularRow grade mode field angle := by
  apply PiLp.ext
  intro index
  rw [apRowLinear_apply, unweightedJet]
  simp only [show scaledCellWeight 1 1 0 = 1 by norm_num [scaledCellWeight], Complex.ofReal_one, one_pow, one_smul]
  change closedContinuousToDiskL2 (closedDerivative (angularClosedJet mode field) (cartesianOrder (derivativeMultiIndex index))
    (cartesianMultiIndexWord (derivativeMultiIndex index))) = _
  rw [angularClosedJet_derivative_continuousMap, closedValueL2_real_smul,
    closedValueL2_integral (angularDerivativeFamily_continuous mode field
      (cartesianMultiIndexWord (derivativeMultiIndex index))).continuousOn.integrableOn_Icc]
  have integrableRow : IntegrableOn (gradeAngularRow grade mode field) (Icc (0 : ℝ) (2 * Real.pi)) :=
    (gradeAngularRow_continuous grade mode field).continuousOn.integrableOn_Icc
  have integralCoordinate := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : DerivativeIndex grade => DiskL2 1) index).integral_comp_comm
    integrableRow).symm
  change _ = (2 * Real.pi)⁻¹ • (∫ angle in Icc (0 : ℝ) (2 * Real.pi), gradeAngularRow grade mode field angle) index
  change (∫ angle in Icc (0 : ℝ) (2 * Real.pi), gradeAngularRow grade mode field angle) index =
    ∫ angle in Icc (0 : ℝ) (2 * Real.pi), gradeAngularRow grade mode field angle index at integralCoordinate
  rw [integralCoordinate]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro angle _
  exact (gradeAngularRow_coordinate grade mode field angle index).symm

def gradeOrbitRow (grade : ℕ) (field : ClosedJet 1) (angle : ℝ) : APRow 1 grade :=
  apRowLinear 1 0 0 1 0 (orthogonalJet (planeRotationEquiv angle) field)

theorem gradeOrbitRow_continuous (grade : ℕ) (field : ClosedJet 1) : Continuous (gradeOrbitRow grade field) := by
  have equality : gradeAngularRow grade 0 field = gradeOrbitRow grade field := by
    funext angle
    simp only [gradeAngularRow, gradeOrbitRow, angularCharacter_zero_mode, one_smul]
  rw [← equality]
  exact gradeAngularRow_continuous grade 0 field

theorem gradeOrbitRow_bound (grade : ℕ) (field : ClosedJet 1) (angle : ℝ) :
    ‖gradeOrbitRow grade field angle‖ ≤
      orthogonalGradeConstant grade * ‖apRowLinear (grade := grade) 1 0 0 1 0 field‖ :=
  apOrthogonal_row_bound 1 0 0 1 0 (planeRotationEquiv angle) field

theorem gradeOrbitRow_periodic (grade : ℕ) (field : ClosedJet 1) :
    Function.Periodic (gradeOrbitRow grade field) (2 * Real.pi) := by
  intro angle
  apply congrArg (apRowLinear (grade := grade) 1 0 0 1 0)
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change field.value (orthogonalClosedPoint (planeRotationEquiv (angle + 2 * Real.pi)) point) =
    field.value (orthogonalClosedPoint (planeRotationEquiv angle) point)
  congr 1
  apply Subtype.ext
  change planeRotationEquiv (angle + 2 * Real.pi) point.val = planeRotationEquiv angle point.val
  simpa only [← physicalRotation_eq_orthogonal] using physicalRotation_periodic point.val angle

def gradeOrbitCircle (grade : ℕ) (field : ClosedJet 1) : CellCircle → APRow 1 grade :=
  AddCircle.liftIco (2 * Real.pi) 0 (gradeOrbitRow grade field)

theorem gradeOrbitCircle_continuous (grade : ℕ) (field : ClosedJet 1) :
    Continuous (gradeOrbitCircle grade field) :=
  AddCircle.liftIco_continuous ((gradeOrbitRow_periodic grade field) 0).symm
    (gradeOrbitRow_continuous grade field).continuousOn

theorem gradeOrbitCircle_bound (grade : ℕ) (field : ClosedJet 1) (angle : CellCircle) :
    ‖gradeOrbitCircle grade field angle‖ ≤
      orthogonalGradeConstant grade * ‖apRowLinear (grade := grade) 1 0 0 1 0 field‖ := by
  unfold gradeOrbitCircle AddCircle.liftIco
  exact gradeOrbitRow_bound grade field _

theorem angularCharacter_fourier (mode : ℤ) (angle : ℝ) :
    angularCharacter mode angle = fourier (-mode) (angle : CellCircle) := by
  change cellExponential (-mode) angle = cellCharacter (-mode) (angle : CellCircle)
  exact (cellCharacter_coe _ _).symm

theorem gradeOrbitCircle_coefficient (grade : ℕ) (field : ClosedJet 1) (mode : ℤ) :
    fourierCoeff (gradeOrbitCircle grade field) mode =
      apRowLinear (grade := grade) 1 0 0 1 0 (angularClosedJet mode field) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, gradeAngularRow_integral]
  simp only [zero_add, one_div]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  intro angle inside
  have lower : angle ∈ Ico (0 : ℝ) (2 * Real.pi) := Ioo_subset_Ico_self inside
  dsimp only
  rw [gradeOrbitCircle, AddCircle.liftIco_coe_apply (by simpa only [zero_add] using lower)]
  rw [← angularCharacter_fourier]
  rfl

end Grad.AngularSobolevTruncation
