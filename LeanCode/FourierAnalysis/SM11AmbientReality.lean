import SM10FourierReality

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Grad.SmoothingFamily

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension
open Grad.DiskExtension.Operator

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem weightedSmooth_reality {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension)
    (real : cartesianCoreConjugation parameters field = field) :
    IsRealDiskCellField (weightedSmoothEquiv parameters field) := by
  intro point coordinate
  change conj ((weightedSmoothEquiv parameters field).value point coordinate) =
    (weightedSmoothEquiv parameters field).value point coordinate
  obtain ⟨representative, equality⟩ := QuotientAddGroup.mk_surjective point.2
  have gradeReal : GradeCoreReality parameters (GradeCore.ofCoreLinear (grade := 0) field) :=
    (gradeCoreConjugation_fixed_iff_reality parameters _).1 (congrArg GradeCore.ofCoreLinear real)
  have evaluated := congrArg (fun value : ComplexEuclidean dimension => value coordinate)
    (physicalEvaluationLift_real parameters (GradeCore.ofCoreLinear (grade := 0) field)
      gradeReal point.1 representative)
  change conj ((weightedSmoothEquiv parameters field).value (point.1, (representative : CellCircle)) coordinate) =
    (weightedSmoothEquiv parameters field).value (point.1, (representative : CellCircle)) coordinate at evaluated
  simpa only [equality] using evaluated

theorem diskCellFourierCoefficient_reality {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (real : IsRealDiskCellField field) (cell : ℤ) :
    closedJetConjugate (diskCellFourierCoefficientJet field (-cell)) =
      diskCellFourierCoefficientJet field cell := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  rw [closedJetConjugate_value_apply, ← diskCellComponent_fourierCoeff,
    ← diskCellComponent_fourierCoeff]
  simp only [fourierCoeff, neg_neg]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with circle
  change conj (fourier cell circle * field.value (point, circle) coordinate) =
    fourier (-cell) circle * field.value (point, circle) coordinate
  rw [map_mul, fourier_neg]
  exact congrArg (fun value : ℂ => conj (fourier cell circle) * value) (real (point, circle) coordinate)

theorem weightedSmooth_inverse_reality {dimension : ℕ} (parameters : PhaseParameters)
    (field : DiskCellClosedJet dimension) (real : IsRealDiskCellField field) :
    cartesianCoreConjugation parameters ((weightedSmoothEquiv parameters).symm field) =
      (weightedSmoothEquiv parameters).symm field := by
  let original := (weightedSmoothEquiv parameters).symm field
  have coefficient (cell : ℤ) : phaseWeightedJet parameters cell (original.1 cell) =
      diskCellFourierCoefficientJet field cell := by
    rw [← diskCellFourierCoefficientJet_weightedSmoothEquiv]
    exact congrArg (fun value => diskCellFourierCoefficientJet value cell)
      ((weightedSmoothEquiv parameters).apply_symm_apply field)
  apply Subtype.ext
  funext cell
  apply phaseWeightedJet_injective parameters cell
  change phaseWeightedJet parameters cell (closedJetConjugate (original.1 (-cell))) =
    phaseWeightedJet parameters cell (original.1 cell)
  rw [phaseWeightedJet_conjugate_reflect, coefficient, coefficient]
  exact diskCellFourierCoefficient_reality field real cell

theorem weightedFourierExtension_reality {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension)
    (real : cartesianCoreConjugation parameters field = field) :
    FourierReality (weightedFourierExtension parameters field) := by
  have extendedReal := ordinaryExtensionRetraction_linearity_real.2.2.2.2.2.1 dimension
    (weightedSmoothEquiv parameters field) (weightedSmooth_reality parameters field real)
  intro mode coordinate
  apply continuousFourierCoefficient_reality
  intro point output
  exact extendedReal (torusCellToProduct.symm point) output

theorem weightedFourierRetraction_reality {dimension : ℕ} (parameters : PhaseParameters)
    (values : JCore (ComplexEuclidean dimension)) (real : FourierReality values) :
    cartesianCoreConjugation parameters (weightedFourierRetraction parameters values) =
      weightedFourierRetraction parameters values := by
  apply weightedSmooth_inverse_reality
  apply ordinaryExtensionRetraction_linearity_real.2.2.2.2.2.2 dimension
  intro point coordinate
  exact reconstructedTorus_reality values real (torusCellToProduct point) coordinate

theorem ambientScaleDerivative_reality {dimension : ℕ} (parameters : PhaseParameters)
    (order : ℕ) (scale : ℝ) (field : ACore parameters dimension)
    (real : cartesianCoreConjugation parameters field = field) :
    cartesianCoreConjugation parameters (ambientScaleDerivative parameters order scale field) =
      ambientScaleDerivative parameters order scale field :=
  weightedFourierRetraction_reality parameters _
    (fourierScaleDerivative_reality order scale _ (weightedFourierExtension_reality parameters field real))

theorem ambientSmoothing_reality {dimension : ℕ} (parameters : PhaseParameters)
    (scale : ℝ) (field : ACore parameters dimension)
    (real : cartesianCoreConjugation parameters field = field) :
    cartesianCoreConjugation parameters (ambientSmoothing parameters scale field) =
      ambientSmoothing parameters scale field := by
  rw [← ambientScaleDerivative_zero]
  exact ambientScaleDerivative_reality parameters 0 scale field real

theorem constrainedSmoothing_reality {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (scale : ℝ)
    (field : projection.map.range) (real : cartesianCoreConjugation parameters field.1 = field.1) :
    cartesianCoreConjugation parameters (constrainedSmoothing projection scale field).1 =
      (constrainedSmoothing projection scale field).1 := by
  rw [constrainedSmoothing_apply, projection.real, ambientSmoothing_reality parameters scale field.1 real]

theorem constrainedScaleDerivative_reality {dimension : ℕ} {parameters : PhaseParameters}
    (projection : SameGradeRealProjection parameters dimension) (order : ℕ) (scale : ℝ)
    (field : projection.map.range) (real : cartesianCoreConjugation parameters field.1 = field.1) :
    cartesianCoreConjugation parameters (constrainedScaleDerivative projection order scale field).1 =
      (constrainedScaleDerivative projection order scale field).1 := by
  change cartesianCoreConjugation parameters (projection.map (ambientScaleDerivative parameters order scale field.1)) = _
  rw [projection.real, ambientScaleDerivative_reality parameters order scale field.1 real]
  rfl

end Grad.SmoothingFamily
