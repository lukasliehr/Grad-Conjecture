import ASG11GradeInclusions

noncomputable section
set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

abbrev AnnularSourceBulk (_parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (_angular _cell : ℕ) := lp (fun _ : ℤ × ℤ => RadialL2 dimension lower) 2

theorem weightedRadialCoordinate_bound (dimension : ℕ) (lower : ℝ) (coordinate : Fin 2)
    (field : WeightedRadialH1 dimension lower) :
    ‖weightedRadialCoordinate dimension lower coordinate field‖ ≤ 1 * ‖field‖ := by
  have identity := weightedRadialH1_norm_sq dimension lower field
  fin_cases coordinate
  · change ‖weightedRadialCoordinate dimension lower 0 field‖ ≤ 1 * ‖field‖
    nlinarith [sq_nonneg ‖weightedRadialCoordinate dimension lower 1 field‖,
      norm_nonneg field, norm_nonneg (weightedRadialCoordinate dimension lower 0 field)]
  · change ‖weightedRadialCoordinate dimension lower 1 field‖ ≤ 1 * ‖field‖
    nlinarith [sq_nonneg ‖weightedRadialCoordinate dimension lower 0 field‖,
      norm_nonneg field, norm_nonneg (weightedRadialCoordinate dimension lower 1 field)]

/-- The actual weighted bulk and derivative coordinates on the entire completed
Fourier graph. Coordinate zero is the faithful source inclusion. -/
def annularSourceCoordinate (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) (coordinate : Fin 2) :
    AnnularSourceH1 parameters dimension lower angular cell →L[ℝ]
      AnnularSourceBulk parameters dimension lower angular cell :=
  lpTwoMap (fun _ => weightedRadialCoordinate dimension lower coordinate) 1 zero_le_one
    (fun _ => weightedRadialCoordinate_bound dimension lower coordinate)

theorem annularSourceCoordinate_apply (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) (coordinate : Fin 2)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (mode : ℤ × ℤ) :
    annularSourceCoordinate parameters dimension lower angular cell coordinate field mode =
      weightedRadialCoordinate dimension lower coordinate (field mode) := rfl

theorem annularSourceCoordinate_bound (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) (coordinate : Fin 2)
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    ‖annularSourceCoordinate parameters dimension lower angular cell coordinate field‖ ≤ ‖field‖ := by
  unfold annularSourceCoordinate
  simpa only [one_mul] using lpTwoMap_bound
    (fun _ : ℤ × ℤ => weightedRadialCoordinate dimension lower coordinate) 1 zero_le_one
    (fun _ => weightedRadialCoordinate_bound dimension lower coordinate) field

theorem annularSource_bulk_injective (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ) :
    Function.Injective (annularSourceCoordinate parameters dimension lower angular cell 0) := by
  intro first second same
  apply Subtype.ext
  funext mode
  apply weightedRadial_value_injective dimension lower positive bounded
  exact congrArg (fun bulk : AnnularSourceBulk parameters dimension lower angular cell => bulk mode) same

/-- The natural bulk inclusion rescales only the polynomial Fourier weight. -/
def annularBulkInclusion (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell) :
    AnnularSourceBulk parameters dimension lower highAngular highCell →L[ℝ]
      AnnularSourceBulk parameters dimension lower lowAngular lowCell :=
  lpTwoMap (sourceGradeFamily (RadialL2 dimension lower) lowAngular lowCell highAngular highCell)
    1 zero_le_one (sourceGradeFamily_bound _ _ _ _ _ angularLe cellLe)

theorem annularSourceInclusion_coordinate (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (coordinate : Fin 2) (lowAngular lowCell highAngular highCell : ℕ)
    (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularSourceH1 parameters dimension lower highAngular highCell) :
    annularSourceCoordinate parameters dimension lower lowAngular lowCell coordinate
      (annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field) =
    annularBulkInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe
      (annularSourceCoordinate parameters dimension lower highAngular highCell coordinate field) := by
  apply Subtype.ext
  funext mode
  change weightedRadialCoordinate dimension lower coordinate
    (sourceGradeRatio lowAngular lowCell highAngular highCell mode • field mode) =
      sourceGradeRatio lowAngular lowCell highAngular highCell mode •
        weightedRadialCoordinate dimension lower coordinate (field mode)
  exact map_smul _ _ _

/-- The AH10 weak derivative is inherited from the accepted genuine radial
H1 graph on every Fourier mode. -/
theorem annularSource_weak (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (mode : ℤ × ℤ) :
    CollarWeakDerivative lower
      (collarH1Coordinate (ComplexEuclidean dimension) lower 0
        (weightedToOrdinary dimension lower positive bounded (field mode)))
      (collarH1Coordinate (ComplexEuclidean dimension) lower 1
        (weightedToOrdinary dimension lower positive bounded (field mode))) :=
  weightedRadial_weak dimension lower positive bounded (field mode)

end Grad.AnnularSourceGraph
