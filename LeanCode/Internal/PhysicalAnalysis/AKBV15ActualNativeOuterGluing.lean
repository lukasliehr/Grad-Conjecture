import AKBV14SameRescaledWeightedJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set Filter
open scoped ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.Constraints
open Grad.ActualSmoothPhysicalField Grad.SourceCollarDivision Grad.ActualCartesianDescent Grad.PhaseAlgebra Grad.PhysicalAxisEquation

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

theorem weightedCartesianField_cell (point : SpatialPlane) (inside : ‖point‖ ∈ Icc lower 1) (cell : ℤ) :
    angularCoefficient (fun axial => weightedCartesianField curves bounded (point,axial)) cell =
      cartesianWeight parameters cell point •
        angularCoefficient (fun axial => curves.cartesianField bounded (point,axial)) cell := by
  simp only [weightedCartesianField,SmoothLowPhysicalRow.cartesianField,cartesianPhysicalField,
    cartesianFromPolar,Grad.BoundaryLift.complexCoordinate_norm]
  rw [weightedFullField_cell curves bounded ‖point‖ inside]
  rw [cartesianWeight_exp,← radialPhase_eq_cartesianPhase parameters ‖point‖ cell point rfl]
  rw [Complex.coe_smul]

def nativeWeightedOuter (point : SpatialCell) : ComplexEuclidean dimension :=
  weightedCartesianField curves bounded (planarPart point,point 2)

theorem nativeWeightedOuter_smooth :
    ContDiffOn ℝ ∞ (nativeWeightedOuter curves bounded) {point | ‖planarPart point‖ ∈ Icc lower 1} := by
  exact (weightedCartesianField_smooth_closed curves bounded).comp
    ((planarPartCLM.contDiff.prodMk cellCoordinateCLM.contDiff).contDiffOn) (fun _ member => member)

theorem nativeWeightedOuter_periodic (point : SpatialPlane) :
    Function.Periodic (fun axial => nativeWeightedOuter curves bounded (assembleSpatialCell point axial)) (2*Real.pi) := by
  intro axial
  simp only [nativeWeightedOuter,planarPart_assembleSpatialCell,weightedCartesianField,
    cartesianPhysicalField,cartesianFromPolar]
  exact weightedFullField_cell_periodic curves bounded _ _ axial

theorem nativeWeightedOuter_continuous_cell (point : SpatialPlane) (inside : ‖point‖ ∈ Icc lower 1) :
    Continuous (fun axial => nativeWeightedOuter curves bounded (assembleSpatialCell point axial)) :=
  (nativeWeightedOuter_smooth curves bounded).continuousOn.comp_continuous
    (assembleSpatialCellCLM.continuous.comp (continuous_const.prodMk continuous_id))
    (fun axial => by
      change ‖planarPart (assembleSpatialCell point axial)‖ ∈ Icc lower 1
      rw [planarPart_assembleSpatialCell]
      exact inside)

theorem nativeWeightedOuter_cell (point : SpatialPlane) (inside : ‖point‖ ∈ Icc lower 1) (cell : ℤ) :
    angularCoefficient (fun axial => nativeWeightedOuter curves bounded (assembleSpatialCell point axial)) cell =
      cartesianWeight parameters cell point •
        angularCoefficient (fun axial => curves.cartesianField bounded (point,axial)) cell := by
  change angularCoefficient (fun axial => weightedCartesianField curves bounded (point,axial)) cell = _
  exact weightedCartesianField_cell curves bounded point inside cell

/-- The overlap agreement needed for analytic gluing follows from the SAME full-cell representatives, not from a new smooth-field matching hypothesis. -/
theorem rescaledWeightedInterior_same_native (weighted : DiskCellClosedJet dimension)
    (scale : ℝ) (scalePositive : 0 < scale) (upper : ℝ) (upperOne : upper ≤ 1) (upperScale : upper ≤ scale)
    (sameCells : ∀ (point : SpatialPlane) (inside : ‖point‖ ∈ Ioo lower upper) (cell : ℤ),
      (diskCellFourierCoefficientJet weighted cell).value
        (inverseScaledDiskPoint scale scalePositive point (inside.2.le.trans upperScale)) =
      cartesianWeight parameters cell point •
        angularCoefficient (fun axial => curves.cartesianField bounded (point,axial)) cell) :
    EqOn (rescaledWeightedInterior weighted scale) (nativeWeightedOuter curves bounded)
      {point | ‖planarPart point‖ ∈ Ioo lower upper} := by
  intro point inside
  have closed : ‖planarPart point‖ ∈ Icc lower 1 := ⟨inside.1.le,inside.2.le.trans upperOne⟩
  have insideScale : ‖planarPart point‖ ≤ scale := inside.2.le.trans upperScale
  have equal := periodicFourier_ext
    (fun axial => rescaledWeightedInterior weighted scale (assembleSpatialCell (planarPart point) axial))
    (fun axial => nativeWeightedOuter curves bounded (assembleSpatialCell (planarPart point) axial))
    ((rescaledWeightedInterior_smooth weighted scale).continuous.comp
      (assembleSpatialCellCLM.continuous.comp (continuous_const.prodMk continuous_id)))
    (nativeWeightedOuter_continuous_cell curves bounded _ closed)
    (rescaledWeightedInterior_periodic weighted scale _) (nativeWeightedOuter_periodic curves bounded _) (by
      intro cell
      rw [rescaledWeightedInterior_cell weighted scale scalePositive _ insideScale,
        nativeWeightedOuter_cell curves bounded _ closed]
      exact sameCells _ inside cell)
  have assembled : assembleSpatialCell (planarPart point) (point 2) = point := by
    ext coordinate
    fin_cases coordinate <;> rfl
  simpa only [assembled] using congrFun equal (point 2)

end Grad.CartesianCoreRecovery
