import ProductCellSeries

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

abbrev CellAssignments (arity : ℕ) (cell : ℤ) :=
  {cells : Fin arity → ℤ // ∑ index, cells index = cell}

theorem weightedProductAssignment_bound {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (positiveArity : 0 < arity) (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index))
    (cell : ℤ) (order : ℕ) (assignment : CellAssignments arity cell) (point : SpatialPlane)
    (pointIn : point ∈ closedUnitDisk) :
    ‖iteratedFDeriv ℝ order (weightedProductSmooth parameters assignment.val multiplication
      (fun index => (fields index).val (assignment.val index))) point‖ ≤
      productSeriesMajorant parameters multiplication fields order assignment.val :=
  weightedProduct_series_point_bound positiveArity parameters multiplication fields assignment.val order ⟨point, pointIn⟩

def weightedProductCoefficientJet {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (positiveArity : 0 < arity) (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index)) (cell : ℤ) : ClosedJet outputDimension :=
  smoothSeriesClosedJet
    (fun assignment : CellAssignments arity cell => weightedProductSmooth parameters assignment.val multiplication
      (fun index => (fields index).val (assignment.val index)))
    (fun assignment => weightedProductSmooth_smooth parameters assignment.val multiplication _)
    (fun order assignment => productSeriesMajorant parameters multiplication fields order assignment.val)
    (fun order => (productSeriesMajorant_summable parameters multiplication fields order).subtype _)
    (weightedProductAssignment_bound positiveArity parameters multiplication fields cell)

theorem weightedProductSmooth_value {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index))
    (cells : Fin arity → ℤ) (point : ClosedDisk) :
    weightedProductSmooth parameters cells multiplication
      (fun index => (fields index).val (cells index)) point.val =
      cartesianWeight parameters (∑ index, cells index) point.val •
        multiplication (fun index => ((fields index).val (cells index)).value point) := by
  have equality := congrArg (fun jet : ClosedJet outputDimension => jet.value point)
    (phaseWeighted_multilinearProduct parameters cells multiplication (fun index => (fields index).val (cells index)))
  simpa only [phaseWeightedJet_value, jetMultilinearProduct_value, globalClosedJet_value] using equality.symm

theorem weightedProductCoefficientJet_value {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (positiveArity : 0 < arity) (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index)) (cell : ℤ) (point : ClosedDisk) :
    (weightedProductCoefficientJet positiveArity parameters multiplication fields cell).value point =
      cartesianWeight parameters cell point.val • productCoefficientValue multiplication fields cell point := by
  rw [weightedProductCoefficientJet, smoothSeriesClosedJet_value]
  calc
    _ = ∑' assignment : CellAssignments arity cell, cartesianWeight parameters cell point.val •
        multiplication (fun index => ((fields index).val (assignment.val index)).value point) := by
      apply tsum_congr
      intro assignment
      rw [weightedProductSmooth_value, assignment.property]
    _ = _ := tsum_const_smul'' (cartesianWeight parameters cell point.val)

/-- The literal unweighted product coefficient, now constructed as a smooth
closed jet. ACore membership is proved separately from these raw coefficients. -/
def productCoefficientJet {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (positiveArity : 0 < arity) (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index)) (cell : ℤ) : ClosedJet outputDimension :=
  phaseInverseWeightedJet parameters cell (weightedProductCoefficientJet positiveArity parameters multiplication fields cell)

theorem productCoefficientJet_value {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (positiveArity : 0 < arity) (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index)) (cell : ℤ) (point : ClosedDisk) :
    (productCoefficientJet positiveArity parameters multiplication fields cell).value point =
      productCoefficientValue multiplication fields cell point := by
  change cartesianInverseWeight parameters cell point.val •
    (weightedProductCoefficientJet positiveArity parameters multiplication fields cell).value point = _
  rw [weightedProductCoefficientJet_value, smul_smul, mul_comm, cartesianWeight_mul_inverse, one_smul]

end Grad.NonlinearProduct
