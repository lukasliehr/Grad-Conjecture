import AKBE11ClosedRepresentativeAngularAverage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped Interval ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.CartesianStartup Grad.GenericCarriers Grad.PDEBootstrap

/-- The literal nonsingular radial reflection formula on physical disk values. -/
def closedRadialReflectionValue (raw : ClosedDisk → ComplexEuclidean 2) (point : ClosedDisk) : ComplexEuclidean 2 :=
  raw point - (1/2 : ℂ) • (closedEquivariantValue raw point +
    reflectionValueMap (closedEquivariantValue raw (orthogonalClosedPoint cartesianReflectionEquiv point)))

/-- Actual rough full-cell Qrad has exactly the literal physical reflection
formula on a continuous representative of the selected cell. -/
theorem originalQrad_closedRepresentative (field : StartupL2 2) (cell : ℤ)
    (raw : ClosedDisk → ComplexEuclidean 2) (continuousRaw : Continuous raw)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => (startupGenuineQradKernel field) point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (closedRadialReflectionValue raw) := by
  let average := originalAverageKernel field
  let reflected := startupPointKernel reflectionValueMap cartesianReflectionEquiv average
  have averaged := originalAverage_closedRepresentative field cell raw continuousRaw same
  have reflectedAverage := (startupOrthogonal_disk_preserving cartesianReflectionEquiv).quasiMeasurePreserving.ae averaged
  rw [startupGenuineQrad_reflection]
  filter_upwards [same,averaged,reflectedAverage,
    startupPointKernel_field_ae reflectionValueMap cartesianReflectionEquiv average,
    Lp.coeFn_sub field ((1/2 : ℂ) • (average+reflected)),
    Lp.coeFn_smul (1/2 : ℂ) (average+reflected),Lp.coeFn_add average reflected,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point original averageAt reflectedAt reflectedValue difference scalar addition inside
  let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact le_of_lt inside⟩
  have originalClosed := closedFieldExtension_value raw closed
  have averageClosed := closedFieldExtension_value (closedEquivariantValue raw) closed
  have reflectedClosed := closedFieldExtension_value (closedEquivariantValue raw)
    (orthogonalClosedPoint cartesianReflectionEquiv closed)
  have resultClosed := closedFieldExtension_value (closedRadialReflectionValue raw) closed
  change closedFieldExtension raw point = _ at originalClosed
  change closedFieldExtension (closedEquivariantValue raw) point = _ at averageClosed
  change closedFieldExtension (closedEquivariantValue raw) (cartesianReflectionEquiv point) = _ at reflectedClosed
  change closedFieldExtension (closedRadialReflectionValue raw) point = _ at resultClosed
  change (field - (1/2 : ℂ) • (average+reflected)) point cell = _
  have differenceCell : (field - (1/2 : ℂ) • (average+reflected)) point cell =
      field point cell - ((1/2 : ℂ) • (average+reflected)) point cell :=
    congrArg (fun values : CellValues 2 => values cell) difference
  have scalarCell : ((1/2 : ℂ) • (average+reflected)) point cell =
      (1/2 : ℂ) • (average+reflected) point cell :=
    congrArg (fun values : CellValues 2 => values cell) scalar
  have additionCell : (average+reflected) point cell = average point cell + reflected point cell :=
    congrArg (fun values : CellValues 2 => values cell) addition
  rw [differenceCell,scalarCell,additionCell]
  rw [original,averageAt,reflectedValue cell,reflectedAt,originalClosed,averageClosed,reflectedClosed,resultClosed]
  rfl

/-- Pointwise physical fidelity of that SAME reflection formula at every
polar circle, including its exact centered Fourier mean. -/
theorem closedRadialReflectionValue_polar (raw : ClosedDisk → ComplexEuclidean 2)
    (continuousRaw : Continuous raw) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedRadialReflectionValue raw (Grad.Constraints.polarClosedPoint radius bounded angle) =
      raw (Grad.Constraints.polarClosedPoint radius bounded angle) -
        Grad.BoundaryTrace.angularCoefficient (fun polar => polarRadialComponent polar
          (raw (Grad.Constraints.polarClosedPoint radius bounded polar))) 0 • polarRadialVector angle :=
  (closedRadialReflection_polar raw continuousRaw radius bounded angle).trans
    (closedOriginalRadialProjection_fourier raw continuousRaw radius bounded angle)

end Grad.ActualCartesianWeakEquations
