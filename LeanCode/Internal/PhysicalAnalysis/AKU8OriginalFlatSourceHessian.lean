import AKU7AxisCoordinateLaplacian

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.AxisSplit Grad.AxisJet

def sourceRadialContractionCore {parameters : PhaseParameters} (source : SmoothQuotient parameters) : ACore parameters 1 :=
  coordinateCore parameters 0 (cartesianSpinFirst source) +
    coordinateCore parameters 1 (cartesianSpinSecond source)

theorem sourceRadialContraction_raw {parameters : PhaseParameters} (source : SmoothQuotient parameters) :
    sourceRadialContractionCore source = (1/2 : ℂ) •
      (starZMulCore parameters (source 0) + zMulCore parameters (source 1)) := by
  change coordinateCore parameters 0 ((1/2 : ℂ) • (source 0 + source 1)) +
    coordinateCore parameters 1 ((-Complex.I/2) • (source 0 - source 1)) = _
  simp only [map_smul,map_add,map_sub,starZMulCore,zMulCore,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply]
  module

theorem sourceRadialContraction_jet {parameters : PhaseParameters} (source : SmoothQuotient parameters) (cell : ℤ) :
    (sourceRadialContractionCore source).val cell =
      planarRadialContractionJet ((cartesianSourceVector source).val cell) := by
  have first := congrArg (fun core : ACore parameters 1 => core.val cell)
    (componentCore_vectorTuple (cartesianSpinFirst source) (cartesianSpinSecond source) 0)
  have second := congrArg (fun core : ACore parameters 1 => core.val cell)
    (componentCore_vectorTuple (cartesianSpinFirst source) (cartesianSpinSecond source) 1)
  change valueMapJet (componentValue 2 0) ((cartesianSourceVector source).val cell) =
    (cartesianSpinFirst source).val cell at first
  change valueMapJet (componentValue 2 1) ((cartesianSourceVector source).val cell) =
    (cartesianSpinSecond source).val cell at second
  unfold planarRadialContractionJet
  rw [first,second]
  rfl

theorem sourceRadialContraction_mean_zero {parameters : PhaseParameters} (source : SmoothQuotient parameters)
    (flat : IsFlat source) : angularCore parameters 0 (sourceRadialContractionCore source) = 0 := by
  have firstModeZero : firstMode parameters source = 0 := by
    have modeZero := congrFun flat.1.2.2.1 (0 : Fin 4)
    exact modeZero
  rw [sourceRadialContraction_raw,map_smul,rawFirstPair_mean,firstModeZero,map_zero,smul_zero,smul_zero]

def originalSourceHessian {parameters : PhaseParameters} (source : SmoothQuotient parameters) (cell : ℤ) :
    Matrix (Fin 2) (Fin 2) ℂ := axisFirstMatrix ((cartesianSourceVector source).val cell)

theorem originalSourceHessian_traceFree {parameters : PhaseParameters} (source : SmoothQuotient parameters)
    (flat : IsFlat source) (cell : ℤ) :
    originalSourceHessian source cell 0 0 + originalSourceHessian source cell 1 1 = 0 := by
  apply axisFirstMatrix_traceFree
  have mean := congrArg (fun core : ACore parameters 1 => core.val cell)
    (sourceRadialContraction_mean_zero source flat)
  change angularClosedJet 0 ((sourceRadialContractionCore source).val cell) = 0 at mean
  rwa [sourceRadialContraction_jet] at mean

theorem originalSourceHessian_symmetric {parameters : PhaseParameters} (source : SmoothQuotient parameters)
    (flat : IsFlat source) (cell : ℤ) :
    originalSourceHessian source cell 0 1 = originalSourceHessian source cell 1 0 := by
  have curlZero := (isFlat_iff_cartesian source).mp flat |>.2.2.1
  have value := congrArg (fun data : Grad.AxisCore.AxisSmoothCore parameters 1 => data.val cell 0) curlZero
  change (Grad.GaugeCoefficients.Physical.Compensated.partialJet 0
      (valueMapJet (componentValue 2 1) ((cartesianSourceVector source).val cell))).value closedOrigin 0 -
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet 1
      (valueMapJet (componentValue 2 0) ((cartesianSourceVector source).val cell))).value closedOrigin 0 = 0 at value
  rw [Grad.GaugeCoefficients.Physical.Compensated.partialJet_valueMap,
    Grad.GaugeCoefficients.Physical.Compensated.partialJet_valueMap,valueMapJet_value,valueMapJet_value,
    componentValue_apply,componentValue_apply] at value
  exact (sub_eq_zero.mp value).symm

def originalScalarSourceJetCoefficients {parameters : PhaseParameters} (source : SmoothQuotient parameters)
    (cell : ℤ) : QuadraticScalarCoefficients := scalarHessianCoefficients (originalSourceHessian source cell)

theorem originalScalarSourceJet_mean_zero {parameters : PhaseParameters} (source : SmoothQuotient parameters)
    (flat : IsFlat source) (cell : ℤ) :
    angularClosedJet 0 (quadraticScalarJet (originalScalarSourceJetCoefficients source cell)) = 0 :=
  scalarHessian_mean_zero _ (originalSourceHessian_traceFree source flat cell)

/-- JF2 now uses the literal full original Cartesian source, with symmetry
and trace-free conditions proved from its existing flat source membership. -/
theorem originalScalarSourceJet_gradient {parameters : PhaseParameters} (source : SmoothQuotient parameters)
    (flat : IsFlat source) (cell : ℤ) (point : ClosedDisk) (component : Fin 2) :
    (Grad.GaugeCoefficients.Physical.Compensated.gradientJet
      (quadraticScalarJet (originalScalarSourceJetCoefficients source cell))).value point component =
    originalSourceHessian source cell component 0 * (point.val 0 : ℂ) +
      originalSourceHessian source cell component 1 * (point.val 1 : ℂ) :=
  scalarHessian_gradient_value _ (originalSourceHessian_symmetric source flat cell) point component

end Grad.FinitePhysicalJetLift
