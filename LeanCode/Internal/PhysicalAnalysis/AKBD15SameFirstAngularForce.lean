import AKBD14SameAngularMeanAndXiRadial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.ActualPolarFlux Grad.ActualCartesianEquations
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularSourceGraph
open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade solution weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive solution grade) (Icc lower 1))
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))
    (force : SmoothLowPhysicalRow parameters lower positive (strongKnownBulk parameters lower positive bounded.le data 3))

include allGrades smooth

/-- Exact first angular force component from the genuine SAME Xi radial
law. The scalar source projection is explicit, so this identity holds before
the original flat-source mean constraint is supplied. -/
theorem sameCovariant_firstAngularForce (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ)
    (radialLaw : HasDerivWithinAt
      (fun query => originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1 (query,polar,axial))
      (((curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).add force).meanFree.fullField bounded (radius,polar,axial))
      (Icc lower 1) radius) :
    let covariant := curves.covariant parameters length compact lower positive bounded state.val
    scalarDirectionalField covariant bounded 0 (0,1,0) (radius,polar,axial) =
      curves.fullField bounded (radius,polar,axial) 3 +
      (radius : ℂ) * scalarDirectionalField curves bounded 3 (1,0,0) (radius,polar,axial) +
      removePolarMean (fun angles => (covariant.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0) (polar,axial) -
      removePolarMean (fun angles => force.fullField bounded (radius,angles) 0) (polar,axial) := by
  let covariant := curves.covariant parameters length compact lower positive bounded state.val
  let retained := covariant.retainedForce parameters length compact lower positive bounded state
  let j := curves.lowPhysicalCurves parameters length compact lower positive bounded state 0
  have closed : radius ∈ Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  have scalarLaw := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius
    (radialLaw.hasDerivAt (Icc_mem_nhds inside.1 inside.2))
  have equality := (samePhysicalXi_scalarRadial parameters length lower positive bounded lengthPositive data solution allGrades smooth curves
    radius inside polar axial).unique scalarLaw
  change curves.fullField bounded (radius,polar,axial) 3 + (radius : ℂ)*scalarDirectionalField curves bounded 3 (1,0,0) (radius,polar,axial) =
    (j.add force).meanFree.fullField bounded (radius,polar,axial) 0 at equality
  rw [(j.add force).fullField_meanFree bounded radius closed (polar,axial),
    removePolarMean_coordinate _ ((j.add force).fullField_continuous_angles bounded radius closed) (polar,axial)] at equality
  have scalarSum (angles : ℝ × ℝ) : (j.add force).fullField bounded (radius,angles) 0 =
      scalarDirectionalField covariant bounded 0 (0,1,0) (radius,angles) - retained.fullField bounded (radius,angles) 0 + force.fullField bounded (radius,angles) 0 := by
    rw [j.fullField_add bounded force radius closed angles]
    change j.fullField bounded (radius,angles) 0 + force.fullField bounded (radius,angles) 0 = _
    rw [sameFirstPhysicalRow_pointwise parameters length compact lower positive bounded state curves radius closed angles]
    change ((curves.rotatedCovariant parameters length compact lower positive bounded state.val).bulkUnit (0 : Fin 1) 0).fullField bounded (radius,angles) 0 -
      retained.fullField bounded (radius,angles) 0 + force.fullField bounded (radius,angles) 0 = _
    rw [fullField_bulkUnit_zero_scalar _ bounded 0 radius closed angles,
      sameCovariant_scalarPolar parameters length compact lower positive bounded state lengthPositive data solution curves 0 radius inside angles.1 angles.2]
  simp_rw [scalarSum] at equality
  have retainedContinuous : Continuous (fun angles => retained.fullField bounded (radius,angles) 0) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp (retained.fullField_continuous_angles bounded radius closed)
  have forceContinuous : Continuous (fun angles => force.fullField bounded (radius,angles) 0) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp (force.fullField_continuous_angles bounded radius closed)
  have rotatedContinuous := scalarDirectionalField_continuous_angles covariant bounded 0 (0,1,0) radius inside
  rw [congrFun (removePolarMean_add (fun angles => scalarDirectionalField covariant bounded 0 (0,1,0) (radius,angles) - retained.fullField bounded (radius,angles) 0) (fun angles => force.fullField bounded (radius,angles) 0) (rotatedContinuous.sub retainedContinuous) forceContinuous) (polar,axial),
    congrFun (removePolarMean_sub (fun angles => scalarDirectionalField covariant bounded 0 (0,1,0) (radius,angles)) (fun angles => retained.fullField bounded (radius,angles) 0) rotatedContinuous retainedContinuous) (polar,axial),
    sameScalarAngular_meanFree covariant bounded 0 radius inside (polar,axial)] at equality
  dsimp only
  linear_combination -equality

end Grad.ActualDeterminantEquations
