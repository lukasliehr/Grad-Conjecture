import AKBD16LiteralRadialSourceMean

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


/-- The literal signed polar divergence before its single scalar projection. -/
def polarDeterminantDivergence (radius : ℝ) (angles : ℝ × ℝ) : ℂ :=
  scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0) bounded 0 (1,0,0) (radius,angles) +
  (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0).fullField bounded (radius,angles) 0 / (radius : ℂ) +
  scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 1) bounded 0 (0,1,0) (radius,angles) / (radius : ℂ) +
  scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 2) bounded 0 (0,0,1) (radius,angles) / (length : ℂ)

/-- The full original source correction, including the circular contribution
of the signed second cofactor row. -/
def sameDeterminantSourceCorrection (radius : ℝ) (angles : ℝ × ℝ) : ℂ :=
  (originalCofactorSmoothEntry parameters length compact state 1 0 radius angles * force.fullField bounded (radius,angles) 0 +
    originalCofactorSmoothEntry parameters length compact state 1 1 radius angles * curves.fullField bounded (radius,angles) 4 -
    originalCofactorSmoothEntry parameters length compact state 1 2 radius angles * curves.fullField bounded (radius,angles) 6) / (radius : ℂ)

include allGrades smooth

/-- Genuine AD13--AD17 reversal on the SAME reconstructed full fields. All
radial and angular derivatives are actual Frechet derivatives, and both
variable-coefficient internal projections remain in the proof. -/
theorem sameDeterminant_productExpansion (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ)
    (radialLaw : HasDerivWithinAt
      (fun query => originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1 (query,polar,axial))
      (((curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).add force).meanFree.fullField bounded (radius,polar,axial))
      (Icc lower 1) radius)
    (sourceMean : removePolarMean (fun angles => force.fullField bounded (radius,angles) 0) (polar,axial) =
      force.fullField bounded (radius,polar,axial) 0) :
    scalarDirectionalField (rawCorrectedPCurves parameters length compact lower positive bounded state curves) bounded 0 (1,0,0) (radius,polar,axial) +
      (rawCorrectedPCurves parameters length compact lower positive bounded state curves).fullField bounded (radius,polar,axial) 0 / (radius : ℂ) +
      scalarDirectionalField (curves.bThree parameters length compact lower positive bounded state) bounded 0 (0,0,1) (radius,polar,axial) / (length : ℂ) +
      retainedRVRawField parameters length compact lower positive bounded state curves radius (polar,axial) 0 / (radius : ℂ) -
      sameDeterminantSourceCorrection parameters length compact lower positive bounded state lengthPositive data solution curves force radius (polar,axial) =
    polarDeterminantDivergence parameters length compact lower positive bounded state lengthPositive data solution curves radius (polar,axial) := by
  let covariant := curves.covariant parameters length compact lower positive bounded state.val
  have closed : radius ∈ Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  let point : RadialPoint := ⟨radius,⟨(positive.trans inside.1).le,inside.2.le⟩⟩
  have samePoint : collarRadius lower positive bounded.le radius = point :=
    Subtype.ext (collarRadius_literal lower positive bounded.le radius closed)
  have first := sameCovariant_firstAngularForce parameters length compact lower positive bounded state lengthPositive data solution allGrades smooth curves force radius inside polar axial radialLaw
  rw [sourceMean] at first
  have second := sameCovariant_secondAngularForce parameters length compact lower positive bounded state lengthPositive data solution curves radius inside polar axial
  have third := sameCovariant_thirdAngularForce parameters length compact lower positive bounded state lengthPositive data solution curves radius inside polar axial
  dsimp only at first second third
  have product := correctedFlux_sourceCancellation (radius : ℂ) (length : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (positive.trans inside.1)))
    (Complex.ofReal_ne_zero.mpr (ne_of_gt lengthPositive))
    ((polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0).fullField bounded (radius,polar,axial) 0)
    (scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0) bounded 0 (1,0,0) (radius,polar,axial))
    (scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 2) bounded 0 (0,0,1) (radius,polar,axial))
    (curves.fullField bounded (radius,polar,axial) 3)
    (scalarDirectionalField curves bounded 3 (1,0,0) (radius,polar,axial))
    (scalarDirectionalField curves bounded 3 (0,1,0) (radius,polar,axial))
    (scalarDirectionalField curves bounded 3 (0,0,1) (radius,polar,axial))
    (fun component => originalCofactorSmoothEntry parameters length compact state 1 component radius (polar,axial))
    (originalCofactorJetSeries parameters length compact state 1 0 1 0 point (polar,axial))
    (originalCofactorJetSeries parameters length compact state 1 2 0 2 point (polar,axial))
    (∑ component : Fin 3,originalCofactorJetSeries parameters length compact state 1 component 0 1 point (polar,axial) * covariant.fullField bounded (radius,polar,axial) component)
    ((covariant.forceZero parameters length compact lower positive bounded state).fullField bounded (radius,polar,axial) 0)
    (removePolarMean (fun angles => (covariant.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0) (polar,axial))
    (removePolarMean (fun angles => (physicalForceCurves parameters length compact lower positive bounded state.val 1 covariant).fullField bounded (radius,angles) 0) (polar,axial))
    (curves.fullField bounded (radius,polar,axial) 4)
    (force.fullField bounded (radius,polar,axial) 0)
    (curves.fullField bounded (radius,polar,axial) 6)
    (fun component => scalarDirectionalField covariant bounded component (0,1,0) (radius,polar,axial)) first second third
  rw [rawCorrectedP_radial parameters length compact lower positive bounded state curves radius inside polar axial,
    rawCorrectedP_same parameters length compact lower positive bounded state curves radius closed (polar,axial),
    bThree_axial parameters length compact lower positive bounded state curves radius inside polar axial,
    retainedRVRawField_scalar parameters length compact lower positive bounded state curves radius (polar,axial),
    sameKV_scalar parameters length compact lower positive bounded state covariant radius closed (polar,axial)]
  unfold polarDeterminantDivergence
  change _ = _ + _ + scalarDirectionalField (covariant.signedCofactorRow parameters length compact lower positive bounded state 1) bounded 0 (0,1,0) (radius,polar,axial) / (radius : ℂ) + _
  rw [signedCofactorFlux_polar parameters length compact lower positive bounded state covariant 1 radius inside polar axial,
    ← sameSeven_scalarPolar parameters length lower positive bounded lengthPositive data solution curves radius inside polar axial]
  simp only [samePoint,sameDeterminantSourceCorrection,Fin.sum_univ_three] at product ⊢
  convert product using 1 <;> dsimp only [point,covariant] <;> ring

end Grad.ActualDeterminantEquations
