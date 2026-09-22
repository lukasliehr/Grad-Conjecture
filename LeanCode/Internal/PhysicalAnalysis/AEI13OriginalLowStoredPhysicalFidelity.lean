import AEI12LiteralLowOutputCoefficientLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

theorem lowStoredValue_section_ae (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      field.val 0 index radius = lowStorageWeight lower positive radius •
        radialSectionExtension 1 lower bounded.le (lowEnergySection lower length positive bounded field index) radius := by
  let sectionValue := lowEnergySection lower length positive bounded field index
  have representative := (collarContinuous_memLp (ComplexEuclidean 1) lower
    (radialSectionExtension 1 lower bounded.le sectionValue)).coeFn_toLp
  change ∀ᵐ radius ∂volume.restrict (Icc lower 1),
    radialSectionL2 1 lower positive bounded.le sectionValue radius =
      radialSectionExtension 1 lower bounded.le sectionValue radius at representative
  have encoded : collarScalar 1 lower (lowStorageWeight lower positive)
      (radialSectionL2 1 lower positive bounded.le sectionValue) = field.val 0 index := by
    rw [lowEnergySection_bulk]
    exact lowStorage_encode_decode lower positive (field.val 0 index)
  filter_upwards [representative, collarScalar_ae 1 lower (lowStorageWeight lower positive)
    (radialSectionL2 1 lower positive bounded.le sectionValue)] with radius representative multiplied
  rw [← encoded, multiplied, representative]

def lowPhysicalStoredWeight (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (radius : ℝ) : ℂ :=
  ((lowStorageWeight lower positive radius * Real.exp (radialPhase parameters radius mode.val.2) : ℝ) : ℂ)

/-- Completed low graph coefficients produce exactly the rho-stored physical
seven-tuple from xi and x. The analytic phase is the original one. -/
theorem lowNormalizedSevenInput_physical (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (mode : LowAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0) mode.val radius =
        lowPhysicalStoredWeight parameters lower positive mode radius • lowPhysicalSevenSymbol radius mode
          (radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field (0, mode)) radius 0)
          (radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field (1, mode)) radius 0) := by
  filter_upwards [lowNormalizedSevenInput_ae parameters lower length lengthPositive positive (field.val 0) mode,
    lowStoredValue_section_ae lower length positive bounded field (0, mode),
    lowStoredValue_section_ae lower length positive bounded field (1, mode),
    ae_restrict_mem measurableSet_Icc] with radius packet firstValue secondValue inside
  let point : Icc lower 1 := ⟨radius, inside⟩
  have firstExtension : radialSectionExtension 1 lower bounded.le
      (lowEnergySection lower length positive bounded field (0, mode)) radius =
        lowEnergySection lower length positive bounded field (0, mode) point := by
    exact congrArg (lowEnergySection lower length positive bounded field (0, mode)) (radialClamp_eq lower bounded.le radius inside)
  have secondExtension : radialSectionExtension 1 lower bounded.le
      (lowEnergySection lower length positive bounded field (1, mode)) radius =
        lowEnergySection lower length positive bounded field (1, mode) point := by
    exact congrArg (lowEnergySection lower length positive bounded field (1, mode)) (radialClamp_eq lower bounded.le radius inside)
  have xiExtension : radialSectionExtension 1 lower bounded.le
      (lowPhysicalSection parameters lower length positive bounded field (0, mode)) radius =
        lowPhysicalSection parameters lower length positive bounded field (0, mode) point := by
    exact congrArg (lowPhysicalSection parameters lower length positive bounded field (0, mode)) (radialClamp_eq lower bounded.le radius inside)
  have xExtension : radialSectionExtension 1 lower bounded.le
      (lowPhysicalSection parameters lower length positive bounded field (1, mode)) radius =
        lowPhysicalSection parameters lower length positive bounded field (1, mode) point := by
    exact congrArg (lowPhysicalSection parameters lower length positive bounded field (1, mode)) (radialClamp_eq lower bounded.le radius inside)
  rw [firstExtension, ← lowPhysicalSection_xi parameters lower length positive bounded field mode point] at firstValue
  rw [secondExtension, ← lowPhysicalSection_x parameters lower length positive bounded field mode point] at secondValue
  have firstScalar : field.val 0 (0, mode) radius = scalarOne
      (lowPhysicalStoredWeight parameters lower positive mode radius *
        ((lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2 : ℝ) : ℂ) *
        lowPhysicalSection parameters lower length positive bounded field (0, mode) point 0) := by
    rw [firstValue]
    apply PiLp.ext
    intro entry
    fin_cases entry
    simp [lowPhysicalStoredWeight, scalarOne_apply_zero, Complex.real_smul, point]
    ring
  have secondScalar : field.val 0 (1, mode) radius = scalarOne
      (lowPhysicalStoredWeight parameters lower positive mode radius *
        lowPhysicalSection parameters lower length positive bounded field (1, mode) point 0) := by
    rw [secondValue]
    apply PiLp.ext
    intro entry
    fin_cases entry
    simp [lowPhysicalStoredWeight, scalarOne_apply_zero, Complex.real_smul, point]
    ring
  rw [packet, firstScalar, secondScalar, xiExtension, xExtension]
  exact lowSevenInputSymbol_physical parameters lower length lengthPositive positive mode radius inside.1 _ _ _

end Grad.AnnularCurrentLow
