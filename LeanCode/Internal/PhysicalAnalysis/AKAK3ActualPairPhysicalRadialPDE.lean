import AKAK2SameRadialEquationRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.GaugeCoefficients.Physical.Allocation

/-- The SAME physical Hilbert field differentiates to the Fourier series of
its genuine coefficient derivatives. Summability follows from the existing
closed Hilbert jet, so no independent convergence premise is introduced. -/
theorem hilbertPhysicalField_radial_of_coefficients (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (curve : ℕ → ℝ → CellL2 1)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (same : ∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
      curve grade radius mode = ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • curve 0 radius mode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (slope : (ℤ × ℤ) → ComplexEuclidean 1)
    (derivatives : ∀ mode, HasDerivWithinAt (fun current => curve 0 current mode) (slope mode) (Icc lower 1) radius)
    (angles : ℝ × ℝ) :
    HasDerivWithinAt (fun current => hilbertPhysicalField lower bounded curve (current,angles))
      (physicalCharacterSeries slope angles) (Icc lower 1) radius := by
  rw [hilbertPhysicalField_eq_jet lower positive bounded curve smooth same]
  have derivative := physicalMixedFourierSection_radialDerivative lower positive bounded
    (physicalJetOfHilbert lower positive bounded curve smooth same) 0 0 0 angles radius inside
  have coefficients (mode : ℤ × ℤ) :
      hilbertRadialJetSection lower bounded curve smooth 1 0 mode ⟨radius,inside⟩ = slope mode := by
    have jet := hilbertRadialJetSection_derivative lower bounded curve smooth 0 0 mode radius inside
    simp only [iteratedDerivWithin_zero,Nat.zero_add] at jet
    exact (jet.derivWithin (uniqueDiffOn_Icc bounded radius inside)).symm.trans
      ((derivatives mode).derivWithin (uniqueDiffOn_Icc bounded radius inside))
  have sameSlope : physicalMixedFourierField lower positive bounded
      (physicalJetOfHilbert lower positive bounded curve smooth same) 1 0 0 (radius,angles) =
      physicalCharacterSeries slope angles := by
    rw [physicalMixedFourierField_baseSeries,radialClamp_eq lower bounded.le radius inside]
    change physicalCharacterSeries
      (fun mode => hilbertRadialJetSection lower bounded curve smooth 1 0 mode ⟨radius,inside⟩) angles = _
    rw [funext coefficients]
  rw [← sameSlope]
  simpa only [physicalMixedFourierField,radialSectionExtension,
    radialClamp_eq lower bounded.le radius inside,ContinuousMap.coe_mk,Nat.zero_add] using derivative

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted)

/-- Actual high, low and zero radial equations for the SAME original physical
(x,xi) reconstruction. The RHS is the existing genuine full-source weak PDE,
with its actual representative, not an assumed physical equation. -/
theorem generalShared_physicalField_radial (component : Fin 2)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt
      (fun current => originalPhysicalComponentField parameters lower length positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
        component (current,angles))
      (physicalCharacterSeries (fun mode =>
        if component = 0 then (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data
          (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
          curves allGrades mode radius).1
        else (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data
          (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
          curves allGrades mode radius).2) angles) (Icc lower 1) radius := by
  let solution := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have smooth := generalShared_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades
  apply hilbertPhysicalField_radial_of_coefficients lower positive (lowerHalf.trans_lt (by norm_num))
    (originalPhysicalComponentCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive solution component)
    (originalPhysicalComponentCurve_smooth parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive solution allGrades smooth component)
    (originalPhysicalComponentCurve_grade parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive solution allGrades component)
    radius inside
  intro mode
  have derivative := generalShared_physical_derivative parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades mode radius inside
  unfold originalPhysicalComponentCurve
  by_cases zero : component = 0
  · simp only [if_pos zero]
    exact (ContinuousLinearMap.fst ℝ (ComplexEuclidean 1) (ComplexEuclidean 1)).hasFDerivAt.comp_hasDerivWithinAt radius derivative
  · simp only [if_neg zero]
    exact (ContinuousLinearMap.snd ℝ (ComplexEuclidean 1) (ComplexEuclidean 1)).hasFDerivAt.comp_hasDerivWithinAt radius derivative

end Grad.ActualPolarEquations
