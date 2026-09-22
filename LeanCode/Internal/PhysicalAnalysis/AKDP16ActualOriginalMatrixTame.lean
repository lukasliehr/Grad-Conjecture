import AKDP13ActualMatrixPlanarGraphBound
import AKDP14ActualMatrixCellEndpoint
import AKDP15OriginalMatrixCoreConstruction
import AKDM10OriginalBaseAndEndpointAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.CartesianCoreRecovery Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- The actual original full-cell matrix is a same-order tame multiplier
on the original core. This follows from its genuine planar and signed-cell
endpoints; no intermediate core estimate is assumed. -/
theorem startupOriginalMatrix_core_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (offset grade : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade) :
    ∃ constant : ℝ,0≤constant ∧
    ∀ (input output : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile family reference)
      (core : ACore parameters input) (image : ACore parameters output),
      (originalSourceMoments parameters image).field =
        originalMatrixKernel admissible family estimate.actualCoherent (originalSourceMoments parameters core).field →
      physicalBudget parameters baseField rho curvature offset≤1 →
      originalGradeNorm grade image ≤ constant*(originalGradeNorm grade core+
        (1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by
  obtain ⟨planar,planarNonnegative,planarBound⟩ := startupEstimatedMatrix_planarGraph parameters admissible
    offset grade profile fixedNonnegative deviationNonnegative
  obtain ⟨cell,cellNonnegative,cellBound⟩ := startupEstimatedMatrix_cellEndpoint parameters admissible lengthNonzero scaleNonzero
    offset grade profile fixedNonnegative deviationNonnegative
  let endpoint := 2*apMassEndpointConstant 0 grade
  have endpointNonnegative : 0≤endpoint := mul_nonneg (by norm_num) (apMassEndpointConstant_nonnegative 0 grade)
  refine ⟨endpoint*(planar+cell)+cell,by positivity,?_⟩
  intro input output baseField rho curvature family reference estimate core image same low
  have inputNonnegative := add_nonneg (originalGradeNorm_nonnegative grade core)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative parameters baseField rho curvature (offset+grade)))
      (originalGradeNorm_nonnegative 0 core))
  have cellEstimate := cellBound input output baseField rho curvature family reference estimate core
    (startupOriginalSignedFamily parameters core L ell) image rfl same low
  by_cases zero : grade=0
  · subst grade
    rw [originalGradeNorm_zero_eq_cell parameters image]
    apply cellEstimate.trans
    apply mul_le_mul_of_nonneg_right _ inputNonnegative
    exact le_add_of_nonneg_left (mul_nonneg endpointNonnegative (add_nonneg planarNonnegative cellNonnegative))
  · have positive : 0<grade := Nat.pos_of_ne_zero zero
    obtain ⟨jet,jetSame⟩ := startupOriginal_reservedGraph parameters core lengthNonzero scaleNonzero grade grade
    let imageGraph := originalSourceSpatialGraph parameters image grade
    have imageGraphSame := originalSourceSpatialGraph_base parameters image grade
    have represented : base output grade openUnitDisk (fun _ => 0) imageGraph =
        originalMatrixKernel admissible family estimate.actualCoherent (originalSourceMoments parameters core).field :=
      imageGraphSame.trans same
    have planarEstimate := planarBound input output baseField rho curvature family reference estimate core jet imageGraph jetSame represented low
    rw [← startupOriginalPlanarNorm_eq_graph parameters image imageGraph imageGraphSame] at planarEstimate
    have mixed := originalMixedNorm_pureEndpoints parameters grade positive image
    have paid := mul_le_mul_of_nonneg_left (add_le_add planarEstimate cellEstimate) endpointNonnegative
    apply (mixed.trans paid).trans
    have extra := mul_nonneg cellNonnegative inputNonnegative
    nlinarith only [extra]

/-- A single actual image core is constructed for every input; the tame
constants at every order are selected before the coefficient state or
input. Both the same-field identity and original width are retained. -/
theorem startupOriginalMatrix_core_tame (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (offset : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade) :
    ∃ constants : ℕ → ℝ,(∀ grade,0≤constants grade) ∧
    ∀ (input output : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile family reference)
      (core : ACore parameters input),
      physicalBudget parameters baseField rho curvature offset≤1 →
      ∃ image : ACore parameters output,
        (originalSourceMoments parameters image).field =
          originalMatrixKernel admissible family estimate.actualCoherent (originalSourceMoments parameters core).field ∧
        ∀ grade,originalGradeNorm grade image ≤ constants grade*(originalGradeNorm grade core+
          (1+physicalBudget parameters baseField rho curvature (offset+grade))*originalGradeNorm 0 core) := by
  classical
  have each (grade : ℕ) := startupOriginalMatrix_core_oneHigh parameters admissible lengthNonzero scaleNonzero
    offset grade profile fixedNonnegative deviationNonnegative
  choose constants nonnegative estimates using each
  refine ⟨constants,nonnegative,?_⟩
  intro input output baseField rho curvature family reference estimate core low
  obtain ⟨image,same⟩ := startupOriginalMatrix_core_exists parameters admissible lengthNonzero scaleNonzero family estimate.actualCoherent core
  exact ⟨image,same,fun grade => estimates grade input output baseField rho curvature family reference estimate core image same low⟩

end Grad.CartesianStartup
