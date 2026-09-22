import AKT1CofinalClosedSectionGluing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set
namespace Grad.ActualPuncturedFamily
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularHighGenerators Grad.AnnularRestriction
open Grad.AnnularWeightedSmoothCore Grad.AnnularSmoothCore Grad.AnnularIncomingIntegrability Grad.PhaseAlgebra

/-- The SAME corrected flux X and scalar xi, carrying the original phase
and the selected full Fourier grade in a continuous Hilbert curve. -/
def nativeLocalWeightedPair (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (grade : ℕ) : C(Icc lower (1 : ℝ), CellL2 1 × CellL2 1) :=
  ⟨fun radius => (conjugatedCoupledXSection parameters lower length positive bounded lengthPositive grade field radius,
      conjugatedCoupledXiSection parameters lower length positive bounded lengthPositive grade field radius),
    (conjugatedCoupledXSection_continuous parameters lower length positive bounded lengthPositive field allGrades grade).prodMk
      (conjugatedCoupledXiSection_continuous parameters lower length positive bounded lengthPositive field allGrades grade)⟩

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (decreasing : Antitone lower)
    (fields : ∀ index, CoupledSpace (lower index) length (positive index) lengthPositive)
    (allGrades : ∀ index grade, ∃ weighted : CoupledSpace (lower index) length (positive index) lengthPositive,
      CoupledInsertedGrade (lower index) length (positive index) lengthPositive grade (fields index) weighted)
    (compatible : ActualRetainedFamilyCompatible length lengthPositive lower positive bounded decreasing fields)

include compatible

/-- Exact native endpoint restriction identifies the full phase-weighted
Hilbert curves pointwise at every retained radius and grade. -/
theorem nativeLocalWeightedPair_ordered (grade first second : ℕ) (order : first ≤ second)
    (radius : ℝ) (inside : radius ∈ Icc (lower first) 1) :
    nativeLocalWeightedPair parameters (lower first) length (positive first) (bounded first) lengthPositive
      (fields first) (allGrades first) grade ⟨radius,inside⟩ =
    nativeLocalWeightedPair parameters (lower second) length (positive second) (bounded second) lengthPositive
      (fields second) (allGrades second) grade ⟨radius,(decreasing order).trans inside.1,inside.2⟩ := by
  apply Prod.ext
  · apply lp.ext
    funext mode
    change conjugatedCoupledXSection _ _ _ _ _ _ _ _ _ mode = conjugatedCoupledXSection _ _ _ _ _ _ _ _ _ mode
    rw [conjugatedCoupledXSection_physical parameters (lower first) length (positive first) (bounded first) lengthPositive
      (fields first) (allGrades first) grade,
      conjugatedCoupledXSection_physical parameters (lower second) length (positive second) (bounded second) lengthPositive
      (fields second) (allGrades second) grade]
    apply congrArg (fun value : ComplexEuclidean 1 => Real.exp (radialPhase parameters radius mode.2) • value)
    have observed := congrArg (fun value : CoupledSpace (lower first) length (positive first) lengthPositive =>
      sameCoupledXCoefficient parameters (lower first) length (positive first) (bounded first) lengthPositive value grade ⟨radius,inside⟩ mode)
      (compatible first second order)
    exact observed.symm.trans (coupledEndpointRestriction_x parameters (lower second) (lower first) length
      (positive second) (positive first) (bounded first) lengthPositive (decreasing order) (fields second) grade ⟨radius,inside⟩ mode)
  · apply lp.ext
    funext mode
    change conjugatedCoupledXiSection _ _ _ _ _ _ _ _ _ mode = conjugatedCoupledXiSection _ _ _ _ _ _ _ _ _ mode
    rw [conjugatedCoupledXiSection_physical parameters (lower first) length (positive first) (bounded first) lengthPositive
      (fields first) (allGrades first) grade,
      conjugatedCoupledXiSection_physical parameters (lower second) length (positive second) (bounded second) lengthPositive
      (fields second) (allGrades second) grade]
    apply congrArg (fun value : ComplexEuclidean 1 => Real.exp (radialPhase parameters radius mode.2) • value)
    have observed := congrArg (fun value : CoupledSpace (lower first) length (positive first) lengthPositive =>
      sameCoupledXiCoefficient parameters (lower first) length (positive first) (bounded first) lengthPositive value grade ⟨radius,inside⟩ mode)
      (compatible first second order)
    exact observed.symm.trans (coupledEndpointRestriction_xi parameters (lower second) (lower first) length
      (positive second) (positive first) (bounded first) lengthPositive (decreasing order) (fields second) grade ⟨radius,inside⟩ mode)

theorem nativeLocalWeightedPair_compatible (grade first second : ℕ)
    (radius : ℝ) (one : radius ∈ Icc (lower first) 1) (two : radius ∈ Icc (lower second) 1) :
    nativeLocalWeightedPair parameters (lower first) length (positive first) (bounded first) lengthPositive
      (fields first) (allGrades first) grade ⟨radius,one⟩ =
    nativeLocalWeightedPair parameters (lower second) length (positive second) (bounded second) lengthPositive
      (fields second) (allGrades second) grade ⟨radius,two⟩ := by
  rcases le_total first second with order | order
  · exact nativeLocalWeightedPair_ordered parameters length lengthPositive lower positive bounded decreasing fields allGrades compatible grade first second order radius one
  · exact (nativeLocalWeightedPair_ordered parameters length lengthPositive lower positive bounded decreasing fields allGrades compatible grade second first order radius two).symm

end Grad.ActualPuncturedFamily
