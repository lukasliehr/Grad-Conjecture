import AKT3SamePuncturedWeightedHilbertField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set
namespace Grad.ActualPuncturedFamily
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularHighGenerators Grad.AnnularRestriction
open Grad.AnnularWeightedSmoothCore Grad.AnnularSmoothCore Grad.AnnularIncomingIntegrability Grad.PhaseAlgebra

/-- The SAME physical corrected flux X and scalar xi, with the selected
full Fourier grade in a continuous Hilbert curve. -/
def nativeLocalPhysicalPair (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (grade : ℕ) : C(Icc lower (1 : ℝ), CellL2 1 × CellL2 1) :=
  ⟨fun radius => (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive grade field radius,
      sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive grade field radius),
    (sameCoupledPhysicalXSection_continuous parameters lower length positive bounded lengthPositive field allGrades grade).prodMk
      (sameCoupledPhysicalXiSection_continuous parameters lower length positive bounded lengthPositive field allGrades grade)⟩

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (decreasing : Antitone lower)
    (fields : ∀ index, CoupledSpace (lower index) length (positive index) lengthPositive)
    (allGrades : ∀ index grade, ∃ weighted : CoupledSpace (lower index) length (positive index) lengthPositive,
      CoupledInsertedGrade (lower index) length (positive index) lengthPositive grade (fields index) weighted)
    (compatible : ActualRetainedFamilyCompatible length lengthPositive lower positive bounded decreasing fields)

include compatible

/-- Exact native endpoint restriction identifies the full physical
Hilbert curves pointwise at every retained radius and grade. -/
theorem nativeLocalPhysicalPair_ordered (grade first second : ℕ) (order : first ≤ second)
    (radius : ℝ) (inside : radius ∈ Icc (lower first) 1) :
    nativeLocalPhysicalPair parameters (lower first) length (positive first) (bounded first) lengthPositive
      (fields first) (allGrades first) grade ⟨radius,inside⟩ =
    nativeLocalPhysicalPair parameters (lower second) length (positive second) (bounded second) lengthPositive
      (fields second) (allGrades second) grade ⟨radius,(decreasing order).trans inside.1,inside.2⟩ := by
  apply Prod.ext
  · apply lp.ext
    funext mode
    change sameCoupledPhysicalXSection _ _ _ _ _ _ _ _ _ mode = sameCoupledPhysicalXSection _ _ _ _ _ _ _ _ _ mode
    rw [sameCoupledPhysicalXSection_coefficient parameters (lower first) length (positive first) (bounded first) lengthPositive
      (fields first) (allGrades first) grade,
      sameCoupledPhysicalXSection_coefficient parameters (lower second) length (positive second) (bounded second) lengthPositive
      (fields second) (allGrades second) grade]
    have observed := congrArg (fun value : CoupledSpace (lower first) length (positive first) lengthPositive =>
      sameCoupledXCoefficient parameters (lower first) length (positive first) (bounded first) lengthPositive value grade ⟨radius,inside⟩ mode)
      (compatible first second order)
    exact observed.symm.trans (coupledEndpointRestriction_x parameters (lower second) (lower first) length
      (positive second) (positive first) (bounded first) lengthPositive (decreasing order) (fields second) grade ⟨radius,inside⟩ mode)
  · apply lp.ext
    funext mode
    change sameCoupledPhysicalXiSection _ _ _ _ _ _ _ _ _ mode = sameCoupledPhysicalXiSection _ _ _ _ _ _ _ _ _ mode
    rw [sameCoupledPhysicalXiSection_coefficient parameters (lower first) length (positive first) (bounded first) lengthPositive
      (fields first) (allGrades first) grade,
      sameCoupledPhysicalXiSection_coefficient parameters (lower second) length (positive second) (bounded second) lengthPositive
      (fields second) (allGrades second) grade]
    have observed := congrArg (fun value : CoupledSpace (lower first) length (positive first) lengthPositive =>
      sameCoupledXiCoefficient parameters (lower first) length (positive first) (bounded first) lengthPositive value grade ⟨radius,inside⟩ mode)
      (compatible first second order)
    exact observed.symm.trans (coupledEndpointRestriction_xi parameters (lower second) (lower first) length
      (positive second) (positive first) (bounded first) lengthPositive (decreasing order) (fields second) grade ⟨radius,inside⟩ mode)

theorem nativeLocalPhysicalPair_compatible (grade first second : ℕ)
    (radius : ℝ) (one : radius ∈ Icc (lower first) 1) (two : radius ∈ Icc (lower second) 1) :
    nativeLocalPhysicalPair parameters (lower first) length (positive first) (bounded first) lengthPositive
      (fields first) (allGrades first) grade ⟨radius,one⟩ =
    nativeLocalPhysicalPair parameters (lower second) length (positive second) (bounded second) lengthPositive
      (fields second) (allGrades second) grade ⟨radius,two⟩ := by
  rcases le_total first second with order | order
  · exact nativeLocalPhysicalPair_ordered parameters length lengthPositive lower positive bounded decreasing fields allGrades compatible grade first second order radius one
  · exact (nativeLocalPhysicalPair_ordered parameters length lengthPositive lower positive bounded decreasing fields allGrades compatible grade second first order radius two).symm

end Grad.ActualPuncturedFamily
