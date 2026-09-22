import AKBY1AllNaturalCellMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.AnnularCurrentLow
open Grad.ActualCartesianDescent Grad.CartesianStartup

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

/-- The existing native carrier at each inserted grade forms one simultaneous all-power family. -/
def sameNativeAllCellMoments
    (finite : ∀ power : ℕ, (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves power radius‖ ^ 2)) < ⊤) :
    StartupAllMoments dimension where
  field := sameNativeCellField parameters lower positive bounded cofinal decreasing rows curves compatible 0 (finite 0)
  moment power := sameNativeCellField parameters lower positive bounded cofinal decreasing rows curves compatible power (finite power)
  zero := rfl
  same := by
    apply ae_all_iff.mpr
    intro power
    exact sameNativeCellField_moment parameters lower positive bounded cofinal decreasing rows curves compatible power (finite 0) (finite power)

theorem sameNativeAllCellMoments_same
    (finite : ∀ power : ℕ, (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves power radius‖ ^ 2)) < ⊤) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (sameNativeAllCellMoments parameters lower positive bounded cofinal decreasing rows curves compatible finite).field point cell =
        cartesianWeight parameters cell point •
          gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point := by
  simpa only [sameNativeAllCellMoments,pow_zero,one_smul] using
    sameNativeCellField_same parameters lower positive bounded cofinal decreasing rows curves compatible 0 (finite 0)

end Grad.ActualNativeCellMoments
