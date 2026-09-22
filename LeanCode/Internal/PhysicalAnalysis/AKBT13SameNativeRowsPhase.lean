import AKBT12SameNativeERRowRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.Constraints

 theorem StartupRadialRelated.radialQrad {symbol : ℤ → Spatial → ℝ}
    {weighted original : StartupL2 2} (same : StartupRadialRelated symbol weighted original)
    (radial : ∀ cell (first second : Spatial), ‖first‖=‖second‖ → symbol cell first=symbol cell second) :
    StartupRadialRelated symbol (startupGenuineQradKernel weighted) (startupGenuineQradKernel original) :=
  same.add (((same.value quarterValueMap).radialTangential radial).value quarterValueMap)

 theorem StartupRadialRelated.scalarMeanFree {symbol : ℤ → Spatial → ℝ}
    {weighted original : StartupL2 1} (same : StartupRadialRelated symbol weighted original)
    (radial : ∀ cell (first second : Spatial), ‖first‖=‖second‖ → symbol cell first=symbol cell second) :
    StartupRadialRelated symbol (originalScalarMeanFreeKernel weighted) (originalScalarMeanFreeKernel original) :=
  same.sub (same.angular (fun cell _angle point => radial cell _ point (LinearIsometryEquiv.norm_map _ _))
    (angularCharacter 0) (angularCharacter_smooth 0))

/-- All eight ER phase identities follow from six SAME native base fields.
Only fixed angular maps are commuted with the original radial weight. -/
 theorem nativeERRows_phase {symbol : ℤ → Spatial → ℝ}
    (radial : ∀ cell (first second : Spatial), ‖first‖=‖second‖ → symbol cell first=symbol cell second)
    (covariant force cofactor rawCovariant rawForce rawCofactor : StartupMoments 3)
    (knownForce rawKnownForce : StartupMoments 2)
    (knownThird determinant rawKnownThird rawDeterminant : StartupMoments 1)
    (covariantSame : StartupRadialRelated symbol covariant.field rawCovariant.field)
    (forceSame : StartupRadialRelated symbol force.field rawForce.field)
    (cofactorSame : StartupRadialRelated symbol cofactor.field rawCofactor.field)
    (knownForceSame : StartupRadialRelated symbol knownForce.field rawKnownForce.field)
    (knownThirdSame : StartupRadialRelated symbol knownThird.field rawKnownThird.field)
    (determinantSame : StartupRadialRelated symbol determinant.field rawDeterminant.field) :
    StartupNativeERRowsRelated symbol (nativeERRows covariant force cofactor knownForce knownThird determinant)
      (nativeERRows rawCovariant rawForce rawCofactor rawKnownForce rawKnownThird rawDeterminant) := by
  refine ⟨covariantSame,knownForceSame.radialQrad radial,((forceSame.value planarPartMap).radialQrad radial).smul 2,
    knownThirdSame,((forceSame.value toroidalPartMap).scalarMeanFree radial).smul 2,determinantSame,?_,?_⟩
  · have total := (cofactorSame.add covariantSame).value planarPartMap
    exact total.sub (total.radialAverage radial)
  · exact ((cofactorSame.add covariantSame).value toroidalPartMap).scalarMeanFree radial

end Grad.CartesianStartup
