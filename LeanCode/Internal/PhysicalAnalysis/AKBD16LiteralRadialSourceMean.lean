import AKBD15SameFirstAngularForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.ActualSmoothPhysicalField Grad.ActualCartesianEquations
open Grad.ActualOriginalThirdSource Grad.ExhaustionSourceAllocation Grad.QuotientProjection Grad.FlatSourceProjection
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollar

/-- Zero angular Fourier mode on every integer cell gives the actual
pointwise circular projection identity. -/
theorem meanFree_of_doubleCoefficient_zero {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field)
    (angular : ∀ axial,Function.Periodic (fun polar => field (polar,axial)) (2*Real.pi))
    (axial : ∀ polar,Function.Periodic (fun axial => field (polar,axial)) (2*Real.pi))
    (zero : ∀ cell : ℤ, doubleCoefficient field (0,cell) = 0) : removePolarMean field = field := by
  have continuousProjected := removePolarMean_continuous field continuousField
  have periodic := removePolarMean_periodic field angular axial
  apply doubleFourier_ext _ _ continuousProjected continuousField periodic.1 angular periodic.2 axial
  intro mode
  rw [← doubleCoefficient_swap _ continuousProjected,← doubleCoefficient_swap _ continuousField]
  change doubleCoefficient (removePolarMean field) mode = doubleCoefficient field mode
  have projected := doubleCoefficient_removePolarMean field continuousField mode
  change doubleCoefficient (removePolarMean field) mode = (if mode.1 = 0 then 0 else doubleCoefficient field mode) at projected
  rw [projected]
  by_cases angularZero : mode.1 = 0
  · rw [if_pos angularZero]
    have sameMode : mode = (0,mode.2) := Prod.ext angularZero rfl
    rw [sameMode,zero]
  · rw [if_neg angularZero]

/-- The original IsFlat radial constraint supplies PF1=F1 pointwise, on
all circles and all axial angles at the unchanged analytic width. -/
theorem literalRadialSource_meanFree (parameters : PhaseParameters) (length : ℝ)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    removePolarMean (literalPrimitiveSource parameters length source radius nonnegative bounded 0) =
      literalPrimitiveSource parameters length source radius nonnegative bounded 0 := by
  have periodic := literalPrimitiveSource_periodic parameters length source radius nonnegative bounded 0
  apply meanFree_of_doubleCoefficient_zero _ (literalPrimitiveSource_continuous parameters length source radius nonnegative bounded 0)
    periodic.1 periodic.2
  intro cell
  rw [literalPrimitiveSource_doubleCoefficient]
  exact originalRadialCircle_mean_zero parameters (cartesianSourceVector source)
    ((isFlat_iff_cartesian source).mp flat).1 cell radius nonnegative bounded

end Grad.ActualDeterminantEquations
