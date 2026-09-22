import AAW1WeakEndpointDifferentiation
import ADY7OriginalLowPhysicalCoordinates
import AEA9PhysicalBalancingDerivative
import AJC16SharedPhysicalWeakGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowClassical
open Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction
open Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularRegularity
open Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The actual low weak graph gives a closed-interval derivative of its
canonical normalized representative whenever its genuine slope has a
continuous representative. No ODE inverse or assumed derivative is used. -/
theorem lowEnergySection_derivative (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex)
    (slope : C(ℝ, ComplexEuclidean 1))
    (same : lowEnergyDerivative lower length positive index field.val =ᵐ[volume.restrict (Icc lower 1)] slope)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le (lowEnergySection lower length positive bounded field index))
      (slope radius) (Icc lower 1) radius :=
  annularSection_derivative_of_weak lower positive bounded
    (lowEnergyValue lower positive index field.val) (lowEnergyDerivative lower length positive index field.val)
    (field.property index) (lowEnergySection lower length positive bounded field index)
    (lowEnergySection_bulk lower length positive bounded field index) slope same radius inside

theorem lowSectionExtension_eval (lower : ℝ) (bounded : lower ≤ 1)
    (sectionValue : RadialContinuousSection 1 lower) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    radialSectionExtension 1 lower bounded sectionValue radius = sectionValue ⟨radius, inside⟩ := by
  change sectionValue (radialClamp lower bounded radius) = _
  rw [radialClamp_eq lower bounded radius inside]

end Grad.AnnularLowClassical
