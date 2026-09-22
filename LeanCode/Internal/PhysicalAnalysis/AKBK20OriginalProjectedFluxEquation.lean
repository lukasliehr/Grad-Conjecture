import AKBK16LiteralCircleProjectionAlgebra
import AKBK17OriginalForceFluxIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.Constraints Grad.Constraints.Gauges Grad.SourceCollar Grad.SourceCollarFullSource
open Grad.BoundaryTrace Grad.SourceCollarDivision Grad.PDEBootstrap Grad.ActualSmoothPhysicalField
open Grad.CartesianStartup Grad.RepresentedKernel.SpatialProduct

def nativePlanarForceLower (covariant correction : Spatial → ComplexEuclidean 3) (point : Spatial) : ComplexEuclidean 2 :=
  quarterValueMap (planarPartMap (covariant point)) - planarPartMap (correction point)

def nativePlanarForceSource (source : Spatial → ComplexEuclidean 2)
    (covariant correction : Spatial → ComplexEuclidean 3) (point : Spatial) : ComplexEuclidean 2 :=
  source point + nativePlanarForceLower covariant correction point

def nativePlanarForceFlux (xi : Spatial → ComplexEuclidean 1) (covariant : Spatial → ComplexEuclidean 3) :
    Fin 2 → Fin 2 → Spatial → ℂ :=
  originalForceFlux (fun point => xi point 0) (fun point => planarPartMap (covariant point))

theorem puncturedField_circle_continuous {E : Type*} [TopologicalSpace E] (field : Spatial → E)
    (continuousField : ContinuousOn field (openUnitDisk \ {(0 : Spatial)}))
    (radius : ℝ) (positive : 0 < radius) (inside : radius < 1) :
    Continuous (fun angle => field (polarPlane (radius,angle))) := by
  apply continuousField.comp_continuous (polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_id))
  intro angle
  have normValue : ‖polarPlane (radius,angle)‖ = radius := by rw [polarPlane_norm,abs_of_pos positive]
  refine ⟨by change ‖polarPlane (radius,angle)‖ < 1; rw [normValue]; exact inside,?_⟩
  simpa only [mem_singleton_iff] using norm_pos_iff.mp (normValue.symm ▸ positive)

theorem nativePlanarForceFlux_smooth (xi : Spatial → ComplexEuclidean 1) (covariant : Spatial → ComplexEuclidean 3)
    (xiSmooth : ContDiffOn ℝ ∞ xi (openUnitDisk \ {(0 : Spatial)}))
    (covariantSmooth : ContDiffOn ℝ ∞ covariant (openUnitDisk \ {(0 : Spatial)}))
    (coordinate direction : Fin 2) :
    ContDiffOn ℝ ∞ (nativePlanarForceFlux xi covariant coordinate direction) (openUnitDisk \ {(0 : Spatial)}) :=
  originalForceFlux_smooth _ _ _
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).contDiff.comp_contDiffOn xiSmooth)
    ((planarPartMap.restrictScalars ℝ).contDiff.comp_contDiffOn covariantSmooth) coordinate direction

theorem originalPlanarDivergence_continuous (flux : Fin 2 → Fin 2 → Spatial → ℂ)
    (smooth : ∀ coordinate direction, ContDiffOn ℝ ∞ (flux coordinate direction) (openUnitDisk \ {(0 : Spatial)})) :
    ContinuousOn (originalPlanarDivergence flux) (openUnitDisk \ {(0 : Spatial)}) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro coordinate
  exact continuousOn_finsetSum _ (fun direction _ =>
    (directionDerivative_smooth (openUnitDisk_isOpen.sdiff isClosed_singleton) direction (smooth coordinate direction)).continuousOn)

theorem nativePlanarForceLower_continuous (covariant correction : Spatial → ComplexEuclidean 3)
    (covariantContinuous : ContinuousOn covariant (openUnitDisk \ {(0 : Spatial)}))
    (correctionContinuous : ContinuousOn correction (openUnitDisk \ {(0 : Spatial)})) :
    ContinuousOn (nativePlanarForceLower covariant correction) (openUnitDisk \ {(0 : Spatial)}) :=
  (quarterValueMap.continuous.comp_continuousOn (planarPartMap.continuous.comp_continuousOn covariantContinuous)).sub
    (planarPartMap.continuous.comp_continuousOn correctionContinuous)

/-- Literal projected force becomes the exact closed-disk projected flux
law required by the accepted axis-removal consumer. -/
theorem nativePlanarForce_projected_flux (xi : Spatial → ComplexEuclidean 1)
    (covariant correction : Spatial → ComplexEuclidean 3) (source : Spatial → ComplexEuclidean 2)
    (xiSmooth : ContDiffOn ℝ ∞ xi (openUnitDisk \ {(0 : Spatial)}))
    (covariantSmooth : ContDiffOn ℝ ∞ covariant (openUnitDisk \ {(0 : Spatial)}))
    (correctionContinuous : ContinuousOn correction (openUnitDisk \ {(0 : Spatial)}))
    (sourceContinuous : ContinuousOn source (openUnitDisk \ {(0 : Spatial)}))
    (equation : ∀ (radius : ℝ), 0 < radius → radius < 1 → ∀ angle : ℝ,
      originalCircleRadialProjection (fun polar => nativePlanarForceCell xi covariant correction (polarPlane (radius,polar))) angle =
      originalCircleRadialProjection (fun polar => source (polarPlane (radius,polar))) angle) :
    ∀ point : ClosedDisk, 0 < ‖point.val‖ → ‖point.val‖ < 1 →
      closedRadialReflectionValue (fun closed : ClosedDisk => nativePlanarForceSource source covariant correction closed.val) point =
      closedRadialReflectionValue (fun closed : ClosedDisk => originalPlanarDivergence (nativePlanarForceFlux xi covariant) closed.val) point := by
  have lowerContinuous := nativePlanarForceLower_continuous covariant correction covariantSmooth.continuousOn correctionContinuous
  have rhsContinuous : ContinuousOn (nativePlanarForceSource source covariant correction) (openUnitDisk \ {(0 : Spatial)}) :=
    sourceContinuous.add lowerContinuous
  have divergenceContinuous := originalPlanarDivergence_continuous _ (nativePlanarForceFlux_smooth xi covariant xiSmooth covariantSmooth)
  intro point positive inside
  obtain ⟨angle,represented⟩ := closedPoint_has_polar_angle point
  have rhs := originalCircleRadialProjection_closed _ rhsContinuous ‖point.val‖ positive inside
    (by rw [abs_of_pos positive]; exact inside.le) angle
  have divergence := originalCircleRadialProjection_closed _ divergenceContinuous ‖point.val‖ positive inside
    (by rw [abs_of_pos positive]; exact inside.le) angle
  rw [represented] at rhs divergence
  rw [rhs,divergence]
  have forceSame : (fun polar => nativePlanarForceCell xi covariant correction (polarPlane (‖point.val‖,polar))) =
      fun polar => originalPlanarDivergence (nativePlanarForceFlux xi covariant) (polarPlane (‖point.val‖,polar)) -
        nativePlanarForceLower covariant correction (polarPlane (‖point.val‖,polar)) := by
    funext polar
    have normValue : ‖polarPlane (‖point.val‖,polar)‖ = ‖point.val‖ := by rw [polarPlane_norm,abs_of_pos positive]
    have membership : polarPlane (‖point.val‖,polar) ∈ openUnitDisk \ {(0 : Spatial)} :=
      ⟨normValue.trans_lt inside,by simpa only [mem_singleton_iff] using norm_pos_iff.mp (normValue.symm ▸ positive)⟩
    have neighborhood := (openUnitDisk_isOpen.sdiff isClosed_singleton).mem_nhds membership
    rw [nativePlanarForceCell_flux xi covariant correction _
      ((xiSmooth.contDiffAt neighborhood).differentiableAt (by simp))
      ((covariantSmooth.contDiffAt neighborhood).differentiableAt (by simp))]
    change _ = _ - (_ - _)
    dsimp only [nativePlanarForceFlux]
    abel
  have projected := equation ‖point.val‖ positive inside angle
  rw [forceSame] at projected
  exact originalCircleRadialProjection_move _ _ _
    (puncturedField_circle_continuous _ divergenceContinuous ‖point.val‖ positive inside)
    (puncturedField_circle_continuous _ lowerContinuous ‖point.val‖ positive inside)
    (puncturedField_circle_continuous _ sourceContinuous ‖point.val‖ positive inside) angle projected

end Grad.ActualCartesianWeakEquations
