import AKCX40SameDerivativeSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct

variable (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    {order : ℕ}

def startupCutoffDerivativeGraph (direction : Fin 2) :
    GraphGrade 3 order 0 openUnitDisk →L[ℂ] GraphGrade 3 order 0 openUnitDisk :=
  startupCutoffSpatialGraph (directionDerivative direction cutoff)
    (startupTestDerivative_smooth cutoff smooth direction) (startupTestDerivative_compact cutoff compact direction) order 0

def startupCutoffSecondDerivativeGraph (outer inner : Fin 2) :
    GraphGrade 3 order 0 openUnitDisk →L[ℂ] GraphGrade 3 order 0 openUnitDisk :=
  startupCutoffSpatialGraph (directionDerivative outer (directionDerivative inner cutoff))
    (startupTestDerivative_smooth _ (startupTestDerivative_smooth cutoff smooth inner) outer)
    (startupTestDerivative_compact _ (startupTestDerivative_compact cutoff compact inner) outer) order 0

theorem startupCutoffDerivativeGraph_base (direction : Fin 2) (field : GraphGrade 3 order 0 openUnitDisk) :
    base 3 order openUnitDisk (fun _ => 0) (startupCutoffDerivativeGraph cutoff smooth compact direction field) =
      startupCutoffDerivative cutoff smooth compact direction (base 3 order openUnitDisk (fun _ => 0) field) :=
  startupCutoffSpatialGraph_base _ _ _ _ _ _

theorem startupCutoffSecondDerivativeGraph_base (outer inner : Fin 2) (field : GraphGrade 3 order 0 openUnitDisk) :
    base 3 order openUnitDisk (fun _ => 0) (startupCutoffSecondDerivativeGraph cutoff smooth compact outer inner field) =
      startupCutoffSecondDerivative cutoff smooth compact outer inner (base 3 order openUnitDisk (fun _ => 0) field) :=
  startupCutoffSpatialGraph_base _ _ _ _ _ _

def startupCutoffEquationZerothGraph (field zeroth : GraphGrade 3 order 0 openUnitDisk)
    (tensor : Fin 2 → Fin 2 → GraphGrade 3 order 0 openUnitDisk) (flux : Fin 2 → GraphGrade 3 order 0 openUnitDisk) :
    GraphGrade 3 order 0 openUnitDisk :=
  startupCutoffSpatialGraph cutoff smooth compact order 0 zeroth+
    (∑ outer : Fin 2, ∑ inner : Fin 2, startupCutoffSecondDerivativeGraph cutoff smooth compact outer inner (tensor outer inner))+
    (∑ direction : Fin 2, startupCutoffDerivativeGraph cutoff smooth compact direction (flux direction))-
    ∑ direction : Fin 2, startupCutoffSecondDerivativeGraph cutoff smooth compact direction direction field

def startupCutoffEquationFluxGraph (field : GraphGrade 3 order 0 openUnitDisk)
    (tensor : Fin 2 → Fin 2 → GraphGrade 3 order 0 openUnitDisk) (flux : Fin 2 → GraphGrade 3 order 0 openUnitDisk) (direction : Fin 2) :
    GraphGrade 3 order 0 openUnitDisk :=
  startupCutoffSpatialGraph cutoff smooth compact order 0 (flux direction)+
    (∑ inner : Fin 2, startupCutoffDerivativeGraph cutoff smooth compact inner (tensor direction inner))+
    (∑ outer : Fin 2, startupCutoffDerivativeGraph cutoff smooth compact outer (tensor outer direction))-
    (2 : ℂ) • startupCutoffDerivativeGraph cutoff smooth compact direction field

theorem startupCutoffEquationZerothGraph_base (field zeroth : GraphGrade 3 order 0 openUnitDisk)
    (tensor : Fin 2 → Fin 2 → GraphGrade 3 order 0 openUnitDisk) (flux : Fin 2 → GraphGrade 3 order 0 openUnitDisk) :
    base 3 order openUnitDisk (fun _ => 0) (startupCutoffEquationZerothGraph cutoff smooth compact field zeroth tensor flux) =
      startupCutoffEquationZeroth cutoff smooth compact (base 3 order openUnitDisk (fun _ => 0) field)
        (base 3 order openUnitDisk (fun _ => 0) zeroth)
        (fun outer inner => base 3 order openUnitDisk (fun _ => 0) (tensor outer inner))
        (fun direction => base 3 order openUnitDisk (fun _ => 0) (flux direction)) := by
  simp only [startupCutoffEquationZerothGraph,map_sub,map_add,map_sum,startupCutoffSpatialGraph_base,
    startupCutoffDerivativeGraph_base,startupCutoffSecondDerivativeGraph_base]
  rfl

theorem startupCutoffEquationFluxGraph_base (field : GraphGrade 3 order 0 openUnitDisk)
    (tensor : Fin 2 → Fin 2 → GraphGrade 3 order 0 openUnitDisk) (flux : Fin 2 → GraphGrade 3 order 0 openUnitDisk) (direction : Fin 2) :
    base 3 order openUnitDisk (fun _ => 0) (startupCutoffEquationFluxGraph cutoff smooth compact field tensor flux direction) =
      startupCutoffEquationFlux cutoff smooth compact (base 3 order openUnitDisk (fun _ => 0) field)
        (fun outer inner => base 3 order openUnitDisk (fun _ => 0) (tensor outer inner))
        (fun dir => base 3 order openUnitDisk (fun _ => 0) (flux dir)) direction := by
  simp only [startupCutoffEquationFluxGraph,map_sub,map_add,map_sum,map_smul,startupCutoffSpatialGraph_base,
    startupCutoffDerivativeGraph_base]
  rfl

end Grad.CartesianStartup
