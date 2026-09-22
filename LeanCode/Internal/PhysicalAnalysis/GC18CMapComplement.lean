import GC18CMapAngular
import GC18APFixedJet

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.GenericCarriers
open Grad.GaugeCoefficients.Radial

def cMapEquivariant : C(ClosedDisk, ComplexEuclidean 2) →L[ℂ] C(ClosedDisk, ComplexEuclidean 2) :=
  (positiveHelicity.compLeftContinuous ℂ ClosedDisk).comp (cMapAngular 2 1) +
    (negativeHelicity.compLeftContinuous ℂ ClosedDisk).comp (cMapAngular 2 (-1))

theorem cMapEquivariant_apply (field : C(ClosedDisk, ComplexEuclidean 2)) (point : ClosedDisk) :
    cMapEquivariant field point = closedEquivariantValue field point := rfl

def cMapReflection : C(ClosedDisk, ComplexEuclidean 2) →L[ℂ] C(ClosedDisk, ComplexEuclidean 2) :=
  (reflectionValueMap.compLeftContinuous ℂ ClosedDisk).comp
    (ContinuousMap.compCLM (R := ℂ) (ComplexEuclidean 2)
      ⟨orthogonalClosedPoint cartesianReflectionEquiv, continuous_orthogonalClosedPoint cartesianReflectionEquiv⟩)

def cMapTangential : C(ClosedDisk, ComplexEuclidean 2) →L[ℂ] C(ClosedDisk, ComplexEuclidean 2) :=
  (1 / 2 : ℂ) • ((ContinuousLinearMap.id ℂ _ - cMapReflection).comp cMapEquivariant)

theorem cMapTangential_apply (field : C(ClosedDisk, ComplexEuclidean 2)) (point : ClosedDisk) :
    cMapTangential field point = closedTangentialValue field point := rfl

/-- The literal nonsingular Cartesian C0 on continuous values. -/
def cMapComplement : C(ClosedDisk, ComplexEuclidean 3) →L[ℂ] C(ClosedDisk, ComplexEuclidean 3) :=
  (planarInclusionMap.compLeftContinuous ℂ ClosedDisk).comp
    (cMapTangential.comp (planarPartMap.compLeftContinuous ℂ ClosedDisk)) +
  (toroidalInclusionMap.compLeftContinuous ℂ ClosedDisk).comp
    ((cMapAngular 1 0).comp (toroidalPartMap.compLeftContinuous ℂ ClosedDisk))

theorem cMapComplement_apply (field : C(ClosedDisk, ComplexEuclidean 3)) :
    cMapComplement field = cartesianComplementMap field := rfl

theorem cMapComplement_jet (field : ClosedJet 3) :
    cMapComplement field.value = (fixedComplementJet field).value := by
  apply ContinuousMap.ext
  intro point
  exact (fixedComplementJet_value field point).symm

end Grad.GaugeCoefficients.Physical.RadialLedger
