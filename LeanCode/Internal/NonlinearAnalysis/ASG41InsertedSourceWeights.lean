import ASG40FourierSectionEvaluation

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

/-- Insert the literal total frequency nu^t exactly once, keeping both
original split grades and the original phase normalization. -/
def sourceInsertedWeight (angular cell grade : ℕ) (mode : ℤ × ℤ) : ℝ :=
  annularFrequency mode.1 mode.2 ^ grade * splitTangentialWeight angular cell mode

theorem sourceInsertedWeight_pos (angular cell grade : ℕ) (mode : ℤ × ℤ) :
    0 < sourceInsertedWeight angular cell grade mode :=
  mul_pos (pow_pos (annularFrequency_pos mode) _) (splitTangentialWeight_pos angular cell mode)

abbrev AnnularTotalSourceH1 (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) (_grade : ℕ) := AnnularSourceH1 parameters dimension lower angular cell

abbrev AnnularTotalEndpointTrace (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ)
    (angular cell : ℕ) (_grade : ℕ) := AnnularEndpointTrace parameters dimension radius angular cell

def totalConjugatedMode (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (mode : ℤ × ℤ) :
    CollarH1 (ComplexEuclidean dimension) lower :=
  (sourceInsertedWeight angular cell grade mode)⁻¹ •
    weightedToOrdinary dimension lower positive bounded (field mode)

def totalConjugatedCoordinate (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (mode : ℤ × ℤ)
    (coordinate : Fin 2) : CollarL2 (ComplexEuclidean dimension) lower :=
  collarH1Coordinate (ComplexEuclidean dimension) lower coordinate
    (totalConjugatedMode parameters dimension lower positive bounded angular cell grade field mode)

theorem totalConjugatedCoordinate_weak (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (mode : ℤ × ℤ) :
    CollarWeakDerivative lower
      (totalConjugatedCoordinate parameters dimension lower positive bounded angular cell grade field mode 0)
      (totalConjugatedCoordinate parameters dimension lower positive bounded angular cell grade field mode 1) :=
  collarH1_weak lower bounded _

def totalSourceCoefficient (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (mode : ℤ × ℤ)
    (radius : ℝ) : ComplexEuclidean dimension :=
  (Real.exp (radialPhase parameters radius mode.2))⁻¹ •
    totalConjugatedCoordinate parameters dimension lower positive bounded angular cell grade field mode 0 radius

def totalNormalizeCore (parameters : PhaseParameters) (dimension angular cell grade : ℕ)
    (mode : ℤ × ℤ) : SmoothRadialCore dimension →ₗ[ℝ] SmoothRadialCore dimension :=
  (annularFrequency mode.1 mode.2 ^ grade) • annularNormalizeCore parameters dimension angular cell mode

def totalDenormalizeCore (parameters : PhaseParameters) (dimension angular cell grade : ℕ)
    (mode : ℤ × ℤ) : SmoothRadialCore dimension →ₗ[ℝ] SmoothRadialCore dimension :=
  (annularFrequency mode.1 mode.2 ^ grade)⁻¹ • annularDenormalizeCore parameters dimension angular cell mode

theorem totalNormalizeCore_right (parameters : PhaseParameters) (dimension angular cell grade : ℕ)
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) :
    totalNormalizeCore parameters dimension angular cell grade mode
      (totalDenormalizeCore parameters dimension angular cell grade mode core) = core := by
  unfold totalNormalizeCore totalDenormalizeCore
  simp only [LinearMap.smul_apply, map_smul, annularNormalizeCore_right, smul_smul,
    inv_mul_cancel₀ (pow_pos (annularFrequency_pos mode) grade).ne', one_smul]

def physicalTotalSourceCore (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell grade : ℕ) :
    ((ℤ × ℤ) →₀ SmoothRadialCore dimension) →ₗ[ℝ]
      AnnularTotalSourceH1 parameters dimension lower angular cell grade :=
  (finiteSourceCore parameters dimension lower angular cell).comp
    (finiteRadialModeMap dimension (totalNormalizeCore parameters dimension angular cell grade))

theorem physicalTotalSourceCore_apply (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell grade : ℕ) (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    physicalTotalSourceCore parameters dimension lower angular cell grade core mode =
      weightedRadialCoreInto dimension lower
        (totalNormalizeCore parameters dimension angular cell grade mode (core mode)) := by
  rw [physicalTotalSourceCore, LinearMap.comp_apply, finiteSourceCore_apply, finiteRadialModeMap_apply]

theorem physicalTotalSourceCore_denseRange (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell grade : ℕ) : DenseRange (physicalTotalSourceCore parameters dimension lower angular cell grade) := by
  apply (finiteSourceCore_denseRange parameters dimension lower angular cell).mono
  rintro _ ⟨core, rfl⟩
  refine ⟨finiteRadialModeMap dimension (totalDenormalizeCore parameters dimension angular cell grade) core, ?_⟩
  unfold physicalTotalSourceCore
  rw [LinearMap.comp_apply]
  congr 1
  apply Finsupp.ext
  intro mode
  rw [finiteRadialModeMap_apply, finiteRadialModeMap_apply, totalNormalizeCore_right]

end Grad.AnnularSourceGraph
