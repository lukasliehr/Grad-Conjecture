import ASG43InsertedEndpointTrace

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

/-- Continuous l2-valued representative of exactly nu^t times the original
polynomially weighted phase-conjugated source. -/
def totalFourierSection (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ) :
    AnnularTotalSourceH1 parameters dimension lower angular cell grade →L[ℝ] FourierContinuousSection dimension lower :=
  annularFourierSection parameters dimension lower positive bounded angular cell

def totalConjugatedSection (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (mode : ℤ × ℤ) :
    RadialContinuousSection dimension lower :=
  (sourceInsertedWeight angular cell grade mode)⁻¹ •
    weightedRadialSection dimension lower positive bounded (field mode)

theorem totalFourierSection_conjugated (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade)
    (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    totalFourierSection parameters dimension lower positive bounded angular cell grade field radius mode =
      sourceInsertedWeight angular cell grade mode •
        totalConjugatedSection parameters dimension lower positive bounded angular cell grade field mode radius := by
  rw [totalFourierSection, annularFourierSection_apply]
  change _ = sourceInsertedWeight angular cell grade mode •
    ((sourceInsertedWeight angular cell grade mode)⁻¹ • weightedRadialSection dimension lower positive bounded (field mode) radius)
  rw [smul_smul, mul_inv_cancel₀ (sourceInsertedWeight_pos angular cell grade mode).ne', one_smul]

theorem totalConjugatedSection_ae (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      radialSectionExtension dimension lower bounded.le
        (totalConjugatedSection parameters dimension lower positive bounded angular cell grade field mode) radius =
      totalConjugatedCoordinate parameters dimension lower positive bounded.le angular cell grade field mode 0 radius := by
  have actual := weightedRadialSection_ae dimension lower positive bounded
    ((sourceInsertedWeight angular cell grade mode)⁻¹ • field mode)
  rw [map_smul, map_smul] at actual
  exact actual

theorem totalFourierSection_endpoint (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (endpoint : Fin 2) :
    totalFourierSection parameters dimension lower positive bounded angular cell grade field
      ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩ =
    totalSourceTrace parameters dimension lower positive bounded angular cell grade endpoint field :=
  annularFourierSection_endpoint parameters dimension lower positive bounded angular cell field endpoint

theorem totalFourierSection_physical_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    totalFourierSection parameters dimension lower positive bounded angular cell grade
      (physicalTotalSourceCore parameters dimension lower angular cell grade core) radius mode =
      totalEndpointWeight parameters angular cell grade mode radius.val • (core mode).val.val.1 radius.val := by
  rw [totalFourierSection, annularFourierSection_apply, physicalTotalSourceCore_apply, weightedRadialSection_core]
  exact totalNormalizeCore_value parameters dimension angular cell grade mode (core mode) radius.val

theorem totalSourceTrace_representative (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (endpoint : Fin 2) (mode : ℤ × ℤ) :
    totalEndpointCoefficient parameters dimension (radialEndpointRadius lower endpoint) angular cell grade
      (totalSourceTrace parameters dimension lower positive bounded angular cell grade endpoint field) mode =
    (totalEndpointWeight parameters angular cell grade mode (radialEndpointRadius lower endpoint))⁻¹ •
      totalFourierSection parameters dimension lower positive bounded angular cell grade field
        ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩ mode := by
  rw [totalFourierSection_endpoint]
  rfl

end Grad.AnnularSourceGraph
