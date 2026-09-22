import AIX5RegularRadialOrbitActions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity

/-- The unitary uses the same complex scalar in every actual radial L2 representative. -/
theorem orbitDivisionRow_ae {dimension : ℕ} (lower : ℝ) (tau : OrbitParameter) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      orbitLpAction (RadialL2 dimension lower) tau field mode radius =
        orbitCharacter tau mode • field mode radius := by
  rw [ae_all_iff]
  intro mode
  exact Lp.coeFn_smul (orbitCharacter tau mode) (field mode)

/-- Literal AHT completed bulk orbit equals conjugation by the norm-isometric
angular/cell translations, on the unchanged radial and analytic weights. -/
theorem radialOrbitAction_conjugation {src tgt : ℕ} (parameters : PhaseParameters)
    (kernel : (r : RadialPoint) → RadialKernel parameters r src tgt) (regular : RegularKernelFamily kernel)
    (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (tau : OrbitParameter) :
    radialOrbitAction parameters kernel regular power lower positive bounded tau =
      (orbitLpAction (RadialL2 tgt lower) tau).comp
        ((regularRadialBulkAction parameters power lower positive bounded kernel regular).comp
          (orbitLpAction (RadialL2 src lower) (-tau))) := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  apply Lp.ext
  let input := orbitLpAction (RadialL2 src lower) (-tau) field
  let output := regularRadialBulkAction parameters power lower positive bounded kernel regular input
  have original := completedBulkKernel_ae parameters power lower
    (collarRadius lower positive bounded) (collarRadius_continuous lower positive bounded)
    (fun x => kernel (collarRadius lower positive bounded x))
    (regularRadialBulk_measurable parameters lower positive bounded kernel regular)
    (regularRadialBulkBound parameters power kernel regular)
    (regularRadialBulk_moment parameters power lower positive bounded kernel regular) input
  have translated := completedBulkKernel_ae parameters power lower
    (collarRadius lower positive bounded) (collarRadius_continuous lower positive bounded)
    (fun x => kernelOrbit tau (kernel (collarRadius lower positive bounded x)))
    (regularRadialBulk_measurable parameters lower positive bounded (fun r => kernelOrbit tau (kernel r))
      (kernelOrbit_regular parameters kernel regular tau))
    (regularRadialBulkBound parameters power (fun r => kernelOrbit tau (kernel r))
      (kernelOrbit_regular parameters kernel regular tau))
    (regularRadialBulk_moment parameters power lower positive bounded (fun r => kernelOrbit tau (kernel r))
      (kernelOrbit_regular parameters kernel regular tau)) field
  filter_upwards [original, translated, orbitDivisionRow_ae lower (-tau) field,
    orbitDivisionRow_ae lower tau output] with radius base orbit inputLaw outputLaw
  change radialOrbitAction parameters kernel regular power lower positive bounded tau field mode radius =
    orbitLpAction (RadialL2 tgt lower) tau output mode radius
  rw [outputLaw mode]
  apply (orbit mode).unique
  have scaled := (base mode).const_smul (orbitCharacter tau mode)
  convert scaled using 1
  · funext shift
    rw [inputLaw]
    change (bulkWeightRatio parameters power (collarRadius lower positive bounded radius).val shift mode : ℂ) •
        (orbitCharacter tau shift • (kernel (collarRadius lower positive bounded radius)).entry shift
          (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode) radius)) =
      orbitCharacter tau mode • ((bulkWeightRatio parameters power (collarRadius lower positive bounded radius).val shift mode : ℂ) •
        (kernel (collarRadius lower positive bounded radius)).entry shift (twoFrequencyTranslation shift mode)
          (orbitCharacter (-tau) (twoFrequencyTranslation shift mode) • field (twoFrequencyTranslation shift mode) radius))
    rw [map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    calc
      _ = (bulkWeightRatio parameters power (collarRadius lower positive bounded radius).val shift mode : ℂ) *
          (orbitCharacter tau mode * orbitCharacter (-tau) (twoFrequencyTranslation shift mode)) := by
        rw [orbitCharacter_displacement]
      _ = _ := by ring
  · rfl

end Grad.AnnularKernelOrbit
