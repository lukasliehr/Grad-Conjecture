import AKBM6ActualCurveAngularDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped Topology
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.ActualCartesianEquations
open Grad.OriginalKernelCovariantRecovery Grad.AnnularCurrentLow Grad.AnnularOriginalSmoothCore Grad.ActualDeterminantEquations

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower} {row : DivisionRow 1 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)

theorem originalDifferentiatedCurves_axial (radius : ℝ) (inside : radius∈Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => curves.fullField bounded (radius,polar,angle))
      ((originalDifferentiatedCurves curves bounded true).2.fullField bounded (radius,polar,axial)) axial := by
  have law := fullField_axialDerivative_of_coefficients curves (originalDifferentiatedCurves curves bounded true).2 bounded
    radius inside 1 (fun mode => by
      have actual := originalCurveNegativeAxial_coefficient curves bounded ⟨radius,inside⟩ mode
      rw [← originalDifferentiatedCurves_negativeAxial,originalCurveNegativeTrace_coefficient _ bounded ⟨radius,inside⟩,
        originalCurveNegativeTrace_coefficient curves bounded ⟨radius,inside⟩,
        SmoothLowPhysicalRow.fullField_doubleCoefficient _ bounded radius inside mode,
        curves.fullField_doubleCoefficient bounded radius inside mode] at actual
      simpa only [one_smul] using actual) polar axial
  simpa only [one_smul] using law

variable {pressureRow xiRow : DivisionRow 1 lower}
    (pressure : SmoothLowPhysicalRow parameters lower positive pressureRow)
    (xi : SmoothLowPhysicalRow parameters lower positive xiRow)
    (radius : ℝ) (inside : radius∈Ioo lower 1) (polar axial : ℝ)

include inside

theorem originalSmoothSeven_scalarAngular :
    scalarDirectionalField (originalSmoothSevenCurves pressure xi bounded) bounded 3 (0,1,0) (radius,polar,axial)=
      (originalSmoothSevenCurves pressure xi bounded).fullField bounded (radius,polar,axial) 1 := by
  let seven := originalSmoothSevenCurves pressure xi bounded
  have closed : radius∈Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  have derivative := ((PiLp.proj (𝕜:=ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt polar
    ((originalDifferentiatedCurves_angular xi bounded radius closed polar axial).const_smul ((radius:ℂ)⁻¹))
  change HasDerivAt (fun angle => (radius:ℂ)⁻¹*xi.fullField bounded (radius,angle,axial) 0)
    ((radius:ℂ)⁻¹*(originalDifferentiatedCurves xi bounded false).2.fullField bounded (radius,polar,axial) 0) polar at derivative
  have actual : HasDerivAt (fun angle => seven.fullField bounded (radius,angle,axial) 3)
      (seven.fullField bounded (radius,polar,axial) 1) polar := by
    rw [originalSmoothSevenCurves_fullField bounded pressure xi radius closed (polar,axial)]
    apply derivative.congr_of_eventuallyEq
    exact Eventually.of_forall (fun angle => by
      dsimp only
      rw [originalSmoothSevenCurves_fullField bounded pressure xi radius closed (angle,axial)]
      rfl)
  exact (scalarPolar_hasDerivAt seven bounded 3 radius inside polar axial).unique actual

theorem originalSmoothSeven_scalarAxial :
    scalarDirectionalField (originalSmoothSevenCurves pressure xi bounded) bounded 3 (0,0,1) (radius,polar,axial)=
      (radius:ℂ)⁻¹*(originalSmoothSevenCurves pressure xi bounded).fullField bounded (radius,polar,axial) 2 := by
  let seven := originalSmoothSevenCurves pressure xi bounded
  have closed : radius∈Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  have derivative := ((PiLp.proj (𝕜:=ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt axial
    ((originalDifferentiatedCurves_axial xi bounded radius closed polar axial).const_smul ((radius:ℂ)⁻¹))
  change HasDerivAt (fun angle => (radius:ℂ)⁻¹*xi.fullField bounded (radius,polar,angle) 0)
    ((radius:ℂ)⁻¹*(originalDifferentiatedCurves xi bounded true).2.fullField bounded (radius,polar,axial) 0) axial at derivative
  have actual : HasDerivAt (fun angle => seven.fullField bounded (radius,polar,angle) 3)
      ((radius:ℂ)⁻¹*seven.fullField bounded (radius,polar,axial) 2) axial := by
    rw [originalSmoothSevenCurves_fullField bounded pressure xi radius closed (polar,axial)]
    apply derivative.congr_of_eventuallyEq
    exact Eventually.of_forall (fun angle => by
      dsimp only
      rw [originalSmoothSevenCurves_fullField bounded pressure xi radius closed (polar,angle)]
      rfl)
  exact (scalarAxial_hasDerivAt seven bounded 3 radius inside polar axial).unique actual

/-- Xi=r*q differentiates without any equation or division at the axis. -/
theorem originalSmoothSeven_scalarRadial :
    scalarDirectionalField xi bounded 0 (1,0,0) (radius,polar,axial)=
      (originalSmoothSevenCurves pressure xi bounded).fullField bounded (radius,polar,axial) 3+
      (radius:ℂ)*scalarDirectionalField (originalSmoothSevenCurves pressure xi bounded) bounded 3 (1,0,0) (radius,polar,axial) := by
  let seven := originalSmoothSevenCurves pressure xi bounded
  have product : HasDerivAt (fun location : ℝ => (location:ℂ)*seven.fullField bounded (location,polar,axial) 3)
      (seven.fullField bounded (radius,polar,axial) 3+
        (radius:ℂ)*scalarDirectionalField seven bounded 3 (1,0,0) (radius,polar,axial)) radius := by
    have given := (hasDerivAt_id radius).smul (scalarRadial_hasDerivAt seven bounded 3 radius inside polar axial)
    simp only [one_smul,Complex.real_smul,id_eq,add_comm] at given
    convert given using 1 <;> rfl
  have actual : HasDerivAt (fun location => xi.fullField bounded (location,polar,axial) 0)
      (seven.fullField bounded (radius,polar,axial) 3+
        (radius:ℂ)*scalarDirectionalField seven bounded 3 (1,0,0) (radius,polar,axial)) radius := by
    apply product.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds inside.1 inside.2] with location member
    rw [originalSmoothSevenCurves_fullField bounded pressure xi location ⟨member.1.le,member.2.le⟩ (polar,axial)]
    change _=(location:ℂ)*((location:ℂ)⁻¹*xi.fullField bounded (location,polar,axial) 0)
    rw [← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (positive.trans member.1).ne'),one_mul]
  exact (scalarRadial_hasDerivAt xi bounded 0 radius inside polar axial).unique actual

end Grad.OriginalKernelHomogeneousGraph
