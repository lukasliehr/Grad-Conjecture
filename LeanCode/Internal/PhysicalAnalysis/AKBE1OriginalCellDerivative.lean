import AKAT25OriginalCartesianForceConsumer
import AKAM5SameOriginalFluxFidelity
import BT13CoefficientCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.Constraints Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarFullSource

variable {Source Value : Type} [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [ProperSpace Source] [NormedAddCommGroup Value] [NormedSpace ℂ Value]

/-- Differentiating a genuine axial cell preserves the original field's
spatial derivative. Only smoothness on the punctured open domain is used. -/
theorem originalCell_hasFDerivAt {domain : Set Source} (openDomain : IsOpen domain)
    (field : Source × ℝ → Value) (smooth : ContDiffOn ℝ ∞ field (domain ×ˢ univ))
    (cell : ℤ) (point : Source) (inside : point ∈ domain) :
    HasFDerivAt (fun current => angularCoefficient (fun axial => field (current,axial)) cell)
      ((2*Real.pi)⁻¹ • ∫ axial in Icc (-Real.pi) Real.pi,
        cellExponential (-cell) axial • integralParameterDerivative field (point,axial)) point := by
  let integrand : Source × ℝ → Value := fun argument => cellExponential (-cell) argument.2 • field argument
  have integrandSmooth : ContDiffOn ℝ ∞ integrand (domain ×ˢ univ) :=
    (((cellExponential_smooth (-cell)).comp contDiff_snd).contDiffOn).smul smooth
  have given := hasFDerivAt_compactIntegral openDomain integrandSmooth (-Real.pi) Real.pi point inside
  have same (axial : ℝ) : integralParameterDerivative integrand (point,axial) =
      cellExponential (-cell) axial • integralParameterDerivative field (point,axial) := by
    have atPoint : (point,axial) ∈ domain ×ˢ (univ : Set ℝ) := ⟨inside,mem_univ _⟩
    have fieldDiff := (smooth.contDiffAt ((openDomain.prod isOpen_univ).mem_nhds atPoint)).differentiableAt (by simp)
    have integrandDiff := (integrandSmooth.contDiffAt ((openDomain.prod isOpen_univ).mem_nhds atPoint)).differentiableAt (by simp)
    rw [integralParameterDerivative_eq point axial integrandDiff,integralParameterDerivative_eq point axial fieldDiff]
    have insertion : HasFDerivAt (fun current : Source => (current,axial))
        (ContinuousLinearMap.inl ℝ Source ℝ) point := by
      convert (hasFDerivAt_id point).prodMk (hasFDerivAt_const axial point) using 1 <;> ext direction <;> rfl
    exact ((fieldDiff.hasFDerivAt.comp point insertion).const_smul (cellExponential (-cell) axial)).fderiv.trans
      (congrArg (fun derivative : Source →L[ℝ] Value => cellExponential (-cell) axial • derivative)
        (fieldDiff.hasFDerivAt.comp point insertion).fderiv.symm)
  simp_rw [same] at given
  have functionEquality : (fun current => angularCoefficient (fun axial => field (current,axial)) cell) =
      fun current => (2*Real.pi)⁻¹ • ∫ axial in Icc (-Real.pi) Real.pi, integrand (current,axial) := by
    funext current
    exact angularCoefficient_compact_general _ _
  rw [functionEquality]
  apply (given.const_smul ((2*Real.pi)⁻¹)).congr_fderiv
  rfl

/-- The actual directional derivative commutes with axial projection; this
is the cellwise fidelity used by the original compact-test PDE consumer. -/
theorem originalCell_fderiv_apply {domain : Set Source} (openDomain : IsOpen domain)
    (field : Source × ℝ → Value) (smooth : ContDiffOn ℝ ∞ field (domain ×ˢ univ))
    (cell : ℤ) (point : Source) (inside : point ∈ domain) (direction : Source) :
    fderiv ℝ (fun current => angularCoefficient (fun axial => field (current,axial)) cell) point direction =
      angularCoefficient (fun axial => integralParameterDerivative field (point,axial) direction) cell := by
  have continuousDerivative : Continuous (fun axial : ℝ =>
      cellExponential (-cell) axial • integralParameterDerivative field (point,axial)) :=
    (cellExponential_smooth (-cell)).continuous.smul
      ((integralParameterDerivative_smooth openDomain smooth).continuousOn.comp_continuous
        (continuous_const.prodMk continuous_id) (fun _ => ⟨inside,mem_univ _⟩))
  rw [(originalCell_hasFDerivAt openDomain field smooth cell point inside).fderiv,
    smul_apply,angularCoefficient_compact_general]
  congr 1
  rw [ContinuousLinearMap.integral_apply continuousDerivative.continuousOn.integrableOn_Icc]
  rfl

end Grad.ActualCartesianWeakEquations
