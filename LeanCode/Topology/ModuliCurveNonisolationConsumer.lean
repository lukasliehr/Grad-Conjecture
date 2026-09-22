import ModuliCurveNonisolation

noncomputable section

namespace Grad.MainAssembly.ModuliCurveNonisolation.Consumer

open Grad.MainTarget
open Grad.MainAssembly.ModuliCurveNonisolation

/-- Exact target consumer: validity plus continuity and injectivity of the
literal quotient curve suffice to construct the full frozen `ModuliCurve`
predicate, including every interior singleton non-openness clause. -/
theorem moduliCurve_of_continuous_injective
    {interval : Set ℝ} (regularity : Regularity)
    (family : interval → Representative)
    (validity : ∀ parameter, IsConfiguration regularity (family parameter))
    (curveContinuous : Continuous (fun parameter =>
      moduliClass regularity
        (⟨family parameter, validity parameter⟩ : Configuration regularity)))
    (curveInjective : Function.Injective (fun parameter =>
      moduliClass regularity
        (⟨family parameter, validity parameter⟩ : Configuration regularity))) :
    ModuliCurve regularity interval family := by
  refine ⟨validity, curveContinuous, curveInjective, ?_⟩
  intro parameter parameterInterior
  exact not_isOpen_singleton_image
    (fun other => moduliClass regularity
      (⟨family other, validity other⟩ : Configuration regularity))
    curveContinuous curveInjective parameter parameterInterior

end Grad.MainAssembly.ModuliCurveNonisolation.Consumer
