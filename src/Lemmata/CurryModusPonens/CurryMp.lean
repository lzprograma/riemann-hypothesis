module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

universe u_1 u_2

namespace Bl.CurryModusPonens

open MeasureTheory

private lemma curry_mp {ι : Type u_1} {κ : Type u_2} {X : Type} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (Function.curry : (ι × κ → X) → ι → κ → X)
      (Measure.pi fun _ : ι × κ => μ) (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ) := by
  let e := (MeasurableEquiv.curry ι κ X).symm
  refine MeasurePreserving.symm e ⟨e.measurable, (Measure.pi_eq ?_).symm⟩
  intro s _
  have hpre : e ⁻¹' (Set.univ.pi s) = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext f
    simp [e, MeasurableEquiv.coe_curry_symm, Set.mem_pi, Prod.forall]
  rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- Currying preserves Lebesgue measure on finite products of copies of `ℂ`. -/
theorem goal1 (ι : Type u_1) (κ : Type u_2) [Fintype ι] [Fintype κ] :
    MeasurePreserving (Function.curry : (ι × κ → ℂ) → ι → κ → ℂ) volume volume :=
  curry_mp (volume : Measure ℂ)

end Bl.CurryModusPonens
