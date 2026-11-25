module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

namespace Bl.general_b_fact_third_bis

/-- A matrix preserving a finitely generated submodule that spans the ambient module is integral. -/
theorem isIntegral_of_preserves_span {R S ι : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Fintype ι] [DecidableEq ι] (L : Submodule R (ι → S))
    (hL : L.FG) (hspan : Submodule.span S (L : Set (ι → S)) = ⊤)
    (M : Matrix ι ι S) (hM : ∀ x ∈ L, M.mulVec x ∈ L) : IsIntegral R M := by
  let : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  let f := M.toLin'.restrictScalars R
  obtain ⟨p, hp, h⟩ := LinearMap.exists_monic_and_aeval_eq_zero R (f.restrict hM)
  refine ⟨p, hp, Matrix.toLin'.map_eq_zero_iff.mp (LinearMap.ext_on hspan fun x hx => ?_)⟩
  change (Polynomial.aeval M p).mulVec x = 0
  simp only [Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec, Matrix.smul_mulVec]
  simpa [Polynomial.aeval_eq_sum_range, Module.End.pow_restrict (f' := f) _ hM, f,
    LinearMap.coe_restrict_apply, ← Matrix.toLin'_apply, pow_apply_eq_iterate]
    using congrArg (fun g : Module.End R L => (g ⟨x, hx⟩ : ι → S)) h

/-- The trace of an integral matrix is integral after embedding its field in `ℂ`. -/
theorem isIntegral_trace_of_isIntegral {E ι : Type*} [Field E] [Fintype ι]
    [DecidableEq ι] (φ : E →+* ℂ) (M : Matrix ι ι E) (hM : IsIntegral ℤ M) :
    IsIntegral ℤ M.trace := by
  apply (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).mp
  rw [RingHom.toIntAlgHom_apply, AddMonoidHom.map_trace φ M, Matrix.trace_eq_sum_roots_charpoly]
  obtain ⟨p, hp, hz : Polynomial.aeval (M.map φ) p = 0⟩ := hM.map φ.mapMatrix.toIntAlgHom
  refine IsIntegral.multiset_sum fun r hr => ⟨p, hp, ?_⟩
  apply eq_zero_of_pow_eq_zero (n := Fintype.card ι)
  simpa [↓Polynomial.aeval_map_algebraMap, hz, Matrix.mem_spectrum_iff_isRoot_charpoly,
    Polynomial.IsRoot.def, Polynomial.eval_map] using
    spectrum.subset_polynomial_aeval (M.map φ) (p.map (algebraMap ℤ ℂ))
      ⟨r, Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.mem_roots'.mp hr).2, rfl⟩

end Bl.general_b_fact_third_bis
