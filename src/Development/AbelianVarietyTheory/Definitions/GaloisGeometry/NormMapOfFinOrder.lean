module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.GroupTheory.OrderOfElement
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker

theorem norm_map_of_finOrder {K : Type} [Field K] (σ : K →+* ℂ) {ζ : Kˣ} (h : IsOfFinOrder ζ) : ‖σ (ζ : K)‖ = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, e, Units.val_one, map_one, norm_one]

end GlobalTheory.GO
