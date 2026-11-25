module

public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.SharpRestriction.FamCore
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ZetaProductPairs

open Formalism.BasicNotions

structure Loc (D : D7) (T : ThetaX D) where

  gl1 : D.what₂.Word → T.Gf (D.sp.Y 0)

  glSym : D.what₂.Word → T.Gf (D.sp.Y 0)

  ArchDat : D.what₂.Word → Type
  ArchDat_ne : ∀ u, Nonempty (ArchDat u)

  ellT : ∀ u, ArchDat u → ℂ

  Au : ∀ u, ArchDat u → ℂ

  B0 : ∀ u, D.what₂.Mu u →ₗ[ℂ] D.what₂.EE →ₗ[ℂ] ℂ

  zeX : D.what₂.Word → D.what₂.Tup → ℂ

  zeta_at_base_tuple : ∀ u, zeX u D.what₂.mu0 = 1

  zeX_fin : ∀ u μ, ∃ n : ℕ, 0 < n ∧ zeX u μ ^ n = 1

variable {D : D7}

variable {T : ThetaX D}

section Local

open MeasureTheory Matrix ComplexConjugate Finset

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def zetaProd (q : ℝ) (n : ℕ) : ℝ := (qE q 1 n)⁻¹

def idxPar (q : ℝ) (r s : ℕ) : ℝ := TH.parIdx q r s

def Lpair (q : ℝ) (t : ℕ) (x : ℂ) : ℂ :=
  (∏ s ∈ Icc 1 t, ((1 - x * ((q : ℂ) ^ (-(s : ℤ)))) * (1 - x⁻¹ * ((q : ℂ) ^ (-(s : ℤ))))))⁻¹


end Local

end Formalism.MainNotions.ZetaProductPairs

end
