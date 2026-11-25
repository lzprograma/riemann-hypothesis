module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
open Formalism.UG (cT)
open scoped TensorProduct Matrix

namespace GlobalTheory.BlockForms.LeviLoc

section Lin

variable (R : Type) [CommRing R] {l d n : ℕ}

variable {R}

theorem map_formula {T : Type} [CommRing T] (p : R →+* T) (s : R →+* R) (X Y : Matrix (Fin n) (Fin d) R)
    (X' Y' : Matrix (Fin d) (Fin n) R) (P Q : Matrix (Fin d) (Fin d) R) (hQ : Q.map (p.comp s) = 1) :
    (1 + X * (P - 1) * Y' + Y * (cT s Q - 1) * X').map p = 1 + X.map p * (P.map p - 1) * Y'.map p := by
  have h1 : (cT s Q).map p = 1 := by
    rw [← Matrix.transpose_one, ← hQ]; rfl
  rw [Matrix.map_add _ (map_add p), Matrix.map_add _ (map_add p), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub p), Matrix.map_sub _ (map_sub p), h1,
    Matrix.map_one _ (map_zero p) (map_one p), Matrix.map_one _ (map_zero p) (map_one p)]
  simp

end Lin

section Adele

theorem gl_entry {R : Type} [CommRing R] {d : ℕ} {x y : GL (Fin d) R} (h : x = y) (a b : Fin d) : x.1 a b = y.1 a b := by
  rw [h]

open GlobalTheory.LFun GlobalTheory.CuspRep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compFin_eq (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u z = Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E) (finTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

omit [NumberField E] in
theorem compFin_sigR (σ : E →ₐ[F] E) (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u (sigR _ σ z) = sigR _ σ (compFin F E u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]


theorem compFin_eq_zero (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = u → pLoc E w (finAdEquiv F E (finTens F E z)) = 0) :
    compFin F E u z = 0 := by
  have h1 : ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E)) * finTens F E z = 0 := by
    refine (finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun w => ?_)
    rw [map_mul, map_zero]
    change pLoc E w (_ * _) = pLoc E w 0
    rw [map_mul, map_zero]
    by_cases hw : w.under (𝓞 F) = u
    · rw [hz w hw, mul_zero]
    · have e : pLoc E w (finAdEquiv F E ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) = 0 := by
        refine Eq.trans (b := toCompl (rfl : w.under (𝓞 F) = _) _)
          (finAdEquiv_apply rfl ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) ?_
        rw [Algebra.TensorProduct.map_tmul, evalV_singleFin_ne hw, TensorProduct.zero_tmul, map_zero]
      rw [e, zero_mul]
  have h2 := congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E)) h1
  rwa [map_mul, map_zero, Algebra.TensorProduct.map_tmul, evalV_singleFin_self, map_one,
    ← Algebra.TensorProduct.one_def, one_mul, ← compFin_eq] at h2



variable {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
  (hΦ : ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z))) {d : ℕ}
include hΦ

theorem fin_symm (a : Ad E) : finAdEquiv F E (finTens F E (Φ.symm a)) = pFin E a :=
  (congrArg Prod.snd (hΦ (Φ.symm a))).symm.trans (congrArg (pFin E) (Φ.apply_symm_apply a))

end Adele


end GlobalTheory.BlockForms.LeviLoc

end
