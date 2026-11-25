module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionsGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnitaryZariskiDense
public import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.MvPolynomial
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsGeneric

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Matrix

noncomputable section

def entries {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Fin a × Fin b → ℂ :=
  FiniteProjectionsGeneric.entries A

def rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  FiniteProjectionsGeneric.rowsPoly F s p

theorem eval_rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    eval (entries U) (rowsPoly F s p) = eval (entries ((F * U).submatrix s id)) p :=
  FiniteProjectionsGeneric.eval_rowsPoly F s p U

theorem exists_rows_eq {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A :=
  FiniteProjectionsGeneric.exists_rows_eq hF hs A

theorem rowsPoly_ne_zero {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 :=
  FiniteProjectionsGeneric.rowsPoly_ne_zero hF hs hA

theorem GenericProjectionFinite.proof (hO : FiniteProjectionsContainOpen.Statement)
    (hU : UnitaryZariskiDense.Statement) :
    GenericProjectionFinite.Statement := by
  intro n d J hJ hd
  obtain ⟨⟨W, hW, ⟨A₀, hA₀⟩, hsub⟩, h1, h2⟩ := FiniteProjectionsGeneric.proof hO hU n d J hJ hd
  exact ⟨⟨W, hW, ⟨A₀, hA₀⟩, hsub⟩, ⟨A₀, hsub hA₀⟩, h1, h2⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
