module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.absHalf_blockDet_integralGL_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m k : GLw a w × GLw b w),
    k.1 ∈ GlobalTheory.LFun.KGL w (n := a) → k.2 ∈ GlobalTheory.LFun.KGL w (n := b) →
    absHalf w ((k * m).1.val.det ^ b / (k * m).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) ∧
      absHalf w ((m * k).1.val.det ^ b / (m * k).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
  first | exact @GlobalTheory.BCT.absHalf_blockDet_KGL_invariant
