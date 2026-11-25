module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramified

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.blockLevels_eq_integralGL_of_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ), (∀ u ∈ GlobalTheory.LFun.KGL w (n := 1), μ (GeneralLinearGroup.det u) = 1) →
    lev₁ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := a) ∧ lev₂ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := b) := by
  first | exact @GlobalTheory.BCT.CtLevel.lev_KGL_of_unram
