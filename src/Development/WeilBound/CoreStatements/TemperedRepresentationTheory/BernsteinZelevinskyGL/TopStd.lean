module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength

@[expose] public section

namespace PositivityTheory.Tls2.BZGL

theorem standardFunctorsFiniteLength_top : GlobalTheory.Published.StandardFunctorsFiniteLength := by
  intro k _ _ _ _ r d _
  refine ⟨fun V _ _ π hπ hl => ?_, fun W _ _ ρ hρ hl => ?_⟩
  · exact _root_.GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k (Fin r) (Fin (∑ a, d a)) (fun a => Fin (d a)) finSigmaFinEquiv V π hπ hl
  · exact _root_.GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k (Fin r) (Fin (∑ a, d a)) (fun a => Fin (d a)) finSigmaFinEquiv W ρ hρ hl

end PositivityTheory.Tls2.BZGL
