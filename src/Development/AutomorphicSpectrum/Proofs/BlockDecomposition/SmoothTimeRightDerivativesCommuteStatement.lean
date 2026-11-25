module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommute

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
open scoped Matrix.Norms.Elementwise
