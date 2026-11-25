module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair

@[expose] public section

namespace GlobalTheory.CovTop

structure HypothesesX : Prop where

  ks : GlobalTheory.Published.ToroidalForFanKS

  lie : GlobalTheory.Published.SemiAbelianLieSeminegative

  green : GlobalTheory.Published.GreenCuspidal

  sep : GlobalTheory.Published.PointSeparationPair

end GlobalTheory.CovTop
