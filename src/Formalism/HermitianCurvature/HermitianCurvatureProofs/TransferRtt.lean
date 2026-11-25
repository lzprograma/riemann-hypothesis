module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
public import Formalism.HermitianCurvature.StatementM
public import Mathlib.LinearAlgebra.Dual.Defs
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelNablaStarRelations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MultiplicationOpHom
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas

section

namespace Formalism.FourierDecayAlt.P.Mx6

open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
open Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations
  (Good rho_up xC_split xEx_split xEx_up rr good0 good1 goodm1 good_star xC_ne
   coordinate_shift_ne_zero lc lc1 lcs lca commutator_identity_one commutator_identity_two
   raising_pair_relation commutator_identity_four diagonal_lowering_absorb raising_operator_absorb
   abs_Nc abs_Nsc abs_Ncz absSand absN half hh absCC star_xC star_qC)

noncomputable section

def mt (P : Par) (Y : ℂ) : A P := star (lA P (star Y))

variable (P : Par)

alias kap_eq := _root_.Formalism.FourierDecayAlt.P.Mx4.kap_eq

end

noncomputable section

variable (P : Par)

theorem star_lA (u : ℂ) : star (lA P (star u)) = mt P u := rfl

end

end Formalism.FourierDecayAlt.P.Mx6

end

@[expose] public section

namespace Formalism.FourierDecayAlt.P.Mx6.PC

open Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W

section Entries

variable {B : Type} [Ring B]

theorem kronecker_E1_E2_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E1 M * E2 N) (i, k) (j, l) = M i j * N k l :=
  Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.PC.kronecker_E1_E2_apply M N i k j l

theorem kronecker_embed_mul_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E2 N * E1 M) (i, k) (j, l) = N k l * M i j :=
  Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.PC.kronecker_embed_mul_apply M N i k j l

theorem Pf_mul_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i k : Fin 2) (p : Fin 2 × Fin 2) :
    (Pf B * X) (i, k) p = X (k, i) p :=
  Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.PC.Pf_mul_apply X i k p

theorem mul_Pf_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (p : Fin 2 × Fin 2) (j l : Fin 2) :
    (X * Pf B) p (j, l) = X p (l, j) :=
  Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.PC.mul_Pf_apply X p j l

end Entries

end Formalism.FourierDecayAlt.P.Mx6.PC
