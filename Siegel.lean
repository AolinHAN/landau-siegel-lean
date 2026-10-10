import Siegel.Main
import Siegel.Statement
import Siegel.PrimeBias
import Siegel.Interpolation
import Siegel.InterpolationPolynomial
import Siegel.InterpolationBudgets
import Siegel.ConvexGeometry
import Siegel.Algebra
import Siegel.WeightedRows
import Siegel.GreedyBasis
import Siegel.ScaledRows
import Siegel.WeightedTriangular
import Siegel.RowReplacement
import Siegel.Frobenius
import Siegel.Archimedean
import Siegel.IntegerNormBounds
import Siegel.BiquadraticRing
import Siegel.ConjugateProjection
import Siegel.BiquadraticPoints
import Siegel.IntegralDeterminant
import Siegel.SelectedIntegral
import Siegel.MertensLower
import Siegel.EulerPrimeComparison
import Siegel.PrimePartition
import Siegel.PrimeBiasAssembly
import Siegel.ScalarComparison
import Siegel.ParameterLimit
import Siegel.MainReduction
import Siegel.PrimitiveGaussSum
import Siegel.QuadraticModel
import Siegel.HolomorphicLog
import Siegel.LogDerivativeDisk
import Siegel.LFunctionGrowth
import Siegel.LFunctionCenter
import Siegel.LFunctionZeroCount
import Siegel.CanonicalFactorBounds
import Siegel.AnalyticZeroQuotient
import Siegel.ZetaPoleBound
import Siegel.Estimates
import Siegel.AnalyticBridge

import Siegel.PaperZeroIdentity
import Siegel.SingleZeroBound
import Siegel.TorusInterpretation
import Siegel.MertensTwoSided
import Siegel.ZetaPoleError
import Siegel.SquarefreeModel
import Siegel.CeilingParameters
import Siegel.RealCharacter
import Siegel.RealCharacterMain
import Siegel.PaperCompletion
import Siegel.PaperRealIdentity
import Siegel.SquarefreeCharacter
import Siegel.SquarefreeIndependence
import Siegel.BiquadraticField
import Siegel.SectionFour

/-!
# Uniform exclusion of Landau-Siegel zeros

The source is the nine-page PDF in this directory, dated October 1, 2026.
The main theorem is `Siegel.uniform_exclusion_of_landau_siegel_zeros`.
Equation (2.3), including convergence and positivity of the actual
multiplicity-weighted nontrivial-zero sum, is
`Siegel.paper_equation_two_three_complete`.
See PAPER_COVERAGE.md for all numbered formulas and Remark 5.
-/
