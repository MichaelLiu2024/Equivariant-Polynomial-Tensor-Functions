(* ::Package:: *)

BeginPackage[
 "UnitTestTools`",
 {
  "GrowMultiplicitySpaceTree`",
  "CombinatoricsTools`",
  "BooleanTools`"
  }
 ];


UnitTest
Benchmark


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Public Functions*)


UnitTest[] :=
 Module[
  {
   \[Lambda]s = {1, 2}, m\[Lambda]s = {2, 2}, \[Nu] = 0, DMax = 4,
   tree,
   alg, polys,
   v1, v2, a1, a2, \[Epsilon], temp
  },
  
  tree = IsotypicDataTree[\[Lambda]s, m\[Lambda]s, \[Nu], DMax];
  alg = AlgebraBasis[tree];
  polys = Chop @ FullSimplify @ Flatten @ SphericalBasisToMonomialBasis @ EvaluateBasis[alg, generateVariables[\[Lambda]s, m\[Lambda]s]];
  
  v1 = SymmetricTensor[1, 1];
  v2 = SymmetricTensor[1, 2];
  a1 = SymmetricTensor[2, 1];
  a2 = SymmetricTensor[2, 2];
  \[Epsilon] = LeviCivitaTensor[3];
  
  temp = TensorContract[a1 . a2 . \[Epsilon], {1, 2}];
  
  FullSimplify @ Chop @ FullSimplify[
   1 / polys *
    {
     1, (*1*)

     v1 . v1, v2 . v2, v1 . v2,
     Tr[a1 . a1], Tr[a2 . a2], Tr[a1 . a2], (*6*)

     Tr[a1 . a1 . a1], Tr[a2 . a2 . a2], Tr[a1 . a1 . a2], Tr[a1 . a2 . a2],
     v1 . a1 . v1, v1 . a2 . v1, v2 . a1 . v2, v2 . a2 . v2, v1 . a1 . v2, v1 . a2 . v2,
     v1 . temp, v2 . temp, (*12*)

     temp . temp,
     v1 . \[Epsilon] . v2 . a1 . v1, v1 . \[Epsilon] . v2 . a2 . v1, v1 . \[Epsilon] . v2 . a1 . v2, v1 . \[Epsilon] . v2 . a2 . v2,
     temp . a1 . v1, temp . a2 . v1,
     temp . a1 . v2, temp . a2 . v2,
     v1 . \[Epsilon] . v2 . temp,
     v1 . a1 . a1 . v1 - 1 / 3 Tr[a1 . a1]v1 . v1, v1 . a2 . a2 . v1 - 1 / 3 Tr[a2 . a2]v1 . v1, v1 . a1 . a2 . v1 - 1 / 3 Tr[a1 . a2]v1 . v1,
     v2 . a1 . a1 . v2 - 1 / 3 Tr[a1 . a1]v2 . v2, v2 . a2 . a2 . v2 - 1 / 3 Tr[a2 . a2]v2 . v2, v2 . a1 . a2 . v2 - 1 / 3 Tr[a1 . a2]v2 . v2,
     v1 . a1 . a1 . v2 - 1 / 3 Tr[a1 . a1]v1 . v2, v1 . a2 . a2 . v2 - 1 / 3 Tr[a2 . a2]v1 . v2, v1 . a1 . a2 . v2 - 1 / 3 Tr[a1 . a2]v1 . v2 + v1 . a2 . a1 . v2 - 1 / 3 Tr[a1 . a2]v1 . v2(*19*)
    },
   Assumptions -> _ \[Element] Reals \[And] Tr[a1] == 0 \[And] Tr[a2] == 0
  ]
 ]


MinimalIntegrityBasisSize[
 {1},
 {1},
 0,
 DMax_?NonNegativeIntegerQ
] := Take[{1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, DMax + 1]


MinimalIntegrityBasisSize[
 {1},
 {2},
 0,
 DMax_?NonNegativeIntegerQ
] := Take[{1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, DMax + 1]


MinimalIntegrityBasisSize[
 {1},
 {3},
 0,
 DMax_?NonNegativeIntegerQ
] := Take[{1, 0, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, DMax + 1]


MinimalIntegrityBasisSize[
 {2},
 {2},
 0,
 DMax_?NonNegativeIntegerQ
] := Take[{1, 0, 3, 4, 1, 0}, DMax + 1]


MinimalIntegrityBasisSize[
 {4},
 {1},
 0,
 DMax_?NonNegativeIntegerQ
] := Take[{1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0}, DMax + 1]


MinimalIntegrityBasisSize[
 {1, 3},
 {1, 1},
 0,
 DMax_?NonNegativeIntegerQ
] := Take[{1, 0, 2, 0, 4, 0, 5, 3, 1, 7, 1, 2, 0, 1, 0, 1}, DMax + 1]


MinimalIntegrityBasisSize[
 {2, 3},
 {1, 1},
 0,
 DMax_?NonNegativeIntegerQ
] := Take[{1, 0, 2, 2, 4, 4, 9, 9, 8, 5, 3, 2, 1, 1, 1}, DMax + 1]


MinimalIntegrityBasisSize[
 {1, 2, 3},
 {1, 1, 1},
 0,
 DMax_?NonNegativeIntegerQ
] := Take[{1, 0, 3, 4, 12, 15, 37, 42, 38, 22, 9, 6, 3, 2, 1, 1}, DMax + 1]


MinimalIntegrityBasisSize[
 {2, 3},
 {2, 1},
 0,
 DMax_?NonNegativeIntegerQ
] := Take[{1, 0, 4, 7, 14, 26, 52, 68}, DMax + 1]


MinimalIntegrityBasisSize[
 {2, 3},
 {2, 1},
 4,
 DMax_?NonNegativeIntegerQ
] := Take[{0, 0, 6, 21, 63, 147, 264, 284}, DMax + 1]


MinimalIntegrityBasisSize[
 {2, 4},
 {2, 1},
 0,
 DMax_?NonNegativeIntegerQ
] := Take[{{1, 0, 0, 0, 0}, {0, 0, 0, 0, 0}, {1, 1, 1, 0, 0}, {1, 1, 2, 2, 1}, {1, 0, 1, 4, 6}, {1, 0, 0, 7, 18}, {1, 0, 0, 10, 36}, {1, 0, 0, 11, 53}, {1, 0, 0, 10, 45}, {1, 0, 0, 5, 10}, {1, 0, 0, 2, 2}, {0, 0, 0, 1, 3}} . {1, 2, 1, 2, 1}, DMax + 1]


MinimalIntegrityBasisSize[
 \[Lambda]s_?DistinctPositiveIntegersQ,
 m\[Lambda]s_?PositiveIntegersQ,
 \[Nu]_?NonNegativeIntegerQ,
 DMax_?NonNegativeIntegerQ
] := ConstantArray[0, DMax + 1]


Benchmark[
 \[Lambda]s_?DistinctPositiveIntegersQ,
 m\[Lambda]s_?PositiveIntegersQ,
 \[Nu]_?NonNegativeIntegerQ,
 DMax_?NonNegativeIntegerQ
] :=
 Module[
  {
   invariantIsotypicDataTree, covariantIsotypicDataTree,
   invariantVectorSpaceBasis, covariantVectorSpaceBasis,
   invariantAlgebraBasis, covariantModuleBasis
  },
  
  invariantIsotypicDataTree = AbsoluteTiming @ IsotypicDataTree[\[Lambda]s, m\[Lambda]s, 0, DMax];
  
  If[\[Nu] != 0, covariantIsotypicDataTree = AbsoluteTiming @ IsotypicDataTree[\[Lambda]s, m\[Lambda]s, \[Nu], DMax]];
  
  invariantVectorSpaceBasis = VectorSpaceBasis @ Last @ invariantIsotypicDataTree;
  
  If[\[Nu] != 0, covariantVectorSpaceBasis = VectorSpaceBasis @ Last @ covariantIsotypicDataTree];
  
  invariantAlgebraBasis = AbsoluteTiming @ AlgebraBasis @ Last @ invariantIsotypicDataTree;
  
  If[\[Nu] != 0, covariantModuleBasis = AbsoluteTiming @ ModuleBasis[Last @ invariantIsotypicDataTree, Last @ covariantIsotypicDataTree]];
  
  Print["Computed number of candidate algebra generators by degree: ", spaceDimensions @ invariantVectorSpaceBasis];
  Print["Actual number of candidate algebra generators by degree: ", HilbertSeries[\[Lambda]s, m\[Lambda]s, 0, DMax]];
  Print["Total time to compute candidate algebra generators: ", First @ invariantIsotypicDataTree];
  Print[];
  
  If[\[Nu] != 0, Print["Computed number of candidate module generators by degree: ", spaceDimensions @ covariantVectorSpaceBasis];
  Print["Actual number of candidate module generators by degree: ", HilbertSeries[\[Lambda]s, m\[Lambda]s, \[Nu], DMax]];
  Print["Total time to compute candidate module generators: ", First @ covariantIsotypicDataTree];
  Print[]];
  
  Print["Computed number of independent algebra generators by degree: ", Length /@ Last @ invariantAlgebraBasis];
  Print["Actual number of independent algebra generators by degree: ", MinimalIntegrityBasisSize[\[Lambda]s, m\[Lambda]s, 0, DMax]];
  Print["Total time to compute independent algebra generators: ", First @ invariantAlgebraBasis];
  Print[];
  
  If[\[Nu] != 0, Print["Computed number of independent module generators by degree: ", Length /@ Last @ covariantModuleBasis];
  Print["Actual number of independent module generators by degree: ", MinimalIntegrityBasisSize[\[Lambda]s, m\[Lambda]s, \[Nu], DMax]];
  Print["Total time to compute independent module generators: ", First @ covariantModuleBasis]];
 ]


(* ::Subsubsection:: *)
(*Private Functions*)


(*https://resources.wolframcloud.com/FunctionRepository/resources/SolidHarmonicR/*)
SolidHarmonicR[
 l_?NonNegativeIntegerQ,
 m_Integer,
 x_,
 y_,
 z_
] /; Abs[m] <= l :=
 N @ With[
  {dpower = If[#2 == 0, 1, #1^#2] &, s = Sign[m], am = Abs[m]},
  
  (-1)^((1 - s)am / 2)Sqrt[(l - am)!/(l + am)!]dpower[x + I s y, am] *
  Sum[
   (-1)^((l + am) / 2 - k)(l + am + 2k - 1)!!dpower[z, 2k]dpower[x^2 + y^2 + z^2, (l - am) / 2 - k] / ((2k)!(l - am - 2k)!!),
   {k, Mod[l - am, 2] / 2, (l - am) / 2},
   Method -> "Procedural"
  ]
 ]


HarmonicTensorCoordinates[
 \[Lambda]_Integer?Positive,
 m_Integer
] :=
 HarmonicTensorCoordinates[\[Lambda], m] =
 Total @ ReplaceAll[
  CoefficientRules[SolidHarmonicR[\[Lambda], m, x, y, z], {x, y, z}],
  (powers_ -> coefficients_) :> coefficients * x[Sequence @@ Join @@ MapThread[ConstantArray, {Range[3], powers}]]
 ]


SphericalBasisToMonomialBasis[sphericalPolynomials_] :=
 ReplaceAll[
  sphericalPolynomials,
  Global`x[\[Lambda]_][multiplicity_][m_] :> (HarmonicTensorCoordinates[\[Lambda], m] /. x[indices__] :> Global`x[\[Lambda]][multiplicity][indices])
 ]


IndependentSymmetricIndices[\[Lambda]_?NonNegativeIntegerQ] := Join @@ MapThread[ConstantArray, {Range[3], #}] & /@ WeakCompositions[\[Lambda], 3]


SymmetricTensor[
 \[Lambda]_?NonNegativeIntegerQ,
 multiplicity_?NonNegativeIntegerQ
] :=
 SymmetrizedArray[
  # -> Global`x[\[Lambda]][multiplicity][Sequence @@ #] & /@ IndependentSymmetricIndices[\[Lambda]],
  ConstantArray[3, \[Lambda]],
  Symmetric
 ]


SetAttributes[generateVariables, Listable]
generateVariables[
 \[Lambda]_Integer?Positive,
 m\[Lambda]_Integer?Positive
] :=
 {Table[Global`x[\[Lambda]][multiplicity][m], {multiplicity, 1, m\[Lambda]}, {m, -\[Lambda], \[Lambda]}]}


End[];


EndPackage[];
