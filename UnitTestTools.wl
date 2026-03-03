(* ::Package:: *)

BeginPackage["UnitTestTools`",{"GrowMultiplicitySpaceTree`","CombinatoricsTools`"}];


UnitTest


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


(*https://resources.wolframcloud.com/FunctionRepository/resources/SolidHarmonicR/*)
SolidHarmonicR[
 l_?NonNegativeIntegerQ,
 m_Integer,
 x_,
 y_,
 z_
]  /;  Abs[m] <= l :=
N@With[
 {dpower=If[#2==0,1,#1^#2]&,s=Sign[m],am=Abs[m]},
  
 (-1)^((1-s)am/2)Sqrt[(l-am)!/(l+am)!]dpower[x+I s y,am]*
 Sum[
 (-1)^((l+am)/2-k)(l+am+2k-1)!!dpower[z,2k]dpower[x^2+y^2+z^2,(l-am)/2-k]/((2k)!(l-am-2k)!!),
 {k,Mod[l-am,2]/2,(l-am)/2},
 Method->"Procedural"
 ]
 ]


HarmonicTensorCoordinates[
 \[Lambda]_?PositiveIntegerQ,
 m_Integer
] :=
HarmonicTensorCoordinates[\[Lambda], m] =
 Total@ReplaceAll[
 CoefficientRules[SolidHarmonicR[\[Lambda],m,x,y,z],{x,y,z}],
 (powers_->coefficients_):>coefficients*x[Sequence@@Join@@MapThread[ConstantArray,{Range[3],powers}]]
 ]


SphericalBasisToMonomialBasis[
 sphericalPolynomials_
] :=
ReplaceAll[
 sphericalPolynomials,
 Global`x[\[Lambda]_][multiplicity_][m_]:>(HarmonicTensorCoordinates[\[Lambda],m]/.x[indices__]:>Global`x[\[Lambda]][multiplicity][indices])
 ]


IndependentSymmetricIndices[
 \[Lambda]_?NonNegativeIntegerQ
] :=
Join @@ MapThread[ConstantArray, {Range[3], #}] & /@ WeakCompositions[\[Lambda], 3]


SymmetricTensor[
 \[Lambda]_?NonNegativeIntegerQ,
 multiplicity_?NonNegativeIntegerQ
] :=
SymmetrizedArray[
 #->Global`x[\[Lambda]][multiplicity][Sequence@@#]&/@IndependentSymmetricIndices[\[Lambda]],
 ConstantArray[3,\[Lambda]],
 Symmetric
 ]


SetAttributes[generateVariables,Listable]
generateVariables[
 \[Lambda]_?PositiveIntegerQ,
 m\[Lambda]_?PositiveIntegerQ
] :=
{Table[Global`x[\[Lambda]][multiplicity][m], {multiplicity, 1, m\[Lambda]}, {m, -\[Lambda], \[Lambda]}]}


(* ::Subsubsection:: *)
(*Public Functions*)


UnitTest[
 ] :=
Module[
 {
 \[Lambda]s={1,2},m\[Lambda]s={2,2},DMax=4,
 alg,polys,
 v1,v2,a1,a2,\[Epsilon],temp
 },
  
 alg=AlgebraBasis[\[Lambda]s,m\[Lambda]s,DMax];
 polys=Chop@FullSimplify@Flatten@SphericalBasisToMonomialBasis@EvaluateBasis[alg,generateVariables[\[Lambda]s,m\[Lambda]s]];
  
 v1=SymmetricTensor[1,1];
 v2=SymmetricTensor[1,2];
 a1=SymmetricTensor[2,1];
 a2=SymmetricTensor[2,2];
 \[Epsilon]=LeviCivitaTensor[3];
  
 temp=TensorContract[a1 . a2 . \[Epsilon],{1,2}];
  
 FullSimplify@Chop@FullSimplify[
 1/polys*
 {
 1,(*1*)

 v1 . v1,v2 . v2,v1 . v2,
 Tr[a1 . a1],Tr[a2 . a2],Tr[a1 . a2],(*6*)

 Tr[a1 . a1 . a1],Tr[a2 . a2 . a2],Tr[a1 . a1 . a2],Tr[a1 . a2 . a2],
 v1 . a1 . v1,v1 . a2 . v1,v2 . a1 . v2,v2 . a2 . v2,v1 . a1 . v2,v1 . a2 . v2,
 v1 . temp,v2 . temp,(*12*)

 temp . temp,
 v1 . \[Epsilon] . v2 . a1 . v1,v1 . \[Epsilon] . v2 . a2 . v1,v1 . \[Epsilon] . v2 . a1 . v2,v1 . \[Epsilon] . v2 . a2 . v2,
 temp . a1 . v1,temp . a2 . v1,
 temp . a1 . v2,temp . a2 . v2,
 v1 . \[Epsilon] . v2 . temp,
 v1 . a1 . a1 . v1-1/3 Tr[a1 . a1]v1 . v1,v1 . a2 . a2 . v1-1/3 Tr[a2 . a2]v1 . v1,v1 . a1 . a2 . v1-1/3 Tr[a1 . a2]v1 . v1,
 v2 . a1 . a1 . v2-1/3 Tr[a1 . a1]v2 . v2,v2 . a2 . a2 . v2-1/3 Tr[a2 . a2]v2 . v2,v2 . a1 . a2 . v2-1/3 Tr[a1 . a2]v2 . v2,
 v1 . a1 . a1 . v2-1/3 Tr[a1 . a1]v1 . v2,v1 . a2 . a2 . v2-1/3 Tr[a2 . a2]v1 . v2,v1 . a1 . a2 . v2-1/3 Tr[a1 . a2]v1 . v2 + v1 . a2 . a1 . v2-1/3 Tr[a1 . a2]v1 . v2(*19*)
 },
 Assumptions->_\[Element]Reals\[And]Tr[a1]==0\[And]Tr[a2]==0
 ]
 ]


End[];


EndPackage[];
