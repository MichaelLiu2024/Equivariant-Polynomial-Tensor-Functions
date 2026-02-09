(* ::Package:: *)

BeginPackage["UnitTestTools`",{"CombinatoricsTools`"}];


SymmetricTensor


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


IndependentSymmetricIndices[\[Lambda]_Integer?NonNegative]:=Join@@MapThread[ConstantArray,{Range[3],#}]&/@WeakCompositions[\[Lambda],3]


(* ::Subsubsection:: *)
(*Public Functions*)


SymmetricTensor[\[Lambda]_Integer?NonNegative,mult_Integer?NonNegative]:=
 SymmetrizedArray[
  #->Subscript[Global`x, mult,#]&/@IndependentSymmetricIndices[\[Lambda]],
  ConstantArray[3,\[Lambda]],
  Symmetric
 ]


(*unit test*)
dsOriginal={1,2,3,4,5};
d=Total@dsOriginal;
test=SymmetrizedMonomialCP[{x1,x2,x3,x4,x5},dsOriginal];


test[[1]]*(First/@test[[2]]) . (Last/@test[[2]])^d//Expand//Chop


1.` x1 x2^2 x3^3 x4^4 x5^5


End[];


EndPackage[];
