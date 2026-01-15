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


End[];


EndPackage[];
