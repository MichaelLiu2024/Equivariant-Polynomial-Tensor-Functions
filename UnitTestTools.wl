(* ::Package:: *)

BeginPackage["UnitTestTools`",{"CombinatoricsTools`"}];


SymmetricTensor


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


IndependentSymmetricIndices[\[Lambda]_Integer?NonNegative]:=Join@@MapThread[ConstantArray,{Range[3],#}]&/@WeakCompositions[\[Lambda],3]


(* ::Subsubsection:: *)
(*Public Functions*)


SymmetricTensor[\[Lambda]_Integer?NonNegative,multiplicity_Integer?NonNegative]:=
 SymmetrizedArray[
  #->Global`x[\[Lambda]][multiplicity][Sequence@@#]&/@IndependentSymmetricIndices[\[Lambda]],
  ConstantArray[3,\[Lambda]],
  Symmetric
 ]


End[];


EndPackage[];
