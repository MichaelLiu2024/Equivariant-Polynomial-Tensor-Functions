(* ::Package:: *)

BeginPackage["TensorTools`",{"CombinatoricsTools`"}];


EvaluateTensorTrain
EvaluateAntisymmetrizedTensorTrain
EvaluateSymmetrizedTensorTrain


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


ContractVectors[vector1_?VectorQ,{vector2_?VectorQ,tensor_?ArrayQ}]:=Dot[vector2,Dot[vector1,tensor]]


(* ::Subsubsection:: *)
(*Public Functions*)


(*add input checks*)
EvaluateTensorTrain::usage="evaluates the tensorTrain at the vectors."
EvaluateTensorTrain[tensorTrain_List,vectors_List]/;Depth[vectors]==3:=
 If[
  tensorTrain==={1},
  First@vectors,
  Chop@Fold[ContractVectors,First@vectors,Transpose[{vectors[[2;;1+Length@tensorTrain]],tensorTrain}]]
 ]


EvaluateAntisymmetrizedTensorTrain::usage="contracts the antisymmetrized tensorTrain with the vectors."
(*assumes the first tensor factor is Antisymmetric[{1,2}]*)
EvaluateAntisymmetrizedTensorTrain[tensorTrain_List,vectors_List]/;Depth[vectors]==3:=
 Switch[
  Length[tensorTrain],
  1,EvaluateTensorTrain[tensorTrain,vectors],
  2,
   (EvaluateTensorTrain[tensorTrain,vectors]
   -EvaluateTensorTrain[tensorTrain,vectors[[{3,2,1}]]]
   -EvaluateTensorTrain[tensorTrain,vectors[[{1,3,2}]]])/3
 ]


EvaluateSymmetrizedTensorTrain::usage="evaluates the symmetrized tensor train representation of CG((\[Lambda],...,\[Lambda]),\[Gamma]s) at the inputs (x,...,x)."
EvaluateSymmetrizedTensorTrain[tensorTrain_List,vector_List?VectorQ]:=
 If[
  tensorTrain==={1},
  vector,
  Chop@Fold[Dot[vector,Dot[#1,#2]]&,vector,tensorTrain]
 ]


End[];


EndPackage[];
