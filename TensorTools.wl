(* ::Package:: *)

BeginPackage["TensorTools`",{"CombinatoricsTools`"}];


EvaluateTensorTrain
EvaluateAntisymmetrizedTensorTrain
EvaluateSymmetrizedTensorTrain
EvaluateAntisymmetrizedTensorTree
EvaluateYoungSymmetrizedTensorTree


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


ContractVectors[vector1_,{vector2_,tensor_}]:=Dot[vector2,Dot[vector1,tensor]]


(* ::Subsubsection:: *)
(*Public Functions*)


EvaluateTensorTrain::usage="evaluates the tensorTrain at the vectors."
EvaluateTensorTrain[{1},vectors_List]:=First@vectors
EvaluateTensorTrain[tensorTrain_List,vectors_List]:=Fold[ContractVectors,First@vectors,Transpose[{vectors[[2;;1+Length@tensorTrain]],tensorTrain}]]


EvaluateAntisymmetrizedTensorTrain::usage="contracts the antisymmetrized tensorTrain with the vectors."
(*assumes the first tensor factor is Antisymmetric[{1,2}]*)
(*have to Take the appropriate number of vectors to contract, but this is done automatically*)
EvaluateAntisymmetrizedTensorTrain[tensorTrain_List,vectors_List]:=
 Switch[
  Length[tensorTrain],
  1,EvaluateTensorTrain[tensorTrain,vectors],
  2,
   (EvaluateTensorTrain[tensorTrain,vectors[[{1,2,3}]]]
   -EvaluateTensorTrain[tensorTrain,vectors[[{3,2,1}]]]
   -EvaluateTensorTrain[tensorTrain,vectors[[{1,3,2}]]])/3,
  3,
   (EvaluateTensorTrain[tensorTrain,vectors[[{1,2,3}]]]
   -EvaluateTensorTrain[tensorTrain,vectors[[{3,2,1}]]]
   -EvaluateTensorTrain[tensorTrain,vectors[[{1,3,2}]]])/3,(*TODO: fix this*)
  4,
   (EvaluateTensorTrain[tensorTrain,vectors[[{1,2,3}]]]
   -EvaluateTensorTrain[tensorTrain,vectors[[{3,2,1}]]]
   -EvaluateTensorTrain[tensorTrain,vectors[[{1,3,2}]]])/3(*TODO: fix this*)
 ]


EvaluateSymmetrizedTensorTrain::usage="evaluates the symmetrized tensor train representation of CG((\[Lambda],...,\[Lambda]),\[Gamma]s) at the inputs (x,...,x)."
EvaluateSymmetrizedTensorTrain[tensorTrain_List,vector_List?VectorQ]:=
 If[
  tensorTrain==={1},
  vector,
  Fold[Dot[vector,Dot[#1,#2]]&,vector,tensorTrain]
 ]


EvaluateAntisymmetrizedTensorTree[tensorTrees_Association,vectors_List]:=
 With[
  {interiorVectors=Map[EvaluateAntisymmetrizedTensorTrain[#,vectors]&,tensorTrees[["leafObjects"]],{2}]},
  
  MapThread[EvaluateTensorTrain,{tensorTrees[["interiorTensorTrains"]],interiorVectors}]
 ]


(*check that powers is weakly increasing and numerical*)
SymmetrizedMonomialCP[powers_List]/;
 VectorQ[powers,Positive]:=
  SymmetrizedMonomialCP[powers]=
   With[
    {ds=ReplacePart[powers,1->0]},
    {\[Zeta]s=Exp[(2\[Pi]*I)/(ds+1)]},
    {grid=Sequence@@(\[Zeta]s^Range[0,ds])},
    
    <|
     "globalCoefficient"->1/(Times@@(ds+1)*Multinomial@@powers),
     "localCoefficients"->Flatten[Outer[Times,grid]],
     "localVariables"->Function[variables,Flatten[Outer[{##} . variables&,grid],Length@powers-1]]
    |>
   ]


SymmetrizedMonomialCP[variables_List,powers_List]:=
 With[
  {assoc=SymmetrizedMonomialCP[powers]},
   
  {
   assoc[["globalCoefficient"]],
   Transpose[
    {
     assoc[["localCoefficients"]],
     assoc[["localVariables"]][variables]
    }
   ]
  }
 ]


PartiallySymmetrizedMonomialCP[variables_List,SSYT_List]:=
 Transpose@MapThread[
  SymmetrizedMonomialCP,
  {(variables[[#]]&)/@First/@SSYT,Last/@SSYT}
 ]


EvaluateYoungSymmetrizedTensorTree[tensorTrees_Association,SSYTs_List,variables_List]:=
 If[
  SSYTs=={{}},
  ConstantArray[{{{1}}},Length@variables],
  With[
   {
    (*variables; SSYTs; globalCoefficient, localCoefficientsVariables*)
    CPData=Outer[PartiallySymmetrizedMonomialCP,variables,SSYTs,1]
   },
   
   (*
   Level 1: variables
   Level 2: SSYTs
   Level 3: tensorTrees
   Object:  vector
   *)
   Map[
    Times@@#[[1]]*IteratedSum[Times@@(First/@{##})*EvaluateAntisymmetrizedTensorTree[tensorTrees,Last/@{##}]&,#[[2]]]&,
    CPData,
    {2}
   ]
  ]
 ]


End[];


EndPackage[];
