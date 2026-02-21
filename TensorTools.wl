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


ContractVectors[vector1_?VectorQ,{vector2_?VectorQ,tensor_?ArrayQ}]:=Dot[vector2,Dot[vector1,tensor]]


(* ::Subsubsection:: *)
(*Public Functions*)


(*add input checks*)
EvaluateTensorTrain::usage="evaluates the tensorTrain at the vectors."
EvaluateTensorTrain[tensorTrain_List,vectors__]:=EvaluateTensorTrain[tensorTrain,{vectors}]
EvaluateTensorTrain[tensorTrain_List,vectors_List]:=
 If[
  tensorTrain==={1},
  First@vectors,
  Chop@Fold[ContractVectors,First@vectors,Transpose[{vectors[[2;;1+Length@tensorTrain]],tensorTrain}]]
 ]


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
   -EvaluateTensorTrain[tensorTrain,vectors[[{1,3,2}]]])/3
 ]


EvaluateSymmetrizedTensorTrain::usage="evaluates the symmetrized tensor train representation of CG((\[Lambda],...,\[Lambda]),\[Gamma]s) at the inputs (x,...,x)."
EvaluateSymmetrizedTensorTrain[tensorTrain_List,vector_List?VectorQ]:=
 If[
  tensorTrain==={1},
  vector,
  Chop@Fold[Dot[vector,Dot[#1,#2]]&,vector,tensorTrain]
 ]


EvaluateAntisymmetrizedTensorTree[tensorTrees_Association,vectors_List]:=
 With[
  {interiorVectors=Map[EvaluateAntisymmetrizedTensorTrain[#,vectors]&,tensorTrees[["leafObjects"]],{2}]},
  
  MapThread[EvaluateTensorTrain,{tensorTrees[["interiorTensorTrains"]],interiorVectors}]
 ]


MonomialQ[variables_List,powers_List]:=
 Length@variables==Length@powers\[And]
 VectorQ[powers,PositiveIntegerQ]


SymmetrizedMonomialCP[variables_List,powers_List]/;MonomialQ[variables,powers]:=
 With[
  {ds=N@ReplacePart[Sort@powers,1->0]},
  {\[Zeta]s=Exp[(2\[Pi]*I)/(ds+1)]},
  {grid=Sequence@@(\[Zeta]s^Range[0,ds])},
  
  {
   1/(Times@@(ds+1)*Multinomial@@N@powers),(*global coefficient*)
   Chop@Transpose[
    {
     Flatten[Outer[Times,grid]],(*local coefficients*)
     Flatten[Outer[{##} . variables[[Ordering@powers]]&,grid],Length@ds-1](*local variables*)
    }
   ]
  }
 ]


PartiallySymmetrizedMonomialCP[variables_List][SSYT_List]:=PartiallySymmetrizedMonomialCP[variables,SSYT]
PartiallySymmetrizedMonomialCP[variables_List,SSYT_List]:=
 With[
  {conjugateTableau=ConjugateTableau@SSYT},(*eventually, move these up as Map[ConjugateTableau,SSYTs,blah], same with below. maybe we can merge this function with EvaluateYoungSYmmetrizedTensorTree*)
  {
   powersList=Values@*Counts/@conjugateTableau,
   variablesList=variables[[DeleteDuplicates[#]]]&/@conjugateTableau
  },
  
  Transpose@MapThread[SymmetrizedMonomialCP,{variablesList,powersList}]
 ]


EvaluateYoungSymmetrizedTensorTree[tensorTrees_Association,SSYTs_List,variables_List]:=
 If[
  SSYTs=={{}},
  ConstantArray[{{{1}}},Length@variables],
  With[
   {
    (*
    Level 1: variables
    Level 2: SSYTs
    Object:  
    *)
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
